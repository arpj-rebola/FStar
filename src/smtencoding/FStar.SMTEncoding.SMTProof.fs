#light "off"

module FStar.SMTEncoding.SMTProof
open FStar
open FStar.All
open FStar.Range
open FStar.Util
open FStar.SMTEncoding.SMTProof
module ST = FStar.SMTEncoding.Term

type smt_term =
    | SMTBoundVariable of int
    | SMTApplication of operator * list<smt_term>
    | SMTInteger of string
    | SMTBoolean of string
    | SMTBinding of quantifier * list<sort> * smt_term

type smt_proof =
    | SMTMeta of string
    | SMTSkolemization of smt_term
    | SMTNnf
    | SMTArbitrary of smt_proof * smt_term
    | SMTGeneralization of smt_term  //Can these two be post-hoc merged?
    | SMTPremise of string
    | SMTResolution of list<smt_proof> * smt_term
    | SMTCongruence of list<smt_proof> * smt_term
    | SMTInstantiation of list<smt_term> * smt_term
    | SMTRewrite of smt_term
    | SMTArithmetics of smt_term

type smt_declaration =
    | SMTFunctionDeclaration of string * list<sort> * sort
    | SMTMacroDefinition of string * list<sort> * sort * smt_term
    | SMTTermDefinition of string * list<sort> * smt_term
    | SMTMetaDefinition of string * smt_proof

type smt_derivation = list<smt_declaration>

type smt_derivation_info = {
    smt_derivation_info_table : smap<smt_declaration> ;
    smt_derivation_info_hash : smap<int> ;
    smt_derivation_info_assertions : ref<(list<(int * string)>)> ;
}

let hash_of_int_list (l : list<int>) : int =
    let aux ((sum , prod , xoor) : int * int * int) (x : int) : int * int * int =
        (sum + x , prod * x , xoor ^^^ x)
    in
    let (s , p , x) : int * int * int = List.fold_left aux (0 , 1 , 0) l in
    1023 * s + p ^^^ (31 * x)

let rec hash_list_of_smt_term (info : smt_derivation_info) (n : int) (pars : list<(list<int>)>) (t : smt_term) : list<int> =
    match t with
        | SMTBoundVariable x -> if x > n then [500 + (x - n)] else List.nth pars (x - 1)
        | SMTApplication (DefinedTerm s , args) -> begin
            let h_args : list<(list<int>)> = List.map (hash_list_of_smt_term info n pars) args in
            match smap_try_find info.smt_derivation_info_table s with
                | Some (SMTTermDefinition (_ , _ , tx))
                | Some (SMTMacroDefinition (_ , _ , _ , tx)) ->
                    hash_list_of_smt_term info (List.length args) h_args tx
                | _ -> failwith "Impossible"
        end
        | SMTApplication (o , args) -> (hash_of_operator o) :: (List.map (hash_list_of_smt_term info n pars) args)
        | SMTInteger s -> [310 , hashcode s]
        | SMTBoolean True -> [311]
        | SMTBoolean False -> [312]
        | SMTBinding (q , bs , scp) -> ((hash_of_quantifier q) :: (List.map hash_of_sort bs)) @ (hash_list_of_smt_term info n pars scp)

let hash_list_of_smt_proof (info : smt_derivation_info) (p : smt_proof) : list<int> =
    match t with
        | SMTMeta s -> begin
            match smap_try_find info.smt_derivation_info_table s with
                | Some SMTMetaDefinition (_ , px) -> hash_list_of_smt_proof info px
                | _ -> failwith "Impossible"
        | SMTSkolemization q -> 900 :: (hash_list_of_smt_proof info q)
        | SMTNnf -> 901
        | SMTArbitrary (q , r) -> (902 :: (hash_list_of_smt_proof info q)) @ (hash_list_of_smt_term info 0 [] r)
        | SMTGeneralization r -> 903 :: (hash_list_of_smt_term info 0 [] r)
        | SMTPremise s -> 904 :: (hashcode s)
        | SMTResolution (qs , r) -> (905 :: (List.concat (hash_list_of_smt_proof info) qs)) @ (hash_list_of_smt_term info 0 [] r)
        | SMTCongruence (qs , r) -> (906 :: (List.concat (hash_list_of_smt_proof info) qs)) @ (hash_list_of_smt_term info 0 [] r)
        | SMTInstantiation (insts , r) -> (907 :: (List.concat (hash_list_of_smt_term info) insts)) @ (hash_list_of_smt_term info 0 [] r)
        | SMTRewrite r -> 908 :: (hash_list_of_smt_term info 0 [] r)
        | SMTArithmetics r -> 909 :: (hash_list_of_smt_term info 0 [] r)

let smt_derivation_from_declarations (info : smt_derivation_info) (ds : list<ST.decl>) : smt_derivation =
    let table : smap<smt_declaration> = info.smt_derivation_info_table in
    let hash : smap<int> = info.smt_derivation_info_hash in
    let assertions : ref<(list<(int * string)>)> = info.smt_derivation_info_assertions in
    let add_to_table (nm : string) (d : smt_declaration) : unit =
        match smap_try_find table nm with
            | Some _ -> failwith ("Repeated identifier " ^ nm)
            | None -> smap_add table nm d
    in
    let add_to_assertions (nm : string) (tm : smt_term) : unit =
        if for_some (fun (h , s) -> s = nm) !assertions then
            failwith "Repeated assertion name"
        else
            assertions := (hash_list_of_smt_term info 0 [] tm , nm)
    in
    let term_sort_to_smt_sort (s : ST.sort) : sort =
        match s with
            | Bool_sort -> Boolean
            | Int_sort -> Integer
            | String_sort -> String
            | Term_sort -> Term
            | Fuel_sort -> Fuel
            | _ -> failwith "Unrecognized sort"
    in
    let term_operator_to_smt_operator (o : ST.op) : operator =
        match o with
            | Not -> Negation
            | And
            | Or
            | Imp
            | Iff
            | Eq
            | LT
            | LTE
            | GT
            | GTE
            | Add
            | Sub
            | Div
            | Mul
            | Minus
            | Mod
            | BvAnd
            | BvXor
            | BvOr
            | BvAdd
            | BvSub
            | BvShl
            | BvShr  // unsigned shift right\
            | BvUdiv
            | BvMod
            | BvMul
            | BvUlt
            | BvUext of Prims.int
            | NatToBv of Prims.int // need to explicitly define the size of the bitvector
            | BvToNat
            | ITE
            | Var of string //Op corresponding to a user/encoding-defined uninterpreted function
    let term_quantifier_to_smt_quantifier (q : ST.qop) : quantifier =
        match q with
            | ST.Forall -> Forall
            | ST.Exists -> Exists
    in
    let smt_term_from_term (t : ST.term) : smt_term =
        match t.tm with
            | Integer s -> SMTInteger s
            | BoundV n -> SMTBoundVariable n
            | FreeV (var , st) -> failwith "Finalized SMT terms should not contain free variables"
            | App (o , args) ->

            | Quant (q , _ , _ , bs , scp , _) ->

            | Let (bs , scp) ->

            | Labeled (tx , _, _)
            | LblPos (tx , _) -> smt_term_from_term tx

    in
    let add_function_declaration (nm : string) (sg : list<ST.sort>) (st : ST.sort) (o : smt_derivation) : smt_derivation =
        let d : smt_declaration = SMTFunctionDeclaration (nm , List.map term_sort_to_smt_sort sg , term_sort_to_smt_sort st) in
        add_to_table nm d ;
        d :: o        
    in
    let add_macro_definition (nm : string) (sg : list<ST.sort>) (st : ST.sort) (tm : ST.term) (o : smt_derivation) : smt_derivation =
        let (px , tmx) : smt_derivation * smt_term = smt_term_from_term tm in
        let d : smt_declaration = SMTMacroDefinition (nm , List.map term_sort_to_smt_sort sg , term_sort_to_smt_sort st , tmx) in
        add_to_table nm d ;
        (d :: px) @ o
    in
    let add_assertion (a : ST.assumption) (o : smt_derivation) : smt_derivation =
        let (px , tmx) : smt_derivation * smt_term = smt_term_from_term a.assumption_term in
        let nm : string = a.assumption_name in
        let d : smt_declaration = SMTTermDefinition (nm , [] , tmx)
        add_to_table nm d ;
        add_to_assertions nm tmx ;
        (d :: px) @ o
    in
    let rec aux (i : list<ST.decl>) (o : smt_derivation) : smt_derivation =
        match i with
            | ST.DefPrelude :: tl -> aux (preludeDecls @ tl) o
            | ST.DeclFun (nm , sg , st , _) :: tl ->
                aux tl (add_function_declaration nm sg st o)
            | ST.DefineFun (nm , sg , st , tm , _) :: tl ->
                aux tl (add_macro_definition nm sg st tm o)
            | Assume a :: tl ->
                aux tl (add_assertion a o)
            | Module (_ , l) :: tl -> aux (l @ tl) o
            | _ :: tl -> aux tl o
            | [] -> List.rev o
    in
    aux (smap_create 1000) ds []
    