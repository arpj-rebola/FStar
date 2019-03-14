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

let rec hash_list_of_smt_term (dict : smap<int>) (t : smt_term) : list<int> =
    match t with
        | SMTBoundVariable x -> [500 + x]
        | SMTApplication (o , args) -> (hash_of_operator dict o) :: (List.map (hash_list_of_smt_term dict) args)
        | SMTInteger s -> [310 , hashcode s]
        | SMTBoolean True -> [311]
        | SMTBoolean False -> [312]
        | SMTBinding (q , bs , scp) -> ((hash_of_quantifier q) :: (List.map hash_of_sort bs)) @ (hash_list_of_smt_term dict scp)

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

let hash_list_of_smt_proof (dict : smap<int>) (p : smt_proof) : list<int> =
    match t with
        | SMTMeta s -> [dict s]
        | SMTSkolemization q -> 900 :: (hash_list_of_smt_proof dict q)
        | SMTNnf -> 901
        | SMTArbitrary (q , r) -> (902 :: (hash_list_of_smt_proof dict q)) @ (hash_list_of_smt_term dict r)
        | SMTGeneralization r -> 903 :: (hash_list_of_smt_term dict r)
        | SMTPremise s -> 904 :: (hashcode s)
        | SMTResolution (qs , r) -> (905 :: (List.concat (hash_list_of_smt_proof dict) qs)) @ (hash_list_of_smt_term dict r)
        | SMTCongruence (qs , r) -> (906 :: (List.concat (hash_list_of_smt_proof dict) qs)) @ (hash_list_of_smt_term dict r)
        | SMTInstantiation (insts , r) -> (907 :: (List.concat (hash_list_of_smt_term dict) insts)) @ (hash_list_of_smt_term dict r)
        | SMTRewrite r -> 908 :: (hash_list_of_smt_term r)
        | SMTArithmetics r -> 909 :: (hash_list_of_smt_term r)

type smt_declaration =
    | SMTFunctionDeclaration of string * list<sort> * sort
    | SMTMacroDefinition of string * list<sort> * sort * smt_term
    | SMTTermDefinition of string * list<sort> * sort * smt_term
    | SMTMetaDefinition of string * list<sort> * sort * smt_proof

type smt_proof = list<smt_declaration>

type smt_proof_info = {
    smt_proof_info_table : smap<smt_declaration> ;
    smt_proof_info_hash : smap<int> ;
    smt_proof_info_assertions : ref<(list<(int * string)>)> ;
}

let smt_proof_from_declarations (info : smt_proof_info) (ds : list<ST.decl>) : smt_proof =
    let table : smap<smt_declaration> = info.smt_proof_info_table in
    let hash : smap<int> = info.smt_proof_info_hash in
    let assertions : ref<(list<(int * string)>)> = info.smt_proof_info_assertions in
    let term_sort_to_smt_sort (s : ST.sort) : sort =
        match s with
          | Bool_sort -> Boolean
          | Int_sort -> Integer
          | String_sort -> String
          | Term_sort -> Term
          | Fuel_sort -> Fuel
          | _ -> failwith "Unrecognized sort"
    in
    let add_function_declaration (nm : string) (sg : list<ST.sort>) (st : ST.sort) (o : smt_proof) : smt_proof =
        let d : smt_declaration = SMTFunctionDeclaration (nm , List.map term_sort_to_smt_sort sg , term_sort_to_smt_sort st) in
        begin match smap_try_find table nm with
            | Some _ -> failwith ("Repeated identifier " ^ nm)
            | None -> smap_add table nm d
        end ;
        d :: o        
    in
    let add_macro_definition (nm : string) (sg : list<ST.sort>) (st : ST.sort) (tm : ST.term) (o : smt_proof) : smt_proof =
        let tmx : smt_term = smt_term_from_term sg tm in
        let d : smt_declaration = SMTMacroDefinition (nm , List.map term_sort_to_smt_sort sg , term_sort_to_smt_sort st , smt_term_from_term tm) in
        begin match smap_try_find table nm with
            | Some _ -> failwith ("Repeated identifier " ^ nm)
            | None -> smap_add table nm d
        end ;
        d :: o
    in
    let add_assertion (a : ST.assumption) (o : smt_proof) : smt_proof =


    in

    let rec aux (i : list<ST.decl>) (o : smt_proof) : smt_proof =
        match i with
            | ST.DefPrelude :: tl -> aux (preludeDecls @ tl) o
            | ST.DeclFun (nm , sg , st , _) ->
                aux tl (add_function_declaration nm sg st o)
            | ST.DefineFun (nm , sg , st , tm , _) ->
                aux tl (add_macro_definition nm sg st tm o)
            | Assume a ->
                aux tl (add_assertion a o)
            | 
            | _ :: tl -> aux tl o
            | [] -> List.rev o
    in
    aux (smap_create 1000) ds []
    