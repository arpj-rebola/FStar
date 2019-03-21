#light "off"

module FStar.SMTEncoding.SMTProof
open FStar
open FStar.All
open FStar.Range
open FStar.Util
open FStar.SMTEncoding.RawProof
open FStar.SMTEncoding.Z3
open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing

module PP = FStar.SMTEncoding.ProofParser
module PL = FStar.SMTEncoding.ProofLexer
module ST = FStar.SMTEncoding.Term

type smt_term =
    | SMTBoundVariable of int
    | SMTApplication of operator * list<smt_term>
    | SMTInteger of string
    | SMTBoolean of bool
    | SMTBinding of quantifier * list<sort> * smt_term
    | SMTFuel of option<smt_term>

// let rec string_of_smt_term (k : int) (level : int) (t : smt_term) : string =
//     let new_line (kk : int) : string = "\n" ^ (repeat kk "\t") in
//     match t with
//         | SMTBoundVariable n -> "@@" ^ (string_of_int n)
//         | SMTApplication (Branch , [cond ; thn ; els ]) ->
//             "(" ^ (string_of_smt_term k level cond) ^ " ? " ^ (string_of_smt_term k level thn) ^ " : " ^ (string_of_smt_term k level els) ^ ")"
//         | SMTApplication (o , args) when infix_operator o ->
//             let opening : string = if List.isEmpty args then "" else "(" in
//             let closing : string = if List.isEmpty args then "" else ")" in
//             opening ^ (String.concat (" " ^ (string_of_operator o) ^ " ") (List.map (string_of_smt_term k level) args)) ^ closing
//         | SMTApplication (o , args) ->
//             let opening : string = if List.isEmpty args then "" else "(" in
//             let closing : string = if List.isEmpty args then "" else ")" in
//             let ss : list<string> = (string_of_operator o) :: (List.map (string_of_smt_term k level) args) in
//             opening ^ (String.concat " " ss) ^ closing
//         | SMTInteger s -> s
//         | SMTBoolean true -> "True"
//         | SMTBoolean false -> "False"
//         | SMTBinding (q , bd , scp) ->
//             let (kx , bdx) : int * list<string> =
//                 fold_n_map (fun (kk : int) (s : sort) -> (kk + 1 , "(@@" ^ (string_of_int (kk + 1)) ^ " : " ^ (string_of_sort s) ^ ")")) k bd
//             in
//             let ss : list<string> = (string_of_quantifier q) :: bdx in
//             "{" ^ (String.concat " " ss) ^ " ." ^ (new_line (level + 1)) ^ (string_of_smt_term kx (level + 1) scp) ^ (new_line level) ^ "}"
//         | SMTFuel None -> "0F"        
//         | SMTFuel (Some f) -> "(" ^ (string_of_smt_term k level f) ^ " ++ 1F)"

type smt_proof =
    | SMTMeta of string
    | SMTPremise of string
    | SMTSkolemization of smt_term
    | SMTRewriting of smt_term
    | SMTNnf of list<smt_proof> * smt_term
    | SMTResolution of list<smt_proof> * smt_term
    | SMTCongruence of list<smt_proof> * smt_term
    | SMTGeneralization of smt_proof * smt_term
    | SMTInstantiation of list<smt_term> * smt_term
    | SMTArithmetics of list<smt_term> * list<smt_term>

// let rec string_of_smt_proof (k : int) (level : int) (pf : smt_proof) : string =
//     let new_line (kk : int) : string = "\n" ^ (repeat kk "\t") in
//     match pf with
//         | SMTDefinedMeta s -> "$" ^ s
//         | SMTPremise s -> "[Premise: " ^ s ^ "]"
//         | SMTSkolemization t -> "[Skolem: " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTRewriting t -> "[Rewriting: " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTNnf (ps , t) -> "[Nnf from " ^ (String.concat " , " (List.map (string_of_smt_proof k level) ps)) ^ " : " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTResolution (ps , t) -> "[Resolution from " ^ (String.concat " , " (List.map (string_of_smt_proof k level) ps)) ^ " : " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTCongruence (ps , t) -> "[Congruence from " ^ (String.concat " , " (List.map (string_of_smt_proof k level) ps)) ^ " : " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTGeneralization (p , t) -> "[Generalization from " ^ (string_of_smt_proof k level p) ^ " : " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTInstantiation (ts , t) -> "[Congruence from " ^ (String.concat " , " (List.map (string_of_smt_term k level) ts)) ^ " : " ^ (string_of_smt_term k level t) ^ "]"
//         | SMTArithmetics (ts , rs) ->
//             "[Arithmetics from " ^ (String.concat " , " (List.map (string_of_smt_term k level) ts)) ^ " : " ^ (String.concat " , " (List.map (string_of_smt_term k level) rs)) ^ "]"

// type smt_pt = either<smt_proof , smt_term>

type smt_pt =
    | SMTTerm of smt_term
    | SMTProof of smt_proof

let as_proof (pt : smt_pt) : smt_proof =
    match pt with
        | SMTTerm t -> failwith "Tried to assign proof type to a term"
        | SMTProof p -> p

let as_term (pt : smt_pt) : smt_proof =
    match pt with
        | SMTTerm t -> t
        | SMTProof p -> failwith "Tried to assign term type to a proof"

type smt_uninterpreted = {
    smt_uninterpreted_name : string ;
    smt_uninterpreted_signature : list<sort> ;
    smt_uninterpreted_sort : sort ;
}

type smt_term_macro = {
    smt_term_macro_name : string ;
    smt_term_macro_arguments : int ;
    smt_term_macro_definition : smt_term ;
    smt_term_macro_fundef : bool ;
}

type smt_meta_macro = {
    smt_meta_macro_name : string ;
    smt_meta_macro_arguments : int ;
    smt_meta_macro_definition : smt_proof ;
}

type smt_declaration =
    | SMTUninterpretedFunction of smt_uninterpreted ;
    | SMTTermMacro of smt_term_macro ;
    | SMTMetaMacro of smt_meta_macro

type smt_derivation = {
    smt_derivation_table : smap<smt_declaration> ;
    smt_derivation_assertions : ref<(list<string>)> ;
    smt_derivation_count : ref<int> ;
    smt_derivation_sequence : ref<(list<string>)> ;
}

// let string_of_smt_derivation (info : smt_derivation_info) (dv : smt_derivation) : string =
//     let aux_signature (sg : list<sort>): string =
//         let f (k : int) (s : sort) : int * string = (k + 1 , "(@@" ^ (string_of_int (k + 1)) ^ " : " ^ (string_of_sort s) ^ ")") in
//         let (_ , ss) : int * list<string> = fold_n_map f 0 sg in
//         String.concat " " ss
//     in
//     let aux_decl (d : smt_declaration) : string =
//         match d with
//             | SMTFunctionDeclaration (nm , sg , st) ->
//                 "[Declare] " ^ nm ^ " : " ^ (String.concat " * " (List.map string_of_sort sg)) ^ (if List.isEmpty sg then "" else " -> ") ^ (string_of_sort st) ^ "\n"
//             | SMTMacroDefinition (nm , sg , _ , df) ->
//                 "[Define ] #" ^ nm ^ " " ^ (aux_signature sg) ^ (if List.isEmpty sg then "" else " ") ^ ":=\n\t" ^ (string_of_smt_term (List.length sg) 1 df) ^ "\n"
//             | SMTTermDefinition (nm , sg , df) ->
//                 "[Define ] $" ^ nm ^ " " ^ (aux_signature sg) ^ (if List.isEmpty sg then "" else " ") ^ ":=\n\t" ^ (string_of_smt_term (List.length sg) 1 df) ^ "\n"
//             | SMTMetaDefinition (nm , df) ->
//                 "[Define ] &" ^ nm ^ " :=\n\t" ^ (string_of_smt_proof 0 1 df) ^ "\n"
//     in
//     let aux_main (o : list<string>) (s : string) : list<string> =
//         match smap_try_find info.smt_derivation_info_table s with
//             | None -> failwith "Could not find derivation identifier in derivation table"
//             | Some d -> (aux_decl d) :: o
//     in
//     let dcs : list<string> = List.fold_left aux_main [] dv in
//     let ass : list<string> = List.map (fun ((_ , s) : int * string) -> "[Premise] " ^ s) !(info.smt_derivation_info_assertions) in
//     String.concat "\n" (dcs @ ass)  

let new_smt_derivation () : smt_derivation = {
    smt_derivation_table = smap_create 1000 ;
    smt_derivation_assertions = mk_ref [] ;
    smt_derivation_count = mk_ref 0 ;
    smt_derivation_sequence = mk_ref [] ;
}

let add_to_table (dv : smt_derivation) (nm : string) (d : smt_declaration) : unit =
    match smap_try_find dv.smt_derivation_table nm with
        | Some _ -> failwith ("Tried to introduce identifier " ^ nm ^ " but it already occurs in the table")
        | None ->
            let ls : ref<(list<string>)> = dv.smt_derivation_sequence in
            ls := nm :: !ls ;
            smap_add dv.smt_derivation_table nm d ;


let add_to_assertions (dv : smt_derivation) (nm : string) (d : smt_declaration) : unit =
    let ls : ref<(list<string>)> = dv.smt_derivation_assertions in
    ls := nm :: !ls

let find_in_table (dv : smt_derivation) (nm : string) : option<smt_declaration> =
    smap_try_find dv.smt_derivation_table nm

let new_name (dv : smt_derivation) (prefix : string) : string =
    let x : int = !(dv.smt_derivation_count) in
    incr dv.smt_derivation_count ;
    prefix ^ (string_of_int x)

let new_term_name (dv : smt_derivation) : string = new_name dv "$tm"
let new_proof_name (dv : smt_derivation) : string = new_name dv "$pf"
let new_skolem_name (dv : smt_derivation) : string = new_name dv "$sk"
let is_term_name (s : string) : bool = starts_with s "$tm"
let is_proof_name (s : string) : bool = starts_with s "$pf"
let is_skolem_name (s : string) : bool = starts_with s "$sk"

let arguments_from_context (n : int) (ctx: list<smt_term>) : list<smt_term> =
    let rec aux (m : int) (i : list<smt_term>) (o : smt_term) : list<smt_term> =
        if m <= 0 then List.rev o else aux (m - 1) (List.tl i) ((List.hd i) :: o)
    in
    aux n ctx []

let add_to_context (n : int) (ctx : list<smt_term>) : list<smt_term> =
    let nn : int = List.length ctx in
    let rec aux (m : int) (acc : list<smt_term>) : list<smt_term> =
        if m < n then aux (m + 1) ((SMTBoundVariable (m + nn)) :: acc) else List.rev acc
    in
    ctx @ (aux 0 [])

let term_sort_to_smt_sort (s : ST.sort) : sort =
    match s with
        | ST.Bool_sort -> Boolean
        | ST.Int_sort -> Integer
        | ST.String_sort -> String
        | ST.Term_sort -> Term
        | ST.Fuel_sort -> Fuel
        | _ -> failwith "Unrecognized sort"

let term_operator_to_smt_operator (o : ST.op) : operator =
    match o with
        | ST.Not -> Negation
        | ST.And -> Conjunction
        | ST.Or -> Disjunction
        | ST.Imp -> Implication
        | ST.Iff -> Equality
        | ST.ITE -> Branch
        | ST.Eq -> Equality
        | ST.LT -> LtInequality
        | ST.LTE -> LeqInequality
        | ST.GT -> GtInequality
        | ST.GTE -> GeqInequality
        | ST.Add -> Addition
        | ST.Mul -> Product
        | ST.Div -> Division
        | ST.Minus -> Opposite
        | ST.Sub -> Substraction
        | ST.Mod -> Remainder
        | ST.TrueOp
        | ST.FalseOp -> failwith "Boolean term operators cannot be matched to SMT operators"
        | ST.BvAnd
        | ST.BvXor
        | ST.BvOr
        | ST.BvAdd
        | ST.BvSub
        | ST.BvShl
        | ST.BvShr
        | ST.BvUdiv
        | ST.BvMod
        | ST.BvMul
        | ST.BvUlt
        | ST.BvToNat
        | ST.BvUext _
        | ST.NatToBv _ -> failwith "Bit-vector term operators cannot be matched to SMT operators"
        | ST.Var _ -> failwith "Uninterpreted term operators cannot be immediately matched to SMT operators"

let term_quantifier_to_smt_quantifier (q : ST.qop) : quantifier =
    match q with
        | ST.Forall -> Forall
        | ST.Exists -> Exists

let term_term_to_smt_term (dv : smt_derivation) (id : string) (tm : ST.term) : smt_term =
    let count : ref<int> = mk_ref 0 in
    let aux (mt : list<(either<string , int>)>) (ctx : list<smt_term>) (t : ST.term) : smt_term =
        match t.tm with
            | ST.Integer s -> SMTInteger s
            | ST.BoundV n -> begin match List.nth mt n with
                | Inl s -> begin match find_in_table dv s with
                    | Some (SMTTermMacro mc) ->
                        let arity : int = mc.smt_term_macro_arguments in
                        SMTApplication (Macro s , arguments_from_context arity ctx)
                    | _ -> failwith ("Could not appropriately match identifier '" ^ s ^ "' in the table")
                end
                | Inr k -> SMTBoundVariable k
            end
            | ST.App (TrueOp , _) -> SMTBoolean true
            | ST.App (FalseOp , _) -> SMTBoolean false
            | ST.App (ST.Var "ZFuel" , _) -> SMTFuel None
            | ST.App (ST.Var "SFuel" , args) -> SMTFuel (Some (aux mt ctx (List.hd args)))
            | ST.App (ST.Var s , args) -> begin match find_in_table dv s with
                | Some (SMTUninterpretedFunction uf) ->
                    SMTApplication (s , List.map (aux mt ctx) args)
                | Some (SMTTermMacro mc) when mc.smt_term_macro_fundef ->
                    SMTApplication (Macro s , List.map (aux mt ctx) args)
                | _ -> failwith ("Could not appropriately match identifier '" ^ s ^ "' in the table")
            end
            | ST.Quant (q , _ , _ , bd , scp) ->
                let q' : quantifier = term_quantifier_to_smt_quantifier q in
                let bd' : list<sort> = List.map term_sort_to_smt_sort bd in
                let mt' : list<(either<string , int>)> = 
                    let bdl : int = List.length bd ;
                    let rec f (n : int) (c : int) (o : list<(either<string , int>)>) : list<(either<string , int>)> =
                        if n < bdl then f (n + 1) (c + 1) ((Inr c) :: o) else List.rev o
                    in
                    mt @ (List.rev (f 0 (List.length ctx + 1) []))
                in
                let scp' : smt_term = aux mt' (ctx @ bd') scp in
                SMTBinding (q' , bd' , scp')
            | ST.Let (bd , scp) ->
                let n : int = List.length ctx in
                let mt' : list<(either<string , int>)> =
                    let f (b : ST.term) : either<string , int> =
                        let df : smt_term = aux mt ctx b in
                        incr count ;
                        let nm : string = "$" ^ id ^ "#" ^ (string_of_int !count) in
                        let mc : smt_term_macro = {
                            smt_term_macro_name = nm ;
                            smt_term_macro_arguments = n ;
                            smt_term_macro_definition = df ;
                        }
                        add_to_table nm (SMTTermMacro mc) ;
                        Inl nm
                    in
                    mt @ (List.map f bd)
                in
                let ctx' : list<smt_term> = add_to_context (List.length bd) ctx in
                aux mt' ctx' scp
            | ST.Labeled (tmx , _ , _)
            | ST.LblPos (tmx , _) -> aux mt ctx tmx
            | ST.FreeV (s , _) -> begin match find_in_table dv s with
                | Some (SMTUninterpretedFunction uf) ->
                    SMTApplication (Uninterpreted uf.smt_uninterpreted_name , [])
                | Some (SMTTermMacro mc) ->
                    SMTApplication (Macro mc.smt_term_macro_name , [])
                | _ -> failwith "Free variables should not occur in closed SMT terms"
            end
    in
    count := 0 ;
    aux [] [] tm        

let process_smt_declarations (dv : smt_derivation) (ds : list<ST.decl>) : unit =
    let rec aux (i : list<ST.decl>) : unit =
        match i with
            | ST.DeclFun (nm , sg , st , _) :: tl ->
                let d : smt_uninterpreted = {
                    smt_uninterpreted_name = nm ;
                    smt_uninterpreted_signature = List.map term_sort_to_smt_sort sg ;
                    smt_uninterpreted_sort = term_sort_to_smt_sort st ;
                } in
                add_to_table dv d ;
                aux tl
            | ST.DefineFun (nm , sg , st , tm , _) :: tl ->
                let d : smt_term_macro = {
                    smt_term_macro_name = nm ;
                    smt_term_macro_arguments = List.length sg ;
                    smt_term_macro_definition = term_term_to_smt_term dv nm tm ;
                    smt_term_macro_fundef = true ;
                } in
                add_to_table dv d ;
                aux tl
            | ST.Assume a :: tl ->
                let nm : string = a.assumption_name in
                let d : smt_term_macro = {
                    smt_term_macro_name = nm ;
                    smt_term_macro_arguments = 0 ;
                    smt_term_macro_definition = term_term_to_smt_term dv nm a.assumption_term ;
                } in
                add_to_table dv d ;
                add_to_assertions dv nm ;
                aux tl
            | ST.Module (_ , l) :: tl -> aux (l @ tl)
            | _ :: tl -> aux tl
            | [] -> ()
    aux ds    

type renaming = {
    renaming_staging : ref<(list<(list<string>)>)> ;
    renaming_dictionary : smap<(ref<(list<(either<string , int>)>)>)> ;
}

let push_stage (rn : renaming) : unit =
    rn.renaming_staging := [] :: !(rn.renaming_staging) ;

let pull_stage (rn : renaming) : unit =
    let stg : list<(list<string>)> = !(rn.renaming_staging) in
    let vars : list<string> = List.hd stg in
    rn.renaming_staging := List.tl stg ;
    let f (var : string) : unit = match smap_try_find rn.renaming_dictionary var with
        | Some stkref -> stkref := List.tl !(stkref)
        | None -> failwith ("Tried to pop variable '" ^ var ^ "' from dictionary but it wasn't there")
    in
    List.iter f vars

let add_renaming (rn : renaming) (var : string) (nm : either<string , int>) : unit =
    let stg : list<(list<string>)> = !(rn.renaming_staging) in
    let stkref : ref<(list<(either<string , int>)>)> = smap_try_find rn.renaming_dictionary var with
        | Some rf -> rf
        | None ->
            let rf : ref<(list<(either<string , int>)>)> = mk_ref [] in
            smap_add rn.renaming_dictionary var rf ;
            rf
    in
    rn.renaming_staging := (var :: (List.hd stg)) :: (List.tl stg) ;
    rf := nm :: !rf

let get_renaming (rn : renaming) (var : string) : option<(either<string , int>)> =
    match smap_try_find rn.renaming_dictionary var with
        | Some rf -> Some (List.hd !rf)
        | None -> None

let process_raw_function (rn : renaming) (dv : smt_derivation) ((var , sg , st) : string * list<sort> * sort) : unit =
    let nm : string = new_skolem_name dv in
    let d : smt_uninterpreted = {
        smt_uninterpreted_name = nm ;
        smt_uninterpreted_signature = List.map term_sort_to_smt_sort sg ;
        smt_uninterpreted_sort = term_sort_to_smt_sort st ;
    } in
    add_renaming rn var (Inl nm) ;
    add_to_table dv d

let raw_proof_to_smt_proof (rn : renaming) (dv : smt_derivation) (rpf : raw_proof) : smt_pt =
    let aux (ctx : list<smt_term>) (rp : raw_proof) : smt_pt =
        match rp with
            | RawFuel o ->
                let o' : option<smt_term> = bind_opt o (fun (r : raw_proof) -> as_term (aux rn dv r)) in
                SMTTerm (SMTFuel (o'))
            | RawAbstractVar k -> TODO
            | RawApplication (Uninterpreted f , args) -> begin match get_renaming rn f with
                | Some (Inl f') ->
                    if is_skolem_name f' then
                        let args' : list<smt_term> = args |> List.map (aux ctx) |> as_term in
                        SMTTerm (SMTApplication (Uninterpreted f' , args'))
                    else aux ctx (RawApplication (Macro f' , args))
                | Some (Inr k) -> SMTTerm (SMTBoundVariable k)
                | None -> aux ctx (RawApplication (Macro f , args))
            end
            | RawApplication (Macro f , args) -> begin match find_in_table dv f with
                let args' : list<smt_term> = args |> List.map (aux ctx) |> as_term in
                | Some (SMTUninterpretedFunction uf) ->
                    SMTTerm (SMTApplication (Uninterpreted f , args'))
                | Some (SMTTermMacro mc) ->
                    if mc.smt_term_macro_fundef then
                        SMTTerm (SMTApplication (Macro f , args'))
                    else
                        let k : int = mc.smt_term_macro_arguments in
                        SMTTerm (SMTApplication (Macro f , arguments_from_context k ctx))
                | Some (SMTMetaMacro mc) -> SMTProof (SMTMeta f)
                | None -> failwith ("Could not find macro identifier '" ^ f ^ "' in table")
            end
            | RawApplication (o , args) ->
                let args' : list<smt_term> = args |> List.map (aux ctx) |> as_term in
                SMTTerm (SMTApplication (o , args'))

                




// let unroll_term (info : smt_derivation_info) (tm : smt_term) : smt_term =
//     let rec aux (n : int) (pars : list<smt_term>) (t : smt_term) : smt_term =
//         match t with
//             | SMTBoundVariable x -> if x < n then List.nth pars x else SMTBoundVariable (x - n)
//             | SMTApplication (o , args) -> begin
//                 let argsx : list<smt_term> = List.map (aux n pars) args in
//                 match o with
//                     | Macro s
//                     | DefinedTerm s -> begin match smap_try_find info.smt_derivation_info_table s with
//                         | Some (SMTTermDefinition (_ , _ , tx))
//                         | Some (SMTMacroDefinition (_ , _ , _ , tx)) -> aux (List.length argsx) argsx tx
//                         | _ -> failwith "Used DefinedTerm/Macro constructor for a parameter that does not correspond to a term definition or a function macro"
//                     end
//                     | _ -> SMTApplication (o , argsx)
//             end
//             | SMTBinding (q , bs , scp) -> SMTBinding (q , bs , aux n pars scp)
//             | SMTFuel (Some f) -> SMTFuel (Some (aux n pars f))
//             | _ -> t
//     in
//     aux 0 [] tm

// let hash_of_smt_term (info : smt_derivation_info) (tm : smt_term) : int =
//     let hash_of_int_list (l : list<int>) : int =
//         let aux ((sum , prod , xoor) : int * int * int) (x : int) : int * int * int =
//             (sum + x , prod * x , xoor ^^^ x)
//         in
//         let (s , p , x) : int * int * int = List.fold_left aux (0 , 1 , 0) l in
//         1023 * s + p ^^^ (31 * x)
//     in
//     let rec hash_list_of_smt_term (t : smt_term) : list<int> =
//         match t with
//             | SMTBoundVariable x -> [500 + x]
//             | SMTApplication (o , args) -> (hash_of_operator o) @ List.concat (List.map hash_list_of_smt_term args)
//             | SMTInteger s -> [310 ; hashcode s]
//             | SMTBoolean true -> [311]
//             | SMTBoolean false -> [312]
//             | SMTBinding (q , bs , scp) -> ((hash_of_quantifier q) :: (List.map hash_of_sort bs)) @ (hash_list_of_smt_term scp)
//             | SMTFuel None -> [313]
//             | SMTFuel (Some f) -> 314 :: (hash_list_of_smt_term f)
//     in
//     tm |> unroll_term info |> hash_list_of_smt_term |> hash_of_int_list

// let equal_smt_terms (info : smt_derivation_info) (tm1 : smt_term) (tm2 : smt_term) : bool =
//     (unroll_term info tm1) = (unroll_term info tm2)


type staging = list<(list<string>)>
type matching = either<(string * list<smt_term>) , int>
type renaming = smap<(ref<(list<matching>)>)>

let smt_derivation_from_declarations (info : smt_derivation_info) (deriv : smt_derivation) (ds : list<ST.decl>) : smt_derivation =
    let table : smap<smt_declaration> = info.smt_derivation_info_table in
    let assertions : ref<(list<(int * string)>)> = info.smt_derivation_info_assertions in
    let term_sort_to_smt_sort (s : ST.sort) : sort =
        match s with
            | ST.Bool_sort -> Boolean
            | ST.Int_sort -> Integer
            | ST.String_sort -> String
            | ST.Term_sort -> Term
            | ST.Fuel_sort -> Fuel
            | _ -> failwith "Unrecognized sort"
    in
    let term_operator_to_smt_operator (o : ST.op) : operator =
        match o with
            | ST.Not -> Negation
            | ST.And -> Conjunction
            | ST.Or -> Disjunction
            | ST.Imp -> Implication
            | ST.Iff -> Equality
            | ST.ITE -> Branch
            | ST.Eq -> Equality
            | ST.LT -> LtInequality
            | ST.LTE -> LeqInequality
            | ST.GT -> GtInequality
            | ST.GTE -> GeqInequality
            | ST.Add -> Addition
            | ST.Mul -> Product
            | ST.Div -> Division
            | ST.Minus -> Opposite
            | ST.Sub -> Substraction
            | ST.Mod -> Remainder
            | ST.TrueOp
            | ST.FalseOp -> failwith "Boolean term operators cannot be matched to SMT operators"
            | ST.BvAnd
            | ST.BvXor
            | ST.BvOr
            | ST.BvAdd
            | ST.BvSub
            | ST.BvShl
            | ST.BvShr
            | ST.BvUdiv
            | ST.BvMod
            | ST.BvMul
            | ST.BvUlt
            | ST.BvToNat
            | ST.BvUext _
            | ST.NatToBv _ -> failwith "Bit-vector term operators cannot be matched to SMT operators"
            | ST.Var _ -> failwith "Uninterpreted term operators cannot be immediately matched to SMT operators"
    in
    let term_quantifier_to_smt_quantifier (q : ST.qop) : quantifier =
        match q with
            | ST.Forall -> Forall
            | ST.Exists -> Exists
    in
    let smt_term_from_term (id : string) (sg : list<sort>) (t : ST.term) : smt_derivation * smt_term =
        let add_binding_defs (defs : list<matching>) (bs : list<sort>) : list<matching> =
            let aux (n : int) (s : sort) : int * matching = (n + 1 , Inr (n + 1)) in
            let (_ , defsx) : int * list<matching> = fold_n_map aux (List.length defs) bs in
            defs @ defsx
        in
        let make_parameters (ctx : list<sort>) : list<smt_term> =
            let k : int = List.length ctx in
            let rec aux (n : int) (o : list<smt_term>) : list<smt_term> =
                if n = k then List.rev o else aux (n + 1) (SMTBoundVariable n :: o)
            in
            aux 0 []
        in
        let rec aux (defs : list<matching>) (ctx : list<sort>) (idv : int * smt_derivation) (tm : ST.term) : (int * smt_derivation) * smt_term =
            match tm.tm with
                | ST.Integer s -> (idv , SMTInteger s)
                | ST.BoundV n -> begin
                    match List.nth defs n with
                        | Inl (s , args) -> (idv , SMTApplication (DefinedTerm s , args))
                        | Inr k -> (idv , SMTBoundVariable k)
                end
                | ST.App (ST.TrueOp , _) -> (idv , SMTBoolean true)
                | ST.App (ST.FalseOp , _) -> (idv , SMTBoolean false)
                | ST.App (ST.Var "ZFuel" , _) -> (idv , SMTFuel None)
                | ST.App (ST.Var "SFuel" , hd :: tl) ->
                    let (idvx , f) : (int * smt_derivation) * smt_term = aux defs ctx idv hd in
                    (idv , SMTFuel (Some f))
                | ST.App (o , args) ->
                    let ox : operator = match o with
                        | ST.Var s -> begin match smap_try_find table s with
                            | Some (SMTFunctionDeclaration _) -> Uninterpreted s
                            | Some (SMTMacroDefinition _) -> Macro s
                            | Some (SMTTermDefinition _) -> failwith "Found operator identifier corresponding to a term definition name"
                            | Some (SMTMetaDefinition _) -> failwith "Found operator identifier corresponding to a proof definition name"
                            | None -> failwith ("Found unrecognized variable identifier '" ^ s ^ "'")
                        end
                        | _ -> term_operator_to_smt_operator o
                    in
                    let (idvx , argsx) : (int * smt_derivation) * list<smt_term> = fold_n_map (aux defs ctx) idv args in
                    (idvx , SMTApplication (ox , argsx))
                | ST.Quant (q , _ , _ , bs , scp , _) ->
                    let qx : quantifier = term_quantifier_to_smt_quantifier q in
                    let bsx : list<sort> = List.map term_sort_to_smt_sort bs in
                    let defsx : list<matching> = add_binding_defs defs bsx in
                    let ctxx : list<sort> = ctx @ bsx in
                    let (idvx , scpx) : (int * smt_derivation) * smt_term = aux defsx ctxx idv scp in
                    (idvx , SMTBinding (qx , bsx , scpx))
                | ST.Let (bs , scp) ->
                    let f ((d , j , v) : list<matching> * int * smt_derivation) (tmx : ST.term) : list<matching> * int * smt_derivation =
                        let ((jx , vx) , tmxx) : (int * smt_derivation) * smt_term = aux defs ctx (j , v) tmx in
                        let nm : string = id ^ "@" ^ (string_of_int (jx + 1)) in
                        let ctxx : list<smt_term> = make_parameters ctx in
                        add_to_table info nm (SMTTermDefinition (nm , ctx , tmxx)) ;
                        ((Inl (nm , ctxx) :: d) , jx + 1 , nm :: vx)
                    in
                    let (i , dv) : int * smt_derivation = idv in
                    let (dn , ix , vn) : list<matching> * int * smt_derivation = List.fold f ([] , i , dv) bs in
                    let defsx : list<matching> = defs @ (List.rev dn) in
                    aux defsx ctx (ix , vn) scp
                | ST.Labeled (tmx , _ , _)
                | ST.LblPos (tmx , _) -> aux defs ctx idv tmx
                | ST.FreeV (var , st) -> begin match smap_try_find table var with
                    | Some (SMTFunctionDeclaration _) -> (idv , SMTApplication (Uninterpreted var , []))
                    | Some (SMTMacroDefinition _) -> (idv , SMTApplication (Macro var , []))
                    | _ -> failwith "Free variables should not occur in closed SMT terms"
                end
        in
        let ((_ , dv) , tm) : (int * smt_derivation) * smt_term = aux (add_binding_defs [] sg) sg (0 , []) t in
        (dv , tm)
    in
    let rec aux (i : list<ST.decl>) (o : smt_derivation) : smt_derivation =
        match i with
            | ST.DeclFun (nm , sg , st , _) :: tl ->
                let sgx : list<sort> = List.map term_sort_to_smt_sort sg in
                let dx : smt_declaration = SMTFunctionDeclaration (nm , sgx , term_sort_to_smt_sort st) in
                add_to_table info nm dx ;
                aux tl (nm :: o)
            | ST.DefineFun (nm , sg , st , tm , _) :: tl ->
                let sgx : list<sort> = List.map term_sort_to_smt_sort sg in
                let (dv , tmx) : smt_derivation * smt_term = smt_term_from_term nm sgx tm in
                let dx : smt_declaration = SMTMacroDefinition (nm , sgx , term_sort_to_smt_sort st , tmx) in
                add_to_table info nm dx ;
                aux tl ((nm :: dv) @ o)
            | ST.Assume a :: tl ->
                let nm : string = a.assumption_name ^ "@assert" in
                let (dv , tmx) : smt_derivation * smt_term = smt_term_from_term nm [] a.assumption_term in
                let dx : smt_declaration = SMTTermDefinition (nm , [] , tmx) in
                add_to_table info nm dx ;
                add_to_assertions info nm tmx ;
                aux tl ((nm :: dv) @ o)
            | ST.Module (_ , l) :: tl -> aux (l @ tl) o
            | _ :: tl -> aux tl o
            | [] -> o
    in
    aux ds deriv

let smt_derivation_from_raw_proof_section (info : smt_derivation_info) (deriv : smt_derivation) ((funs , pf) : raw_proof_section) : smt_derivation * string =
    let rnm : renaming = smap_create 1000 in
    let reset_renamings () : unit = smap_clear rnm in
    let add_renaming (var : string) (mt : matching) : unit =
        match smap_try_find rnm var with
            | Some ref -> ref := mt :: !ref
            | None -> smap_add rnm var (mk_ref [mt])
    in
    let remove_renaming (var : string) : unit =
        match smap_try_find rnm var with
            | Some ref -> ref := List.tl !ref
            | None -> failwith "Trying to remove an inexistent renaming"
    in
    let get_renaming (var : string) : option<matching> =
        match smap_try_find rnm var with
            | None -> None
            | Some rf -> match !rf with
                | [] -> None
                | hd :: tl -> Some hd
    in
    let make_parameters (ctx : list<sort>) : list<smt_term> =
        let k : int = List.length ctx in
        let rec aux (n : int) (o : list<smt_term>) : list<smt_term> =
            if n = k then List.rev o else aux (n + 1) (SMTBoundVariable n :: o)
        in
        aux 0 []
    in
    let skolem (dv : smt_derivation) ((nm , sg , st) : raw_function) : smt_derivation =
        let nmx : string = new_skolem_name info in
        add_renaming nm (Inl (nmx , make_parameters sg)) ;        
        add_to_table info nm (SMTFunctionDeclaration (nmx , sg , st)) ;
        nm :: dv
    in
    let rec aux (ctx : list<sort>) (dv : smt_derivation) (p : raw_proof) : smt_derivation * smt_pt =
        match p with
            | RawApplication (Uninterpreted s, args) -> begin match get_renaming s with
                | Some (Inl (ss , args_ctx)) ->
                    if is_proof ss then
                        (dv , Inl (SMTDefinedMeta (get_name ss)))
                    elif is_term ss then
                        (dv , Inr (SMTApplication (DefinedTerm (get_name ss) , args_ctx)))
                    else
                        let (dvx , argsx_pt) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv args in
                        (dvx , Inr (SMTApplication (Uninterpreted ss , List.map right argsx_pt)))
                | Some (Inr k) -> (dv , Inr (SMTBoundVariable k))
                | None ->
                    let (dvx , argsx_pt) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv args in
                    let argsx : list<smt_term> = List.map right argsx_pt in
                    let o : operator = match smap_try_find info.smt_derivation_info_table s with
                        | Some (SMTFunctionDeclaration _) -> Uninterpreted s
                        | Some (SMTMacroDefinition _) -> Macro s
                        | _ -> failwith ("Unrecognized variable identifier '" ^ s ^ "'")
                    in
                    (dv , Inr (SMTApplication (o , argsx)))
            end
            | RawApplication (o , args) ->
                let (dvx , argsx_pt) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv args in
                let argsx : list<smt_term> = List.map right argsx_pt in
                let ox : operator = match o with
                    | Opposite -> if List.length args = 1 then Substraction else Opposite
                    | _ -> o
                in
                (dv , Inr (SMTApplication (ox , argsx)))
            | RawBinding (q , bd , scp) ->
                let f (n : int) ((var , _) : string * sort) : int =
                    add_renaming var (Inr (n + 1)) ;
                    n + 1
                in
                ignore <| List.fold_left f (List.length ctx) bd ;                    
                let bdx : list<sort> = List.map (fun ((_ , s) : string * sort) -> s) bd in
                let (dvx , scpx_pt) : smt_derivation * smt_pt = aux (ctx @ bdx) dv scp in
                List.iter (fun ((var , _) : string * sort) -> remove_renaming var) bd ;
                (dv , Inr (SMTBinding (q , bdx , right scpx_pt)))
            | RawLet (bd , scp) ->
                let pars : list<smt_term> = make_parameters ctx in
                let f (d : smt_derivation) ((var , tm) : string * raw_proof) : smt_derivation * smt_pt =
                    let (dvx , ptx) : smt_derivation * smt_pt = aux ctx d tm in
                    let (nm , mark) : string * string = match ptx with
                        | Inl _ -> new_proof_name info
                        | Inr _ -> new_term_name info
                    in
                    add_renaming var (Inl (mark , pars)) ;
                    let dc : smt_declaration = match ptx with
                        | Inl px -> SMTMetaDefinition (nm , px)
                        | Inr tx -> SMTTermDefinition (nm , ctx , tx)
                    in
                    add_to_table info nm dc ;
                    (nm :: dvx , ptx)
                in
                let (dvx , _) : smt_derivation * list<smt_pt> = fold_n_map f dv bd in
                aux ctx dvx scp
            | RawInteger s -> (dv , Inr (SMTInteger s))
            | RawBoolean b -> (dv , Inr (SMTBoolean b))
            | RawFuel None -> (dv , Inr (SMTFuel None))
            | RawFuel (Some f) ->
                let (dvx , fx) : smt_derivation * smt_pt = aux ctx dv f in
                (dvx , Inr (SMTFuel (Some (right fx))))
            | RawPremise tm ->
                let unrolled : raw_proof = unroll_lets tm in
                let (dvx , ptx) : smt_derivation * smt_pt = aux ctx dv unrolled in
                let tx : smt_term = right ptx in
                let hx : int = hash_of_smt_term info tx in
                let f ((hh , ss) : int * string) : bool =
                    hh = hx && begin
                        match smap_try_find info.smt_derivation_info_table ss with
                            | Some (SMTTermDefinition (_ , [] , txx)) -> equal_smt_terms info tx txx
                            | _ -> false
                    end
                in
                begin match find_opt f !(info.smt_derivation_info_assertions) with
                    | Some (hh , ss) -> (dvx , Inl (SMTPremise ss))
                    | None -> failwith "Could not match raw premise to assertion"
                end
            | RawSkolemization p ->
                let (dvx , ptx) : smt_derivation * smt_pt = aux ctx dv p in
                (dvx , Inl (SMTSkolemization (right ptx)))
            | RawRewriting p ->
                let (dvx , ptx) : smt_derivation * smt_pt = aux ctx dv p in
                (dvx , Inl (SMTRewriting (right ptx)))
            | RawNnf (ps , cn) ->
                let (dvx , ptx) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv ps in
                let (dvxx , cnx) : smt_derivation * smt_pt = aux ctx dvx cn in
                (dvxx , Inl (SMTNnf (List.map left ptx , right cnx)))
            | RawResolution (ps , cn) ->
                let (dvx , ptx) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv ps in
                let (dvxx , cnx) : smt_derivation * smt_pt = aux ctx dvx cn in
                (dvxx , Inl (SMTResolution (List.map left ptx , right cnx)))
            | RawCongruence (ps , cn) ->
                let (dvx , ptx) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv ps in
                let (dvxx , cnx) : smt_derivation * smt_pt = aux ctx dvx cn in
                (dvxx , Inl (SMTCongruence (List.map left ptx , right cnx)))
            | RawGeneralization (ant , cn) ->
                let (dvx , antx) : smt_derivation * smt_pt = aux ctx dv ant in
                let (dvxx , cnx) : smt_derivation * smt_pt = aux ctx dvx cn in
                (dvxx , Inl (SMTGeneralization (left antx , right cnx)))
            | RawInstantiation (inst , cn) ->
                let (dvx , instx) : smt_derivation * list<smt_pt> = fold_n_map (aux ctx) dv inst in
                let (dvxx , cnx) : smt_derivation * smt_pt = aux ctx dvx cn in
                (dvxx , Inl (SMTInstantiation (List.map right instx , right cnx)))
            | RawArithmetics (pars , cns) -> (dv , Inl (SMTArithmetics ([] , [])))
    in
    reset_renamings () ;
    let derivx : smt_derivation = List.fold_left skolem deriv funs in
    let (derivxx , mainpt) : smt_derivation * smt_pt = aux [] derivx pf in
    let (lastname , lastmark) : string * string = new_proof_name info in
    let lastmeta : smt_declaration = SMTMetaDefinition (lastname , left mainpt) in
    add_to_table info lastname lastmeta ;
    (lastname :: derivxx , lastname)

let parse_proof (s : string) : raw_proof_section =
    let lexbuf : LexBuffer<char> = LexBuffer<char>.FromString s in
    lexbuf.EndPos <- lexbuf.EndPos.NextLine ;
    try PP.start PL.tokenize lexbuf with
    e ->
        let pos = lexbuf.EndPos in
        let line = pos.Line in
        let column = pos.Column in
        let message = e.Message in 
        let lastToken = new System.String(lexbuf.Lexeme) in
        print "Parse failed at (%s,%s) on token %s\n" [string_of_int line ; string_of_int column ; lastToken] ;
        failwith message

let do_analysis (q : list<ST.decl>) (p : string) (c : list<string>) : unit =
    print "Reading proof...\n" [] ;
    print (p ^ "\n") [] ;
    print "Parsing proof...\n" [] ;
    let rps : raw_proof_section = parse_proof p in
    // print ((string_of_raw_proof_section rps) ^ "\n") [] ;
    let info : smt_derivation_info = new_smt_derivation_info () in
    let dv1 : smt_derivation = smt_derivation_from_declarations info [] q in
    print ((string_of_smt_derivation info dv1) ^ "\n") [] ;
    let (dv2 , pf) : smt_derivation * string = smt_derivation_from_raw_proof_section info dv1 rps in
    print "Done\n" []

let analyze_proof (res : z3result) : unit =
    match res.z3result_status with
        | UNSAT (u , v) -> begin match (u , v) with
            | (_ , None) -> ()
            | (None , Some ls) -> do_analysis res.z3result_query_decls (String.concat " " ls) []
            | (Some core , Some ls) -> do_analysis res.z3result_query_decls (String.concat " " ls) core
        end
        | _ -> ()
