#light "off"

module FStar.SMTEncoding.RawProof
open FStar
open FStar.All
open FStar.Range
open FStar.Util

type sort =
    | Boolean
    | Fuel
    | String
    | Integer
    | Term
    | Proof

let string_of_sort (s : sort) : string =
    match s with
        | Boolean -> "Boolean"
        | Fuel -> "Fuel"
        | String -> "String"
        | Integer -> "Integer"
        | Term -> "Term"
        | Proof -> "Proof"

let hash_of_sort (s : sort) : int =
    match s with
        | Boolean -> 100
        | Fuel -> 101
        | String -> 102
        | Integer -> 103
        | Term -> 104

type operator =
    | Conjunction
    | Disjunction
    | Negation
    | Implication
    | Branch
    | Equality
    | Equivalence
    | LeqInequality
    | LtInequality
    | GeqInequality
    | GtInequality
    | Addition
    | Substraction
    | Product
    | Opposite
    | Division
    | Remainder
    | Macro of string
    | Uninterpreted of string

let hash_of_operator (o : operator) : list<int> =
    match o with
        | Conjunction -> [200]
        | Disjunction -> [201]
        | Negation -> [202]
        | Implication -> [203]
        | Branch -> [205]
        | Equality -> [206]
        | Equivalence -> [207]
        | LeqInequality -> [208]
        | LtInequality -> [209]
        | GeqInequality -> [210]
        | GtInequality -> [211]
        | Addition ->  [212]
        | Substraction -> [213]
        | Product -> [214]
        | Opposite -> [215]
        | Division -> [216]
        | Remainder -> [217]
        | Uninterpreted s -> [218 ; hashcode s]
        | Macro s -> failwith "Cannot compute a parametric hash of an operator"

let string_of_operator (o : operator) : string =
    match o with
        | Conjunction -> "/\\"
        | Disjunction -> "\\/"
        | Negation -> "!"
        | Implication -> "=>"
        | Branch -> "ITE"
        | Equality -> "="
        | Equivalence -> "~"
        | LeqInequality -> "<="
        | LtInequality -> "<"
        | GeqInequality -> ">="
        | GtInequality -> ">="
        | Addition -> "+"
        | Substraction -> "-"
        | Product -> "*"
        | Opposite -> "-"
        | Division -> "/"
        | Remainder -> "%"
        | Uninterpreted s -> s
        | Macro s -> s

let infix_operator (o : operator) : bool =
    match o with
        | Conjunction
        | Disjunction
        | Implication
        | Equality
        | Equivalence
        | LeqInequality
        | LtInequality
        | GeqInequality
        | GtInequality
        | Addition
        | Substraction
        | Product -> true
        | Branch -> failwith "Branching operators are ternary"
        | _ -> false

type quantifier =
    | Forall
    | Exists
    | Lambda

let hash_of_quantifier (q : quantifier) : int =
    match q with
        | Forall -> 301
        | Exists -> 302
        | Lambda -> 303

let string_of_quantifier (q : quantifier) : string =
    match q with
        | Forall -> "forall"
        | Exists -> "exists"
        | Lambda -> "lambda"

type raw_proof =
    | RawFuel of option<raw_proof>
    | RawAbstractVar of int
    | RawApplication of operator * list<raw_proof>
    | RawBinding of quantifier * list<(string * sort)> * raw_proof
    | RawLet of list<(string * raw_proof)> * raw_proof
    | RawInteger of string
    | RawBoolean of bool
    | RawPremise of raw_proof
    | RawSkolemization of raw_proof
    | RawRewriting of raw_proof
    | RawNnf of list<raw_proof> * raw_proof
    | RawResolution of list<raw_proof> * raw_proof
    | RawCongruence of list<raw_proof> * raw_proof
    | RawGeneralization of raw_proof * raw_proof
    | RawInstantiation of list<raw_proof> * raw_proof
    | RawArithmetics of list<raw_proof> * list<raw_proof>

let rec string_of_raw_proof (level : int) (p : raw_proof) : string =
    match p with
        | RawFuel (None) -> "ZFuel"
        | RawFuel (Some p) -> "(SFuel " ^ (string_of_raw_proof level p) ^ ")"
        | RawAbstractVar n -> "?" ^ (string_of_int n)
        | RawApplication (o , args) -> "(" ^ (string_of_operator o) ^ " " ^ (String.concat " " (List.map (string_of_raw_proof level) args)) ^ ")"
        | RawBinding (q , bs , scp) ->
            let bs_s : list<string> = List.map (fun ((var , st) : string * sort) -> "(" ^ var ^ " " ^ (string_of_sort st)) bs in
            "{" ^ (string_of_quantifier q) ^ " " ^ (String.concat " " bs_s) ^ " : " ^ (string_of_raw_proof level scp) ^ "}"
        | RawLet (bs , scp) ->
            let bs_s : list<string> = List.map (fun ((var , p) : string * raw_proof) -> (repeat (level + 1) "\t") ^ var ^ " := " ^ (string_of_raw_proof (level + 1) p)) bs in
            "{\n" ^ (String.concat "\n" bs_s) ^ "\n" ^ (repeat level "\t") ^ ": " ^ (string_of_raw_proof level scp) ^ "}"
        | RawInteger s -> s
        | RawBoolean true -> "True"
        | RawBoolean false -> "False"
        | RawPremise px -> "(premise " ^ (string_of_raw_proof level px) ^ ")"
        | RawSkolemization px -> "(skolem " ^ (string_of_raw_proof level px) ^ ")"
        | RawRewriting px -> "(rewrite " ^ (string_of_raw_proof level px) ^ ")"
        | RawNnf (px , r) -> "(nnf (" ^ (String.concat " " (List.map (string_of_raw_proof level) px)) ^ ") " ^ string_of_raw_proof level r ^ ")"
        | RawResolution (px , r) -> "(resolution (" ^ (String.concat " " (List.map (string_of_raw_proof level) px)) ^ ") " ^ string_of_raw_proof level r ^ ")"
        | RawCongruence (px , r) -> "(congruence (" ^ (String.concat " " (List.map (string_of_raw_proof level) px)) ^ ") " ^ string_of_raw_proof level r ^ ")"
        | RawGeneralization (px , r) -> "(generalization " ^ (string_of_raw_proof level px) ^ " " ^ (string_of_raw_proof level r) ^ ")"
        | RawInstantiation (px , r) -> "(instantiation (" ^ (String.concat " " (List.map (string_of_raw_proof level) px)) ^ ") " ^ string_of_raw_proof level r ^ ")"
        | RawArithmetics (px , rx) -> "(arithmetics (" ^ (String.concat " " (List.map (string_of_raw_proof level) px)) ^ ") " ^ (String.concat " " (List.map (string_of_raw_proof level) rx)) ^ ")"

type raw_function = string * list<sort> * sort
type raw_proof_section = list<raw_function> * raw_proof

let string_of_raw_proof_section ((funs , pf) : raw_proof_section) : string =
    let printfun ((nm , sg , st) : raw_function) : string =
        let sep : string = if List.isEmpty sg then "" else " " in
        nm ^ " : " ^ (String.concat " * " (List.map string_of_sort sg)) ^ sep ^ (string_of_sort st)
    in
    let strings : list<string> = (List.map printfun funs) @ [string_of_raw_proof 0 pf] in
    String.concat "\n" strings

// let unroll_lets (p : raw_proof) : raw_proof =
//     let rec aux (rnm : list<(string * raw_proof)>) (pf : raw_proof) : raw_proof =
//         match pf with
//             | RawApplication (Uninterpreted s , []) -> begin
//                 match find_opt (fun ((ss , _) : string * raw_proof) -> s = ss) rnm with
//                     | Some (ss , lt) -> lt
//                     | None -> pf
//             end
//             | RawApplication (o , args) -> RawApplication (o , List.map (aux rnm) args)
//             | RawBinding (q , bs , scp) -> RawBinding (q , bs , aux rnm scp)
//             | RawLet (bs , scp) -> aux (rnm @ (List.map (fun ((s , t) : string * raw_proof) -> (s , aux rnm t)) bs)) scp
//             | RawPremise px -> RawPremise (aux rnm px)
//             | RawSkolemization px -> RawSkolemization (aux rnm px)
//             | RawRewriting px -> RawRewriting (aux rnm px)
//             | RawNnf (px , r) -> RawNnf (List.map (aux rnm) px , aux rnm r)
//             | RawResolution (px , r) -> RawResolution (List.map (aux rnm) px , aux rnm r)
//             | RawCongruence (px , r) -> RawCongruence (List.map (aux rnm) px , aux rnm r)
//             | RawGeneralization (px , r) -> RawGeneralization (aux rnm px , aux rnm r)
//             | RawInstantiation (px , r) -> RawInstantiation (List.map (aux rnm) px , aux rnm r)
//             | RawArithmetics (px , rx) -> RawArithmetics (List.map (aux rnm) px , List.map (aux rnm) rx)
//             | _ -> pf
//     in
//     aux [] p
