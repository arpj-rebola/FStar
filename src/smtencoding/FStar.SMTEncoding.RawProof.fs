#light "off"

module FStar.SMTEncoding.RawProof
open FStar
open FStar.All
open FStar.Range
open FStar.Util

let hash_of_int_list (l : list<int>) : int =
    let aux ((sum , prod , xoor) : int * int * int) (x : int) : int * int * int =
        (sum + x , prod * x , xoor ^^^ x)
    in
    let (s , p , x) : int * int * int = List.fold_left aux (0 , 1 , 0) l in
    1023 * s + p ^^^ (31 * x)

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
        | Proof -> 105

type operator =
    | Conjunction
    | Disjunction
    | Negation
    | Implication
    | Equality
    | Equivalence
    | LeqInequality
    | LtInequality
    | GeqInequality
    | GtInequality
    | Addition
    | Product
    | Opposite
    | DefinedTerm of string
    | DefinedProof of string
    | Uninterpreted of string

let string_of_operator (o : operator) : string =
    match o with
        | Conjunction -> "/\\"
        | Disjunction -> "\\/"
        | Negation -> "~"
        | Implication -> "=>"
        | Equality -> "="
        | Equivalence -> "~~~"
        | LeqInequality -> "<="
        | LtInequality -> "<"
        | GeqInequality -> ">="
        | GtInequality -> ">="
        | Addition -> "+"
        | Product -> "*"
        | Opposite -> "-"
        | DefinedTerm s -> "$" ^ s
        | DefinedProof s -> "#" ^ s
        | Uninterpreted s -> s

let hash_of_operator (dict : smap<int>) (o : operator) : int =
    match o with
        | Conjunction -> 200
        | Disjunction -> 201
        | Negation -> 202
        | Implication -> 203
        | Equality -> 204
        | Equivalence -> 205
        | LeqInequality -> 206
        | LtInequality -> 206
        | GeqInequality -> 207
        | GtInequality -> 208
        | Addition -> 209
        | Product -> 210
        | Opposite -> 211
        | DefinedTerm s -> dict ("$" ^ s)
        | DefinedProof s -> dict ("#" ^ s)
        | Uninterpreted s -> dict s

type quantifier =
    | Forall
    | Exists
    | Lambda

let string_of_quantifier (q : quantifier) : string =
    match q with
        | Forall -> "forall"
        | Exists -> "exists"
        | Lambda -> "lambda"

let hash_of_quantifier (q : quantifier) : int =
    match q with
        | Forall -> 301
        | Exists -> 302
        | Lambda -> 303

// type raw_proof =
//     | Application of operator * list<raw_proof>
//     | Binding of quantifier * list<(string * sort)> * raw_proof
//     | Let of list<(string * raw_proof)> * raw_proof
//     | IntegerConst of string
//     | BooleanConst of bool
//     | Arbitrary of raw_proof * raw_proof
//     | Congruence of list<raw_proof> * raw_proof
//     | Reflexivity of raw_proof
//     | Symmetry of raw_proof * raw_proof
//     | Transitivity of raw_proof * raw_proof * raw_proof
//     | Reachability of list<raw_proof> * raw_proof
//     | Generalization of raw_proof
//     | Instantiation of list<raw_proof> * raw_proof
//     | Rewrite of raw_proof
//     | ModusPonens of raw_proof * raw_proof * raw_proof
//     | ModusPonensEquiv of raw_proof * raw_proof * raw_proof
//     | Skolemization of raw_proof
//     | PosNnf of list<raw_proof>
//     | NegNnf of list<raw_proof>
//     | UnitResolution of list<raw_proof> * raw_proof
//     | Asserted of raw_proof
//     | TriangleInequality of raw_proof
//     | FarkasLemma of list<raw_proof> * list<raw_proof>
//     | AssignBounds of list<raw_proof> * raw_proof
//     | Arithmetics of raw_proof
//     | ProofEnd

type inference =
    | RawSkolemization
    | RawNnf
    | RawArbitrary
    | RawGeneralization
    | RawPremise
    | RawResolution
    | RawCongruence
    | RawInstantiation of list<raw_proof>
    | RawRewrite
    | RawArithmetics of string * list<raw_proof>

and raw_proof =
    | RawApplication of operator * list<raw_proof>
    | RawBinding of quantifier * list<(string * sort)> * raw_proof
    | RawLet of list<(string * raw_proof)> * raw_proof
    | RawInteger of string
    | RawBoolean of bool
    | RawInference of inference * list<raw_proof>

let string_of_inference (level : int) (dict : smap<int>) (i : inference) : string =
    match i with
        | RawSkolemization -> "Skolem"
        | RawNnf -> "Nnf"
        | RawArbitrary -> "Arbitrary"
        | RawGeneralization -> "Generalize"
        | RawPremise -> "Premise"
        | RawResolution -> "Resolution"
        | RawCongruence -> "Congruence"
        | RawInstantiation p -> "[Instantiate " ^ (String.concat " " (List.map (string_of_raw_proof level dict) p)) ^ "]"
        | RawRewrite -> "Rewrite"
        | RawArithmetics (s , p) -> "[Arithmetics:" ^ s ^ " " ^ (String.concat " " (List.map (string_of_raw_proof level dict) p)) ^ "]"

and string_of_raw_proof (level : int) (dict : smap<int>) (p : raw_proof): string =
    match p with
        | RawApplication (o , args) -> "(" ^ (string_of_operator dict o) ^ " " ^ (String.concat " " (List.map (string_of_raw_proof level dict) args)) ^ ")"
        | RawBinding (q , bs , scp) ->
            let bs_s : list<string> = List.map (fun ((var , st) : string * sort) -> "(" ^ var ^ " " ^ (string_of_sort st)) bs in
            "{" ^ (string_of_quantifier q) ^ " " ^ (String.concat " " bs_s) ^ " : " ^ (string_of_raw_proof level dict scp) ^ "}"
        | RawLet (bs , scp) ->
            let bs_s : list<string> = List.map (fun ((var , p) : string * raw_proof) -> (repeat (level + 1) "\t") ^ var ^ " := " ^ (string_of_raw_proof (level + 1) dict))
            "{\n" ^ (String.concat "\n" bs_s) ^ "\n" ^ (repeat level "\t") ^ ": " ^ (string_of_raw_proof level dict scp) ^ "}"
        | RawInteger s -> s
        | RawBoolean true -> "True"
        | RawBoolean false -> "False"
        | RawInference (i , p) -> "(" ^ (string_of_inference level dict i) ^ (List.concat " " (List.map (string_of_raw_proof level dict) p)) ^ ")"

type raw_function = string * list<sort> * sort
type raw_proof_section = list<raw_function> * raw_proof










