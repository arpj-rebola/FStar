#light "off"

module FStar.SMTEncoding.SMTProof
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
    | Uninterpreted of string


type theory_lemma =
    | ArithTriangle
    | ArithFarkas

type raw_proof =
    | Terminal of string
    | Application of operator * list<raw_proof>
    | Forall of list<(string * sort)> * raw_proof
    | Lambda of list<(string * sort)> * raw_proof
    | Let of list<(string * raw_proof)> * raw_proof
    | IntegerConst of int
    | BooleanConst of bool
    | Arbitrary of raw_proof * raw_proof
    | Congruence of list<raw_proof> * raw_proof
    | Reflexivity of raw_proof
    | Symmetry of raw_proof * raw_proof
    | Transitivity of raw_proof * raw_proof * raw_proof
    | Reachability of list<raw_proof> * raw_proof
    | Generalization of raw_proof
    | Instantiation of raw_proof * raw_proof
    | Rewrite of raw_proof
    | ModusPonens of raw_proof * raw_proof * raw_proof
    | ModusPonensEquiv of raw_proof * raw_proof * raw_proof
    | Skolemization of raw_proof
    | PosNnf // What are the parameters for these three?
    | NegNnf
    | UnitResolution
    | Asserted of raw_proof
    | TheoryLemma of theory_lemma * list<raw_proof>

type smt_function = string * list<sort> * sort
type smt_proof_section = list<smt_function> * raw_proof
type parametric_let = string * list<(string * sort)> * raw_proof

let sort_to_string (s : sort) : string =
    match s with
        | Boolean -> "Bool"
        | Fuel -> "Fuel"
        | String -> "String"
        | Integer -> "Int"
        | Term -> "Term"

let operator_to_string (o : operator) : bool * string =
    match o with
        | Conjunction -> (true , "/\\")
        | Disjunction -> (true , "\\/")
        | Negation -> (false , "~")
        | Implication -> (true , "=>")
        | Equality -> (true , "=")
        | Equivalence -> (true , "~")
        | LeqInequality -> (true , "<=")
        | LtInequality -> (true , "<")
        | GeqInequality -> (true , ">=")
        | GtInequality -> (true , ">")
        | Addition -> (true , "+")
        | Product -> (true , "*")
        | Opposite -> (false , "-")
        | Uninterpreted s -> (false , s)

let theory_lemma_to_string (t : theory_lemma) : string =
    match t with
        | ArithTriangle -> "Arithmetic:TriangleInequality"
        | ArithFarkas -> "Arithmetic:FarkasLemma"

let rec smt_function_to_string ((nm , sg , st) : string * list<sort> * sort) : string =
    nm ^ " : (" ^ (String.concat " , " (List.map sort_to_string sg)) ^ ") ---> " ^ (sort_to_string st) ^ "\n"

let rec raw_proof_to_string (p : raw_proof) : string =
    match p with
        | Terminal s -> s
        | Application (f , args) ->
            let (infix , f_s) : bool * string = operator_to_string f in
            let args_s : list<string> = f_s :: (List.map raw_proof_to_string args) in
            "(" ^ (String.concat " " args_s) ^ ")"
        | Forall (bindings , scope) ->
            let bindings_s : list<string> = List.map (fun ((nm , st) : string * sort ) -> "(" ^ nm ^ (sort_to_string st) ^ ")") bindings in
            "(forall (" ^ (String.concat " " bindings_s) ^ ") " ^ (raw_proof_to_string scope) ^ ")"
        | Lambda (bindings , scope) ->
            let bindings_s : list<string> = List.map (fun ((nm , st) : string * sort ) -> "(" ^ nm ^ (sort_to_string st) ^ ")") bindings in
            "(lambda (" ^ (String.concat " " bindings_s) ^ ") " ^ (raw_proof_to_string scope) ^ ")"
        | Let (bindings , scope) ->
            let bindings_s : list<string> = List.map (fun ((nm , pf) : string * raw_proof) -> "(" ^ nm ^ (raw_proof_to_string pf) ^ ")") bindings in
            "(let (" ^ (String.concat " " bindings_s) ^ ") " ^ (raw_proof_to_string scope) ^ ")"
        | IntegerConst x -> string_of_int x
        | BooleanConst x -> if x then "True" else "False"
        | Arbitrary (p1 , p2) -> "(Arbitrary " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ ")"
        | Congruence (p1 , p2) -> "(Congruence " ^ (String.concat " " (List.map raw_proof_to_string p1)) ^ " " ^ (raw_proof_to_string p2) ^ ")"
        | Reflexivity p1 -> "(Reflexivity " ^ (raw_proof_to_string p1) ^ ")"
        | Symmetry (p1 , p2) -> "(Symmetry " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ ")"
        | Transitivity (p1 , p2 , p3) -> "(Transitivity " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ " " ^ (raw_proof_to_string p3) ^ ")"
        | Reachability (p1 , p2) -> "(Reachability " ^ (String.concat " " (List.map raw_proof_to_string p1)) ^ " " ^ (raw_proof_to_string p2) ^ ")"
        | Generalization p1 -> "(Generalization " ^ (raw_proof_to_string p1) ^ ")"
        | Instantiation (p1 , p2) -> "(Instantiation " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ ")"
        | Rewrite p1 -> "(Rewrite " ^ (raw_proof_to_string p1) ^ ")"
        | ModusPonens (p1 , p2 , p3) -> "(ModusPonens " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ " " ^ (raw_proof_to_string p3) ^ ")"
        | ModusPonensEquiv (p1 , p2 , p3) -> "(ModusPonensEquiv " ^ (raw_proof_to_string p1) ^ " " ^ (raw_proof_to_string p2) ^ " " ^ (raw_proof_to_string p3) ^ ")"
        | Skolemization p1 -> "(Skolemization " ^ (raw_proof_to_string p1) ^ ")"
        | PosNnf -> "(PositiveNnf ...)"
        | NegNnf -> "(NegativeNnf ...)"
        | UnitResolution -> "(UnitResolution ...)"
        | Asserted p -> "(Asserted " ^ (raw_proof_to_string p) ^ ")"
        | TheoryLemma (th , ps) -> "(" ^ (theory_lemma_to_string th) ^ " " ^ (String.concat " " (List.map raw_proof_to_string ps)) ^ ")"

let parametric_let_to_string ((nm , bd , pf) : parametric_let) : string =
    let pars : list<string> = List.map (fun ((var , srt) : string * sort) -> "(" ^ var ^ " " ^ (sort_to_string srt) ^ ")") bd in
    (String.concat " " ("Define" :: nm :: pars)) ^ " := \n\t\t" ^ (raw_proof_to_string pf)


