#light "off"

module FStar.SMTEncoding.RawProof

type sort =
    | Boolean
    | Fuel
    | String
    | Integer
    | Term
    | Proof

val string_of_sort : sort -> string
val hash_of_sort : sort -> int

type operator =
    | Conjunction
    | Disjunction
    | Negation
    | Implication
    | Biimplication
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
    | DefinedTerm of string
    | Uninterpreted of string

val string_of_operator : operator -> string
val hash_of_operator : (operator) -> list<int>
val infix_operator : operator -> bool

type quantifier =
    | Forall
    | Exists
    | Lambda

val string_of_quantifier : quantifier -> string
val hash_of_quantifier : quantifier -> int

type raw_proof =
    | RawSkolemVar of string
    | RawFuel of option<raw_proof>
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

type raw_function = string * list<sort> * sort
type raw_proof_section = list<raw_function> * raw_proof

val string_of_raw_proof : int -> raw_proof -> string
val string_of_raw_proof_section : raw_proof_section -> string
val unroll_lets : raw_proof -> raw_proof
