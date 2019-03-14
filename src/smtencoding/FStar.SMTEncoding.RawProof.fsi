module FStar.SMTEncoding.RawProof

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

val rename_apart : raw_proof -> raw_proof
val topify : raw_proof -> list<parametric_let>
val raw_proof_to_string : raw_proof_to_string