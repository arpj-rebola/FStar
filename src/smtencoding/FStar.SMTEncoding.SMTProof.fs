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

type functor =
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
    | Application of functor * list<string>
    | Forall of list<(string * sort)> * raw_proof
    | Lambda of list<(string * sort)> * raw_proof
    | Let of list<(string * raw_proof)> * raw_proof
    | IntegerConst of bigint
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
    | PositiveNnf // What are the parameters for these three?
    | NegativeNng
    | UnitResolution
    | Asserted of raw_proof
    | TheoryLemma of theory_lemma * list<raw_proof>

type raw_statement =
    | RawDeclareFun of string * list<sort> * sort
    | RawRefutation of raw_proof

type smt_proof_section = SmtProofSection of list<raw_statement>

let rename_apart (p : raw_proof) : raw_proof =
    let ctr : ref<int> = BU.mk_ref 0 in
    let dict : smap<(ref<(list<string>)>)> = smap_create 10000 in
    let stack : ref<(list<(list<string>)>)> = mk_ref [] in
    let fresh_name () : string =
        let x : int = !ctr in
        ctr := !ctr + 1 ;
        "b!" ^ (string_of_int x)
    in
    let reset_names () : unit =
        ctr := 0 ;
        smap_clear dict
    in
    let rename_sorted ((var , x) : string * 'a) : string * 'a * string =
        (var , x , fresh_name ())
    in
    let push (l : list<(string * 'a * string)>) : unit =
        let add_entry ((var , _ , nm) : string *  'a * string) : unit =
            match smap_try_find dict var with
                | None -> smap_add dict var (mk_ref [nm])
                | Some rf -> rf := nm :: !rf
        in
        Map.iter add_entry l ;
        stack := (List.map (fun ((var , _ , _) : string * 'a * string) -> var) l) :: !stack
    in
    let pop () : unit =
        let remove_entry (var : string) : unit =
            match smap_try_find dict var with
                | None -> failwith "Impossible"
                | Some rf -> rf := List.tl !rf
        in
        let stage : list<string> = List.tl !stack in
        Map.iter remove_entry stage ;
        stack := List.tl !stack
    in
    let aux (proof : raw_proof) : raw_proof =
        match proof with
            | Terminal s -> begin match psmap_try_find dict s with
                | None -> proof
                | Some (hd :: tl) -> Terminal hd
                | Some [] -> failwith "Impossible"
            end
            | Application (f , args) -> Application (f , List.map (aux dict stack) args)
            | Forall (bindings , scope)
            | Lambda (bindings , scope) ->
                let renaming : list<(string * sort * string)> = List.map rename_sorted bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((_ , st , nm) : string * sort * string) -> (nm , st)) renaming in
                push renaming ;
                let new_scope : raw_proof = aux scope in
                pop ;
                Forall (new_bindings , new_scope)
            | Let (bindings , scope) ->
                let renaming : list<(string * raw_proof * string)> =
                    bindings |>
                    List.map (fun ((var , pf) : string * raw_proof) -> (var , aux proof)) |>
                    List.map rename_sorted
                in
                let new_bindings : list<(string * raw_proof)> =
                    List.map (fun ((_ , pf , nm) : string * raw_proof * string) -> (nm , pf)) renaming
                in
                push renaming ;
                let new_scope : raw_proof = aux scope in
                pop ;
                Let (new_bindings , new_scope)
            | IntegerConst _
            | BooleanConst _ -> proof
            | Arbitrary (p1 , p2) -> Arbitrary (aux p1 , aux p2)
            | Congruence (p1 , p2) -> Congruence (List.map aux p1 , aux p2)
            | Reflexivity p -> Reflexivity (aux p)
            | Symmetry (p1 , p2) -> Symmetry (aux p1 , aux p2)
            | Transitivity (p1 , p2 , p3) -> Transitivity (aux p1 , aux p2 , aux p3)
            | Reachability (p1 , p2) -> Reachability (List.map aux p1 , aux p2)
            | Generalization p -> Generalization (aux p)
            | Instantiation p1 p2 -> Instantiation (aux p1) (aux p2)
            | Rewrite p -> Rewrite (aux p)
            | ModusPonens (p1 , p2 , p3) -> ModusPonens (aux p1 , aux p2 , aux p3)
            | ModusPonensEquiv (p1 , p2 , p3) -> ModusPonensEquiv (aux p1 , aux p2 , aux p3)
            | Skolemization p -> Skolemization (aux p)
            | PositiveNnf -> PositiveNnf
            | NegativeNnf -> NegativeNnf
            | UnitResolution -> UnitResolution
            | Asserted p -> Asserted (aux p)
            | TheoryLemma (th , ps) -> TheoryLemma (th , List.map aux p)          
    in
    reset_names () ;
    aux p


type parametric_let = string * list<(string * sort)> * raw_proof