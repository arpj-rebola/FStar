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
    | PosNnf // What are the parameters for these three?
    | NegNnf
    | UnitResolution
    | Asserted of raw_proof
    | TheoryLemma of theory_lemma * list<raw_proof>

type raw_statement =
    | RawDeclareFun of string * list<sort> * sort
    | RawRefutation of raw_proof

type smt_proof_section = SmtProofSection of list<raw_statement>

let rename_apart (p : raw_proof) : raw_proof =
    let ctr : ref<int> = mk_ref 0 in
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
        List.iter add_entry l ;
        stack := (List.map (fun ((var , _ , _) : string * 'a * string) -> var) l) :: !stack
    in
    let pop () : unit =
        let remove_entry (var : string) : unit =
            match smap_try_find dict var with
                | None -> failwith "Impossible"
                | Some rf -> rf := List.tl !rf
        in
        let stage : list<string> = List.hd !stack in
        List.iter remove_entry stage ;
        stack := List.tl !stack
    in
    let rec aux (proof : raw_proof) : raw_proof =
        match proof with
            | Terminal s -> begin match smap_try_find dict s with
                | None -> proof
                | Some ref -> match !ref with
                    | hd :: tl -> Terminal hd
                    | [] -> failwith "Impossible"
            end
            | Application (f , args) -> Application (f , List.map aux args)
            | Forall (bindings , scope) ->
                let renaming : list<(string * sort * string)> = List.map rename_sorted bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((_ , st , nm) : string * sort * string) -> (nm , st)) renaming in
                push renaming ;
                let new_scope : raw_proof = aux scope in
                pop () ;
                Forall (new_bindings , new_scope)
            | Lambda (bindings , scope) ->
                let renaming : list<(string * sort * string)> = List.map rename_sorted bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((_ , st , nm) : string * sort * string) -> (nm , st)) renaming in
                push renaming ;
                let new_scope : raw_proof = aux scope in
                pop () ;
                Lambda (new_bindings , new_scope)
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
                pop () ;
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
            | Instantiation (p1 , p2) -> Instantiation (aux p1 , aux p2)
            | Rewrite p -> Rewrite (aux p)
            | ModusPonens (p1 , p2 , p3) -> ModusPonens (aux p1 , aux p2 , aux p3)
            | ModusPonensEquiv (p1 , p2 , p3) -> ModusPonensEquiv (aux p1 , aux p2 , aux p3)
            | Skolemization p -> Skolemization (aux p)
            | PosNnf -> PosNnf
            | NegNnf -> NegNnf
            | UnitResolution -> UnitResolution
            | Asserted p -> Asserted (aux p)
            | TheoryLemma (th , ps) -> TheoryLemma (th , List.map aux ps)          
    in
    let res : raw_proof = aux p in
    reset_names () ;
    res

type parametric_let = string * list<(string * sort)> * raw_proof

let topify (proof : raw_proof) : list<parametric_let> =
    let map_n_cheese (f : 'a -> list<'b> -> 'a * list<'b>) (a : list<'a>) (b : list<'b>) : list<'a> * list<'b> =
        let rec aux (i : list<'a>) (aout : list<'a>) (bout : list<'b>) : list<'a> * list<'b> =
            match i with
                | [] -> (List.rev aout , bout)
                | hd :: tl -> 
                    let (aa , bb) : 'a * list<'b> = f hd bout in
                    aux tl (aa :: aout) bout
        in
        aux a [] b
    in
    let boundvar (var : string) (b : list<(string * sort)>) : string =
        let rec aux (bx : list<(string * sort)>) (n : int) : string =
            match bx with
                | (s , _) :: tl -> if s = var then ("@" ^ (string_of_int n)) else aux tl (n + 1)
                | [] -> var
        in
        aux b 1
    in
    let rec aux (pars : list<(string * sort)>) (p : raw_proof) (out : list<parametric_let>) : raw_proof * list<parametric_let> =
        match p with
            | Terminal s -> (Terminal (boundvar s pars) , out)
            | Application (f , args) ->
                let (ps , ls) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) args out in
                (Application (f , ps) , out)
            | Forall (bindings , scope) ->
                let new_pars : list<(string * sort)> = pars @ bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((var , st) : string * sort) -> (boundvar var new_pars , st)) bindings in
                let (new_scope, new_lets) : raw_proof * list<parametric_let> = aux (pars @ bindings) scope out in
                (Forall (new_bindings , new_scope) , new_lets)
            | Lambda (bindings , scope) ->
                let new_pars : list<(string * sort)> = pars @ bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((var , st) : string * sort) -> (boundvar var new_pars , st)) bindings in
                let (new_scope, new_lets) : raw_proof * list<parametric_let> = aux (pars @ bindings) scope out in
                (Lambda (new_bindings , new_scope) , new_lets)
            | Let (bindings , scope) ->
                let f ((var , pf) : string * raw_proof) (o : list<parametric_let>) : (string * raw_proof) * list<parametric_let> =
                    let (new_pf , new_o) : raw_proof * list<parametric_let> = aux pars pf o in
                    ((var , new_pf) , new_o)
                in
                let (new_bindings , new_lets) : list<(string * raw_proof)> * list<parametric_let> = map_n_cheese f bindings out in
                let new_lets : list<parametric_let> =
                    (List.map (fun ((var , pf) : string * raw_proof) -> (var , pars , pf)) (List.rev new_bindings)) @ new_lets
                in
                aux pars scope new_lets
            | IntegerConst _
            | BooleanConst _ -> (p , out)
            | Arbitrary (p1 , p2) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Arbitrary (q1 , q2) , out)
            | Congruence (p1 , p2) ->
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Congruence (q1 , q2) , out)
            | Reflexivity p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Reflexivity q , out)
            | Symmetry (p1 , p2) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Symmetry (q1 , q2) , out)
            | Transitivity (p1 , p2 , p3) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                let (q3 , out) : raw_proof * list<parametric_let> = aux pars p3 out in
                (Transitivity (q1 , q2 , q3) , out)
            | Reachability (p1 , p2) ->
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Reachability (q1 , q2) , out)
            | Generalization p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Generalization q , out)
            | Instantiation (p1 , p2) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Instantiation (q1 , q2) , out)
            | Rewrite p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Rewrite q , out)
            | ModusPonens (p1 , p2 , p3) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                let (q3 , out) : raw_proof * list<parametric_let> = aux pars p3 out in
                (ModusPonens (q1 , q2 , q3) , out)
            | ModusPonensEquiv (p1 , p2 , p3) ->
                let (q1 , out) : raw_proof * list<parametric_let> = aux pars p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                let (q3 , out) : raw_proof * list<parametric_let> = aux pars p3 out in
                (ModusPonensEquiv (q1 , q2 , q3) , out)
            | Skolemization p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Skolemization q , out)
            | PosNnf -> (PosNnf , out)
            | NegNnf -> (NegNnf , out)
            | UnitResolution -> (UnitResolution , out)
            | Asserted p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Asserted q , out)
            | TheoryLemma (th , ps) ->
                let (qs , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) ps out in
                (TheoryLemma (th , qs) , out)
    in
    let (pf , ls) : raw_proof * list<parametric_let> = aux [] proof [] in
    let last_let : parametric_let = ("!!proof!!" , [] , pf) in
    List.rev (last_let :: ls)