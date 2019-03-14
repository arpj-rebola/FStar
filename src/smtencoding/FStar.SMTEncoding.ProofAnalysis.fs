#light "off"

module FStar.SMTEncoding.ProofAnalysis
open FStar
open FStar.All
open FStar.Range
open FStar.Util
open FStar.SMTEncoding.Z3
open FStar.SMTEncoding.ProofLexer
open FStar.SMTEncoding.ProofParser
open FStar.SMTEncoding.SMTProof
open Microsoft.FSharp.Text.Lexing
module TM = FStar.SMTEncoding.Term

let hash_of_int_list (l : list<int>) : int =
    let aux ((sum , prod , xoor) : int * int * int) (x : int) : int * int * int =
        (sum + x , prod * x , xoor ^^^ x)
    in
    let (s , p , x) : int * int * int = List.fold_left aux (0 , 1 , 0) l in
    1023 * s + p ^^^ (31 * x)

let rec hash_of_encode_sort (st : TM.sort) : list<int> =
    match st with
      | TM.Bool_sort -> [200]
      | TM.Int_sort -> [201]
      | TM.String_sort -> [202]
      | TM.Term_sort -> [203]
      | TM.Fuel_sort -> [204]
      | TM.BitVec_sort n -> [205]
      | TM.Array (s1 , s2) -> 206 :: ((hash_of_encode_sort s1) @ (hash_of_encode_sort s2))
      | TM.Arrow (s1 , s2) -> 207 :: ((hash_of_encode_sort s1) @ (hash_of_encode_sort s2))
      | TM.Sort s -> [208 ; hashcode s]

let hash_of_encode_op (o : TM.op) : list<int> =
    match o with
      | TM.TrueOp -> [0]
      | TM.FalseOp -> [1]
      | TM.Not -> [2]
      | TM.And -> [3]
      | TM.Or -> [4]
      | TM.Imp -> [5]
      | TM.Iff -> [6]
      | TM.Eq -> [7]
      | TM.LT -> [8]
      | TM.LTE -> [9]
      | TM.GT -> [10]
      | TM.GTE -> [11]
      | TM.Add -> [12]
      | TM.Sub -> [13]
      | TM.Div -> [14]
      | TM.Mul -> [15]
      | TM.Minus -> [16]
      | TM.Mod -> [17]
      | TM.BvAnd -> [18]
      | TM.BvXor -> [19]
      | TM.BvOr -> [20]
      | TM.BvAdd -> [21]
      | TM.BvSub -> [22]
      | TM.BvShl -> [23]
      | TM.BvShr -> [24]
      | TM.BvUdiv -> [25]
      | TM.BvMod -> [26]
      | TM.BvMul -> [27]
      | TM.BvUlt -> [28]
      | TM.BvUext n -> [29 ; n]
      | TM.NatToBv n -> [30 ; n]
      | TM.BvToNat -> [31]
      | TM.ITE -> [32]
      | TM.Var s -> [33 ; hashcode s]

let hash_of_encode_qop (q : TM.qop) : int =
    match q with
        | TM.Forall -> 100
        | TM.Exists -> 101

let hash_of_encode_term (t : TM.term) : int =
    let rec to_list (i : TM.term) : list<int> =
        match i.tm with
            | TM.Integer s -> [hashcode s]
            | TM.BoundV n -> [n]
            | TM.FreeV (var , st) -> [hashcode var]
            | TM.App (op , args) -> (hash_of_encode_op op) @ (List.concat (List.map to_list args))
            | TM.Quant (q , _ , _ , sg , scp , _) ->
                (hash_of_encode_qop q) :: (List.concat (List.map hash_of_encode_sort sg)) @ (to_list scp)
            | TM.Let (tms , scp) ->
                (List.concat (List.map to_list tms)) @ (to_list scp)
            | TM.Labeled (t , _ , _)
            | TM.LblPos (t , _) -> to_list t
    in
    hash_of_int_list (to_list t)

let hash_of_raw_sort (st : sort) : list<int> =
    match st with
        | Boolean -> hash_of_encode_sort TM.Bool_sort
        | Fuel -> hash_of_encode_sort TM.Fuel_sort
        | String -> hash_of_encode_sort TM.String_sort
        | Integer -> hash_of_encode_sort TM.Int_sort
        | Term -> hash_of_encode_sort TM.Term_sort
    
let hash_of_raw_operator (o : operator) : list<int> =
    match o with
        | Conjunction -> hash_of_encode_op TM.And
        | Disjunction -> hash_of_encode_op TM.Or
        | Negation -> hash_of_encode_op TM.Not
        | Implication -> hash_of_encode_op TM.Imp
        | Equality -> hash_of_encode_op TM.Eq
        | Equivalence -> [50]
        | LeqInequality -> hash_of_encode_op TM.LTE
        | LtInequality -> hash_of_encode_op TM.LT
        | GeqInequality -> hash_of_encode_op TM.GTE
        | GtInequality -> hash_of_encode_op TM.GT
        | Addition -> hash_of_encode_op TM.Add
        | Product -> hash_of_encode_op TM.Mul
        | Opposite -> hash_of_encode_op TM.Minus
        | Uninterpreted s -> hash_of_encode_op (TM.Var s)

type parametric_let = string * list<(string * sort)> * raw_proof

let parametric_let_to_string ((nm , bd , pf) : parametric_let) : string =
    let pars : list<string> = List.map (fun ((var , srt) : string * sort) -> "(" ^ var ^ " " ^ (sort_to_string srt) ^ ")") bd in
    (String.concat " " ("Define" :: nm :: pars)) ^ " := \n\t\t" ^ (raw_proof_to_string pf)

let parse_proof (s : string) : smt_proof_section =
    let lexbuf = LexBuffer<char>.FromString s in
    lexbuf.EndPos <- lexbuf.EndPos.NextLine ;
    try
        start tokenize lexbuf
        with e ->
            let pos = lexbuf.EndPos in
            let line = pos.Line in
            let column = pos.Column in
            let message = e.Message in 
            let lastToken = new System.String(lexbuf.Lexeme) in
            print "Parse failed at (%s,%s) on token %s\n" [string_of_int line ; string_of_int column ; lastToken] ;
            failwith message

let rename_apart (p : raw_proof) : raw_proof =
    let ctr : ref<int> = mk_ref 0 in
    let dict : smap<(ref<(list<string>)>)> = smap_create 10000 in
    let stack : ref<(list<(list<string>)>)> = mk_ref [] in
    let fresh_name () : string =
        let x : int = !ctr in
        ctr := !ctr + 1 ;
        "@def!" ^ (string_of_int x)
    in
    let reset_names () : unit =
        ctr := 0 ;
        smap_clear dict
    in
    let rename_let ((var , x) : string * raw_proof) : string * raw_proof * string =
        (var , x , fresh_name ())
    in
    let rename_bound (n : int) (l : list<(string * sort)>) : int * list<(string * sort * string)> =
        let rec aux (m : int) (i : list<(string * sort)>) (o : list<(string * sort * string)>) : int * list<(string * sort * string)> =
            match i with
                | (var , st) :: tl -> aux (m + 1) tl ((var , st , "@bind!" ^ (string_of_int (m + 1))) :: o)
                | [] -> (m , List.rev o)
        in
        aux n l []
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
    let rec aux (n : int) (proof : raw_proof) : raw_proof =
        match proof with
            // | Terminal s -> begin match smap_try_find dict s with
            //     | None -> proof
            //     | Some ref -> match !ref with
            //         | hd :: tl -> Terminal hd
            //         | [] -> failwith "Impossible"
            // end
            | Application (f , args) -> Application (f , List.map (aux n) args)
            | Binding (quant , bindings , scope) ->
                let (nx , renaming) : int * list<(string * sort * string)> = rename_bound n bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((_ , st , nm) : string * sort * string) -> (nm , st)) renaming in
                push renaming ;
                let new_scope : raw_proof = aux nx scope in
                pop () ;
                Binding (quant , new_bindings , new_scope)
            | Let (bindings , scope) ->
                let renaming : list<(string * raw_proof * string)> =
                    bindings |>
                    List.map (fun ((var , pf) : string * raw_proof) -> (var , aux n proof)) |>
                    List.map rename_let
                in
                let new_bindings : list<(string * raw_proof)> =
                    List.map (fun ((_ , pf , nm) : string * raw_proof * string) -> (nm , pf)) renaming
                in
                push renaming ;
                let new_scope : raw_proof = aux n scope in
                pop () ;
                Let (new_bindings , new_scope)
            | IntegerConst _
            | BooleanConst _ -> proof
            | Arbitrary (p1 , p2) -> Arbitrary (aux n p1 , aux n p2)
            | Congruence (p1 , p2) -> Congruence (List.map (aux n) p1 , aux n p2)
            | Reflexivity p -> Reflexivity (aux n p)
            | Symmetry (p1 , p2) -> Symmetry (aux n p1 , aux n p2)
            | Transitivity (p1 , p2 , p3) -> Transitivity (aux n p1 , aux n p2 , aux n p3)
            | Reachability (p1 , p2) -> Reachability (List.map (aux n) p1 , aux n p2)
            | Generalization p -> Generalization (aux n p)
            | Instantiation (p1 , p2) -> Instantiation (List.map (aux n) p1 , aux n p2)
            | Rewrite p -> Rewrite (aux n p)
            | ModusPonens (p1 , p2 , p3) -> ModusPonens (aux n p1 , aux n p2 , aux n p3)
            | ModusPonensEquiv (p1 , p2 , p3) -> ModusPonensEquiv (aux n p1 , aux n p2 , aux n p3)
            | Skolemization p -> Skolemization (aux n p)
            | PosNnf p -> PosNnf p
            | NegNnf p -> NegNnf p
            | UnitResolution (p1 , p2) -> UnitResolution (p1 , p2)
            | Asserted p -> Asserted (aux n p)
            | TriangleInequality p -> TriangleInequality (aux n p)
            | FarkasLemma (p1 , p2) -> FarkasLemma (List.map (aux n) p1 , List.map (aux n) p2)
            | AssignBounds (p1 , p2) -> AssignBounds (List.map (aux n) p1 , aux n p2)
            | Arithmetics p -> Arithmetics (aux n p)
            | ProofEnd -> failwith "ProofEnd found while renaming proof apart"
    in
    let res : raw_proof = aux 0 p in
    let top_let : raw_proof = Let ([(fresh_name () , res)] , ProofEnd) in
    reset_names () ;
    top_let

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
            // | Terminal s -> (Terminal (boundvar s pars) , out)
            | Application (f , args) ->
                let (ps , ls) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) args out in
                (Application (f , ps) , out)
            | Binding (quant , bindings , scope) ->
                let new_pars : list<(string * sort)> = pars @ bindings in
                let new_bindings : list<(string * sort)> = List.map (fun ((var , st) : string * sort) -> (boundvar var new_pars , st)) bindings in
                let (new_scope, new_lets) : raw_proof * list<parametric_let> = aux (pars @ bindings) scope out in
                (Binding (quant , new_bindings , new_scope) , new_lets)
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
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
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
            | PosNnf p ->
                let (q , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p out in
                (PosNnf q , out)
            | NegNnf p ->
                let (q , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p out in
                (NegNnf q , out)
            | UnitResolution (p1 , p2) ->
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (Instantiation (q1 , q2) , out)
            | Asserted p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Asserted q , out)
            | TriangleInequality p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (TriangleInequality p , out)
            | FarkasLemma (p1 , p2) ->
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
                let (q2 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p2 out in
                (FarkasLemma (q1 , q2) , out)
            | AssignBounds (p1 , p2) ->
                let (q1 , out) : list<raw_proof> * list<parametric_let> = map_n_cheese (aux pars) p1 out in
                let (q2 , out) : raw_proof * list<parametric_let> = aux pars p2 out in
                (AssignBounds (q1 , q2) , out)
            | Arithmetics p ->
                let (q , out) : raw_proof * list<parametric_let> = aux pars p out in
                (Arithmetics p , out)
            | ProofEnd -> (ProofEnd , out)
    in
    let (_ , ls) : raw_proof * list<parametric_let> = aux [] proof [] in
    List.rev ls

let check_dependencies (refutation : list<parametric_let>) : bool =
    let check_binding ((res , n) : bool * int) ((var , st) : string * sort) : bool * int =
        (res && (var = "@bind!" ^ (string_of_int (n + 1))) , n + 1)
    in
    let check_let (lets : list<string>) ((nm , bd , pf) : parametric_let) : bool =
        let (bindings_ok , _) : bool * int = List.fold_left check_binding (true , 0) bd in
        let name_ok : bool = for_all (fun (s : string) -> s <> nm) lets in
        let rec proof_ok (n : int) (pf : raw_proof) : bool =
            match pf with
                // | Terminal s -> begin
                //     if starts_with s "@def!" then for_some (fun (ss : string) -> ss = s) lets
                //     elif starts_with s "@bind!" then (int_of_string (substring_from s 6)) <= n
                //     else true
                // end
                | Application (_ , args) -> for_all (proof_ok n) args
                | Binding (quant, bindings , scope) ->
                    proof_ok (n + (List.length bindings)) scope
                | Let (bindings , scope) -> false
                | IntegerConst _
                | BooleanConst _ -> true
                | Arbitrary (p1 , p2)
                | Symmetry (p1 , p2) -> (proof_ok n p1) && (proof_ok n p2)
                | Transitivity (p1 , p2 , p3)
                | ModusPonens (p1 , p2 , p3)
                | ModusPonensEquiv (p1 , p2 , p3) -> (proof_ok n p1) && (proof_ok n p2) && (proof_ok n p3)
                | Reachability (p1 , p2) 
                | Instantiation (p1 , p2)
                | Congruence (p1 , p2)
                | UnitResolution (p1 , p2)
                | AssignBounds (p1 , p2) -> (for_all (proof_ok n) p1) && (proof_ok n p2)
                | Rewrite p
                | Generalization p
                | Skolemization p
                | Asserted p
                | Reflexivity p
                | Arithmetics p
                | TriangleInequality p -> proof_ok n p
                | FarkasLemma (p1 , p2) -> (for_all (proof_ok n) p1) && (for_all (proof_ok n) p2)
                | PosNnf p
                | NegNnf p -> (for_all (proof_ok n) p)
                | ProofEnd -> failwith "ProofEnd found while checking parametric let dependencies"
        in
        bindings_ok && name_ok && (proof_ok 0 pf)
    in
    let aux ((b , ls) : bool * list<string>) (pl : parametric_let) : bool * list<string> =
        let (nm , _ , _) : string * list<(string * sort)> * raw_proof = pl in
        (b && (check_let ls pl) , nm :: ls)
    in
    let (res, _) : bool * list<string> = List.fold_left aux (true , []) refutation in
    res

// type smt_term =
//     | TermVariable of int
//     | TermReference of string
//     | Application of operator * smt_term
//     | Forall of list<sort> * smt_term
//     | Lambda of list<sort> * smt_term
//     | IntegerConst of int
//     | BooleanConst of bool

// type smt_proof =
//     | ProofReference of string
//     | Arbitrary of smt_proof * smt_term
//     | Congruence of list<smt_proof> * smt_term
//     | Reachability of list<smt_proof> * smt_term
    

let analyze_proof (res : z3result) : unit =
    match res.z3result_status with
        | UNSAT(_ , Some reft) -> begin
            print "\n\nProof:\n\n" [];
            // print (String.concat "\n" reft) [] ;
            // print "\n\n" [] ;
            print (String.concat " " reft) [] ;
            print "\n\n" [] ;
            let str : string = String.concat " " reft in
            let (fundecls , raw) : smt_proof_section = parse_proof str in
            // let renamed : raw_proof = rename_apart raw in
            // let topified : list<parametric_let> = topify raw in
            // if check_dependencies topified
            //     then print "Proof dependencies checked OK" []
            //     else print "Proof dependencies failed to checked" [] ;
            ()
        end
        | _ -> ()