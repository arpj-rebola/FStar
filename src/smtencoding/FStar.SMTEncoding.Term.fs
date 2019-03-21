(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

module FStar.SMTEncoding.Term
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util
module BU = FStar.Util
module U = FStar.Syntax.Util

let escape (s:string) = BU.replace_char s '\'' '_'

type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of int // BitVectors parameterized by their size
  | Array of sort * sort
  | Arrow of sort * sort
  | Sort of string

let rec strSort x = match x with
  | Bool_sort  -> "Bool"
  | Int_sort  -> "Int"
  | Term_sort -> "Term"
  | String_sort -> "FString"
  | Fuel_sort -> "Fuel"
  | BitVec_sort n -> format1 "(_ BitVec %s)" (string_of_int n)
  | Array(s1, s2) -> format2 "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> format2 "(%s -> %s)" (strSort s1) (strSort s2)
  | Sort s -> s

type op =
  | TrueOp
  | FalseOp
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | BvAnd
  | BvXor
  | BvOr
  | BvAdd
  | BvSub
  | BvShl
  | BvShr  // unsigned shift right\
  | BvUdiv
  | BvMod
  | BvMul
  | BvUlt
  | BvUext of Prims.int
  | NatToBv of Prims.int // need to explicitly define the size of the bitvector
  | BvToNat
  | ITE
  | Var of string //Op corresponding to a user/encoding-defined uninterpreted function

type qop =
  | Forall
  | Exists

//de Bruijn representation of terms in locally nameless style
type term' =
  | Integer    of string //unbounded mathematical integers
  | BoundV     of int
  | FreeV      of fv
  | App        of op  * list<term> //ops are always fully applied; we're in a first-order theory
  | Quant      of qop
                  * list<list<pat>>  //disjunction of conjunctive patterns
                  * option<int>      //an optional weight; seldom used
                  * list<sort>       //sorts of each bound variable
                  * term             //body
                  * Syntax.memo<string>   //qid
  | Let        of list<term> // bound terms
                * term       // body
  | Labeled    of term * string * Range.range
  | LblPos     of term * string
and pat  = term
and term = {tm:term'; freevars:Syntax.memo<fvs>; rng:Range.range}
and fv = string * sort
and fvs = list<fv>

type caption = option<string>
type binders = list<(string * sort)>
type constructor_field = string  //name of the field
                       * sort    //sort of the field
                       * bool    //true if the field is projectible
type constructor_t = (string * list<constructor_field> * sort * int * bool)
type constructors  = list<constructor_t>
type fact_db_id =
    | Name of Ident.lid
    | Namespace of Ident.lid
    | Tag of string
type assumption = {
    assumption_term: term;
    assumption_caption: caption;
    assumption_name: string;
    assumption_fact_ids:list<fact_db_id>
}

type decl =
  | FuelDeclaration
  | SortDeclaration of string
  | GenerateOptions
  | Hardcoded  of string
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<sort> * sort * term * caption
  | Assume     of assumption
  | Caption    of string
  | Module     of string * list<decl>
  | Eval       of term
  | Echo       of string
  | RetainAssumptions of list<string>
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption  of string * string
  | GetStatistics
  | GetReasonUnknown
type decls_t = list<decl>

type error_label = (fv * string * Range.range)
type error_labels = list<error_label>

let fv_eq (x:fv) (y:fv) = fst x = fst y
let fv_sort x = snd x
let freevar_eq x y = match x.tm, y.tm with
    | FreeV x, FreeV y -> fv_eq x y
    | _ -> false
let freevar_sort  = function
    | {tm=FreeV x} -> fv_sort x
    | _ -> failwith "impossible"
let fv_of_term = function
    | {tm=FreeV fv} -> fv
    | _ -> failwith "impossible"
let rec freevars t = match t.tm with
  | Integer _
  | BoundV _ -> []
  | FreeV fv -> [fv]
  | App(_, tms) -> List.collect freevars tms
  | Quant(_, _, _, _, t, _)
  | Labeled(t, _, _)
  | LblPos(t, _) -> freevars t
  | Let (es, body) -> List.collect freevars (body::es)

//memo-ized
let free_variables t = match !t.freevars with
  | Some b -> b
  | None ->
    let fvs = BU.remove_dups fv_eq (freevars t) in
    t.freevars := Some fvs;
    fvs

let rec assign_qids (d : decl) : unit =
    let in_terms (nm : string) (t : term) : unit =
        let set_qid (qid : Syntax.memo<string>) (n : int) : int =
            match !qid with
                | Some _ -> n
                | None ->
                    qid := Some (nm ^ "." ^ (string_of_int n)) ;
                    n + 1
        in
        let rec aux (n : int) (tx : term) : int =
            match tx.tm with
                | App (_ , tms) -> List.fold_left aux n tms
                | Quant (_ , _ , _ , _ , scp , qid) ->
                    let nx : int = set_qid qid n in
                    aux nx scp
                | Let (tms , scp) ->
                    let nx : int = List.fold_left aux n tms in
                    aux nx scp
                | Labeled (scp , _ , _)
                | LblPos (scp, _) -> aux n scp
                | _ -> n

        in
        aux 0 t |> ignore
    in
    match d with
        | DefineFun (nm , _ , _ , tm , _) -> in_terms ("funqid_" ^ nm) tm
        | Assume a -> in_terms a.assumption_name a.assumption_term
        | Module (_ , ds) -> List.iter assign_qids ds
        | _ -> ()

(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let qop_to_string = function
  | Forall -> "forall"
  | Exists -> "exists"

let op_to_string = function
  | TrueOp -> "true"
  | FalseOp -> "false"
  | Not -> "not"
  | And -> "and"
  | Or  -> "or"
  | Imp -> "=>"
  | Iff -> "iff"
  | Eq  -> "="
  | LT  -> "<"
  | LTE -> "<="
  | GT  -> ">"
  | GTE -> ">="
  | Add -> "+"
  | Sub -> "-"
  | Div -> "div"
  | Mul -> "*"
  | Minus -> "-"
  | Mod  -> "mod"
  | ITE -> "ite"
  | BvAnd -> "bvand"
  | BvXor -> "bvxor"
  | BvOr -> "bvor"
  | BvAdd -> "bvadd"
  | BvSub -> "bvsub"
  | BvShl -> "bvshl"
  | BvShr -> "bvlshr"
  | BvUdiv -> "bvudiv"
  | BvMod -> "bvurem"
  | BvMul -> "bvmul"
  | BvUlt -> "bvult"
  | BvToNat -> "bv2int"
  | BvUext n -> format1 "(_ zero_extend %s)" (string_of_int n)
  | NatToBv n -> format1 "(_ int2bv %s)" (string_of_int n)
  | Var s -> s

let weightToSmt = function
  | None -> ""
  | Some i -> BU.format1 ":weight %s\n" (string_of_int i)

let rec hash_of_term' (t : term') : string = match t with
  | Integer i ->  i
  | BoundV i  -> "@"^string_of_int i
  | FreeV x   -> fst x ^ ":" ^ strSort (snd x) //Question: Why is the sort part of the hash?
  | App(op, tms) -> "("^(op_to_string op)^(List.map hash_of_term tms |> String.concat " ")^")"
  | Labeled(t, r1, r2) -> hash_of_term t ^ r1 ^ (Range.string_of_range r2)
  | LblPos(t, r) -> "(! " ^hash_of_term t^ " :lblpos " ^r^ ")"
  | Quant(qop, pats, wopt, sorts, body, _) ->
      "("
    ^ (qop_to_string qop)
    ^ " ("
    ^ (List.map strSort sorts |> String.concat " ")
    ^ ")(! "
    ^ (hash_of_term body)
    ^ " "
    ^ (weightToSmt wopt)
    ^ " "
    ^ (pats |> List.map (fun pats -> (List.map hash_of_term pats |> String.concat " ")) |> String.concat "; ")
    ^ "))"
  | Let (es, body) ->
    "(let (" ^ (List.map hash_of_term es |> String.concat " ") ^ ") " ^ hash_of_term body ^ ")"
and hash_of_term (tm : term) : string = hash_of_term' tm.tm

let mkBoxFunctions (s : string) : string * string = (s, s ^ "_proj_0")
let boxIntFun : string * string                   = mkBoxFunctions "BoxInt"
let boxBoolFun : string * string                  = mkBoxFunctions "BoxBool"
let boxStringFun : string * string                = mkBoxFunctions "BoxString"
let boxBitVecFun (sz : int) : string * string     = mkBoxFunctions ("BoxBitVec" ^ (string_of_int sz))

// Assume the Box/Unbox functions to be injective
let isInjective (s : string) : bool =
    if (FStar.String.length s >= 3) then
        String.substring s 0 3 = "Box" &&
        not (List.existsML (fun c -> c = '.') (FStar.String.list_of_string s))
    else false

let mk (t : term') (r : Range.range) : term                         = {tm=t; freevars=BU.mk_ref None; rng=r}
let mkTrue (r : Range.range) : term                                 = mk (App(TrueOp, [])) r
let mkFalse (r : Range.range) : term                                = mk (App(FalseOp, [])) r
let mkInteger (i : string) (r : Range.range) : term                 = mk (Integer (ensure_decimal i)) r
let mkInteger' (i : int) (r : Range.range) : term                   = mkInteger (string_of_int i) r
let mkBoundV (i : int) (r : Range.range) : term                     = mk (BoundV i) r
let mkFreeV (x : fv) (r : Range.range) : term                       = mk (FreeV x) r
let mkApp' (f : op * list<term>)  (r : Range.range) : term          = mk (App f) r
let mkApp ((s , args) : string * list<term>) (r : Range.range) : term = mk (App (Var s, args)) r
let mkNot (t : term) (r : Range.range) : term = match t.tm with
  | App(TrueOp, _)  -> mkFalse r
  | App(FalseOp, _) -> mkTrue r
  | _ -> mkApp'(Not, [t]) r
let mkAnd ((t1 , t2) : term * term) (r : Range.range) : term = match t1.tm, t2.tm with
  | App(TrueOp, _), _ -> t2
  | _, App(TrueOp, _) -> t1
  | App(FalseOp, _), _
  | _, App(FalseOp, _) -> mkFalse r
  | App(And, ts1), App(And, ts2) -> mkApp'(And, ts1@ts2) r
  | _, App(And, ts2) -> mkApp'(And, t1::ts2) r
  | App(And, ts1), _ -> mkApp'(And, ts1@[t2]) r
  | _ -> mkApp'(And, [t1;t2]) r
let mkOr ((t1 , t2) : term * term) (r : Range.range) : term = match t1.tm, t2.tm with
  | App(TrueOp, _), _
  | _, App(TrueOp, _) -> mkTrue r
  | App(FalseOp, _), _ -> t2
  | _, App(FalseOp, _) -> t1
  | App(Or, ts1), App(Or, ts2) -> mkApp'(Or, ts1@ts2) r
  | _, App(Or, ts2) -> mkApp'(Or, t1::ts2) r
  | App(Or, ts1), _ -> mkApp'(Or, ts1@[t2]) r
  | _ -> mkApp'(Or, [t1;t2]) r
let mkImp ((t1 , t2) : term * term) (r : Range.range) : term = match t1.tm, t2.tm with
  | _, App(TrueOp, _)
  | App(FalseOp, _), _ -> mkTrue r
  | App(TrueOp, _), _ -> t2
  | _, App(Imp, [t1'; t2']) -> mkApp'(Imp, [mkAnd(t1, t1') r; t2']) r
  | _ -> mkApp'(Imp, [t1; t2]) r

let mk_bin_op (op : op) ((t1 , t2) : term * term) (r : Range.range) : term = mkApp'(op, [t1;t2]) r
let mkMinus (t : term) (r : Range.range) : term = mkApp'(Minus, [t]) r
let mkNatToBv (sz : int) (t : term) (r :Range.range) : term = mkApp'(NatToBv sz, [t]) r
let mkBvUext (sz : int) (t : term) (r : Range.range) : term = mkApp'(BvUext sz, [t]) r
let mkBvToNat (t : term) (r : Range.range) : term = mkApp'(BvToNat, [t]) r
let mkBvAnd : (term * term) -> Range.range -> term = mk_bin_op BvAnd
let mkBvXor : (term * term) -> Range.range -> term = mk_bin_op BvXor
let mkBvOr : (term * term) -> Range.range -> term = mk_bin_op BvOr
let mkBvAdd : (term * term) -> Range.range -> term = mk_bin_op BvAdd
let mkBvSub : (term * term) -> Range.range -> term = mk_bin_op BvSub
let mkBvShl (sz : int) ((t1 , t2) : term * term) (r : Range.range) : term = mkApp'(BvShl, [t1;(mkNatToBv sz t2 r)]) r
let mkBvShr (sz : int) ((t1 , t2) : term * term) (r : Range.range) : term  = mkApp'(BvShr, [t1;(mkNatToBv sz t2 r)]) r
let mkBvUdiv (sz : int) ((t1 , t2) : term * term) (r : Range.range) : term  = mkApp'(BvUdiv, [t1;(mkNatToBv sz t2 r)]) r
let mkBvMod (sz : int) ((t1 , t2) : term * term) (r : Range.range) : term  = mkApp'(BvMod, [t1;(mkNatToBv sz t2 r)]) r
let mkBvMul (sz : int) ((t1 , t2) : term * term) (r : Range.range) : term  = mkApp' (BvMul, [t1;(mkNatToBv sz t2 r)]) r
let mkBvUlt : (term * term) -> Range.range -> term = mk_bin_op BvUlt
let mkIff : (term * term) -> Range.range -> term = mk_bin_op Iff
let mkEq ((t1 , t2) : term * term) (r : Range.range) : term  = match t1.tm, t2.tm with
    | App (Var f1, [s1]), App (Var f2, [s2]) when f1 = f2 && isInjective f1 ->
        mk_bin_op Eq (s1, s2) r
    | _ -> mk_bin_op Eq (t1, t2) r
let mkLT : (term * term) -> Range.range -> term = mk_bin_op LT
let mkLTE : (term * term) -> Range.range -> term = mk_bin_op LTE
let mkGT : (term * term) -> Range.range -> term = mk_bin_op GT
let mkGTE : (term * term) -> Range.range -> term = mk_bin_op GTE
let mkAdd : (term * term) -> Range.range -> term = mk_bin_op Add
let mkSub : (term * term) -> Range.range -> term = mk_bin_op Sub
let mkDiv : (term * term) -> Range.range -> term = mk_bin_op Div
let mkMul : (term * term) -> Range.range -> term = mk_bin_op Mul
let mkMod : (term * term) -> Range.range -> term = mk_bin_op Mod
let mkITE ((t1 , t2 , t3) : term * term * term) (r : Range.range) =
  match t1.tm with
  | App(TrueOp, _) -> t2
  | App(FalseOp, _) -> t3
  | _ -> begin
    match t2.tm, t3.tm with
    | App(TrueOp,_), App(TrueOp, _) -> mkTrue r
    | App(TrueOp,_), _ -> mkImp (mkNot t1 t1.rng, t3) r
    | _, App(TrueOp, _) -> mkImp(t1, t2) r
    | _, _ ->  mkApp'(ITE, [t1; t2; t3]) r
  end
let mkCases (t : list<term>) (r : Range.range) = match t with
  | [] -> failwith "Impos"
  | hd::tl -> List.fold_left (fun out t -> mkAnd (out, t) r) hd tl

// Returns None if the pattern is OK, Some term if a subterm is problematic.
// Problematic patterns include boolean connectives, BV operations, quantifiers or LblPos's
let check_pattern_ok (t:term) : option<term> =
    let rec aux (t : term) : option<term> =
        match t.tm with
        | Integer _
        | BoundV _
        | FreeV _ -> None
        | Let(tms, tm) ->
          aux_l (tm::tms)
        | App(head, terms) ->
            let head_ok : bool =
                match head with
                | Var _ -> true
                | TrueOp
                | FalseOp -> true
                | Not
                | And
                | Or
                | Imp
                | Iff
                | Eq -> false
                | LT
                | LTE
                | GT
                | GTE
                | Add
                | Sub
                | Div
                | Mul
                | Minus
                | Mod -> true
                | BvAnd
                | BvXor
                | BvOr
                | BvAdd
                | BvSub
                | BvShl
                | BvShr
                | BvUdiv
                | BvMod
                | BvMul
                | BvUlt
                | BvUext _
                | NatToBv _
                | BvToNat
                | ITE -> false
            in
            if not head_ok then Some t
            else aux_l terms
        | Labeled(t, _, _) ->
          aux t
        | Quant _
        | LblPos _ -> Some t
    and aux_l (ts : list<term>) : option<term> =
        match ts with
        | [] -> None
        | t::ts ->
          match aux t with
          | Some t -> Some t
          | None -> aux_l ts
    in
    aux t

let rec print_smt_term (t:term) : string =
  match t.tm with
  | Integer n               -> BU.format1 "(Integer %s)" n
  | BoundV  n               -> BU.format1 "(BoundV %s)" (BU.string_of_int n)
  | FreeV  fv               -> BU.format1 "(FreeV %s)" (fst fv)
  | App (op, l)             -> BU.format2 "(%s %s)" (op_to_string op) (print_smt_term_list l)
  | Labeled(t, r1, r2)      -> BU.format2 "(Labeled '%s' %s)" r1 (print_smt_term t)
  | LblPos(t, s)            -> BU.format2 "(LblPos %s %s)" s (print_smt_term t)
  | Quant (qop, l, _, _, t, _) -> BU.format3 "(%s %s %s)" (qop_to_string qop) (print_smt_term_list_list l) (print_smt_term t)
  | Let (es, body)          -> BU.format2 "(let %s %s)" (print_smt_term_list es) (print_smt_term body)
and print_smt_term_list (l:list<term>) : string =
  List.map print_smt_term l |> String.concat " "
and print_smt_term_list_list (l:list<list<term>>) : string =
    List.fold_left (fun s l -> (s ^ "; [ " ^ (print_smt_term_list l) ^ " ] ")) "" l

let mkQuantQid (r : Range.range) (check_pats : bool) ((qop , pats , wopt , vars , body , qid) : qop * list<list<pat>> * option<int> * list<sort> * term * Syntax.memo<string>) : term =
    let all_pats_ok (pats : list<list<pat>>) : list<list<pat>> =
        if not check_pats then pats else
        match BU.find_map pats (fun x -> BU.find_map x check_pattern_ok) with
        | None -> pats
        | Some p ->
          begin
            Errors.log_issue
                    r
                    (Errors.Warning_SMTPatternMissingBoundVar,
                     BU.format1 "Pattern (%s) contains illegal symbols; dropping it" (print_smt_term p));
            []
           end
    in
    if List.length vars = 0 then body
    else match body.tm with
         | App(TrueOp, _) -> body
         | _ -> mk (Quant(qop, all_pats_ok pats, wopt, vars, body, qid)) r

let mkQuant (r : Range.range) (check_pats : bool) ((qop , pats , wopt , vars , body) : qop * list<list<pat>> * option<int> * list<sort> * term) : term =
    mkQuantQid r check_pats (qop , pats , wopt , vars , body, BU.mk_ref None)

let mkLet ((es , body) : list<term> * term) (r : Range.range) : term =
  if List.length es = 0 then body
  else mk (Let (es,body)) r

(*****************************************************)
(* abstracting free names; instantiating bound vars  *)
(*****************************************************)
let abstr (fvs : list<fv>) (t : term) : term = //fvs is a subset of the free vars of t; the result closes over fvs
  let nvars : int = List.length fvs in
  let index_of (fv : fv) : option<int> = match BU.try_find_index (fv_eq fv) fvs with
    | None -> None
    | Some i -> Some (nvars - (i + 1))
  in
  let rec aux (ix : int) (t : term) : term =
    match !t.freevars with
    | Some [] -> t
    | _ ->
      begin match t.tm with
        | Integer _
        | BoundV _ -> t
        | FreeV x ->
          begin match index_of x with
            | None -> t
            | Some i -> mkBoundV (i + ix) t.rng
          end
        | App(op, tms) -> mkApp'(op, List.map (aux ix) tms) t.rng
        | Labeled(t, r1, r2) -> mk (Labeled(aux ix t, r1, r2)) t.rng
        | LblPos(t, r) -> mk (LblPos(aux ix t, r)) t.rng
        | Quant(qop, pats, wopt, vars, body, _) ->
          let n = List.length vars in
          mkQuant t.rng false (qop, pats |> List.map (List.map (aux (ix + n))), wopt, vars, aux (ix + n) body)
        | Let (es, body) ->
          let (ix , es_rev) : int * list<term> = List.fold_left (fun (ix, l) e -> ix+1, (aux ix e)::l) (ix, []) es in
          mkLet (List.rev es_rev, aux ix body) t.rng
      end
  in
  aux 0 t

let inst (tms : list<term>) (t : term) : term =
  let tms : list<term> = List.rev tms in //forall x y . t   ... y is an index 0 in t
  let n : int = List.length tms in //instantiate the first n BoundV's with tms, in order
  let rec aux (shift : int) (t : term) : term = match t.tm with
    | Integer _
    | FreeV _ -> t
    | BoundV i ->
      if 0 <= i - shift && i - shift < n
      then List.nth tms (i - shift)
      else t
    | App(op, tms) -> mkApp'(op, List.map (aux shift) tms) t.rng
    | Labeled(t, r1, r2) -> mk (Labeled(aux shift t, r1, r2)) t.rng
    | LblPos(t, r) -> mk (LblPos(aux shift t, r)) t.rng
    | Quant(qop, pats, wopt, vars, body, qid) ->
      let m = List.length vars in
      let shift = shift + m in
      mkQuantQid t.rng false (qop, pats |> List.map (List.map (aux shift)), wopt, vars, aux shift body, qid)
    | Let (es, body) ->
      let shift, es_rev = List.fold_left (fun (ix, es) e -> shift+1, aux shift e::es) (shift, []) es in
      mkLet (List.rev es_rev, aux shift body) t.rng
  in
  aux 0 t

  
let subst (t:term) (fv:fv) (s:term) : term =
  inst [s] (abstr [fv] t)
  
let mkQuant' (r : Range.range) ((qop , pats , wopt , vars , body) : qop * list<list<pat>> * option<int> * list<fv> * term) : term =
    mkQuant r true (qop, pats |> List.map (List.map (abstr vars)), wopt, List.map fv_sort vars, abstr vars body)

//these are the external facing functions for building quantifiers
let mkForall (r : Range.range) ((pats , vars , body) : list<list<pat>> * list<fv> * term) : term =
    mkQuant' r (Forall, pats, None, vars, body)
let mkForall'' (r : Range.range) ((pats , wopt , sorts , body) : list<list<pat>> * option<int> * list<sort> * term) : term =
    mkQuant r true (Forall, pats, wopt, sorts, body)
let mkForall' (r : Range.range) ((pats , wopt , vars , body) : list<list<pat>> * option<int> * list<fv> * term) : term =
    mkQuant' r (Forall, pats, wopt, vars, body)
let mkExists (r : Range.range) ((pats , vars , body): list<list<pat>> * list<fv> * term) =
    mkQuant' r (Exists, pats, None, vars, body)

let mkLet' ((bindings , body) : list<(fv * term)> * term) r =
  let vars, es = List.split bindings in
  mkLet (es, abstr vars body) r

let norng : Range.range = Range.dummyRange
let prrng : Range.range = Range.preludeRange
let mkDefineFun ((nm , vars , s , tm , c) : string * list<fv> * sort * term * caption) : decl =
  DefineFun(nm, List.map fv_sort vars, s, abstr vars tm, c)
let constr_id_of_sort (sort : sort) : string = format1 "%s_constr_id" (strSort sort)

let fresh_token (rng : Range.range) ((tok_name , sort) : string * sort) (id : int) : decl =
    let a_name = "fresh_token_" ^ tok_name in
    let a = {assumption_name=escape a_name;
             assumption_caption=Some "fresh token";
             assumption_term=mkEq(mkInteger' id rng,
                                  mkApp(constr_id_of_sort sort,
                                        [mkApp (tok_name,[]) rng]) rng) rng;
             assumption_fact_ids=[]} in
    Assume a

let fresh_constructor (rng : Range.range) ((name , arg_sorts , sort , id) : string * list<sort> * sort * int) : decl =
  let id = string_of_int id in
  let bvars = arg_sorts |> List.mapi (fun i s -> mkFreeV("x_" ^ string_of_int i, s) norng) in
  let bvar_names = List.map fv_of_term bvars in
  let capp = mkApp(name, bvars) norng in
  let cid_app = mkApp(constr_id_of_sort sort, [capp]) norng in
  let a_name = "constructor_distinct_" ^ name in
  let a = {
    assumption_name=escape a_name;
    assumption_caption=Some "Constructor distinct";
    assumption_term=mkForall rng ([[capp]], bvar_names, mkEq(mkInteger id norng, cid_app) norng);
    assumption_fact_ids=[]
  } in
  Assume a

let injective_constructor (rng : Range.range) ((name , fields , st) : string * list<constructor_field> * sort) : list<decl> =
    let n_bvars = List.length fields in
    let bvar_name (i : int) : string = "x_" ^ string_of_int i in
    let bvar_index (i : int) : int = n_bvars - (i + 1) in
    let bvar (i : int) (s : sort) : Range.range -> term = mkFreeV(bvar_name i, s) in
    let bvars = fields |> List.mapi (fun (i : int) (_, s, _) -> bvar i s norng) in
    let bvar_names = List.map fv_of_term bvars in
    let capp = mkApp(name, bvars) norng in
    fields
    |> List.mapi (fun i (iname, isort, projectible) ->
            let cproj_app = mkApp(iname, [capp]) norng in
            let proj_name = DeclFun(iname, [st], isort, Some "Projector") in
            if projectible
            then let a = {
                    assumption_name = escape ("projection_inverse_" ^ iname);
                    assumption_caption = Some "Projection inverse";
                    assumption_term = mkForall rng ([[capp]], bvar_names, mkEq(cproj_app, bvar i isort norng) norng);
                    assumption_fact_ids = []
                 } in
                 [proj_name; Assume a]
            else [proj_name])
    |> List.flatten

let constructor_to_decl (rng : Range.range) ((name , fields , st , id , injective) : string * list<constructor_field> * sort * int * bool) : list<decl> =
    let injective : bool = injective || true in
    let field_sorts : list<sort> = fields |> List.map (fun (_, sort, _) -> sort) in
    let cdecl : decl = DeclFun(name, field_sorts, st, Some "Constructor") in
    let cid : decl = fresh_constructor rng (name, field_sorts, st, id) in
    let disc : decl =
        let disc_name : string = "is-"^name in
        let xfv : fv = ("x", st) in
        let xx : term = mkFreeV xfv norng in
        let disc_eq : term = mkEq(mkApp(constr_id_of_sort st, [xx]) norng, mkInteger (string_of_int id) norng) norng in
        let (proj_terms , ex_vars) : list<term> * list<list<fv>> =
            fields
         |> List.mapi (fun i (proj, s, projectible) ->
                if projectible
                then mkApp(proj, [xx]) norng, []
                else let fi = ("f_" ^ BU.string_of_int i, s) in
                     mkFreeV fi norng, [fi])
         |> List.split in
        let ex_vars : list<fv> = List.flatten ex_vars in
        let disc_inv_body : term = mkEq(xx, mkApp(name, proj_terms) norng) norng in
        let disc_inv_body : term = match ex_vars with
            | [] -> disc_inv_body
            | _ -> mkExists norng ([], ex_vars, disc_inv_body) in
        let disc_ax : term = mkAnd(disc_eq, disc_inv_body) rng in
        let def : decl = mkDefineFun(disc_name, [xfv], Bool_sort,
                    disc_ax,
                    Some "Discriminator definition") in
        def in
    let projs : list<decl> =
        if injective
        then injective_constructor rng (name, fields, st)
        else [] in
    Caption (format1 "<start constructor %s>" name)::cdecl::cid::projs@[disc]@[Caption (format1 "</end constructor %s>" name)]

(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let name_binders_inner (prefix_opt : option<string>) (outer_names : list<(string * sort)>) (start : int) (sorts : list<sort>) : list<(string * sort)> * list<string> * int =
    let (names , binders , n) : list<(string * sort)> * list<string> * int = sorts |> List.fold_left (fun ((names , binders , n) : list<(string * sort)> * list<string> * int) (s : sort) ->
        let prefix : string = match s with
            | Term_sort -> "@x"
            | _ -> "@u" in
        let prefix : string =
            match prefix_opt with
            | None -> prefix
            | Some p -> p ^ prefix in
        let nm : string = prefix ^ string_of_int n in
        let names : list<(string * sort)> = (nm,s)::names in
        let b : string = BU.format2 "(%s %s)" nm (strSort s) in
        names, b::binders, n+1)
        (outer_names, [], start)  in
    names, List.rev binders, n

let name_macro_binders (sorts : list<sort>) : list<fv> * list<string> =
    let (names , binders , n) : list<(string * sort)> * list<string> * int = name_binders_inner (Some "__") [] 0 sorts in
    List.rev names, binders

let termToSmt : bool -> string -> term -> string =
  fun (print_ranges : bool) (enclosing_name : string) (t : term) ->
      // let next_qid : unit -> string =
      //     let ctr : ref<int> = BU.mk_ref 0 in
      //     fun (depth : unit) ->
      //       let n : int = !ctr in
      //       BU.incr ctr;
      //       if n = 0 then enclosing_name
      //       else BU.format2 "%s.%s" enclosing_name (BU.string_of_int n)
      // in
      let remove_guard_free (pats : list<list<pat>>) : list<list<pat>> =
        pats |> List.map (fun ps ->
          ps |> List.map (fun tm ->
            match tm.tm with
            | App(Var "Prims.guard_free", [{tm=BoundV _}]) -> tm
            | App(Var "Prims.guard_free", [p]) -> p
            | _ -> tm))
      in
      let rec aux' (depth : int) (n : int) (names:list<fv>) (t : term) : string =
          let aux : int -> list<fv> -> term -> string = aux (depth + 1) in
          match t.tm with
          | Integer i     -> i
          | BoundV i -> List.nth names i |> fst
          | FreeV x -> fst x
          | App(op, []) -> op_to_string op
          | App(op, tms) -> BU.format2 "(%s %s)" (op_to_string op) (List.map (aux n names) tms |> String.concat "\n")
          | Labeled(t, _, _) -> aux n names t
          | LblPos(t, s) -> BU.format2 "(! %s :lblpos %s)" (aux n names t) s
          | Quant(qop, pats, wopt, sorts, body, qid) ->
              // let qid : string = next_qid () in
              let qidstr : string = match !qid with
                  | None -> "no-qid"
                  | Some str -> str
              in
            let (names , binders , n) : list<fv> *  list<string> * int = name_binders_inner None names n sorts in
            let binders : string = binders |> String.concat " " in
            let pats : list<list<pat>> = remove_guard_free pats in
            let pats_str : string =
                match pats with
                | [[]]
                | [] -> ";;no pats"
                | _ ->
                    pats
                    |> List.map (fun (pats : list<pat>) ->
                        format1 "\n:pattern (%s)" (String.concat " " (List.map (fun (p : pat) ->
                            format1 "%s" (aux n names p)) pats)))
                    |> String.concat "\n"
            in
            let res : string = BU.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                      [qop_to_string qop;
                       binders;
                       aux n names body;
                       weightToSmt wopt;
                       pats_str;
                       qidstr]
            in
            if not (BU.is_some !qid) then print ("Missing QID:\n" ^ res ^ "\n\n") [];
            res

          | Let (es, body) ->
              (* binders are reversed but according to the smt2 standard *)
              (* substitution should occur in parallel and order should not matter *)
              let (names , binders , n) : list<fv> * list<string> * int =
                  List.fold_left (fun ((names0 , binders , n0) : list<fv> * list<string> * int) (e : term) ->
                      let nm : string = "@lb" ^ string_of_int n0 in
                      let names0 : list<fv> = (nm, Term_sort)::names0 in
                      let b : string = BU.format2 "(%s %s)" nm (aux n names e) in
                      names0, b::binders, n0+1)
                  (names, [], n)
                es
              in
              BU.format2 "(let (%s)\n%s)"
                         (String.concat " " binders)
                         (aux n names body)

      and aux (depth : int) (n : int) (names : list<fv>) (t : term) : string =
          let s : string = aux' depth n names t in
          if print_ranges && t.rng <> norng && t.rng <> prrng
          then BU.format3 "\n;; def=%s; use=%s\n%s\n" (Range.string_of_range t.rng) (Range.string_of_use_range t.rng) s
          else s
      in
      aux 0 0 [] t

let caption_to_string (print_captions : bool) : (option<string> -> string)=
    function
    | Some c
       when print_captions ->
        let c : string = String.split ['\n'] c |> List.map BU.trim_string |> String.concat " " in
        ";;;;;;;;;;;;;;;;" ^ c ^ "\n"
    | _ -> ""


let rec declToSmt' (z3options : string) (print_captions : bool) (decl : decl) : string =
  assign_qids decl ;
  match decl with
  | FuelDeclaration -> "(declare-datatypes () ((Fuel \n\
                                        (ZFuel) \n\
                                        (SFuel (prec Fuel)))))"
  | SortDeclaration s -> "(declare-sort " ^ s ^ ")"
  | GenerateOptions -> z3options
  | Hardcoded s -> s
  | Module (s, decls) ->
    let res : string = List.map (declToSmt' z3options print_captions) decls |> String.concat "\n" in
    if Options.keep_query_captions()
    then BU.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                    s
                    res
                    s
                    (BU.string_of_int (List.length decls))
                    (BU.string_of_int (String.length res))
    else res
  | Caption c ->
    if print_captions
    then "\n" ^ (BU.splitlines c |> List.map (fun s -> "; " ^ s ^ "\n") |> String.concat "")
    else ""
  | DeclFun(f , argsorts , retsort , c) ->
    let l : list<string> = List.map strSort argsorts in
    format4 "%s(declare-fun %s (%s) %s)"
      (caption_to_string print_captions c)
      f
      (String.concat " " l)
      (strSort retsort)
  | DefineFun(f,arg_sorts,retsort,body,c) ->
    let names , binders : list<fv> * list<string> = name_macro_binders arg_sorts in
    let body : term = inst (List.map (fun x -> mkFreeV x norng) names) body in
    format5 "%s(define-fun %s (%s) %s\n %s)"
      (caption_to_string print_captions c)
      f
      (String.concat " " binders)
      (strSort retsort)
      (termToSmt print_captions (escape f) body)
  | Assume a ->
    let fact_ids_to_string (ids : list<fact_db_id>) : list<string> =
        ids |> List.map (function
        | Name n -> "Name " ^ Ident.text_of_lid n
        | Namespace ns -> "Namespace " ^ Ident.text_of_lid ns
        | Tag t -> "Tag " ^ t)
    in
    let fids : string =
        if print_captions
        then BU.format1 ";;; Fact-ids: %s\n"
                        (String.concat "; " (fact_ids_to_string a.assumption_fact_ids))
        else "" in
    let n : string = a.assumption_name in
    format4 "%s%s(assert (! %s\n:named %s))"
            (caption_to_string print_captions a.assumption_caption)
            fids
            (termToSmt print_captions n a.assumption_term)
            n
  | Eval t ->
    format1 "(eval %s)" (termToSmt print_captions "eval" t)
  | Echo s ->
    format1 "(echo \"%s\")" s
  | RetainAssumptions _ ->
    ""
  | CheckSat -> "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
  | GetUnsatCore -> "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
  | Push -> "(push)"
  | Pop -> "(pop)"
  | SetOption (s, v) -> format2 "(set-option :%s %s)" s v
  | GetStatistics -> "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
  | GetReasonUnknown-> "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"

and declToSmt         (z3options : string) (decl : decl) : string = declToSmt' z3options (Options.keep_query_captions())   decl
and declToSmt_no_caps (z3options : string) (decl : decl) : string = declToSmt' z3options false decl
and declsToSmt        (z3options : string) (decls : list<decl>) : string =
    List.map (declToSmt z3options) decls |> String.concat "\n"

and mkPrelude (z3options : string) : string =
  let basic : string = z3options ^
                "(declare-sort FString)\n\
                (declare-fun FString_constr_id (FString) Int)\n\
                \n\
                (declare-sort Term)\n\
                (declare-fun Term_constr_id (Term) Int)\n\
                (declare-datatypes () ((Fuel \n\
                                        (ZFuel) \n\
                                        (SFuel (prec Fuel)))))\n\
                (declare-fun MaxIFuel () Fuel)\n\
                (declare-fun MaxFuel () Fuel)\n\
                (declare-fun PreType (Term) Term)\n\
                (declare-fun Valid (Term) Bool)\n\
                (declare-fun HasTypeFuel (Fuel Term Term) Bool)\n\
                (define-fun HasTypeZ ((x Term) (t Term)) Bool\n\
                    (HasTypeFuel ZFuel x t))\n\
                (define-fun HasType ((x Term) (t Term)) Bool\n\
                    (HasTypeFuel MaxIFuel x t))\n\
                ;;fuel irrelevance\n\
                (assert (forall ((f Fuel) (x Term) (t Term))\n\
                                (! (= (HasTypeFuel (SFuel f) x t)\n\
                                          (HasTypeZ x t))\n\
                                   :pattern ((HasTypeFuel (SFuel f) x t)))))\n\
                (declare-fun NoHoist (Term Bool) Bool)\n\
                ;;no-hoist\n\
                (assert (forall ((dummy Term) (b Bool))\n\
                                (! (= (NoHoist dummy b)\n\
                                          b)\n\
                                   :pattern ((NoHoist dummy b)))))\n\
                (define-fun  IsTyped ((x Term)) Bool\n\
                    (exists ((t Term)) (HasTypeZ x t)))\n\
                (declare-fun ApplyTF (Term Fuel) Term)\n\
                (declare-fun ApplyTT (Term Term) Term)\n\
                (declare-fun Rank (Term) Int)\n\
                (declare-fun Closure (Term) Term)\n\
                (declare-fun ConsTerm (Term Term) Term)\n\
                (declare-fun ConsFuel (Fuel Term) Term)\n\
                (declare-fun Tm_uvar (Int) Term)\n\
                (define-fun Reify ((x Term)) Term x)\n\
                (assert (forall ((t Term))\n\
                            (! (iff (exists ((e Term)) (HasType e t))\n\
                                    (Valid t))\n\
                                :pattern ((Valid t)))))\n\
                (declare-fun Prims.precedes (Term Term Term Term) Term)\n\
                (declare-fun Range_const (Int) Term)\n\
                (declare-fun _mul (Int Int) Int)\n\
                (declare-fun _div (Int Int) Int)\n\
                (declare-fun _mod (Int Int) Int)\n\
                (declare-fun __uu__PartialApp () Term)\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
   in
   let constrs : constructors = [("FString_const", ["FString_const_proj_0", Int_sort, true], String_sort, 0, true);
                                 ("Tm_type",  [], Term_sort, 2, true);
                                 ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)],  Term_sort, 3, false);
                                 ("Tm_unit",  [], Term_sort, 6, true);
                                 (fst boxIntFun,     [snd boxIntFun,  Int_sort, true],   Term_sort, 7, true);
                                 (fst boxBoolFun,    [snd boxBoolFun, Bool_sort, true],  Term_sort, 8, true);
                                 (fst boxStringFun,  [snd boxStringFun, String_sort, true], Term_sort, 9, true);
                                 ("LexCons",    [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true); ("LexCons_2", Term_sort, true)], Term_sort, 11, true)] in
   let bcons = constrs |> List.collect (constructor_to_decl norng) |> List.map (declToSmt z3options) |> String.concat "\n" in
   let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n\
                                   (is-LexCons t))\n\
                       (declare-fun Prims.lex_t () Term)\n\
                       (assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n\
                                    (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n\
                                         (or (Valid (Prims.precedes t1 t2 x1 y1))\n\
                                             (and (= x1 y1)\n\
                                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n\
                      (assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n\
                                                          (! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n\
                                                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n\
                                                          :pattern (Prims.precedes t1 t2 e1 e2))))\n\
                      (assert (forall ((t1 Term) (t2 Term))\n\
                                      (! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n\
                                      (< (Rank t1) (Rank t2)))\n\
                                      :pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in
   basic ^ bcons ^ lex_ordering

let preludeDecls : list<decl> = 
    let tmvarx , tmvary , tmvart = ("x" , Term_sort) , ("y" , Term_sort) , ("t" , Term_sort) in
    let bovarb = ("b" , Bool_sort) in
    let flvarf = ("f" , Fuel_sort) in
    let t1 , t2 , x1 , x2 , y1 , y2 = ("t1" , Term_sort) , ("t2" , Term_sort) , ("x1" , Term_sort) , ("x2" , Term_sort) , ("y1" , Term_sort) , ("y2" , Term_sort) in
    let intvarx , intvary =  ("x" , Int_sort) , ("y" , Int_sort) in
    let hastypez = abstr [tmvarx ; tmvart] ( mkApp ("HasTypeFuel", [
            mkApp ("ZFuel", []) prrng ;
            mkFreeV tmvarx prrng ;
            mkFreeV tmvart prrng
        ]) prrng ) in
    let hastype = abstr [tmvarx ; tmvart] ( mkApp ("HasTypeFuel", [
            mkApp ("MaxIFuel", []) prrng ;
            mkFreeV tmvarx prrng ;
            mkFreeV tmvart prrng
        ]) prrng ) in
    let fuelirrelevance_pat = mkApp ("HasTypeFuel" , [
            mkApp ("SFuel" , [mkFreeV flvarf prrng]) prrng ;
            mkFreeV tmvarx prrng ;
            mkFreeV tmvart prrng
        ]) prrng in
    let fuelirrelevance = mkForall prrng ([[fuelirrelevance_pat]] , [flvarf ; tmvarx ; tmvart] , mkEq ( 
        fuelirrelevance_pat , mkApp ("HasTypeZ" , [
            mkFreeV tmvarx prrng ;
            mkFreeV tmvart prrng
        ]) prrng ) prrng) in
    let nohoist_pat = mkApp ("NoHoist" , [mkFreeV tmvart prrng ; mkFreeV bovarb prrng] ) prrng in
    let nohoist = mkForall prrng ([[nohoist_pat]] , [tmvart ; bovarb] , mkEq (nohoist_pat , mkFreeV bovarb prrng) prrng) in
    let istyped = abstr [tmvarx] (mkExists prrng ([] , [tmvart] , mkApp ("HasTypeZ" , [
            mkFreeV tmvarx prrng ; mkFreeV tmvart prrng
        ]) prrng)) in
    let validity_pat = mkApp ("Valid" , [mkFreeV tmvart prrng]) prrng in
    let validity = mkForall prrng ([[validity_pat]] , [tmvart] , mkIff (
        mkExists prrng ([] , [tmvarx] , mkApp ("HasType" , [mkFreeV tmvarx prrng ; mkFreeV tmvart prrng]) prrng) ,
            validity_pat) prrng)
    in
    let operator_pat (nm : string) : term = mkApp (nm , [mkFreeV intvarx prrng ; mkFreeV intvary prrng]) prrng in
    let operator (nm : string) (o : op) : term = mkForall prrng ([[operator_pat nm]] , [intvarx ; intvary] , mkEq (operator_pat nm ,
        mkApp' (o , [mkFreeV intvarx prrng ; mkFreeV intvary prrng]) prrng
    ) prrng ) in
    let constrs : list<decl> = [
        ("FString_const", ["FString_const_proj_0", Int_sort, true], String_sort, 0, true);
        ("Tm_type",  [], Term_sort, 2, true);
        ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)],  Term_sort, 3, false);
        ("Tm_unit",  [], Term_sort, 6, true);
        (fst boxIntFun,     [snd boxIntFun,  Int_sort, true],   Term_sort, 7, true);
        (fst boxBoolFun,    [snd boxBoolFun, Bool_sort, true],  Term_sort, 8, true);
        (fst boxStringFun,  [snd boxStringFun, String_sort, true], Term_sort, 9, true);
        ("LexCons",    [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true); ("LexCons_2", Term_sort, true)], Term_sort, 11, true)
    ] |> List.collect (constructor_to_decl prrng) in
    let isprims = abstr [tmvart] (mkApp ("is-LexCons" , [mkFreeV tmvart prrng]) prrng) in
    let precedes_lext (tm1 : term) (tm2 : term) =
        let lext = mkApp ("Prims.lex_t" , []) prrng in
        mkApp ("Prims.precedes" , [lext ; lext ; tm1 ; tm2]) prrng
    in
    let lexicographic = mkForall prrng ([] , [t1 ; t2 ; x1 ; x2 ; y1 ; y2] , mkIff (
        mkApp ("Valid" , [precedes_lext (mkApp ("LexCons" , [
                    mkFreeV t1 prrng ;
                    mkFreeV x1 prrng ;
                    mkFreeV x2 prrng
                ]) prrng) (mkApp ("LexCons" , [
                    mkFreeV t2 prrng ;
                    mkFreeV y1 prrng ;
                    mkFreeV y2 prrng
        ]) prrng)]) prrng , mkOr (
            mkApp ("Valid" , [
                mkApp ("Prims.precedes" , [
                    mkFreeV t1 prrng ;
                    mkFreeV t2 prrng ;
                    mkFreeV x1 prrng ;
                    mkFreeV y1 prrng
                ]) prrng
            ]) prrng ,
            mkAnd (
                mkEq (mkFreeV x1 prrng , mkFreeV y1 prrng) prrng ,
                mkApp ("Valid" , [ (precedes_lext (mkFreeV x2 prrng) (mkFreeV y2 prrng)) ]) prrng
            ) prrng
        ) prrng
      ) prrng) in
      let precedes_pat = mkApp ("Prims.precedes" , [mkFreeV t1 prrng ; mkFreeV t2 prrng ; mkFreeV x1 prrng ; mkFreeV x2 prrng]) prrng in
      let precedes = mkForall prrng ([[precedes_pat]] , [t1 ; t2 ; x1 ; x2] , mkIff (
          mkApp ("Valid" , [precedes_pat]) prrng ,
          mkApp ("Valid" , [precedes_lext (mkFreeV x1 prrng) (mkFreeV x2 prrng)]) prrng
      ) prrng) in
      let rank_pat = precedes_lext (mkFreeV t1 prrng) (mkFreeV t2 prrng) in
      let rank = mkForall prrng ([[rank_pat]] , [t1 ; t2] , mkIff (mkApp ("Valid" , [rank_pat]) prrng ,
              mkLT (mkApp ("Rank" , [mkFreeV t1 prrng]) prrng , mkApp ("Rank" , [mkFreeV t2 prrng]) prrng) prrng
          ) prrng) in
    [
        GenerateOptions ;
        SortDeclaration "FString" ;
        DeclFun ("FString_constr_id" , [String_sort] , Int_sort , None) ;
        SortDeclaration "Term" ;
        DeclFun ("Term_constr_id" , [Term_sort] , Int_sort , None) ;
        FuelDeclaration ;
        DeclFun ("MaxIFuel" , [] , Fuel_sort , None) ;
        DeclFun ("MaxFuel" , [] , Fuel_sort , None) ;
        DeclFun ("PreType" , [Term_sort] , Term_sort , None) ;
        DeclFun ("Valid" , [Term_sort] , Bool_sort , None) ;
        DeclFun ("HasTypeFuel" , [Fuel_sort ; Term_sort ; Term_sort] , Bool_sort , None) ;
        DefineFun ("HasTypeZ" , [Term_sort ; Term_sort] , Bool_sort , hastypez , None) ;
        DefineFun ("HasType" , [Term_sort ; Term_sort] , Bool_sort , hastype , None) ;
        Assume ({assumption_name=escape "fuel_irrelevance" ; assumption_caption=Some "Fuel irrelevance" ; assumption_term=fuelirrelevance ; assumption_fact_ids=[]}) ;
        DeclFun ("NoHoist" , [Term_sort ; Bool_sort] , Bool_sort , None) ;
        Assume ({assumption_name=escape "no_hoist" ; assumption_caption=Some "No-hoist" ; assumption_term=nohoist ; assumption_fact_ids=[]}) ;
        DefineFun ("IsTyped" , [Term_sort] , Bool_sort , istyped , None) ;
        DeclFun ("ApplyTF" , [Term_sort ; Fuel_sort] , Term_sort , None) ;
        DeclFun ("ApplyTT" , [Term_sort ; Term_sort] , Term_sort , None) ;
        DeclFun ("Rank" , [Term_sort] , Int_sort , None) ;
        DeclFun ("Closure" , [Term_sort] , Term_sort , None) ;
        DeclFun ("ConsTerm" , [Term_sort ; Term_sort] , Term_sort , None) ;
        DeclFun ("ConsFuel" , [Fuel_sort ; Term_sort] , Term_sort , None) ;
        DeclFun ("Tm_uvar" , [Int_sort] , Term_sort , None) ;
        DefineFun ("Reify" , [Term_sort] , Term_sort , abstr [tmvarx] (mkFreeV tmvarx prrng) , None) ;
        Assume ({assumption_name=escape "validity" ; assumption_caption=Some "Validity" ; assumption_term=validity ; assumption_fact_ids=[]}) ;
        DeclFun ("Prims.precedes" , [Term_sort ; Term_sort ; Term_sort ; Term_sort] , Term_sort , None) ;
        DeclFun ("Range_const" , [Int_sort] , Term_sort , None) ;
        DeclFun ("_mul" , [Int_sort ; Int_sort] , Int_sort , None) ;
        DeclFun ("_div" , [Int_sort ; Int_sort] , Int_sort , None) ;
        DeclFun ("_mod" , [Int_sort ; Int_sort] , Int_sort , None) ;
        DeclFun ("__uu__PartialApp" , [] , Term_sort , None) ;
        Assume ({assumption_name=escape "arithmetic_multiplication" ; assumption_caption=Some "Arithmetic multiplication" ; assumption_term=operator "_mul" Mul ; assumption_fact_ids=[]}) ;
        Assume ({assumption_name=escape "arithmetic_division" ; assumption_caption=Some "Arithmetic division" ; assumption_term=operator "_div" Div ; assumption_fact_ids=[]}) ;
        Assume ({assumption_name=escape "arithmetic_modulus" ; assumption_caption=Some "Arithmetic modulus" ; assumption_term=operator "_mod" Mod ; assumption_fact_ids=[]}) ;
    ] @ constrs @ [
        DefineFun ("is-Prims.LexCons" , [Term_sort] , Bool_sort , isprims , None ) ;
        DeclFun ("Prims.lex_t" , [] , Term_sort , None) ;
        Assume ({assumption_name=escape "lexicographic_ordering" ; assumption_caption=Some "Lexicographic ordering" ; assumption_term=lexicographic ; assumption_fact_ids=[]}) ;
        Assume ({assumption_name=escape "precedes_ordering" ; assumption_caption=Some "Precedes ordering" ; assumption_term=precedes ; assumption_fact_ids=[]}) ;
        Assume ({assumption_name=escape "rank_ordering" ; assumption_caption=Some "Rank ordering" ; assumption_term=rank ; assumption_fact_ids=[]})
    ]

(* Generate boxing/unboxing functions for bitvectors of various sizes. *)
(* For ids, to avoid dealing with generation of fresh ids,
   I am computing them based on the size in this not very robust way.
   z3options are only used by the prelude so passing the empty string should be ok. *)
let mkBvConstructor (sz : int) : list<decl> =
    (fst (boxBitVecFun sz),
        [snd (boxBitVecFun sz), BitVec_sort sz, true], Term_sort, 12+sz, true)
    |> constructor_to_decl norng

let __range_c : ref<int> = BU.mk_ref 0
let mk_Range_const () : term =
    let i : int = !__range_c in
    __range_c := !__range_c + 1;
    mkApp("Range_const", [mkInteger' i norng]) norng

let mk_Term_type : term       = mkApp("Tm_type", []) norng
let mk_Term_app (t1 : term) (t2 : term) (r : Range.range) : term = mkApp("Tm_app", [t1;t2]) r
let mk_Term_uvar (i : int) (r : Range.range) : term = mkApp("Tm_uvar", [mkInteger' i norng]) r
let mk_Term_unit : term       = mkApp("Tm_unit", []) norng
let elim_box (cond : bool) (u : string) (v : string) (t : term) : term =
    match t.tm with
    | App(Var v', [t]) when v=v' && cond -> t
    | _ -> mkApp(u, [t]) t.rng
let maybe_elim_box (u : string) (v : string) (t : term) : term =
    elim_box (Options.smtencoding_elim_box()) u v t
let boxInt (t : term) : term     = maybe_elim_box (fst boxIntFun) (snd boxIntFun) t
let unboxInt (t : term) : term    = maybe_elim_box (snd boxIntFun) (fst boxIntFun) t
let boxBool (t : term) : term     = maybe_elim_box (fst boxBoolFun) (snd boxBoolFun) t
let unboxBool (t : term) : term   = maybe_elim_box (snd boxBoolFun) (fst boxBoolFun) t
let boxString (t : term) : term   = maybe_elim_box (fst boxStringFun) (snd boxStringFun) t
let unboxString (t : term) : term = maybe_elim_box (snd boxStringFun) (fst boxStringFun) t
let boxBitVec (sz:int) (t : term) : term =
    elim_box true (fst (boxBitVecFun sz)) (snd (boxBitVecFun sz)) t
let unboxBitVec (sz:int) (t : term) : term =
    elim_box true (snd (boxBitVecFun sz)) (fst (boxBitVecFun sz)) t
let boxTerm (sort : sort) (t : term) : term = match sort with
  | Int_sort -> boxInt t
  | Bool_sort -> boxBool t
  | String_sort -> boxString t
  | BitVec_sort sz -> boxBitVec sz t
  | _ -> raise Impos
let unboxTerm (sort : sort) (t : term) : term = match sort with
  | Int_sort -> unboxInt t
  | Bool_sort -> unboxBool t
  | String_sort -> unboxString t
  | BitVec_sort sz -> unboxBitVec sz t
  | _ -> raise Impos

let getBoxedInteger (t:term) =
  match t.tm with
  | App(Var s, [t2]) when s = fst boxIntFun ->
    begin
    match t2.tm with
    | Integer n -> Some (int_of_string n)
    | _ -> None
    end
  | _ -> None

let mk_PreType t      = mkApp("PreType", [t]) t.rng
let mk_Valid t        = match t.tm with
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Equality", [_; t1; t2])}]) -> mkEq (t1, t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_disEquality", [_; t1; t2])}]) -> mkNot (mkEq (t1, t2) norng) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThanOrEqual", [t1; t2])}]) -> mkLTE (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThan", [t1; t2])}]) -> mkLT (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThanOrEqual", [t1; t2])}]) -> mkGTE (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThan", [t1; t2])}]) -> mkGT (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_AmpAmp", [t1; t2])}]) -> mkAnd (unboxBool t1, unboxBool t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_BarBar", [t1; t2])}]) -> mkOr (unboxBool t1, unboxBool t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Negation", [t])}]) -> mkNot (unboxBool t) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "FStar.BV.bvult", [t0; t1;t2])}])
    | App(Var "Prims.equals", [_; {tm=App(Var "FStar.BV.bvult", [t0; t1;t2])}; _])
            when (FStar.Util.is_some (getBoxedInteger t0))->
        // sometimes b2t gets needlessly normalized...
        let sz = match getBoxedInteger t0 with | Some sz -> sz | _ -> failwith "impossible" in
        mkBvUlt (unboxBitVec sz t1, unboxBitVec sz t2) t.rng
    | App(Var "Prims.b2t", [t1]) -> {unboxBool t1 with rng=t.rng}
    | _ ->
        mkApp("Valid",  [t]) t.rng
let mk_HasType v t    = mkApp("HasType", [v;t]) t.rng
let mk_HasTypeZ v t   = mkApp("HasTypeZ", [v;t]) t.rng
let mk_IsTyped v      = mkApp("IsTyped", [v]) norng
let mk_HasTypeFuel f v t =
   if Options.unthrottle_inductives()
   then mk_HasType v t
   else mkApp("HasTypeFuel", [f;v;t]) t.rng
let mk_HasTypeWithFuel f v t = match f with
    | None -> mk_HasType v t
    | Some f -> mk_HasTypeFuel f v t
let mk_NoHoist dummy b = mkApp("NoHoist", [dummy;b]) b.rng
let mk_Destruct v     = mkApp("Destruct", [v])
let mk_Rank x         = mkApp("Rank", [x])
let mk_tester n t     = mkApp("is-"^n,   [t]) t.rng
let mk_ApplyTF t t'   = mkApp("ApplyTF", [t;t']) t.rng
let mk_ApplyTT t t'  r  = mkApp("ApplyTT", [t;t']) r
let kick_partial_app t  = mk_ApplyTT (mkApp("__uu__PartialApp", []) t.rng) t t.rng |> mk_Valid
let mk_String_const i r = mkApp("FString_const", [ mkInteger' i norng]) r
let mk_Precedes x1 x2 x3 x4 r = mkApp("Prims.precedes", [x1;x2;x3;x4])  r|> mk_Valid
let mk_LexCons x1 x2 x3 r  = mkApp("LexCons", [x1;x2;x3]) r
let rec n_fuel n =
    if n = 0 then mkApp("ZFuel", []) norng
    else mkApp("SFuel", [n_fuel (n - 1)]) norng
let fuel_2 = n_fuel 2
let fuel_100 = n_fuel 100

let mk_and_opt p1 p2 r = match p1, p2  with
  | Some p1, Some p2 -> Some (mkAnd(p1, p2) r)
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None

let mk_and_opt_l pl r =
  List.fold_right (fun p out -> mk_and_opt p out r) pl None

let mk_and_l l r = List.fold_right (fun p1 p2 -> mkAnd(p1, p2) r) l (mkTrue r)

let mk_or_l l r = List.fold_right (fun p1 p2 -> mkOr(p1,p2) r) l (mkFalse r)

let mk_haseq t = mk_Valid (mkApp ("Prims.hasEq", [t]) t.rng)
