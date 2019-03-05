
open Prims
open FStar_Pervasives

let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))

type sort =
| Bool_sort
| Int_sort
| String_sort
| Term_sort
| Fuel_sort
| BitVec_sort of Prims.int
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string


let uu___is_Bool_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool_sort -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_Int_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int_sort -> begin
true
end
| uu____61 -> begin
false
end))


let uu___is_String_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String_sort -> begin
true
end
| uu____72 -> begin
false
end))


let uu___is_Term_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_sort -> begin
true
end
| uu____83 -> begin
false
end))


let uu___is_Fuel_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fuel_sort -> begin
true
end
| uu____94 -> begin
false
end))


let uu___is_BitVec_sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
true
end
| uu____107 -> begin
false
end))


let __proj__BitVec_sort__item___0 : sort  ->  Prims.int = (fun projectee -> (match (projectee) with
| BitVec_sort (_0) -> begin
_0
end))


let uu___is_Array : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
true
end
| uu____134 -> begin
false
end))


let __proj__Array__item___0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Array (_0) -> begin
_0
end))


let uu___is_Arrow : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
true
end
| uu____170 -> begin
false
end))


let __proj__Arrow__item___0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
_0
end))


let uu___is_Sort : sort  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sort (_0) -> begin
true
end
| uu____203 -> begin
false
end))


let __proj__Sort__item___0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_0) -> begin
_0
end))


let rec strSort : sort  ->  Prims.string = (fun x -> (match (x) with
| Bool_sort -> begin
"Bool"
end
| Int_sort -> begin
"Int"
end
| Term_sort -> begin
"Term"
end
| String_sort -> begin
"FString"
end
| Fuel_sort -> begin
"Fuel"
end
| BitVec_sort (n1) -> begin
(

let uu____231 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ BitVec %s)" uu____231))
end
| Array (s1, s2) -> begin
(

let uu____236 = (strSort s1)
in (

let uu____238 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" uu____236 uu____238)))
end
| Arrow (s1, s2) -> begin
(

let uu____243 = (strSort s1)
in (

let uu____245 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" uu____243 uu____245)))
end
| Sort (s) -> begin
s
end))

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
| BvShr
| BvUdiv
| BvMod
| BvMul
| BvUlt
| BvUext of Prims.int
| NatToBv of Prims.int
| BvToNat
| ITE
| Var of Prims.string


let uu___is_TrueOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TrueOp -> begin
true
end
| uu____277 -> begin
false
end))


let uu___is_FalseOp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FalseOp -> begin
true
end
| uu____288 -> begin
false
end))


let uu___is_Not : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not -> begin
true
end
| uu____299 -> begin
false
end))


let uu___is_And : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| And -> begin
true
end
| uu____310 -> begin
false
end))


let uu___is_Or : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Or -> begin
true
end
| uu____321 -> begin
false
end))


let uu___is_Imp : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Imp -> begin
true
end
| uu____332 -> begin
false
end))


let uu___is_Iff : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iff -> begin
true
end
| uu____343 -> begin
false
end))


let uu___is_Eq : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____354 -> begin
false
end))


let uu___is_LT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LT -> begin
true
end
| uu____365 -> begin
false
end))


let uu___is_LTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LTE -> begin
true
end
| uu____376 -> begin
false
end))


let uu___is_GT : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GT -> begin
true
end
| uu____387 -> begin
false
end))


let uu___is_GTE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTE -> begin
true
end
| uu____398 -> begin
false
end))


let uu___is_Add : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Add -> begin
true
end
| uu____409 -> begin
false
end))


let uu___is_Sub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sub -> begin
true
end
| uu____420 -> begin
false
end))


let uu___is_Div : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Div -> begin
true
end
| uu____431 -> begin
false
end))


let uu___is_Mul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mul -> begin
true
end
| uu____442 -> begin
false
end))


let uu___is_Minus : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Minus -> begin
true
end
| uu____453 -> begin
false
end))


let uu___is_Mod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mod -> begin
true
end
| uu____464 -> begin
false
end))


let uu___is_BvAnd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAnd -> begin
true
end
| uu____475 -> begin
false
end))


let uu___is_BvXor : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvXor -> begin
true
end
| uu____486 -> begin
false
end))


let uu___is_BvOr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvOr -> begin
true
end
| uu____497 -> begin
false
end))


let uu___is_BvAdd : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvAdd -> begin
true
end
| uu____508 -> begin
false
end))


let uu___is_BvSub : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvSub -> begin
true
end
| uu____519 -> begin
false
end))


let uu___is_BvShl : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShl -> begin
true
end
| uu____530 -> begin
false
end))


let uu___is_BvShr : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvShr -> begin
true
end
| uu____541 -> begin
false
end))


let uu___is_BvUdiv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUdiv -> begin
true
end
| uu____552 -> begin
false
end))


let uu___is_BvMod : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMod -> begin
true
end
| uu____563 -> begin
false
end))


let uu___is_BvMul : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvMul -> begin
true
end
| uu____574 -> begin
false
end))


let uu___is_BvUlt : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUlt -> begin
true
end
| uu____585 -> begin
false
end))


let uu___is_BvUext : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
true
end
| uu____598 -> begin
false
end))


let __proj__BvUext__item___0 : op  ->  Prims.int = (fun projectee -> (match (projectee) with
| BvUext (_0) -> begin
_0
end))


let uu___is_NatToBv : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
true
end
| uu____622 -> begin
false
end))


let __proj__NatToBv__item___0 : op  ->  Prims.int = (fun projectee -> (match (projectee) with
| NatToBv (_0) -> begin
_0
end))


let uu___is_BvToNat : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BvToNat -> begin
true
end
| uu____644 -> begin
false
end))


let uu___is_ITE : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ITE -> begin
true
end
| uu____655 -> begin
false
end))


let uu___is_Var : op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____668 -> begin
false
end))


let __proj__Var__item___0 : op  ->  Prims.string = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
_0
end))

type qop =
| Forall
| Exists


let uu___is_Forall : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Forall -> begin
true
end
| uu____690 -> begin
false
end))


let uu___is_Exists : qop  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exists -> begin
true
end
| uu____701 -> begin
false
end))

type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of (Prims.string * sort)
| App of (op * term Prims.list)
| Quant of (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string FStar_Syntax_Syntax.memo)
| Let of (term Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo; rng : FStar_Range.range}


let uu___is_Integer : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
true
end
| uu____864 -> begin
false
end))


let __proj__Integer__item___0 : term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Integer (_0) -> begin
_0
end))


let uu___is_BoundV : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BoundV (_0) -> begin
true
end
| uu____888 -> begin
false
end))


let __proj__BoundV__item___0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_0) -> begin
_0
end))


let uu___is_FreeV : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FreeV (_0) -> begin
true
end
| uu____916 -> begin
false
end))


let __proj__FreeV__item___0 : term'  ->  (Prims.string * sort) = (fun projectee -> (match (projectee) with
| FreeV (_0) -> begin
_0
end))


let uu___is_App : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____957 -> begin
false
end))


let __proj__App__item___0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Quant : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
true
end
| uu____1019 -> begin
false
end))


let __proj__Quant__item___0 : term'  ->  (qop * term Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string FStar_Syntax_Syntax.memo) = (fun projectee -> (match (projectee) with
| Quant (_0) -> begin
_0
end))


let uu___is_Let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____1117 -> begin
false
end))


let __proj__Let__item___0 : term'  ->  (term Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Labeled : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
true
end
| uu____1162 -> begin
false
end))


let __proj__Labeled__item___0 : term'  ->  (term * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
_0
end))


let uu___is_LblPos : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
true
end
| uu____1208 -> begin
false
end))


let __proj__LblPos__item___0 : term'  ->  (term * Prims.string) = (fun projectee -> (match (projectee) with
| LblPos (_0) -> begin
_0
end))


let __proj__Mkterm__item__tm : term  ->  term' = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
tm
end))


let __proj__Mkterm__item__freevars : term  ->  (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
freevars
end))


let __proj__Mkterm__item__rng : term  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {tm = tm; freevars = freevars; rng = rng} -> begin
rng
end))


type pat =
term


type fv =
(Prims.string * sort)


type fvs =
(Prims.string * sort) Prims.list


type caption =
Prims.string FStar_Pervasives_Native.option


type binders =
(Prims.string * sort) Prims.list


type constructor_field =
(Prims.string * sort * Prims.bool)


type constructor_t =
(Prims.string * constructor_field Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list

type fact_db_id =
| Name of FStar_Ident.lid
| Namespace of FStar_Ident.lid
| Tag of Prims.string


let uu___is_Name : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
true
end
| uu____1411 -> begin
false
end))


let __proj__Name__item___0 : fact_db_id  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
_0
end))


let uu___is_Namespace : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
true
end
| uu____1431 -> begin
false
end))


let __proj__Namespace__item___0 : fact_db_id  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
_0
end))


let uu___is_Tag : fact_db_id  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
true
end
| uu____1452 -> begin
false
end))


let __proj__Tag__item___0 : fact_db_id  ->  Prims.string = (fun projectee -> (match (projectee) with
| Tag (_0) -> begin
_0
end))

type assumption =
{assumption_term : term; assumption_caption : caption; assumption_name : Prims.string; assumption_fact_ids : fact_db_id Prims.list}


let __proj__Mkassumption__item__assumption_term : assumption  ->  term = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_term
end))


let __proj__Mkassumption__item__assumption_caption : assumption  ->  caption = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_caption
end))


let __proj__Mkassumption__item__assumption_name : assumption  ->  Prims.string = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_name
end))


let __proj__Mkassumption__item__assumption_fact_ids : assumption  ->  fact_db_id Prims.list = (fun projectee -> (match (projectee) with
| {assumption_term = assumption_term; assumption_caption = assumption_caption; assumption_name = assumption_name; assumption_fact_ids = assumption_fact_ids} -> begin
assumption_fact_ids
end))

type decl =
| FuelDeclaration
| SortDeclaration of Prims.string
| DefPrelude
| GenerateOptions
| Hardcoded of Prims.string
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of assumption
| Caption of Prims.string
| Module of (Prims.string * decl Prims.list)
| Eval of term
| Echo of Prims.string
| RetainAssumptions of Prims.string Prims.list
| Push
| Pop
| CheckSat
| GetUnsatCore
| GetProof
| SetOption of (Prims.string * Prims.string)
| GetStatistics
| GetReasonUnknown


let uu___is_FuelDeclaration : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FuelDeclaration -> begin
true
end
| uu____1654 -> begin
false
end))


let uu___is_SortDeclaration : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SortDeclaration (_0) -> begin
true
end
| uu____1667 -> begin
false
end))


let __proj__SortDeclaration__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| SortDeclaration (_0) -> begin
_0
end))


let uu___is_DefPrelude : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefPrelude -> begin
true
end
| uu____1689 -> begin
false
end))


let uu___is_GenerateOptions : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GenerateOptions -> begin
true
end
| uu____1700 -> begin
false
end))


let uu___is_Hardcoded : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Hardcoded (_0) -> begin
true
end
| uu____1713 -> begin
false
end))


let __proj__Hardcoded__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Hardcoded (_0) -> begin
_0
end))


let uu___is_DeclFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
true
end
| uu____1747 -> begin
false
end))


let __proj__DeclFun__item___0 : decl  ->  (Prims.string * sort Prims.list * sort * caption) = (fun projectee -> (match (projectee) with
| DeclFun (_0) -> begin
_0
end))


let uu___is_DefineFun : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefineFun (_0) -> begin
true
end
| uu____1813 -> begin
false
end))


let __proj__DefineFun__item___0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_0) -> begin
_0
end))


let uu___is_Assume : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
true
end
| uu____1872 -> begin
false
end))


let __proj__Assume__item___0 : decl  ->  assumption = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
_0
end))


let uu___is_Caption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
true
end
| uu____1893 -> begin
false
end))


let __proj__Caption__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_0) -> begin
_0
end))


let uu___is_Module : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
true
end
| uu____1923 -> begin
false
end))


let __proj__Module__item___0 : decl  ->  (Prims.string * decl Prims.list) = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
_0
end))


let uu___is_Eval : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eval (_0) -> begin
true
end
| uu____1964 -> begin
false
end))


let __proj__Eval__item___0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_0) -> begin
_0
end))


let uu___is_Echo : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Echo (_0) -> begin
true
end
| uu____1985 -> begin
false
end))


let __proj__Echo__item___0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_0) -> begin
_0
end))


let uu___is_RetainAssumptions : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RetainAssumptions (_0) -> begin
true
end
| uu____2011 -> begin
false
end))


let __proj__RetainAssumptions__item___0 : decl  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| RetainAssumptions (_0) -> begin
_0
end))


let uu___is_Push : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push -> begin
true
end
| uu____2039 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____2050 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____2061 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____2072 -> begin
false
end))


let uu___is_GetProof : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetProof -> begin
true
end
| uu____2083 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____2101 -> begin
false
end))


let __proj__SetOption__item___0 : decl  ->  (Prims.string * Prims.string) = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
_0
end))


let uu___is_GetStatistics : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetStatistics -> begin
true
end
| uu____2138 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____2149 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____2184 'Auu____2185 . ('Auu____2184 * 'Auu____2185)  ->  'Auu____2185 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____2224 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___119_2235 -> (match (uu___119_2235) with
| {tm = FreeV (x); freevars = uu____2237; rng = uu____2238} -> begin
(fv_sort x)
end
| uu____2254 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___120_2261 -> (match (uu___120_2261) with
| {tm = FreeV (fv); freevars = uu____2263; rng = uu____2264} -> begin
fv
end
| uu____2279 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____2301) -> begin
[]
end
| BoundV (uu____2308) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____2331, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____2342, uu____2343, uu____2344, uu____2345, t1, uu____2347) -> begin
(freevars t1)
end
| Labeled (t1, uu____2373, uu____2374) -> begin
(freevars t1)
end
| LblPos (t1, uu____2378) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____2398 = (FStar_ST.op_Bang t.freevars)
in (match (uu____2398) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____2475 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____2475))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let rec assign_qids : decl  ->  unit = (fun d -> (

let in_terms = (fun nm t -> (

let next_qid = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____2564 -> (

let n1 = (FStar_ST.op_Bang ctr)
in ((FStar_Util.incr ctr);
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
nm
end
| uu____2648 -> begin
(

let uu____2650 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "%s.%s" nm uu____2650))
end);
))))
in (

let set_qid = (fun qid -> (

let uu____2698 = (FStar_ST.op_Bang qid)
in (match (uu____2698) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2750 = (

let uu____2754 = (next_qid ())
in FStar_Pervasives_Native.Some (uu____2754))
in (FStar_ST.op_Colon_Equals qid uu____2750))
end
| FStar_Pervasives_Native.Some (s) -> begin
()
end)))
in (

let rec aux = (fun tm -> (match (tm.tm) with
| App (op, tms) -> begin
(FStar_List.iter aux tms)
end
| Quant (uu____2819, uu____2820, uu____2821, uu____2822, scp, qid) -> begin
((set_qid qid);
(aux scp);
)
end
| uu____2883 -> begin
()
end))
in (aux t)))))
in (match (d) with
| DefineFun (nm, uu____2885, uu____2886, tm, uu____2888) -> begin
(in_terms (Prims.strcat "funqid_" nm) tm)
end
| Assume (a) -> begin
(in_terms a.assumption_name a.assumption_term)
end
| Module (uu____2897, ds) -> begin
(FStar_List.iter assign_qids ds)
end
| uu____2905 -> begin
()
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___121_2912 -> (match (uu___121_2912) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___122_2922 -> (match (uu___122_2922) with
| TrueOp -> begin
"true"
end
| FalseOp -> begin
"false"
end
| Not -> begin
"not"
end
| And -> begin
"and"
end
| Or -> begin
"or"
end
| Imp -> begin
"=>"
end
| Iff -> begin
"iff"
end
| Eq -> begin
"="
end
| LT -> begin
"<"
end
| LTE -> begin
"<="
end
| GT -> begin
">"
end
| GTE -> begin
">="
end
| Add -> begin
"+"
end
| Sub -> begin
"-"
end
| Div -> begin
"div"
end
| Mul -> begin
"*"
end
| Minus -> begin
"-"
end
| Mod -> begin
"mod"
end
| ITE -> begin
"ite"
end
| BvAnd -> begin
"bvand"
end
| BvXor -> begin
"bvxor"
end
| BvOr -> begin
"bvor"
end
| BvAdd -> begin
"bvadd"
end
| BvSub -> begin
"bvsub"
end
| BvShl -> begin
"bvshl"
end
| BvShr -> begin
"bvlshr"
end
| BvUdiv -> begin
"bvudiv"
end
| BvMod -> begin
"bvurem"
end
| BvMul -> begin
"bvmul"
end
| BvUlt -> begin
"bvult"
end
| BvToNat -> begin
"bv2int"
end
| BvUext (n1) -> begin
(

let uu____2957 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____2957))
end
| NatToBv (n1) -> begin
(

let uu____2962 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____2962))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___123_2976 -> (match (uu___123_2976) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____2986 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____2986))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____3006 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____3006))
end
| FreeV (x) -> begin
(

let uu____3015 = (

let uu____3017 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____3017))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____3015))
end
| App (op, tms) -> begin
(

let uu____3028 = (

let uu____3030 = (op_to_string op)
in (

let uu____3032 = (

let uu____3034 = (

let uu____3036 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____3036 (FStar_String.concat " ")))
in (Prims.strcat uu____3034 ")"))
in (Prims.strcat uu____3030 uu____3032)))
in (Prims.strcat "(" uu____3028))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____3053 = (hash_of_term t1)
in (

let uu____3055 = (

let uu____3057 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____3057))
in (Prims.strcat uu____3053 uu____3055)))
end
| LblPos (t1, r) -> begin
(

let uu____3063 = (

let uu____3065 = (hash_of_term t1)
in (Prims.strcat uu____3065 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____3063))
end
| Quant (qop, pats, wopt, sorts, body, uu____3075) -> begin
(

let uu____3100 = (

let uu____3102 = (

let uu____3104 = (

let uu____3106 = (

let uu____3108 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____3108 (FStar_String.concat " ")))
in (

let uu____3118 = (

let uu____3120 = (

let uu____3122 = (hash_of_term body)
in (

let uu____3124 = (

let uu____3126 = (

let uu____3128 = (weightToSmt wopt)
in (

let uu____3130 = (

let uu____3132 = (

let uu____3134 = (

let uu____3136 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____3155 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____3155 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____3136 (FStar_String.concat "; ")))
in (Prims.strcat uu____3134 "))"))
in (Prims.strcat " " uu____3132))
in (Prims.strcat uu____3128 uu____3130)))
in (Prims.strcat " " uu____3126))
in (Prims.strcat uu____3122 uu____3124)))
in (Prims.strcat ")(! " uu____3120))
in (Prims.strcat uu____3106 uu____3118)))
in (Prims.strcat " (" uu____3104))
in (Prims.strcat (qop_to_string qop) uu____3102))
in (Prims.strcat "(" uu____3100))
end
| Let (es, body) -> begin
(

let uu____3182 = (

let uu____3184 = (

let uu____3186 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____3186 (FStar_String.concat " ")))
in (

let uu____3196 = (

let uu____3198 = (

let uu____3200 = (hash_of_term body)
in (Prims.strcat uu____3200 ")"))
in (Prims.strcat ") " uu____3198))
in (Prims.strcat uu____3184 uu____3196)))
in (Prims.strcat "(let (" uu____3182))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____3292 = (

let uu____3294 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____3294))
in (mkBoxFunctions uu____3292)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____3311 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____3311 "Box")) && (

let uu____3318 = (

let uu____3320 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____3320))
in (not (uu____3318))))
end
| uu____3330 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____3344 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____3344; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3421 = (

let uu____3422 = (FStar_Util.ensure_decimal i)
in Integer (uu____3422))
in (mk uu____3421 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3437 = (FStar_Util.string_of_int i)
in (mkInteger uu____3437 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____3507 r -> (match (uu____3507) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____3537) -> begin
(mkFalse r)
end
| App (FalseOp, uu____3542) -> begin
(mkTrue r)
end
| uu____3547 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3563 r -> (match (uu____3563) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3571), uu____3572) -> begin
t2
end
| (uu____3577, App (TrueOp, uu____3578)) -> begin
t1
end
| (App (FalseOp, uu____3583), uu____3584) -> begin
(mkFalse r)
end
| (uu____3589, App (FalseOp, uu____3590)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3607, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____3616) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3623 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3643 r -> (match (uu____3643) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3651), uu____3652) -> begin
(mkTrue r)
end
| (uu____3657, App (TrueOp, uu____3658)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3663), uu____3664) -> begin
t2
end
| (uu____3669, App (FalseOp, uu____3670)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3687, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____3696) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3703 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3723 r -> (match (uu____3723) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____3731, App (TrueOp, uu____3732)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3737), uu____3738) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____3743), uu____3744) -> begin
t2
end
| (uu____3749, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____3754 = (

let uu____3761 = (

let uu____3764 = (mkAnd ((t1), (t1')) r)
in (uu____3764)::(t2')::[])
in ((Imp), (uu____3761)))
in (mkApp' uu____3754 r))
end
| uu____3767 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____3792 r -> (match (uu____3792) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])) r)
end))


let mkMinus : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((Minus), ((t)::[])) r))


let mkNatToBv : Prims.int  ->  term  ->  FStar_Range.range  ->  term = (fun sz t r -> (mkApp' ((NatToBv (sz)), ((t)::[])) r))


let mkBvUext : Prims.int  ->  term  ->  FStar_Range.range  ->  term = (fun sz t r -> (mkApp' ((BvUext (sz)), ((t)::[])) r))


let mkBvToNat : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((BvToNat), ((t)::[])) r))


let mkBvAnd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvAnd)


let mkBvXor : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvXor)


let mkBvOr : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvOr)


let mkBvAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvAdd)


let mkBvSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvSub)


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4002 r -> (match (uu____4002) with
| (t1, t2) -> begin
(

let uu____4011 = (

let uu____4018 = (

let uu____4021 = (

let uu____4024 = (mkNatToBv sz t2 r)
in (uu____4024)::[])
in (t1)::uu____4021)
in ((BvShl), (uu____4018)))
in (mkApp' uu____4011 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4046 r -> (match (uu____4046) with
| (t1, t2) -> begin
(

let uu____4055 = (

let uu____4062 = (

let uu____4065 = (

let uu____4068 = (mkNatToBv sz t2 r)
in (uu____4068)::[])
in (t1)::uu____4065)
in ((BvShr), (uu____4062)))
in (mkApp' uu____4055 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4090 r -> (match (uu____4090) with
| (t1, t2) -> begin
(

let uu____4099 = (

let uu____4106 = (

let uu____4109 = (

let uu____4112 = (mkNatToBv sz t2 r)
in (uu____4112)::[])
in (t1)::uu____4109)
in ((BvUdiv), (uu____4106)))
in (mkApp' uu____4099 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4134 r -> (match (uu____4134) with
| (t1, t2) -> begin
(

let uu____4143 = (

let uu____4150 = (

let uu____4153 = (

let uu____4156 = (mkNatToBv sz t2 r)
in (uu____4156)::[])
in (t1)::uu____4153)
in ((BvMod), (uu____4150)))
in (mkApp' uu____4143 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4178 r -> (match (uu____4178) with
| (t1, t2) -> begin
(

let uu____4187 = (

let uu____4194 = (

let uu____4197 = (

let uu____4200 = (mkNatToBv sz t2 r)
in (uu____4200)::[])
in (t1)::uu____4197)
in ((BvMul), (uu____4194)))
in (mkApp' uu____4187 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____4262 r -> (match (uu____4262) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____4281 -> begin
(mk_bin_op Eq ((t1), (t2)) r)
end)
end))


let mkLT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LT)


let mkLTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LTE)


let mkGT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GT)


let mkGTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GTE)


let mkAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Add)


let mkSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Sub)


let mkDiv : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Div)


let mkMul : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mul)


let mkMod : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mod)


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____4508 r -> (match (uu____4508) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____4519) -> begin
t2
end
| App (FalseOp, uu____4524) -> begin
t3
end
| uu____4529 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____4530), App (TrueOp, uu____4531)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____4540), uu____4541) -> begin
(

let uu____4546 = (

let uu____4551 = (mkNot t1 t1.rng)
in ((uu____4551), (t3)))
in (mkImp uu____4546 r))
end
| (uu____4552, App (TrueOp, uu____4553)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____4558, uu____4559) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(failwith "Impos")
end
| (hd1)::tl1 -> begin
(FStar_List.fold_left (fun out t1 -> (mkAnd ((out), (t1)) r)) hd1 tl1)
end))


let check_pattern_ok : term  ->  term FStar_Pervasives_Native.option = (fun t -> (

let rec aux = (fun t1 -> (match (t1.tm) with
| Integer (uu____4615) -> begin
FStar_Pervasives_Native.None
end
| BoundV (uu____4617) -> begin
FStar_Pervasives_Native.None
end
| FreeV (uu____4619) -> begin
FStar_Pervasives_Native.None
end
| Let (tms, tm) -> begin
(aux_l ((tm)::tms))
end
| App (head1, terms) -> begin
(

let head_ok = (match (head1) with
| Var (uu____4640) -> begin
true
end
| TrueOp -> begin
true
end
| FalseOp -> begin
true
end
| Not -> begin
false
end
| And -> begin
false
end
| Or -> begin
false
end
| Imp -> begin
false
end
| Iff -> begin
false
end
| Eq -> begin
false
end
| LT -> begin
true
end
| LTE -> begin
true
end
| GT -> begin
true
end
| GTE -> begin
true
end
| Add -> begin
true
end
| Sub -> begin
true
end
| Div -> begin
true
end
| Mul -> begin
true
end
| Minus -> begin
true
end
| Mod -> begin
true
end
| BvAnd -> begin
false
end
| BvXor -> begin
false
end
| BvOr -> begin
false
end
| BvAdd -> begin
false
end
| BvSub -> begin
false
end
| BvShl -> begin
false
end
| BvShr -> begin
false
end
| BvUdiv -> begin
false
end
| BvMod -> begin
false
end
| BvMul -> begin
false
end
| BvUlt -> begin
false
end
| BvUext (uu____4672) -> begin
false
end
| NatToBv (uu____4675) -> begin
false
end
| BvToNat -> begin
false
end
| ITE -> begin
false
end)
in (match ((not (head_ok))) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____4683 -> begin
(aux_l terms)
end))
end
| Labeled (t2, uu____4686, uu____4687) -> begin
(aux t2)
end
| Quant (uu____4690) -> begin
FStar_Pervasives_Native.Some (t1)
end
| LblPos (uu____4715) -> begin
FStar_Pervasives_Native.Some (t1)
end))
and aux_l = (fun ts -> (match (ts) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (t1)::ts1 -> begin
(

let uu____4730 = (aux t1)
in (match (uu____4730) with
| FStar_Pervasives_Native.Some (t2) -> begin
FStar_Pervasives_Native.Some (t2)
end
| FStar_Pervasives_Native.None -> begin
(aux_l ts1)
end))
end))
in (aux t)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n1) -> begin
(FStar_Util.format1 "(Integer %s)" n1)
end
| BoundV (n1) -> begin
(

let uu____4765 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____4765))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____4782 = (op_to_string op)
in (

let uu____4784 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____4782 uu____4784)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____4792 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____4792))
end
| LblPos (t1, s) -> begin
(

let uu____4799 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____4799))
end
| Quant (qop, l, uu____4804, uu____4805, t1, uu____4807) -> begin
(

let uu____4832 = (print_smt_term_list_list l)
in (

let uu____4834 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4832 uu____4834)))
end
| Let (es, body) -> begin
(

let uu____4843 = (print_smt_term_list es)
in (

let uu____4845 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____4843 uu____4845)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____4852 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____4852 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____4879 = (

let uu____4881 = (

let uu____4883 = (print_smt_term_list l1)
in (Prims.strcat uu____4883 " ] "))
in (Prims.strcat "; [ " uu____4881))
in (Prims.strcat s uu____4879))) "" l))


let mkQuantQid : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string FStar_Syntax_Syntax.memo)  ->  term = (fun r check_pats uu____4928 -> (match (uu____4928) with
| (qop, pats, wopt, vars, body, qid) -> begin
(

let all_pats_ok = (fun pats1 -> (match ((not (check_pats))) with
| true -> begin
pats1
end
| uu____5007 -> begin
(

let uu____5009 = (FStar_Util.find_map pats1 (fun x -> (FStar_Util.find_map x check_pattern_ok)))
in (match (uu____5009) with
| FStar_Pervasives_Native.None -> begin
pats1
end
| FStar_Pervasives_Native.Some (p) -> begin
((

let uu____5024 = (

let uu____5030 = (

let uu____5032 = (print_smt_term p)
in (FStar_Util.format1 "Pattern (%s) contains illegal symbols; dropping it" uu____5032))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____5030)))
in (FStar_Errors.log_issue r uu____5024));
[];
)
end))
end))
in (match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____5041 -> begin
(match (body.tm) with
| App (TrueOp, uu____5043) -> begin
body
end
| uu____5048 -> begin
(

let uu____5049 = (

let uu____5050 = (

let uu____5075 = (all_pats_ok pats)
in ((qop), (uu____5075), (wopt), (vars), (body), (qid)))
in Quant (uu____5050))
in (mk uu____5049 r))
end)
end))
end))


let mkQuant : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r check_pats uu____5149 -> (match (uu____5149) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5193 = (

let uu____5218 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((qop), (pats), (wopt), (vars), (body), (uu____5218)))
in (mkQuantQid r check_pats uu____5193))
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____5275 r -> (match (uu____5275) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____5292 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of1 = (fun fv -> (

let uu____5325 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____5325) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____5352 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____5352) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____5411 -> begin
(match (t1.tm) with
| Integer (uu____5421) -> begin
t1
end
| BoundV (uu____5423) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____5431 = (index_of1 x)
in (match (uu____5431) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____5445 = (

let uu____5452 = (FStar_List.map (aux ix) tms)
in ((op), (uu____5452)))
in (mkApp' uu____5445 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5462 = (

let uu____5463 = (

let uu____5471 = (aux ix t2)
in ((uu____5471), (r1), (r2)))
in Labeled (uu____5463))
in (mk uu____5462 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5477 = (

let uu____5478 = (

let uu____5484 = (aux ix t2)
in ((uu____5484), (r)))
in LblPos (uu____5478))
in (mk uu____5477 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, uu____5491) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____5517 = (

let uu____5537 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____5558 = (aux (ix + n1) body)
in ((qop), (uu____5537), (wopt), (vars), (uu____5558))))
in (mkQuant t1.rng false uu____5517)))
end
| Let (es, body) -> begin
(

let uu____5579 = (FStar_List.fold_left (fun uu____5599 e -> (match (uu____5599) with
| (ix1, l) -> begin
(

let uu____5623 = (

let uu____5626 = (aux ix1 e)
in (uu____5626)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____5623)))
end)) ((ix), ([])) es)
in (match (uu____5579) with
| (ix1, es_rev) -> begin
(

let uu____5642 = uu____5579
in (

let uu____5650 = (

let uu____5657 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____5657)))
in (mkLet uu____5650 t1.rng)))
end))
end)
end)))
in (aux (Prims.parse_int "0") t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let tms1 = (FStar_List.rev tms)
in (

let n1 = (FStar_List.length tms1)
in (

let rec aux = (fun shift t1 -> (match (t1.tm) with
| Integer (uu____5694) -> begin
t1
end
| FreeV (uu____5696) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____5706 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____5714 = (

let uu____5721 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____5721)))
in (mkApp' uu____5714 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5731 = (

let uu____5732 = (

let uu____5740 = (aux shift t2)
in ((uu____5740), (r1), (r2)))
in Labeled (uu____5732))
in (mk uu____5731 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5746 = (

let uu____5747 = (

let uu____5753 = (aux shift t2)
in ((uu____5753), (r)))
in LblPos (uu____5747))
in (mk uu____5746 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, qid) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____5792 = (

let uu____5817 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____5834 = (aux shift1 body)
in ((qop), (uu____5817), (wopt), (vars), (uu____5834), (qid))))
in (mkQuantQid t1.rng false uu____5792))))
end
| Let (es, body) -> begin
(

let uu____5876 = (FStar_List.fold_left (fun uu____5896 e -> (match (uu____5896) with
| (ix, es1) -> begin
(

let uu____5920 = (

let uu____5923 = (aux shift e)
in (uu____5923)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____5920)))
end)) ((shift), ([])) es)
in (match (uu____5876) with
| (shift1, es_rev) -> begin
(

let uu____5939 = (

let uu____5946 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____5946)))
in (mkLet uu____5939 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____5966 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____5966)))


let mkQuant' : FStar_Range.range  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  term = (fun r uu____5996 -> (match (uu____5996) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____6039 = (

let uu____6059 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____6076 = (FStar_List.map fv_sort vars)
in (

let uu____6080 = (abstr vars body)
in ((qop), (uu____6059), (wopt), (uu____6076), (uu____6080)))))
in (mkQuant r true uu____6039))
end))


let mkForall : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6111 -> (match (uu____6111) with
| (pats, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkForall'' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r uu____6176 -> (match (uu____6176) with
| (pats, wopt, sorts, body) -> begin
(mkQuant r true ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  term = (fun r uu____6251 -> (match (uu____6251) with
| (pats, wopt, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkExists : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6320 -> (match (uu____6320) with
| (pats, vars, body) -> begin
(mkQuant' r ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____6377 r -> (match (uu____6377) with
| (bindings, body) -> begin
(

let uu____6403 = (FStar_List.split bindings)
in (match (uu____6403) with
| (vars, es) -> begin
(

let uu____6422 = (

let uu____6429 = (abstr vars body)
in ((es), (uu____6429)))
in (mkLet uu____6422 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let prrng : FStar_Range.range = FStar_Range.preludeRange


let mkDefineFun : (Prims.string * fv Prims.list * sort * term * caption)  ->  decl = (fun uu____6452 -> (match (uu____6452) with
| (nm, vars, s, tm, c) -> begin
(

let uu____6477 = (

let uu____6491 = (FStar_List.map fv_sort vars)
in (

let uu____6495 = (abstr vars tm)
in ((nm), (uu____6491), (s), (uu____6495), (c))))
in DefineFun (uu____6477))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____6507 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____6507)))


let fresh_token : FStar_Range.range  ->  (Prims.string * sort)  ->  Prims.int  ->  decl = (fun rng uu____6530 id1 -> (match (uu____6530) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____6546 = (

let uu____6547 = (

let uu____6552 = (mkInteger' id1 rng)
in (

let uu____6553 = (

let uu____6554 = (

let uu____6562 = (constr_id_of_sort sort)
in (

let uu____6564 = (

let uu____6567 = (mkApp ((tok_name), ([])) rng)
in (uu____6567)::[])
in ((uu____6562), (uu____6564))))
in (mkApp uu____6554 rng))
in ((uu____6552), (uu____6553))))
in (mkEq uu____6547 rng))
in (

let uu____6574 = (escape a_name)
in {assumption_term = uu____6546; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = uu____6574; assumption_fact_ids = []}))
in Assume (a)))
end))


let fresh_constructor : FStar_Range.range  ->  (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun rng uu____6600 -> (match (uu____6600) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____6640 = (

let uu____6646 = (

let uu____6648 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6648))
in ((uu____6646), (s)))
in (mkFreeV uu____6640 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____6670 = (

let uu____6678 = (constr_id_of_sort sort)
in ((uu____6678), ((capp)::[])))
in (mkApp uu____6670 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____6687 = (

let uu____6688 = (

let uu____6699 = (

let uu____6700 = (

let uu____6705 = (mkInteger id2 norng)
in ((uu____6705), (cid_app)))
in (mkEq uu____6700 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6699)))
in (mkForall rng uu____6688))
in (

let uu____6714 = (escape a_name)
in {assumption_term = uu____6687; assumption_caption = FStar_Pervasives_Native.Some ("Constructor distinct"); assumption_name = uu____6714; assumption_fact_ids = []}))
in Assume (a))))))))
end))


let injective_constructor : FStar_Range.range  ->  (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun rng uu____6737 -> (match (uu____6737) with
| (name, fields, st) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____6769 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6769)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____6808 = (

let uu____6814 = (bvar_name i)
in ((uu____6814), (s)))
in (mkFreeV uu____6808)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6847 -> (match (uu____6847) with
| (uu____6857, s, uu____6859) -> begin
(

let uu____6864 = (bvar i s)
in (uu____6864 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____6886 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6924 -> (match (uu____6924) with
| (iname, isort, projectible) -> begin
(

let cproj_app = (mkApp ((iname), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((iname), ((st)::[]), (isort), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____6957 = (

let uu____6958 = (

let uu____6969 = (

let uu____6970 = (

let uu____6975 = (

let uu____6976 = (bvar i isort)
in (uu____6976 norng))
in ((cproj_app), (uu____6975)))
in (mkEq uu____6970 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6969)))
in (mkForall rng uu____6958))
in (

let uu____6989 = (escape (Prims.strcat "projection_inverse_" iname))
in {assumption_term = uu____6957; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = uu____6989; assumption_fact_ids = []}))
in (proj_name)::(Assume (a))::[])
end
| uu____6994 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____6886 FStar_List.flatten)))))))))
end))


let constructor_to_decl : FStar_Range.range  ->  constructor_t  ->  decls_t = (fun rng uu____7012 -> (match (uu____7012) with
| (name, fields, st, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7075 -> (match (uu____7075) with
| (uu____7084, sort, uu____7086) -> begin
sort
end))))
in (

let cdecl = DeclFun (((name), (field_sorts), (st), (FStar_Pervasives_Native.Some ("Constructor"))))
in (

let cid = (fresh_constructor rng ((name), (field_sorts), (st), (id1)))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (st))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (

let uu____7111 = (

let uu____7116 = (

let uu____7117 = (

let uu____7125 = (constr_id_of_sort st)
in ((uu____7125), ((xx)::[])))
in (mkApp uu____7117 norng))
in (

let uu____7130 = (

let uu____7131 = (FStar_Util.string_of_int id1)
in (mkInteger uu____7131 norng))
in ((uu____7116), (uu____7130))))
in (mkEq uu____7111 norng))
in (

let uu____7133 = (

let uu____7144 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7197 -> (match (uu____7197) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____7237 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____7237), ([])))
end
| uu____7253 -> begin
(

let fi = (

let uu____7261 = (

let uu____7263 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____7263))
in ((uu____7261), (s)))
in (

let uu____7267 = (mkFreeV fi norng)
in ((uu____7267), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____7144 FStar_List.split))
in (match (uu____7133) with
| (proj_terms, ex_vars) -> begin
(

let uu____7319 = uu____7133
in (

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____7334 = (

let uu____7339 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____7339)))
in (mkEq uu____7334 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____7344 -> begin
(mkExists norng (([]), (ex_vars1), (disc_inv_body)))
end)
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body1)) rng)
in (

let def = (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (FStar_Pervasives_Native.Some ("Discriminator definition"))))
in def))))))
end))))))
in (

let projs = (match (injective1) with
| true -> begin
(injective_constructor rng ((name), (fields), (st)))
end
| uu____7369 -> begin
[]
end)
in (

let uu____7371 = (

let uu____7374 = (

let uu____7375 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____7375))
in (uu____7374)::(cdecl)::(cid)::projs)
in (

let uu____7378 = (

let uu____7381 = (

let uu____7384 = (

let uu____7385 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____7385))
in (uu____7384)::[])
in (FStar_List.append ((disc)::[]) uu____7381))
in (FStar_List.append uu____7371 uu____7378)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____7469 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____7533 s -> (match (uu____7533) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____7598 -> begin
"@u"
end)
in (

let prefix2 = (match (prefix_opt) with
| FStar_Pervasives_Native.None -> begin
prefix1
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p prefix1)
end)
in (

let nm = (

let uu____7609 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____7609))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____7627 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____7627))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____7469) with
| (names1, binders, n1) -> begin
(

let uu____7697 = uu____7469
in ((names1), ((FStar_List.rev binders)), (n1)))
end)))


let name_macro_binders : sort Prims.list  ->  (fv Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____7755 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____7755) with
| (names1, binders, n1) -> begin
(

let uu____7815 = uu____7755
in (((FStar_List.rev names1)), (binders)))
end)))


let termToSmt : Prims.bool  ->  Prims.string  ->  term  ->  Prims.string = (fun print_ranges enclosing_name t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____7911); freevars = uu____7912; rng = uu____7913})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____7931 -> begin
tm
end))))))))
in (

let rec aux' = (fun depth n1 names1 t1 -> (

let aux1 = (aux (depth + (Prims.parse_int "1")))
in (match (t1.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____8007 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____8007 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____8036 = (op_to_string op)
in (

let uu____8038 = (

let uu____8040 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____8040 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____8036 uu____8038)))
end
| Labeled (t2, uu____8052, uu____8053) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____8060 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____8060 s))
end
| Quant (qop, pats, wopt, sorts, body, qid) -> begin
(

let qidstr = (

let uu____8095 = (FStar_ST.op_Bang qid)
in (match (uu____8095) with
| FStar_Pervasives_Native.None -> begin
(failwith "no qid was assigned")
end
| FStar_Pervasives_Native.Some (str) -> begin
str
end))
in (

let uu____8153 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____8153) with
| (names2, binders, n2) -> begin
(

let uu____8183 = uu____8153
in (

let binders1 = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats1 = (remove_guard_free pats)
in (

let pats_str = (match (pats1) with
| ([])::[] -> begin
";;no pats"
end
| [] -> begin
";;no pats"
end
| uu____8219 -> begin
(

let uu____8224 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____8243 = (

let uu____8245 = (FStar_List.map (fun p -> (

let uu____8253 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____8253))) pats2)
in (FStar_String.concat " " uu____8245))
in (FStar_Util.format1 "\n:pattern (%s)" uu____8243)))))
in (FStar_All.pipe_right uu____8224 (FStar_String.concat "\n")))
end)
in (

let uu____8263 = (

let uu____8267 = (

let uu____8271 = (

let uu____8275 = (aux1 n2 names2 body)
in (

let uu____8277 = (

let uu____8281 = (weightToSmt wopt)
in (uu____8281)::(pats_str)::(qidstr)::[])
in (uu____8275)::uu____8277))
in (binders1)::uu____8271)
in ((qop_to_string qop))::uu____8267)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____8263))))))
end)))
end
| Let (es, body) -> begin
(

let uu____8297 = (FStar_List.fold_left (fun uu____8330 e -> (match (uu____8330) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____8373 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____8373))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____8382 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____8382))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____8297) with
| (names2, binders, n2) -> begin
(

let uu____8416 = uu____8297
in (

let uu____8429 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____8429)))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match (((print_ranges && (Prims.op_disEquality t1.rng norng)) && (Prims.op_disEquality t1.rng prrng))) with
| true -> begin
(

let uu____8446 = (FStar_Range.string_of_range t1.rng)
in (

let uu____8448 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____8446 uu____8448 s)))
end
| uu____8451 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.bool  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun print_captions uu___124_8477 -> (match (uu___124_8477) with
| FStar_Pervasives_Native.Some (c) when print_captions -> begin
(

let c1 = (

let uu____8487 = (FStar_All.pipe_right (FStar_String.split ((10)::[]) c) (FStar_List.map FStar_Util.trim_string))
in (FStar_All.pipe_right uu____8487 (FStar_String.concat " ")))
in (Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")))
end
| uu____8509 -> begin
""
end))


let rec declToSmt' : Prims.string  ->  Prims.bool  ->  decl  ->  Prims.string = (fun z3options print_captions decl -> ((assign_qids decl);
(match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| FuelDeclaration -> begin
"(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))"
end
| SortDeclaration (s) -> begin
(Prims.strcat "(declare-sort " (Prims.strcat s ")"))
end
| GenerateOptions -> begin
z3options
end
| Hardcoded (s) -> begin
s
end
| Module (s, decls) -> begin
(

let res = (

let uu____8593 = (FStar_List.map (declToSmt' z3options print_captions) decls)
in (FStar_All.pipe_right uu____8593 (FStar_String.concat "\n")))
in (

let uu____8603 = (FStar_Options.keep_query_captions ())
in (match (uu____8603) with
| true -> begin
(

let uu____8607 = (FStar_Util.string_of_int (FStar_List.length decls))
in (

let uu____8609 = (FStar_Util.string_of_int (FStar_String.length res))
in (FStar_Util.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)" s res s uu____8607 uu____8609)))
end
| uu____8612 -> begin
res
end)))
end
| Caption (c) -> begin
(match (print_captions) with
| true -> begin
(

let uu____8618 = (

let uu____8620 = (FStar_All.pipe_right (FStar_Util.splitlines c) (FStar_List.map (fun s -> (Prims.strcat "; " (Prims.strcat s "\n")))))
in (FStar_All.pipe_right uu____8620 (FStar_String.concat "")))
in (Prims.strcat "\n" uu____8618))
end
| uu____8643 -> begin
""
end)
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____8661 = (

let uu____8663 = (caption_to_string print_captions)
in (uu____8663 c))
in (

let uu____8672 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8661 f (FStar_String.concat " " l) uu____8672))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____8687 = (name_macro_binders arg_sorts)
in (match (uu____8687) with
| (names1, binders) -> begin
(

let uu____8710 = uu____8687
in (

let body1 = (

let uu____8721 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____8721 body))
in (

let uu____8736 = (

let uu____8738 = (caption_to_string print_captions)
in (uu____8738 c))
in (

let uu____8747 = (strSort retsort)
in (

let uu____8749 = (

let uu____8751 = (escape f)
in (termToSmt print_captions uu____8751 body1))
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____8736 f (FStar_String.concat " " binders) uu____8747 uu____8749))))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___125_8781 -> (match (uu___125_8781) with
| Name (n1) -> begin
(

let uu____8784 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____8784))
end
| Namespace (ns) -> begin
(

let uu____8788 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____8788))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (match (print_captions) with
| true -> begin
(

let uu____8798 = (

let uu____8800 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____8800))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8798))
end
| uu____8806 -> begin
""
end)
in (

let n1 = a.assumption_name
in (

let uu____8811 = (

let uu____8813 = (caption_to_string print_captions)
in (uu____8813 a.assumption_caption))
in (

let uu____8822 = (termToSmt print_captions n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8811 fids uu____8822 n1))))))
end
| Eval (t) -> begin
(

let uu____8826 = (termToSmt print_captions "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____8826))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____8833) -> begin
""
end
| CheckSat -> begin
"(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
end
| GetUnsatCore -> begin
"(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
end
| GetProof -> begin
"(echo \"<proof>\")\n(get-proof)\n(echo \"</proof>\")"
end
| Push -> begin
"(push)"
end
| Pop -> begin
"(pop)"
end
| SetOption (s, v1) -> begin
(FStar_Util.format2 "(set-option :%s %s)" s v1)
end
| GetStatistics -> begin
"(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
end
| GetReasonUnknown -> begin
"(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
end);
))
and declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (

let uu____8856 = (FStar_Options.keep_query_captions ())
in (declToSmt' z3options uu____8856 decl)))
and declToSmt_no_caps : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' z3options false decl))
and declsToSmt : Prims.string  ->  decl Prims.list  ->  Prims.string = (fun z3options decls -> (

let uu____8869 = (FStar_List.map (declToSmt z3options) decls)
in (FStar_All.pipe_right uu____8869 (FStar_String.concat "\n"))))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____8990 = (

let uu____8994 = (FStar_All.pipe_right constrs (FStar_List.collect (constructor_to_decl norng)))
in (FStar_All.pipe_right uu____8994 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____8990 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let preludeDecls : decl Prims.list = (

let uu____9020 = (((("x"), (Term_sort))), ((("y"), (Term_sort))), ((("t"), (Term_sort))))
in (match (uu____9020) with
| (tmvarx, tmvary, tmvart) -> begin
(

let bovarb = (("b"), (Bool_sort))
in (

let flvarf = (("f"), (Fuel_sort))
in (

let uu____9114 = (((("t1"), (Term_sort))), ((("t2"), (Term_sort))), ((("x1"), (Term_sort))), ((("x2"), (Term_sort))), ((("y1"), (Term_sort))), ((("y2"), (Term_sort))))
in (match (uu____9114) with
| (t1, t2, x1, x2, y1, y2) -> begin
(

let uu____9267 = (((("x"), (Int_sort))), ((("y"), (Int_sort))))
in (match (uu____9267) with
| (intvarx, intvary) -> begin
(

let hastypez = (

let uu____9321 = (

let uu____9322 = (

let uu____9330 = (

let uu____9333 = (mkApp (("ZFuel"), ([])) prrng)
in (

let uu____9338 = (

let uu____9341 = (mkFreeV tmvarx prrng)
in (

let uu____9342 = (

let uu____9345 = (mkFreeV tmvart prrng)
in (uu____9345)::[])
in (uu____9341)::uu____9342))
in (uu____9333)::uu____9338))
in (("HasTypeFuel"), (uu____9330)))
in (mkApp uu____9322 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9321))
in (

let hastype = (

let uu____9351 = (

let uu____9352 = (

let uu____9360 = (

let uu____9363 = (mkApp (("MaxIFuel"), ([])) prrng)
in (

let uu____9368 = (

let uu____9371 = (mkFreeV tmvarx prrng)
in (

let uu____9372 = (

let uu____9375 = (mkFreeV tmvart prrng)
in (uu____9375)::[])
in (uu____9371)::uu____9372))
in (uu____9363)::uu____9368))
in (("HasTypeFuel"), (uu____9360)))
in (mkApp uu____9352 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9351))
in (

let fuelirrelevance_pat = (

let uu____9381 = (

let uu____9389 = (

let uu____9392 = (

let uu____9393 = (

let uu____9401 = (

let uu____9404 = (mkFreeV flvarf prrng)
in (uu____9404)::[])
in (("SFuel"), (uu____9401)))
in (mkApp uu____9393 prrng))
in (

let uu____9409 = (

let uu____9412 = (mkFreeV tmvarx prrng)
in (

let uu____9413 = (

let uu____9416 = (mkFreeV tmvart prrng)
in (uu____9416)::[])
in (uu____9412)::uu____9413))
in (uu____9392)::uu____9409))
in (("HasTypeFuel"), (uu____9389)))
in (mkApp uu____9381 prrng))
in (

let fuelirrelevance = (

let uu____9422 = (

let uu____9433 = (

let uu____9434 = (

let uu____9439 = (

let uu____9440 = (

let uu____9448 = (

let uu____9451 = (mkFreeV tmvarx prrng)
in (

let uu____9452 = (

let uu____9455 = (mkFreeV tmvart prrng)
in (uu____9455)::[])
in (uu____9451)::uu____9452))
in (("HasTypeZ"), (uu____9448)))
in (mkApp uu____9440 prrng))
in ((fuelirrelevance_pat), (uu____9439)))
in (mkEq uu____9434 prrng))
in ((((fuelirrelevance_pat)::[])::[]), ((flvarf)::(tmvarx)::(tmvart)::[]), (uu____9433)))
in (mkForall prrng uu____9422))
in (

let nohoist_pat = (

let uu____9489 = (

let uu____9497 = (

let uu____9500 = (mkFreeV tmvart prrng)
in (

let uu____9501 = (

let uu____9504 = (mkFreeV bovarb prrng)
in (uu____9504)::[])
in (uu____9500)::uu____9501))
in (("NoHoist"), (uu____9497)))
in (mkApp uu____9489 prrng))
in (

let nohoist = (

let uu____9510 = (

let uu____9521 = (

let uu____9522 = (

let uu____9527 = (mkFreeV bovarb prrng)
in ((nohoist_pat), (uu____9527)))
in (mkEq uu____9522 prrng))
in ((((nohoist_pat)::[])::[]), ((tmvart)::(bovarb)::[]), (uu____9521)))
in (mkForall prrng uu____9510))
in (

let istyped = (

let uu____9552 = (

let uu____9553 = (

let uu____9564 = (

let uu____9565 = (

let uu____9573 = (

let uu____9576 = (mkFreeV tmvarx prrng)
in (

let uu____9577 = (

let uu____9580 = (mkFreeV tmvart prrng)
in (uu____9580)::[])
in (uu____9576)::uu____9577))
in (("HasTypeZ"), (uu____9573)))
in (mkApp uu____9565 prrng))
in (([]), ((tmvart)::[]), (uu____9564)))
in (mkExists prrng uu____9553))
in (abstr ((tmvarx)::[]) uu____9552))
in (

let validity_pat = (

let uu____9602 = (

let uu____9610 = (

let uu____9613 = (mkFreeV tmvart prrng)
in (uu____9613)::[])
in (("Valid"), (uu____9610)))
in (mkApp uu____9602 prrng))
in (

let validity = (

let uu____9619 = (

let uu____9630 = (

let uu____9631 = (

let uu____9636 = (

let uu____9637 = (

let uu____9648 = (

let uu____9649 = (

let uu____9657 = (

let uu____9660 = (mkFreeV tmvarx prrng)
in (

let uu____9661 = (

let uu____9664 = (mkFreeV tmvart prrng)
in (uu____9664)::[])
in (uu____9660)::uu____9661))
in (("HasType"), (uu____9657)))
in (mkApp uu____9649 prrng))
in (([]), ((tmvarx)::[]), (uu____9648)))
in (mkExists prrng uu____9637))
in ((uu____9636), (validity_pat)))
in (mkIff uu____9631 prrng))
in ((((validity_pat)::[])::[]), ((tmvart)::[]), (uu____9630)))
in (mkForall prrng uu____9619))
in (

let operator_pat = (fun nm -> (

let uu____9711 = (

let uu____9719 = (

let uu____9722 = (mkFreeV intvarx prrng)
in (

let uu____9723 = (

let uu____9726 = (mkFreeV intvary prrng)
in (uu____9726)::[])
in (uu____9722)::uu____9723))
in ((nm), (uu____9719)))
in (mkApp uu____9711 prrng)))
in (

let operator = (fun nm sm -> (

let uu____9745 = (

let uu____9756 = (

let uu____9761 = (

let uu____9764 = (operator_pat nm)
in (uu____9764)::[])
in (uu____9761)::[])
in (

let uu____9769 = (

let uu____9770 = (

let uu____9775 = (operator_pat nm)
in (

let uu____9776 = (

let uu____9777 = (

let uu____9785 = (

let uu____9788 = (mkFreeV intvarx prrng)
in (

let uu____9789 = (

let uu____9792 = (mkFreeV intvary prrng)
in (uu____9792)::[])
in (uu____9788)::uu____9789))
in ((sm), (uu____9785)))
in (mkApp uu____9777 prrng))
in ((uu____9775), (uu____9776))))
in (mkEq uu____9770 prrng))
in ((uu____9756), ((intvarx)::(intvary)::[]), (uu____9769))))
in (mkForall prrng uu____9745)))
in (

let constrs = (FStar_All.pipe_right (((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]) (FStar_List.collect (constructor_to_decl prrng)))
in (

let isprims = (

let uu____9925 = (

let uu____9926 = (

let uu____9934 = (

let uu____9937 = (mkFreeV tmvart prrng)
in (uu____9937)::[])
in (("is-LexCons"), (uu____9934)))
in (mkApp uu____9926 prrng))
in (abstr ((tmvart)::[]) uu____9925))
in (

let precedes_lext = (fun tm1 tm2 -> (

let lext = (mkApp (("Prims.lex_t"), ([])) prrng)
in (mkApp (("Prims.precedes"), ((lext)::(lext)::(tm1)::(tm2)::[])) prrng)))
in (

let lexicographic = (

let uu____9963 = (

let uu____9974 = (

let uu____9975 = (

let uu____9980 = (

let uu____9981 = (

let uu____9989 = (

let uu____9992 = (

let uu____9993 = (

let uu____9994 = (

let uu____10002 = (

let uu____10005 = (mkFreeV t1 prrng)
in (

let uu____10006 = (

let uu____10009 = (mkFreeV x1 prrng)
in (

let uu____10010 = (

let uu____10013 = (mkFreeV x2 prrng)
in (uu____10013)::[])
in (uu____10009)::uu____10010))
in (uu____10005)::uu____10006))
in (("LexCons"), (uu____10002)))
in (mkApp uu____9994 prrng))
in (

let uu____10018 = (

let uu____10019 = (

let uu____10027 = (

let uu____10030 = (mkFreeV t2 prrng)
in (

let uu____10031 = (

let uu____10034 = (mkFreeV y1 prrng)
in (

let uu____10035 = (

let uu____10038 = (mkFreeV y2 prrng)
in (uu____10038)::[])
in (uu____10034)::uu____10035))
in (uu____10030)::uu____10031))
in (("LexCons"), (uu____10027)))
in (mkApp uu____10019 prrng))
in (precedes_lext uu____9993 uu____10018)))
in (uu____9992)::[])
in (("Valid"), (uu____9989)))
in (mkApp uu____9981 prrng))
in (

let uu____10047 = (

let uu____10048 = (

let uu____10053 = (

let uu____10054 = (

let uu____10062 = (

let uu____10065 = (

let uu____10066 = (

let uu____10074 = (

let uu____10077 = (mkFreeV t1 prrng)
in (

let uu____10078 = (

let uu____10081 = (mkFreeV t2 prrng)
in (

let uu____10082 = (

let uu____10085 = (mkFreeV x1 prrng)
in (

let uu____10086 = (

let uu____10089 = (mkFreeV y1 prrng)
in (uu____10089)::[])
in (uu____10085)::uu____10086))
in (uu____10081)::uu____10082))
in (uu____10077)::uu____10078))
in (("Prims.precedes"), (uu____10074)))
in (mkApp uu____10066 prrng))
in (uu____10065)::[])
in (("Valid"), (uu____10062)))
in (mkApp uu____10054 prrng))
in (

let uu____10098 = (

let uu____10099 = (

let uu____10104 = (

let uu____10105 = (

let uu____10110 = (mkFreeV x1 prrng)
in (

let uu____10111 = (mkFreeV y1 prrng)
in ((uu____10110), (uu____10111))))
in (mkEq uu____10105 prrng))
in (

let uu____10112 = (

let uu____10113 = (

let uu____10121 = (

let uu____10124 = (

let uu____10125 = (mkFreeV x2 prrng)
in (

let uu____10126 = (mkFreeV y2 prrng)
in (precedes_lext uu____10125 uu____10126)))
in (uu____10124)::[])
in (("Valid"), (uu____10121)))
in (mkApp uu____10113 prrng))
in ((uu____10104), (uu____10112))))
in (mkAnd uu____10099 prrng))
in ((uu____10053), (uu____10098))))
in (mkOr uu____10048 prrng))
in ((uu____9980), (uu____10047))))
in (mkIff uu____9975 prrng))
in (([]), ((t1)::(t2)::(x1)::(x2)::(y1)::(y2)::[]), (uu____9974)))
in (mkForall prrng uu____9963))
in (

let precedes_pat = (

let uu____10173 = (

let uu____10181 = (

let uu____10184 = (mkFreeV t1 prrng)
in (

let uu____10185 = (

let uu____10188 = (mkFreeV t2 prrng)
in (

let uu____10189 = (

let uu____10192 = (mkFreeV x1 prrng)
in (

let uu____10193 = (

let uu____10196 = (mkFreeV x2 prrng)
in (uu____10196)::[])
in (uu____10192)::uu____10193))
in (uu____10188)::uu____10189))
in (uu____10184)::uu____10185))
in (("Prims.precedes"), (uu____10181)))
in (mkApp uu____10173 prrng))
in (

let precedes = (

let uu____10202 = (

let uu____10213 = (

let uu____10214 = (

let uu____10219 = (mkApp (("Valid"), ((precedes_pat)::[])) prrng)
in (

let uu____10224 = (

let uu____10225 = (

let uu____10233 = (

let uu____10236 = (

let uu____10237 = (mkFreeV x1 prrng)
in (

let uu____10238 = (mkFreeV x2 prrng)
in (precedes_lext uu____10237 uu____10238)))
in (uu____10236)::[])
in (("Valid"), (uu____10233)))
in (mkApp uu____10225 prrng))
in ((uu____10219), (uu____10224))))
in (mkIff uu____10214 prrng))
in ((((precedes_pat)::[])::[]), ((t1)::(t2)::(x1)::(x2)::[]), (uu____10213)))
in (mkForall prrng uu____10202))
in (

let rank_pat = (

let uu____10277 = (mkFreeV t1 prrng)
in (

let uu____10278 = (mkFreeV t2 prrng)
in (precedes_lext uu____10277 uu____10278)))
in (

let rank = (

let uu____10280 = (

let uu____10291 = (

let uu____10292 = (

let uu____10297 = (mkApp (("Valid"), ((rank_pat)::[])) prrng)
in (

let uu____10302 = (

let uu____10303 = (

let uu____10308 = (

let uu____10309 = (

let uu____10317 = (

let uu____10320 = (mkFreeV t1 prrng)
in (uu____10320)::[])
in (("Rank"), (uu____10317)))
in (mkApp uu____10309 prrng))
in (

let uu____10325 = (

let uu____10326 = (

let uu____10334 = (

let uu____10337 = (mkFreeV t2 prrng)
in (uu____10337)::[])
in (("Rank"), (uu____10334)))
in (mkApp uu____10326 prrng))
in ((uu____10308), (uu____10325))))
in (mkLT uu____10303 prrng))
in ((uu____10297), (uu____10302))))
in (mkIff uu____10292 prrng))
in ((((rank_pat)::[])::[]), ((t1)::(t2)::[]), (uu____10291)))
in (mkForall prrng uu____10280))
in (

let uu____10365 = (

let uu____10368 = (

let uu____10371 = (

let uu____10374 = (

let uu____10377 = (

let uu____10380 = (

let uu____10383 = (

let uu____10386 = (

let uu____10389 = (

let uu____10392 = (

let uu____10395 = (

let uu____10398 = (

let uu____10401 = (

let uu____10404 = (

let uu____10407 = (

let uu____10408 = (

let uu____10409 = (escape "fuel_irrelevance")
in {assumption_term = fuelirrelevance; assumption_caption = FStar_Pervasives_Native.Some ("Fuel irrelevance"); assumption_name = uu____10409; assumption_fact_ids = []})
in Assume (uu____10408))
in (

let uu____10414 = (

let uu____10417 = (

let uu____10420 = (

let uu____10421 = (

let uu____10422 = (escape "no_hoist")
in {assumption_term = nohoist; assumption_caption = FStar_Pervasives_Native.Some ("No-hoist"); assumption_name = uu____10422; assumption_fact_ids = []})
in Assume (uu____10421))
in (

let uu____10427 = (

let uu____10430 = (

let uu____10433 = (

let uu____10436 = (

let uu____10439 = (

let uu____10442 = (

let uu____10445 = (

let uu____10448 = (

let uu____10451 = (

let uu____10454 = (

let uu____10455 = (

let uu____10469 = (

let uu____10470 = (mkFreeV tmvarx prrng)
in (abstr ((tmvarx)::[]) uu____10470))
in (("Reify"), ((Term_sort)::[]), (Term_sort), (uu____10469), (FStar_Pervasives_Native.None)))
in DefineFun (uu____10455))
in (

let uu____10476 = (

let uu____10479 = (

let uu____10480 = (

let uu____10481 = (escape "validity")
in {assumption_term = validity; assumption_caption = FStar_Pervasives_Native.Some ("Validity"); assumption_name = uu____10481; assumption_fact_ids = []})
in Assume (uu____10480))
in (

let uu____10486 = (

let uu____10489 = (

let uu____10492 = (

let uu____10495 = (

let uu____10498 = (

let uu____10501 = (

let uu____10504 = (

let uu____10507 = (

let uu____10508 = (

let uu____10509 = (operator "_mul" "*")
in (

let uu____10512 = (escape "arithmetic_multiplication")
in {assumption_term = uu____10509; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic multiplication"); assumption_name = uu____10512; assumption_fact_ids = []}))
in Assume (uu____10508))
in (

let uu____10517 = (

let uu____10520 = (

let uu____10521 = (

let uu____10522 = (operator "_div" "div")
in (

let uu____10525 = (escape "arithmetic_division")
in {assumption_term = uu____10522; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic division"); assumption_name = uu____10525; assumption_fact_ids = []}))
in Assume (uu____10521))
in (

let uu____10530 = (

let uu____10533 = (

let uu____10534 = (

let uu____10535 = (operator "_mod" "mod")
in (

let uu____10538 = (escape "arithmetic_modulus")
in {assumption_term = uu____10535; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic modulus"); assumption_name = uu____10538; assumption_fact_ids = []}))
in Assume (uu____10534))
in (uu____10533)::[])
in (uu____10520)::uu____10530))
in (uu____10507)::uu____10517))
in (DeclFun ((("__uu__PartialApp"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10504)
in (DeclFun ((("_mod"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10501)
in (DeclFun ((("_div"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10498)
in (DeclFun ((("_mul"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10495)
in (DeclFun ((("Range_const"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10492)
in (DeclFun ((("Prims.precedes"), ((Term_sort)::(Term_sort)::(Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10489)
in (uu____10479)::uu____10486))
in (uu____10454)::uu____10476))
in (DeclFun ((("Tm_uvar"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10451)
in (DeclFun ((("ConsFuel"), ((Fuel_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10448)
in (DeclFun ((("ConsTerm"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10445)
in (DeclFun ((("Closure"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10442)
in (DeclFun ((("Rank"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10439)
in (DeclFun ((("ApplyTT"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10436)
in (DeclFun ((("ApplyTF"), ((Term_sort)::(Fuel_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10433)
in (DefineFun ((("IsTyped"), ((Term_sort)::[]), (Bool_sort), (istyped), (FStar_Pervasives_Native.None))))::uu____10430)
in (uu____10420)::uu____10427))
in (DeclFun ((("NoHoist"), ((Term_sort)::(Bool_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10417)
in (uu____10407)::uu____10414))
in (DefineFun ((("HasType"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastype), (FStar_Pervasives_Native.None))))::uu____10404)
in (DefineFun ((("HasTypeZ"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastypez), (FStar_Pervasives_Native.None))))::uu____10401)
in (DeclFun ((("HasTypeFuel"), ((Fuel_sort)::(Term_sort)::(Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10398)
in (DeclFun ((("Valid"), ((Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10395)
in (DeclFun ((("PreType"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10392)
in (DeclFun ((("MaxFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10389)
in (DeclFun ((("MaxIFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10386)
in (FuelDeclaration)::uu____10383)
in (DeclFun ((("Term_constr_id"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10380)
in (SortDeclaration ("Term"))::uu____10377)
in (DeclFun ((("FString_constr_id"), ((String_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10374)
in (SortDeclaration ("FString"))::uu____10371)
in (GenerateOptions)::uu____10368)
in (

let uu____10665 = (

let uu____10668 = (

let uu____10671 = (

let uu____10674 = (

let uu____10677 = (

let uu____10678 = (

let uu____10679 = (escape "lexicographic_ordering")
in {assumption_term = lexicographic; assumption_caption = FStar_Pervasives_Native.Some ("Lexicographic ordering"); assumption_name = uu____10679; assumption_fact_ids = []})
in Assume (uu____10678))
in (

let uu____10684 = (

let uu____10687 = (

let uu____10688 = (

let uu____10689 = (escape "precedes_ordering")
in {assumption_term = precedes; assumption_caption = FStar_Pervasives_Native.Some ("Precedes ordering"); assumption_name = uu____10689; assumption_fact_ids = []})
in Assume (uu____10688))
in (

let uu____10694 = (

let uu____10697 = (

let uu____10698 = (

let uu____10699 = (escape "rank_ordering")
in {assumption_term = rank; assumption_caption = FStar_Pervasives_Native.Some ("Rank ordering"); assumption_name = uu____10699; assumption_fact_ids = []})
in Assume (uu____10698))
in (uu____10697)::[])
in (uu____10687)::uu____10694))
in (uu____10677)::uu____10684))
in (DeclFun ((("Prims.lex_t"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10674)
in (DefineFun ((("is-Prims.LexCons"), ((Term_sort)::[]), (Bool_sort), (isprims), (FStar_Pervasives_Native.None))))::uu____10671)
in (FStar_List.append constrs uu____10668))
in (FStar_List.append uu____10365 uu____10665))))))))))))))))))))))
end))
end))))
end))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____10724 = (

let uu____10725 = (

let uu____10727 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____10727))
in (

let uu____10736 = (

let uu____10739 = (

let uu____10740 = (

let uu____10742 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____10742))
in ((uu____10740), (BitVec_sort (sz)), (true)))
in (uu____10739)::[])
in ((uu____10725), (uu____10736), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____10724 (constructor_to_decl norng))))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____10785 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____10810 = (

let uu____10812 = (FStar_ST.op_Bang __range_c)
in (uu____10812 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____10810));
(

let uu____10857 = (

let uu____10865 = (

let uu____10868 = (mkInteger' i norng)
in (uu____10868)::[])
in (("Range_const"), (uu____10865)))
in (mkApp uu____10857 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____10911 = (

let uu____10919 = (

let uu____10922 = (mkInteger' i norng)
in (uu____10922)::[])
in (("Tm_uvar"), (uu____10919)))
in (mkApp uu____10911 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____10965 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____10989 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____10989 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11064 = (

let uu____11066 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11066))
in (

let uu____11075 = (

let uu____11077 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11077))
in (elim_box true uu____11064 uu____11075 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11100 = (

let uu____11102 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11102))
in (

let uu____11111 = (

let uu____11113 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11113))
in (elim_box true uu____11100 uu____11111 t))))


let boxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(boxInt t)
end
| Bool_sort -> begin
(boxBool t)
end
| String_sort -> begin
(boxString t)
end
| BitVec_sort (sz) -> begin
(boxBitVec sz t)
end
| uu____11136 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let unboxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(unboxInt t)
end
| Bool_sort -> begin
(unboxBool t)
end
| String_sort -> begin
(unboxString t)
end
| BitVec_sort (sz) -> begin
(unboxBitVec sz t)
end
| uu____11150 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____11176 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____11176))
end
| uu____11179 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____11181 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____11199)::(t1)::(t2)::[]); freevars = uu____11202; rng = uu____11203})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____11219)::(t1)::(t2)::[]); freevars = uu____11222; rng = uu____11223})::[]) -> begin
(

let uu____11239 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____11239 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11242; rng = uu____11243})::[]) -> begin
(

let uu____11259 = (

let uu____11264 = (unboxInt t1)
in (

let uu____11265 = (unboxInt t2)
in ((uu____11264), (uu____11265))))
in (mkLTE uu____11259 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____11268; rng = uu____11269})::[]) -> begin
(

let uu____11285 = (

let uu____11290 = (unboxInt t1)
in (

let uu____11291 = (unboxInt t2)
in ((uu____11290), (uu____11291))))
in (mkLT uu____11285 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11294; rng = uu____11295})::[]) -> begin
(

let uu____11311 = (

let uu____11316 = (unboxInt t1)
in (

let uu____11317 = (unboxInt t2)
in ((uu____11316), (uu____11317))))
in (mkGTE uu____11311 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____11320; rng = uu____11321})::[]) -> begin
(

let uu____11337 = (

let uu____11342 = (unboxInt t1)
in (

let uu____11343 = (unboxInt t2)
in ((uu____11342), (uu____11343))))
in (mkGT uu____11337 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____11346; rng = uu____11347})::[]) -> begin
(

let uu____11363 = (

let uu____11368 = (unboxBool t1)
in (

let uu____11369 = (unboxBool t2)
in ((uu____11368), (uu____11369))))
in (mkAnd uu____11363 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____11372; rng = uu____11373})::[]) -> begin
(

let uu____11389 = (

let uu____11394 = (unboxBool t1)
in (

let uu____11395 = (unboxBool t2)
in ((uu____11394), (uu____11395))))
in (mkOr uu____11389 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____11397; rng = uu____11398})::[]) -> begin
(

let uu____11414 = (unboxBool t1)
in (mkNot uu____11414 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11418; rng = uu____11419})::[]) when (

let uu____11435 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11435)) -> begin
(

let sz = (

let uu____11442 = (getBoxedInteger t0)
in (match (uu____11442) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11450 -> begin
(failwith "impossible")
end))
in (

let uu____11456 = (

let uu____11461 = (unboxBitVec sz t1)
in (

let uu____11462 = (unboxBitVec sz t2)
in ((uu____11461), (uu____11462))))
in (mkBvUlt uu____11456 t.rng)))
end
| App (Var ("Prims.equals"), (uu____11463)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11467; rng = uu____11468})::(uu____11469)::[]) when (

let uu____11485 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11485)) -> begin
(

let sz = (

let uu____11492 = (getBoxedInteger t0)
in (match (uu____11492) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11500 -> begin
(failwith "impossible")
end))
in (

let uu____11506 = (

let uu____11511 = (unboxBitVec sz t1)
in (

let uu____11512 = (unboxBitVec sz t2)
in ((uu____11511), (uu____11512))))
in (mkBvUlt uu____11506 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___126_11517 = (unboxBool t1)
in {tm = uu___126_11517.tm; freevars = uu___126_11517.freevars; rng = t.rng})
end
| uu____11518 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____11579 = (FStar_Options.unthrottle_inductives ())
in (match (uu____11579) with
| true -> begin
(mk_HasType v1 t)
end
| uu____11582 -> begin
(mkApp (("HasTypeFuel"), ((f)::(v1)::(t)::[])) t.rng)
end)))


let mk_HasTypeWithFuel : term FStar_Pervasives_Native.option  ->  term  ->  term  ->  term = (fun f v1 t -> (match (f) with
| FStar_Pervasives_Native.None -> begin
(mk_HasType v1 t)
end
| FStar_Pervasives_Native.Some (f1) -> begin
(mk_HasTypeFuel f1 v1 t)
end))


let mk_NoHoist : term  ->  term  ->  term = (fun dummy b -> (mkApp (("NoHoist"), ((dummy)::(b)::[])) b.rng))


let mk_Destruct : term  ->  FStar_Range.range  ->  term = (fun v1 -> (mkApp (("Destruct"), ((v1)::[]))))


let mk_Rank : term  ->  FStar_Range.range  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n1 t -> (mkApp (((Prims.strcat "is-" n1)), ((t)::[])) t.rng))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[])) t.rng))


let mk_ApplyTT : term  ->  term  ->  FStar_Range.range  ->  term = (fun t t' r -> (mkApp (("ApplyTT"), ((t)::(t')::[])) r))


let kick_partial_app : term  ->  term = (fun t -> (

let uu____11712 = (

let uu____11713 = (mkApp (("__uu__PartialApp"), ([])) t.rng)
in (mk_ApplyTT uu____11713 t t.rng))
in (FStar_All.pipe_right uu____11712 mk_Valid)))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____11731 = (

let uu____11739 = (

let uu____11742 = (mkInteger' i norng)
in (uu____11742)::[])
in (("FString_const"), (uu____11739)))
in (mkApp uu____11731 r)))


let mk_Precedes : term  ->  term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 x4 r -> (

let uu____11773 = (mkApp (("Prims.precedes"), ((x1)::(x2)::(x3)::(x4)::[])) r)
in (FStar_All.pipe_right uu____11773 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 r -> (mkApp (("LexCons"), ((x1)::(x2)::(x3)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____11818 -> begin
(

let uu____11820 = (

let uu____11828 = (

let uu____11831 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____11831)::[])
in (("SFuel"), (uu____11828)))
in (mkApp uu____11820 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____11879 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____11879))
end
| (FStar_Pervasives_Native.Some (p), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (p)) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end))


let mk_and_opt_l : term FStar_Pervasives_Native.option Prims.list  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl FStar_Pervasives_Native.None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____11942 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____11942)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____11962 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____11962)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____11973 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____11973)))




