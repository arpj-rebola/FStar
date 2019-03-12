
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

let set_qid = (fun qid n1 -> (

let uu____2606 = (FStar_ST.op_Bang qid)
in (match (uu____2606) with
| FStar_Pervasives_Native.Some (uu____2658) -> begin
n1
end
| FStar_Pervasives_Native.None -> begin
((

let uu____2663 = (

let uu____2667 = (

let uu____2669 = (

let uu____2671 = (FStar_Util.string_of_int n1)
in (Prims.strcat "." uu____2671))
in (Prims.strcat nm uu____2669))
in FStar_Pervasives_Native.Some (uu____2667))
in (FStar_ST.op_Colon_Equals qid uu____2663));
(n1 + (Prims.parse_int "1"));
)
end)))
in (

let rec aux = (fun n1 tx -> (match (tx.tm) with
| App (uu____2738, tms) -> begin
(FStar_List.fold_left aux n1 tms)
end
| Quant (uu____2745, uu____2746, uu____2747, uu____2748, scp, qid) -> begin
(

let nx = (set_qid qid n1)
in (aux nx scp))
end
| Let (tms, scp) -> begin
(

let nx = (FStar_List.fold_left aux n1 tms)
in (aux nx scp))
end
| Labeled (scp, uu____2820, uu____2821) -> begin
(aux n1 scp)
end
| LblPos (scp, uu____2825) -> begin
(aux n1 scp)
end
| uu____2828 -> begin
n1
end))
in (

let uu____2829 = (aux (Prims.parse_int "0") t)
in (FStar_All.pipe_right uu____2829 (fun a1 -> ()))))))
in (match (d) with
| DefineFun (nm, uu____2834, uu____2835, tm, uu____2837) -> begin
(in_terms (Prims.strcat "funqid_" nm) tm)
end
| Assume (a) -> begin
(in_terms a.assumption_name a.assumption_term)
end
| Module (uu____2846, ds) -> begin
(FStar_List.iter assign_qids ds)
end
| uu____2854 -> begin
()
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___121_2861 -> (match (uu___121_2861) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___122_2871 -> (match (uu___122_2871) with
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

let uu____2906 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____2906))
end
| NatToBv (n1) -> begin
(

let uu____2911 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____2911))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___123_2925 -> (match (uu___123_2925) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____2935 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____2935))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2955 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____2955))
end
| FreeV (x) -> begin
(

let uu____2964 = (

let uu____2966 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____2966))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____2964))
end
| App (op, tms) -> begin
(

let uu____2977 = (

let uu____2979 = (op_to_string op)
in (

let uu____2981 = (

let uu____2983 = (

let uu____2985 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____2985 (FStar_String.concat " ")))
in (Prims.strcat uu____2983 ")"))
in (Prims.strcat uu____2979 uu____2981)))
in (Prims.strcat "(" uu____2977))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____3002 = (hash_of_term t1)
in (

let uu____3004 = (

let uu____3006 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____3006))
in (Prims.strcat uu____3002 uu____3004)))
end
| LblPos (t1, r) -> begin
(

let uu____3012 = (

let uu____3014 = (hash_of_term t1)
in (Prims.strcat uu____3014 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____3012))
end
| Quant (qop, pats, wopt, sorts, body, uu____3024) -> begin
(

let uu____3049 = (

let uu____3051 = (

let uu____3053 = (

let uu____3055 = (

let uu____3057 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____3057 (FStar_String.concat " ")))
in (

let uu____3067 = (

let uu____3069 = (

let uu____3071 = (hash_of_term body)
in (

let uu____3073 = (

let uu____3075 = (

let uu____3077 = (weightToSmt wopt)
in (

let uu____3079 = (

let uu____3081 = (

let uu____3083 = (

let uu____3085 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____3104 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____3104 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____3085 (FStar_String.concat "; ")))
in (Prims.strcat uu____3083 "))"))
in (Prims.strcat " " uu____3081))
in (Prims.strcat uu____3077 uu____3079)))
in (Prims.strcat " " uu____3075))
in (Prims.strcat uu____3071 uu____3073)))
in (Prims.strcat ")(! " uu____3069))
in (Prims.strcat uu____3055 uu____3067)))
in (Prims.strcat " (" uu____3053))
in (Prims.strcat (qop_to_string qop) uu____3051))
in (Prims.strcat "(" uu____3049))
end
| Let (es, body) -> begin
(

let uu____3131 = (

let uu____3133 = (

let uu____3135 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____3135 (FStar_String.concat " ")))
in (

let uu____3145 = (

let uu____3147 = (

let uu____3149 = (hash_of_term body)
in (Prims.strcat uu____3149 ")"))
in (Prims.strcat ") " uu____3147))
in (Prims.strcat uu____3133 uu____3145)))
in (Prims.strcat "(let (" uu____3131))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____3241 = (

let uu____3243 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____3243))
in (mkBoxFunctions uu____3241)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____3260 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____3260 "Box")) && (

let uu____3267 = (

let uu____3269 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____3269))
in (not (uu____3267))))
end
| uu____3279 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____3293 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____3293; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3370 = (

let uu____3371 = (FStar_Util.ensure_decimal i)
in Integer (uu____3371))
in (mk uu____3370 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3386 = (FStar_Util.string_of_int i)
in (mkInteger uu____3386 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____3456 r -> (match (uu____3456) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____3486) -> begin
(mkFalse r)
end
| App (FalseOp, uu____3491) -> begin
(mkTrue r)
end
| uu____3496 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3512 r -> (match (uu____3512) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3520), uu____3521) -> begin
t2
end
| (uu____3526, App (TrueOp, uu____3527)) -> begin
t1
end
| (App (FalseOp, uu____3532), uu____3533) -> begin
(mkFalse r)
end
| (uu____3538, App (FalseOp, uu____3539)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3556, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____3565) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3572 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3592 r -> (match (uu____3592) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3600), uu____3601) -> begin
(mkTrue r)
end
| (uu____3606, App (TrueOp, uu____3607)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3612), uu____3613) -> begin
t2
end
| (uu____3618, App (FalseOp, uu____3619)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3636, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____3645) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3652 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3672 r -> (match (uu____3672) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____3680, App (TrueOp, uu____3681)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3686), uu____3687) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____3692), uu____3693) -> begin
t2
end
| (uu____3698, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____3703 = (

let uu____3710 = (

let uu____3713 = (mkAnd ((t1), (t1')) r)
in (uu____3713)::(t2')::[])
in ((Imp), (uu____3710)))
in (mkApp' uu____3703 r))
end
| uu____3716 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____3741 r -> (match (uu____3741) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3951 r -> (match (uu____3951) with
| (t1, t2) -> begin
(

let uu____3960 = (

let uu____3967 = (

let uu____3970 = (

let uu____3973 = (mkNatToBv sz t2 r)
in (uu____3973)::[])
in (t1)::uu____3970)
in ((BvShl), (uu____3967)))
in (mkApp' uu____3960 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3995 r -> (match (uu____3995) with
| (t1, t2) -> begin
(

let uu____4004 = (

let uu____4011 = (

let uu____4014 = (

let uu____4017 = (mkNatToBv sz t2 r)
in (uu____4017)::[])
in (t1)::uu____4014)
in ((BvShr), (uu____4011)))
in (mkApp' uu____4004 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4039 r -> (match (uu____4039) with
| (t1, t2) -> begin
(

let uu____4048 = (

let uu____4055 = (

let uu____4058 = (

let uu____4061 = (mkNatToBv sz t2 r)
in (uu____4061)::[])
in (t1)::uu____4058)
in ((BvUdiv), (uu____4055)))
in (mkApp' uu____4048 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4083 r -> (match (uu____4083) with
| (t1, t2) -> begin
(

let uu____4092 = (

let uu____4099 = (

let uu____4102 = (

let uu____4105 = (mkNatToBv sz t2 r)
in (uu____4105)::[])
in (t1)::uu____4102)
in ((BvMod), (uu____4099)))
in (mkApp' uu____4092 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4127 r -> (match (uu____4127) with
| (t1, t2) -> begin
(

let uu____4136 = (

let uu____4143 = (

let uu____4146 = (

let uu____4149 = (mkNatToBv sz t2 r)
in (uu____4149)::[])
in (t1)::uu____4146)
in ((BvMul), (uu____4143)))
in (mkApp' uu____4136 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____4211 r -> (match (uu____4211) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____4230 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____4457 r -> (match (uu____4457) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____4468) -> begin
t2
end
| App (FalseOp, uu____4473) -> begin
t3
end
| uu____4478 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____4479), App (TrueOp, uu____4480)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____4489), uu____4490) -> begin
(

let uu____4495 = (

let uu____4500 = (mkNot t1 t1.rng)
in ((uu____4500), (t3)))
in (mkImp uu____4495 r))
end
| (uu____4501, App (TrueOp, uu____4502)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____4507, uu____4508) -> begin
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
| Integer (uu____4564) -> begin
FStar_Pervasives_Native.None
end
| BoundV (uu____4566) -> begin
FStar_Pervasives_Native.None
end
| FreeV (uu____4568) -> begin
FStar_Pervasives_Native.None
end
| Let (tms, tm) -> begin
(aux_l ((tm)::tms))
end
| App (head1, terms) -> begin
(

let head_ok = (match (head1) with
| Var (uu____4589) -> begin
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
| BvUext (uu____4621) -> begin
false
end
| NatToBv (uu____4624) -> begin
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
| uu____4632 -> begin
(aux_l terms)
end))
end
| Labeled (t2, uu____4635, uu____4636) -> begin
(aux t2)
end
| Quant (uu____4639) -> begin
FStar_Pervasives_Native.Some (t1)
end
| LblPos (uu____4664) -> begin
FStar_Pervasives_Native.Some (t1)
end))
and aux_l = (fun ts -> (match (ts) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (t1)::ts1 -> begin
(

let uu____4679 = (aux t1)
in (match (uu____4679) with
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

let uu____4714 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____4714))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____4731 = (op_to_string op)
in (

let uu____4733 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____4731 uu____4733)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____4741 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____4741))
end
| LblPos (t1, s) -> begin
(

let uu____4748 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____4748))
end
| Quant (qop, l, uu____4753, uu____4754, t1, uu____4756) -> begin
(

let uu____4781 = (print_smt_term_list_list l)
in (

let uu____4783 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4781 uu____4783)))
end
| Let (es, body) -> begin
(

let uu____4792 = (print_smt_term_list es)
in (

let uu____4794 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____4792 uu____4794)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____4801 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____4801 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____4828 = (

let uu____4830 = (

let uu____4832 = (print_smt_term_list l1)
in (Prims.strcat uu____4832 " ] "))
in (Prims.strcat "; [ " uu____4830))
in (Prims.strcat s uu____4828))) "" l))


let mkQuantQid : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string FStar_Syntax_Syntax.memo)  ->  term = (fun r check_pats uu____4877 -> (match (uu____4877) with
| (qop, pats, wopt, vars, body, qid) -> begin
(

let all_pats_ok = (fun pats1 -> (match ((not (check_pats))) with
| true -> begin
pats1
end
| uu____4956 -> begin
(

let uu____4958 = (FStar_Util.find_map pats1 (fun x -> (FStar_Util.find_map x check_pattern_ok)))
in (match (uu____4958) with
| FStar_Pervasives_Native.None -> begin
pats1
end
| FStar_Pervasives_Native.Some (p) -> begin
((

let uu____4973 = (

let uu____4979 = (

let uu____4981 = (print_smt_term p)
in (FStar_Util.format1 "Pattern (%s) contains illegal symbols; dropping it" uu____4981))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____4979)))
in (FStar_Errors.log_issue r uu____4973));
[];
)
end))
end))
in (match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____4990 -> begin
(match (body.tm) with
| App (TrueOp, uu____4992) -> begin
body
end
| uu____4997 -> begin
(

let uu____4998 = (

let uu____4999 = (

let uu____5024 = (all_pats_ok pats)
in ((qop), (uu____5024), (wopt), (vars), (body), (qid)))
in Quant (uu____4999))
in (mk uu____4998 r))
end)
end))
end))


let mkQuant : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r check_pats uu____5098 -> (match (uu____5098) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5142 = (

let uu____5167 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((qop), (pats), (wopt), (vars), (body), (uu____5167)))
in (mkQuantQid r check_pats uu____5142))
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____5224 r -> (match (uu____5224) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____5241 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of1 = (fun fv -> (

let uu____5274 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____5274) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____5301 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____5301) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____5360 -> begin
(match (t1.tm) with
| Integer (uu____5370) -> begin
t1
end
| BoundV (uu____5372) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____5380 = (index_of1 x)
in (match (uu____5380) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____5394 = (

let uu____5401 = (FStar_List.map (aux ix) tms)
in ((op), (uu____5401)))
in (mkApp' uu____5394 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5411 = (

let uu____5412 = (

let uu____5420 = (aux ix t2)
in ((uu____5420), (r1), (r2)))
in Labeled (uu____5412))
in (mk uu____5411 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5426 = (

let uu____5427 = (

let uu____5433 = (aux ix t2)
in ((uu____5433), (r)))
in LblPos (uu____5427))
in (mk uu____5426 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, uu____5440) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____5466 = (

let uu____5486 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____5507 = (aux (ix + n1) body)
in ((qop), (uu____5486), (wopt), (vars), (uu____5507))))
in (mkQuant t1.rng false uu____5466)))
end
| Let (es, body) -> begin
(

let uu____5528 = (FStar_List.fold_left (fun uu____5548 e -> (match (uu____5548) with
| (ix1, l) -> begin
(

let uu____5572 = (

let uu____5575 = (aux ix1 e)
in (uu____5575)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____5572)))
end)) ((ix), ([])) es)
in (match (uu____5528) with
| (ix1, es_rev) -> begin
(

let uu____5591 = uu____5528
in (

let uu____5599 = (

let uu____5606 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____5606)))
in (mkLet uu____5599 t1.rng)))
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
| Integer (uu____5643) -> begin
t1
end
| FreeV (uu____5645) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____5655 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____5663 = (

let uu____5670 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____5670)))
in (mkApp' uu____5663 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5680 = (

let uu____5681 = (

let uu____5689 = (aux shift t2)
in ((uu____5689), (r1), (r2)))
in Labeled (uu____5681))
in (mk uu____5680 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5695 = (

let uu____5696 = (

let uu____5702 = (aux shift t2)
in ((uu____5702), (r)))
in LblPos (uu____5696))
in (mk uu____5695 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, qid) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____5741 = (

let uu____5766 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____5783 = (aux shift1 body)
in ((qop), (uu____5766), (wopt), (vars), (uu____5783), (qid))))
in (mkQuantQid t1.rng false uu____5741))))
end
| Let (es, body) -> begin
(

let uu____5825 = (FStar_List.fold_left (fun uu____5845 e -> (match (uu____5845) with
| (ix, es1) -> begin
(

let uu____5869 = (

let uu____5872 = (aux shift e)
in (uu____5872)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____5869)))
end)) ((shift), ([])) es)
in (match (uu____5825) with
| (shift1, es_rev) -> begin
(

let uu____5888 = (

let uu____5895 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____5895)))
in (mkLet uu____5888 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____5915 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____5915)))


let mkQuant' : FStar_Range.range  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  term = (fun r uu____5945 -> (match (uu____5945) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5988 = (

let uu____6008 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____6025 = (FStar_List.map fv_sort vars)
in (

let uu____6029 = (abstr vars body)
in ((qop), (uu____6008), (wopt), (uu____6025), (uu____6029)))))
in (mkQuant r true uu____5988))
end))


let mkForall : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6060 -> (match (uu____6060) with
| (pats, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkForall'' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r uu____6125 -> (match (uu____6125) with
| (pats, wopt, sorts, body) -> begin
(mkQuant r true ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  term = (fun r uu____6200 -> (match (uu____6200) with
| (pats, wopt, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkExists : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6269 -> (match (uu____6269) with
| (pats, vars, body) -> begin
(mkQuant' r ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____6326 r -> (match (uu____6326) with
| (bindings, body) -> begin
(

let uu____6352 = (FStar_List.split bindings)
in (match (uu____6352) with
| (vars, es) -> begin
(

let uu____6371 = (

let uu____6378 = (abstr vars body)
in ((es), (uu____6378)))
in (mkLet uu____6371 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let prrng : FStar_Range.range = FStar_Range.preludeRange


let mkDefineFun : (Prims.string * fv Prims.list * sort * term * caption)  ->  decl = (fun uu____6401 -> (match (uu____6401) with
| (nm, vars, s, tm, c) -> begin
(

let uu____6426 = (

let uu____6440 = (FStar_List.map fv_sort vars)
in (

let uu____6444 = (abstr vars tm)
in ((nm), (uu____6440), (s), (uu____6444), (c))))
in DefineFun (uu____6426))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____6456 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____6456)))


let fresh_token : FStar_Range.range  ->  (Prims.string * sort)  ->  Prims.int  ->  decl = (fun rng uu____6479 id1 -> (match (uu____6479) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____6495 = (

let uu____6496 = (

let uu____6501 = (mkInteger' id1 rng)
in (

let uu____6502 = (

let uu____6503 = (

let uu____6511 = (constr_id_of_sort sort)
in (

let uu____6513 = (

let uu____6516 = (mkApp ((tok_name), ([])) rng)
in (uu____6516)::[])
in ((uu____6511), (uu____6513))))
in (mkApp uu____6503 rng))
in ((uu____6501), (uu____6502))))
in (mkEq uu____6496 rng))
in (

let uu____6523 = (escape a_name)
in {assumption_term = uu____6495; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = uu____6523; assumption_fact_ids = []}))
in Assume (a)))
end))


let fresh_constructor : FStar_Range.range  ->  (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun rng uu____6549 -> (match (uu____6549) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____6589 = (

let uu____6595 = (

let uu____6597 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6597))
in ((uu____6595), (s)))
in (mkFreeV uu____6589 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____6619 = (

let uu____6627 = (constr_id_of_sort sort)
in ((uu____6627), ((capp)::[])))
in (mkApp uu____6619 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____6636 = (

let uu____6637 = (

let uu____6648 = (

let uu____6649 = (

let uu____6654 = (mkInteger id2 norng)
in ((uu____6654), (cid_app)))
in (mkEq uu____6649 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6648)))
in (mkForall rng uu____6637))
in (

let uu____6663 = (escape a_name)
in {assumption_term = uu____6636; assumption_caption = FStar_Pervasives_Native.Some ("Constructor distinct"); assumption_name = uu____6663; assumption_fact_ids = []}))
in Assume (a))))))))
end))


let injective_constructor : FStar_Range.range  ->  (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun rng uu____6686 -> (match (uu____6686) with
| (name, fields, st) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____6718 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6718)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____6757 = (

let uu____6763 = (bvar_name i)
in ((uu____6763), (s)))
in (mkFreeV uu____6757)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6796 -> (match (uu____6796) with
| (uu____6806, s, uu____6808) -> begin
(

let uu____6813 = (bvar i s)
in (uu____6813 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____6835 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6873 -> (match (uu____6873) with
| (iname, isort, projectible) -> begin
(

let cproj_app = (mkApp ((iname), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((iname), ((st)::[]), (isort), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____6906 = (

let uu____6907 = (

let uu____6918 = (

let uu____6919 = (

let uu____6924 = (

let uu____6925 = (bvar i isort)
in (uu____6925 norng))
in ((cproj_app), (uu____6924)))
in (mkEq uu____6919 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6918)))
in (mkForall rng uu____6907))
in (

let uu____6938 = (escape (Prims.strcat "projection_inverse_" iname))
in {assumption_term = uu____6906; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = uu____6938; assumption_fact_ids = []}))
in (proj_name)::(Assume (a))::[])
end
| uu____6943 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____6835 FStar_List.flatten)))))))))
end))


let constructor_to_decl : FStar_Range.range  ->  constructor_t  ->  decls_t = (fun rng uu____6961 -> (match (uu____6961) with
| (name, fields, st, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7024 -> (match (uu____7024) with
| (uu____7033, sort, uu____7035) -> begin
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

let uu____7060 = (

let uu____7065 = (

let uu____7066 = (

let uu____7074 = (constr_id_of_sort st)
in ((uu____7074), ((xx)::[])))
in (mkApp uu____7066 norng))
in (

let uu____7079 = (

let uu____7080 = (FStar_Util.string_of_int id1)
in (mkInteger uu____7080 norng))
in ((uu____7065), (uu____7079))))
in (mkEq uu____7060 norng))
in (

let uu____7082 = (

let uu____7093 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7146 -> (match (uu____7146) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____7186 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____7186), ([])))
end
| uu____7202 -> begin
(

let fi = (

let uu____7210 = (

let uu____7212 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____7212))
in ((uu____7210), (s)))
in (

let uu____7216 = (mkFreeV fi norng)
in ((uu____7216), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____7093 FStar_List.split))
in (match (uu____7082) with
| (proj_terms, ex_vars) -> begin
(

let uu____7268 = uu____7082
in (

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____7283 = (

let uu____7288 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____7288)))
in (mkEq uu____7283 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____7293 -> begin
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
| uu____7318 -> begin
[]
end)
in (

let uu____7320 = (

let uu____7323 = (

let uu____7324 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____7324))
in (uu____7323)::(cdecl)::(cid)::projs)
in (

let uu____7327 = (

let uu____7330 = (

let uu____7333 = (

let uu____7334 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____7334))
in (uu____7333)::[])
in (FStar_List.append ((disc)::[]) uu____7330))
in (FStar_List.append uu____7320 uu____7327)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____7418 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____7482 s -> (match (uu____7482) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____7547 -> begin
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

let uu____7558 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____7558))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____7576 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____7576))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____7418) with
| (names1, binders, n1) -> begin
(

let uu____7646 = uu____7418
in ((names1), ((FStar_List.rev binders)), (n1)))
end)))


let name_macro_binders : sort Prims.list  ->  (fv Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____7704 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____7704) with
| (names1, binders, n1) -> begin
(

let uu____7764 = uu____7704
in (((FStar_List.rev names1)), (binders)))
end)))


let termToSmt : Prims.bool  ->  Prims.string  ->  term  ->  Prims.string = (fun print_ranges enclosing_name t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____7860); freevars = uu____7861; rng = uu____7862})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____7880 -> begin
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

let uu____7957 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____7957 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____7986 = (op_to_string op)
in (

let uu____7988 = (

let uu____7990 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____7990 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____7986 uu____7988)))
end
| Labeled (t2, uu____8002, uu____8003) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____8010 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____8010 s))
end
| Quant (qop, pats, wopt, sorts, body, qid) -> begin
(

let qidstr = (

let uu____8045 = (FStar_ST.op_Bang qid)
in (match (uu____8045) with
| FStar_Pervasives_Native.None -> begin
"no-qid"
end
| FStar_Pervasives_Native.Some (str) -> begin
str
end))
in (

let uu____8102 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____8102) with
| (names2, binders, n2) -> begin
(

let uu____8132 = uu____8102
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
| uu____8168 -> begin
(

let uu____8173 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____8192 = (

let uu____8194 = (FStar_List.map (fun p -> (

let uu____8202 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____8202))) pats2)
in (FStar_String.concat " " uu____8194))
in (FStar_Util.format1 "\n:pattern (%s)" uu____8192)))))
in (FStar_All.pipe_right uu____8173 (FStar_String.concat "\n")))
end)
in (

let res = (

let uu____8214 = (

let uu____8218 = (

let uu____8222 = (

let uu____8226 = (aux1 n2 names2 body)
in (

let uu____8228 = (

let uu____8232 = (weightToSmt wopt)
in (uu____8232)::(pats_str)::(qidstr)::[])
in (uu____8226)::uu____8228))
in (binders1)::uu____8222)
in ((qop_to_string qop))::uu____8218)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____8214))
in ((

let uu____8243 = (

let uu____8245 = (

let uu____8247 = (FStar_ST.op_Bang qid)
in (FStar_Util.is_some uu____8247))
in (not (uu____8245)))
in (match (uu____8243) with
| true -> begin
(FStar_Util.print (Prims.strcat "Missing QID:\n" (Prims.strcat res "\n\n")) [])
end
| uu____8303 -> begin
()
end));
res;
))))))
end)))
end
| Let (es, body) -> begin
(

let uu____8311 = (FStar_List.fold_left (fun uu____8344 e -> (match (uu____8344) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____8387 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____8387))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____8396 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____8396))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____8311) with
| (names2, binders, n2) -> begin
(

let uu____8430 = uu____8311
in (

let uu____8443 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____8443)))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match (((print_ranges && (Prims.op_disEquality t1.rng norng)) && (Prims.op_disEquality t1.rng prrng))) with
| true -> begin
(

let uu____8460 = (FStar_Range.string_of_range t1.rng)
in (

let uu____8462 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____8460 uu____8462 s)))
end
| uu____8465 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.bool  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun print_captions uu___124_8491 -> (match (uu___124_8491) with
| FStar_Pervasives_Native.Some (c) when print_captions -> begin
(

let c1 = (

let uu____8501 = (FStar_All.pipe_right (FStar_String.split ((10)::[]) c) (FStar_List.map FStar_Util.trim_string))
in (FStar_All.pipe_right uu____8501 (FStar_String.concat " ")))
in (Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")))
end
| uu____8523 -> begin
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

let uu____8607 = (FStar_List.map (declToSmt' z3options print_captions) decls)
in (FStar_All.pipe_right uu____8607 (FStar_String.concat "\n")))
in (

let uu____8617 = (FStar_Options.keep_query_captions ())
in (match (uu____8617) with
| true -> begin
(

let uu____8621 = (FStar_Util.string_of_int (FStar_List.length decls))
in (

let uu____8623 = (FStar_Util.string_of_int (FStar_String.length res))
in (FStar_Util.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)" s res s uu____8621 uu____8623)))
end
| uu____8626 -> begin
res
end)))
end
| Caption (c) -> begin
(match (print_captions) with
| true -> begin
(

let uu____8632 = (

let uu____8634 = (FStar_All.pipe_right (FStar_Util.splitlines c) (FStar_List.map (fun s -> (Prims.strcat "; " (Prims.strcat s "\n")))))
in (FStar_All.pipe_right uu____8634 (FStar_String.concat "")))
in (Prims.strcat "\n" uu____8632))
end
| uu____8657 -> begin
""
end)
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____8675 = (

let uu____8677 = (caption_to_string print_captions)
in (uu____8677 c))
in (

let uu____8686 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8675 f (FStar_String.concat " " l) uu____8686))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____8701 = (name_macro_binders arg_sorts)
in (match (uu____8701) with
| (names1, binders) -> begin
(

let uu____8724 = uu____8701
in (

let body1 = (

let uu____8735 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____8735 body))
in (

let uu____8750 = (

let uu____8752 = (caption_to_string print_captions)
in (uu____8752 c))
in (

let uu____8761 = (strSort retsort)
in (

let uu____8763 = (

let uu____8765 = (escape f)
in (termToSmt print_captions uu____8765 body1))
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____8750 f (FStar_String.concat " " binders) uu____8761 uu____8763))))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___125_8795 -> (match (uu___125_8795) with
| Name (n1) -> begin
(

let uu____8798 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____8798))
end
| Namespace (ns) -> begin
(

let uu____8802 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____8802))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (match (print_captions) with
| true -> begin
(

let uu____8812 = (

let uu____8814 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____8814))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8812))
end
| uu____8820 -> begin
""
end)
in (

let n1 = a.assumption_name
in (

let uu____8825 = (

let uu____8827 = (caption_to_string print_captions)
in (uu____8827 a.assumption_caption))
in (

let uu____8836 = (termToSmt print_captions n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8825 fids uu____8836 n1))))))
end
| Eval (t) -> begin
(

let uu____8840 = (termToSmt print_captions "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____8840))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____8847) -> begin
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

let uu____8870 = (FStar_Options.keep_query_captions ())
in (declToSmt' z3options uu____8870 decl)))
and declToSmt_no_caps : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' z3options false decl))
and declsToSmt : Prims.string  ->  decl Prims.list  ->  Prims.string = (fun z3options decls -> (

let uu____8883 = (FStar_List.map (declToSmt z3options) decls)
in (FStar_All.pipe_right uu____8883 (FStar_String.concat "\n"))))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____9004 = (

let uu____9008 = (FStar_All.pipe_right constrs (FStar_List.collect (constructor_to_decl norng)))
in (FStar_All.pipe_right uu____9008 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____9004 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let preludeDecls : decl Prims.list = (

let uu____9034 = (((("x"), (Term_sort))), ((("y"), (Term_sort))), ((("t"), (Term_sort))))
in (match (uu____9034) with
| (tmvarx, tmvary, tmvart) -> begin
(

let bovarb = (("b"), (Bool_sort))
in (

let flvarf = (("f"), (Fuel_sort))
in (

let uu____9128 = (((("t1"), (Term_sort))), ((("t2"), (Term_sort))), ((("x1"), (Term_sort))), ((("x2"), (Term_sort))), ((("y1"), (Term_sort))), ((("y2"), (Term_sort))))
in (match (uu____9128) with
| (t1, t2, x1, x2, y1, y2) -> begin
(

let uu____9281 = (((("x"), (Int_sort))), ((("y"), (Int_sort))))
in (match (uu____9281) with
| (intvarx, intvary) -> begin
(

let hastypez = (

let uu____9335 = (

let uu____9336 = (

let uu____9344 = (

let uu____9347 = (mkApp (("ZFuel"), ([])) prrng)
in (

let uu____9352 = (

let uu____9355 = (mkFreeV tmvarx prrng)
in (

let uu____9356 = (

let uu____9359 = (mkFreeV tmvart prrng)
in (uu____9359)::[])
in (uu____9355)::uu____9356))
in (uu____9347)::uu____9352))
in (("HasTypeFuel"), (uu____9344)))
in (mkApp uu____9336 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9335))
in (

let hastype = (

let uu____9365 = (

let uu____9366 = (

let uu____9374 = (

let uu____9377 = (mkApp (("MaxIFuel"), ([])) prrng)
in (

let uu____9382 = (

let uu____9385 = (mkFreeV tmvarx prrng)
in (

let uu____9386 = (

let uu____9389 = (mkFreeV tmvart prrng)
in (uu____9389)::[])
in (uu____9385)::uu____9386))
in (uu____9377)::uu____9382))
in (("HasTypeFuel"), (uu____9374)))
in (mkApp uu____9366 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9365))
in (

let fuelirrelevance_pat = (

let uu____9395 = (

let uu____9403 = (

let uu____9406 = (

let uu____9407 = (

let uu____9415 = (

let uu____9418 = (mkFreeV flvarf prrng)
in (uu____9418)::[])
in (("SFuel"), (uu____9415)))
in (mkApp uu____9407 prrng))
in (

let uu____9423 = (

let uu____9426 = (mkFreeV tmvarx prrng)
in (

let uu____9427 = (

let uu____9430 = (mkFreeV tmvart prrng)
in (uu____9430)::[])
in (uu____9426)::uu____9427))
in (uu____9406)::uu____9423))
in (("HasTypeFuel"), (uu____9403)))
in (mkApp uu____9395 prrng))
in (

let fuelirrelevance = (

let uu____9436 = (

let uu____9447 = (

let uu____9448 = (

let uu____9453 = (

let uu____9454 = (

let uu____9462 = (

let uu____9465 = (mkFreeV tmvarx prrng)
in (

let uu____9466 = (

let uu____9469 = (mkFreeV tmvart prrng)
in (uu____9469)::[])
in (uu____9465)::uu____9466))
in (("HasTypeZ"), (uu____9462)))
in (mkApp uu____9454 prrng))
in ((fuelirrelevance_pat), (uu____9453)))
in (mkEq uu____9448 prrng))
in ((((fuelirrelevance_pat)::[])::[]), ((flvarf)::(tmvarx)::(tmvart)::[]), (uu____9447)))
in (mkForall prrng uu____9436))
in (

let nohoist_pat = (

let uu____9503 = (

let uu____9511 = (

let uu____9514 = (mkFreeV tmvart prrng)
in (

let uu____9515 = (

let uu____9518 = (mkFreeV bovarb prrng)
in (uu____9518)::[])
in (uu____9514)::uu____9515))
in (("NoHoist"), (uu____9511)))
in (mkApp uu____9503 prrng))
in (

let nohoist = (

let uu____9524 = (

let uu____9535 = (

let uu____9536 = (

let uu____9541 = (mkFreeV bovarb prrng)
in ((nohoist_pat), (uu____9541)))
in (mkEq uu____9536 prrng))
in ((((nohoist_pat)::[])::[]), ((tmvart)::(bovarb)::[]), (uu____9535)))
in (mkForall prrng uu____9524))
in (

let istyped = (

let uu____9566 = (

let uu____9567 = (

let uu____9578 = (

let uu____9579 = (

let uu____9587 = (

let uu____9590 = (mkFreeV tmvarx prrng)
in (

let uu____9591 = (

let uu____9594 = (mkFreeV tmvart prrng)
in (uu____9594)::[])
in (uu____9590)::uu____9591))
in (("HasTypeZ"), (uu____9587)))
in (mkApp uu____9579 prrng))
in (([]), ((tmvart)::[]), (uu____9578)))
in (mkExists prrng uu____9567))
in (abstr ((tmvarx)::[]) uu____9566))
in (

let validity_pat = (

let uu____9616 = (

let uu____9624 = (

let uu____9627 = (mkFreeV tmvart prrng)
in (uu____9627)::[])
in (("Valid"), (uu____9624)))
in (mkApp uu____9616 prrng))
in (

let validity = (

let uu____9633 = (

let uu____9644 = (

let uu____9645 = (

let uu____9650 = (

let uu____9651 = (

let uu____9662 = (

let uu____9663 = (

let uu____9671 = (

let uu____9674 = (mkFreeV tmvarx prrng)
in (

let uu____9675 = (

let uu____9678 = (mkFreeV tmvart prrng)
in (uu____9678)::[])
in (uu____9674)::uu____9675))
in (("HasType"), (uu____9671)))
in (mkApp uu____9663 prrng))
in (([]), ((tmvarx)::[]), (uu____9662)))
in (mkExists prrng uu____9651))
in ((uu____9650), (validity_pat)))
in (mkIff uu____9645 prrng))
in ((((validity_pat)::[])::[]), ((tmvart)::[]), (uu____9644)))
in (mkForall prrng uu____9633))
in (

let operator_pat = (fun nm -> (

let uu____9725 = (

let uu____9733 = (

let uu____9736 = (mkFreeV intvarx prrng)
in (

let uu____9737 = (

let uu____9740 = (mkFreeV intvary prrng)
in (uu____9740)::[])
in (uu____9736)::uu____9737))
in ((nm), (uu____9733)))
in (mkApp uu____9725 prrng)))
in (

let operator = (fun nm sm -> (

let uu____9759 = (

let uu____9770 = (

let uu____9775 = (

let uu____9778 = (operator_pat nm)
in (uu____9778)::[])
in (uu____9775)::[])
in (

let uu____9783 = (

let uu____9784 = (

let uu____9789 = (operator_pat nm)
in (

let uu____9790 = (

let uu____9791 = (

let uu____9799 = (

let uu____9802 = (mkFreeV intvarx prrng)
in (

let uu____9803 = (

let uu____9806 = (mkFreeV intvary prrng)
in (uu____9806)::[])
in (uu____9802)::uu____9803))
in ((sm), (uu____9799)))
in (mkApp uu____9791 prrng))
in ((uu____9789), (uu____9790))))
in (mkEq uu____9784 prrng))
in ((uu____9770), ((intvarx)::(intvary)::[]), (uu____9783))))
in (mkForall prrng uu____9759)))
in (

let constrs = (FStar_All.pipe_right (((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]) (FStar_List.collect (constructor_to_decl prrng)))
in (

let isprims = (

let uu____9939 = (

let uu____9940 = (

let uu____9948 = (

let uu____9951 = (mkFreeV tmvart prrng)
in (uu____9951)::[])
in (("is-LexCons"), (uu____9948)))
in (mkApp uu____9940 prrng))
in (abstr ((tmvart)::[]) uu____9939))
in (

let precedes_lext = (fun tm1 tm2 -> (

let lext = (mkApp (("Prims.lex_t"), ([])) prrng)
in (mkApp (("Prims.precedes"), ((lext)::(lext)::(tm1)::(tm2)::[])) prrng)))
in (

let lexicographic = (

let uu____9977 = (

let uu____9988 = (

let uu____9989 = (

let uu____9994 = (

let uu____9995 = (

let uu____10003 = (

let uu____10006 = (

let uu____10007 = (

let uu____10008 = (

let uu____10016 = (

let uu____10019 = (mkFreeV t1 prrng)
in (

let uu____10020 = (

let uu____10023 = (mkFreeV x1 prrng)
in (

let uu____10024 = (

let uu____10027 = (mkFreeV x2 prrng)
in (uu____10027)::[])
in (uu____10023)::uu____10024))
in (uu____10019)::uu____10020))
in (("LexCons"), (uu____10016)))
in (mkApp uu____10008 prrng))
in (

let uu____10032 = (

let uu____10033 = (

let uu____10041 = (

let uu____10044 = (mkFreeV t2 prrng)
in (

let uu____10045 = (

let uu____10048 = (mkFreeV y1 prrng)
in (

let uu____10049 = (

let uu____10052 = (mkFreeV y2 prrng)
in (uu____10052)::[])
in (uu____10048)::uu____10049))
in (uu____10044)::uu____10045))
in (("LexCons"), (uu____10041)))
in (mkApp uu____10033 prrng))
in (precedes_lext uu____10007 uu____10032)))
in (uu____10006)::[])
in (("Valid"), (uu____10003)))
in (mkApp uu____9995 prrng))
in (

let uu____10061 = (

let uu____10062 = (

let uu____10067 = (

let uu____10068 = (

let uu____10076 = (

let uu____10079 = (

let uu____10080 = (

let uu____10088 = (

let uu____10091 = (mkFreeV t1 prrng)
in (

let uu____10092 = (

let uu____10095 = (mkFreeV t2 prrng)
in (

let uu____10096 = (

let uu____10099 = (mkFreeV x1 prrng)
in (

let uu____10100 = (

let uu____10103 = (mkFreeV y1 prrng)
in (uu____10103)::[])
in (uu____10099)::uu____10100))
in (uu____10095)::uu____10096))
in (uu____10091)::uu____10092))
in (("Prims.precedes"), (uu____10088)))
in (mkApp uu____10080 prrng))
in (uu____10079)::[])
in (("Valid"), (uu____10076)))
in (mkApp uu____10068 prrng))
in (

let uu____10112 = (

let uu____10113 = (

let uu____10118 = (

let uu____10119 = (

let uu____10124 = (mkFreeV x1 prrng)
in (

let uu____10125 = (mkFreeV y1 prrng)
in ((uu____10124), (uu____10125))))
in (mkEq uu____10119 prrng))
in (

let uu____10126 = (

let uu____10127 = (

let uu____10135 = (

let uu____10138 = (

let uu____10139 = (mkFreeV x2 prrng)
in (

let uu____10140 = (mkFreeV y2 prrng)
in (precedes_lext uu____10139 uu____10140)))
in (uu____10138)::[])
in (("Valid"), (uu____10135)))
in (mkApp uu____10127 prrng))
in ((uu____10118), (uu____10126))))
in (mkAnd uu____10113 prrng))
in ((uu____10067), (uu____10112))))
in (mkOr uu____10062 prrng))
in ((uu____9994), (uu____10061))))
in (mkIff uu____9989 prrng))
in (([]), ((t1)::(t2)::(x1)::(x2)::(y1)::(y2)::[]), (uu____9988)))
in (mkForall prrng uu____9977))
in (

let precedes_pat = (

let uu____10187 = (

let uu____10195 = (

let uu____10198 = (mkFreeV t1 prrng)
in (

let uu____10199 = (

let uu____10202 = (mkFreeV t2 prrng)
in (

let uu____10203 = (

let uu____10206 = (mkFreeV x1 prrng)
in (

let uu____10207 = (

let uu____10210 = (mkFreeV x2 prrng)
in (uu____10210)::[])
in (uu____10206)::uu____10207))
in (uu____10202)::uu____10203))
in (uu____10198)::uu____10199))
in (("Prims.precedes"), (uu____10195)))
in (mkApp uu____10187 prrng))
in (

let precedes = (

let uu____10216 = (

let uu____10227 = (

let uu____10228 = (

let uu____10233 = (mkApp (("Valid"), ((precedes_pat)::[])) prrng)
in (

let uu____10238 = (

let uu____10239 = (

let uu____10247 = (

let uu____10250 = (

let uu____10251 = (mkFreeV x1 prrng)
in (

let uu____10252 = (mkFreeV x2 prrng)
in (precedes_lext uu____10251 uu____10252)))
in (uu____10250)::[])
in (("Valid"), (uu____10247)))
in (mkApp uu____10239 prrng))
in ((uu____10233), (uu____10238))))
in (mkIff uu____10228 prrng))
in ((((precedes_pat)::[])::[]), ((t1)::(t2)::(x1)::(x2)::[]), (uu____10227)))
in (mkForall prrng uu____10216))
in (

let rank_pat = (

let uu____10291 = (mkFreeV t1 prrng)
in (

let uu____10292 = (mkFreeV t2 prrng)
in (precedes_lext uu____10291 uu____10292)))
in (

let rank = (

let uu____10294 = (

let uu____10305 = (

let uu____10306 = (

let uu____10311 = (mkApp (("Valid"), ((rank_pat)::[])) prrng)
in (

let uu____10316 = (

let uu____10317 = (

let uu____10322 = (

let uu____10323 = (

let uu____10331 = (

let uu____10334 = (mkFreeV t1 prrng)
in (uu____10334)::[])
in (("Rank"), (uu____10331)))
in (mkApp uu____10323 prrng))
in (

let uu____10339 = (

let uu____10340 = (

let uu____10348 = (

let uu____10351 = (mkFreeV t2 prrng)
in (uu____10351)::[])
in (("Rank"), (uu____10348)))
in (mkApp uu____10340 prrng))
in ((uu____10322), (uu____10339))))
in (mkLT uu____10317 prrng))
in ((uu____10311), (uu____10316))))
in (mkIff uu____10306 prrng))
in ((((rank_pat)::[])::[]), ((t1)::(t2)::[]), (uu____10305)))
in (mkForall prrng uu____10294))
in (

let uu____10379 = (

let uu____10382 = (

let uu____10385 = (

let uu____10388 = (

let uu____10391 = (

let uu____10394 = (

let uu____10397 = (

let uu____10400 = (

let uu____10403 = (

let uu____10406 = (

let uu____10409 = (

let uu____10412 = (

let uu____10415 = (

let uu____10418 = (

let uu____10421 = (

let uu____10422 = (

let uu____10423 = (escape "fuel_irrelevance")
in {assumption_term = fuelirrelevance; assumption_caption = FStar_Pervasives_Native.Some ("Fuel irrelevance"); assumption_name = uu____10423; assumption_fact_ids = []})
in Assume (uu____10422))
in (

let uu____10428 = (

let uu____10431 = (

let uu____10434 = (

let uu____10435 = (

let uu____10436 = (escape "no_hoist")
in {assumption_term = nohoist; assumption_caption = FStar_Pervasives_Native.Some ("No-hoist"); assumption_name = uu____10436; assumption_fact_ids = []})
in Assume (uu____10435))
in (

let uu____10441 = (

let uu____10444 = (

let uu____10447 = (

let uu____10450 = (

let uu____10453 = (

let uu____10456 = (

let uu____10459 = (

let uu____10462 = (

let uu____10465 = (

let uu____10468 = (

let uu____10469 = (

let uu____10483 = (

let uu____10484 = (mkFreeV tmvarx prrng)
in (abstr ((tmvarx)::[]) uu____10484))
in (("Reify"), ((Term_sort)::[]), (Term_sort), (uu____10483), (FStar_Pervasives_Native.None)))
in DefineFun (uu____10469))
in (

let uu____10490 = (

let uu____10493 = (

let uu____10494 = (

let uu____10495 = (escape "validity")
in {assumption_term = validity; assumption_caption = FStar_Pervasives_Native.Some ("Validity"); assumption_name = uu____10495; assumption_fact_ids = []})
in Assume (uu____10494))
in (

let uu____10500 = (

let uu____10503 = (

let uu____10506 = (

let uu____10509 = (

let uu____10512 = (

let uu____10515 = (

let uu____10518 = (

let uu____10521 = (

let uu____10522 = (

let uu____10523 = (operator "_mul" "*")
in (

let uu____10526 = (escape "arithmetic_multiplication")
in {assumption_term = uu____10523; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic multiplication"); assumption_name = uu____10526; assumption_fact_ids = []}))
in Assume (uu____10522))
in (

let uu____10531 = (

let uu____10534 = (

let uu____10535 = (

let uu____10536 = (operator "_div" "div")
in (

let uu____10539 = (escape "arithmetic_division")
in {assumption_term = uu____10536; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic division"); assumption_name = uu____10539; assumption_fact_ids = []}))
in Assume (uu____10535))
in (

let uu____10544 = (

let uu____10547 = (

let uu____10548 = (

let uu____10549 = (operator "_mod" "mod")
in (

let uu____10552 = (escape "arithmetic_modulus")
in {assumption_term = uu____10549; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic modulus"); assumption_name = uu____10552; assumption_fact_ids = []}))
in Assume (uu____10548))
in (uu____10547)::[])
in (uu____10534)::uu____10544))
in (uu____10521)::uu____10531))
in (DeclFun ((("__uu__PartialApp"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10518)
in (DeclFun ((("_mod"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10515)
in (DeclFun ((("_div"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10512)
in (DeclFun ((("_mul"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10509)
in (DeclFun ((("Range_const"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10506)
in (DeclFun ((("Prims.precedes"), ((Term_sort)::(Term_sort)::(Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10503)
in (uu____10493)::uu____10500))
in (uu____10468)::uu____10490))
in (DeclFun ((("Tm_uvar"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10465)
in (DeclFun ((("ConsFuel"), ((Fuel_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10462)
in (DeclFun ((("ConsTerm"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10459)
in (DeclFun ((("Closure"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10456)
in (DeclFun ((("Rank"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10453)
in (DeclFun ((("ApplyTT"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10450)
in (DeclFun ((("ApplyTF"), ((Term_sort)::(Fuel_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10447)
in (DefineFun ((("IsTyped"), ((Term_sort)::[]), (Bool_sort), (istyped), (FStar_Pervasives_Native.None))))::uu____10444)
in (uu____10434)::uu____10441))
in (DeclFun ((("NoHoist"), ((Term_sort)::(Bool_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10431)
in (uu____10421)::uu____10428))
in (DefineFun ((("HasType"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastype), (FStar_Pervasives_Native.None))))::uu____10418)
in (DefineFun ((("HasTypeZ"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastypez), (FStar_Pervasives_Native.None))))::uu____10415)
in (DeclFun ((("HasTypeFuel"), ((Fuel_sort)::(Term_sort)::(Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10412)
in (DeclFun ((("Valid"), ((Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10409)
in (DeclFun ((("PreType"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10406)
in (DeclFun ((("MaxFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10403)
in (DeclFun ((("MaxIFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10400)
in (FuelDeclaration)::uu____10397)
in (DeclFun ((("Term_constr_id"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10394)
in (SortDeclaration ("Term"))::uu____10391)
in (DeclFun ((("FString_constr_id"), ((String_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10388)
in (SortDeclaration ("FString"))::uu____10385)
in (GenerateOptions)::uu____10382)
in (

let uu____10679 = (

let uu____10682 = (

let uu____10685 = (

let uu____10688 = (

let uu____10691 = (

let uu____10692 = (

let uu____10693 = (escape "lexicographic_ordering")
in {assumption_term = lexicographic; assumption_caption = FStar_Pervasives_Native.Some ("Lexicographic ordering"); assumption_name = uu____10693; assumption_fact_ids = []})
in Assume (uu____10692))
in (

let uu____10698 = (

let uu____10701 = (

let uu____10702 = (

let uu____10703 = (escape "precedes_ordering")
in {assumption_term = precedes; assumption_caption = FStar_Pervasives_Native.Some ("Precedes ordering"); assumption_name = uu____10703; assumption_fact_ids = []})
in Assume (uu____10702))
in (

let uu____10708 = (

let uu____10711 = (

let uu____10712 = (

let uu____10713 = (escape "rank_ordering")
in {assumption_term = rank; assumption_caption = FStar_Pervasives_Native.Some ("Rank ordering"); assumption_name = uu____10713; assumption_fact_ids = []})
in Assume (uu____10712))
in (uu____10711)::[])
in (uu____10701)::uu____10708))
in (uu____10691)::uu____10698))
in (DeclFun ((("Prims.lex_t"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10688)
in (DefineFun ((("is-Prims.LexCons"), ((Term_sort)::[]), (Bool_sort), (isprims), (FStar_Pervasives_Native.None))))::uu____10685)
in (FStar_List.append constrs uu____10682))
in (FStar_List.append uu____10379 uu____10679))))))))))))))))))))))
end))
end))))
end))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____10738 = (

let uu____10739 = (

let uu____10741 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____10741))
in (

let uu____10750 = (

let uu____10753 = (

let uu____10754 = (

let uu____10756 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____10756))
in ((uu____10754), (BitVec_sort (sz)), (true)))
in (uu____10753)::[])
in ((uu____10739), (uu____10750), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____10738 (constructor_to_decl norng))))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____10799 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____10824 = (

let uu____10826 = (FStar_ST.op_Bang __range_c)
in (uu____10826 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____10824));
(

let uu____10871 = (

let uu____10879 = (

let uu____10882 = (mkInteger' i norng)
in (uu____10882)::[])
in (("Range_const"), (uu____10879)))
in (mkApp uu____10871 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____10925 = (

let uu____10933 = (

let uu____10936 = (mkInteger' i norng)
in (uu____10936)::[])
in (("Tm_uvar"), (uu____10933)))
in (mkApp uu____10925 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____10979 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____11003 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____11003 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11078 = (

let uu____11080 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11080))
in (

let uu____11089 = (

let uu____11091 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11091))
in (elim_box true uu____11078 uu____11089 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11114 = (

let uu____11116 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11116))
in (

let uu____11125 = (

let uu____11127 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11127))
in (elim_box true uu____11114 uu____11125 t))))


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
| uu____11150 -> begin
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
| uu____11164 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____11190 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____11190))
end
| uu____11193 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____11195 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____11213)::(t1)::(t2)::[]); freevars = uu____11216; rng = uu____11217})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____11233)::(t1)::(t2)::[]); freevars = uu____11236; rng = uu____11237})::[]) -> begin
(

let uu____11253 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____11253 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11256; rng = uu____11257})::[]) -> begin
(

let uu____11273 = (

let uu____11278 = (unboxInt t1)
in (

let uu____11279 = (unboxInt t2)
in ((uu____11278), (uu____11279))))
in (mkLTE uu____11273 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____11282; rng = uu____11283})::[]) -> begin
(

let uu____11299 = (

let uu____11304 = (unboxInt t1)
in (

let uu____11305 = (unboxInt t2)
in ((uu____11304), (uu____11305))))
in (mkLT uu____11299 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11308; rng = uu____11309})::[]) -> begin
(

let uu____11325 = (

let uu____11330 = (unboxInt t1)
in (

let uu____11331 = (unboxInt t2)
in ((uu____11330), (uu____11331))))
in (mkGTE uu____11325 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____11334; rng = uu____11335})::[]) -> begin
(

let uu____11351 = (

let uu____11356 = (unboxInt t1)
in (

let uu____11357 = (unboxInt t2)
in ((uu____11356), (uu____11357))))
in (mkGT uu____11351 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____11360; rng = uu____11361})::[]) -> begin
(

let uu____11377 = (

let uu____11382 = (unboxBool t1)
in (

let uu____11383 = (unboxBool t2)
in ((uu____11382), (uu____11383))))
in (mkAnd uu____11377 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____11386; rng = uu____11387})::[]) -> begin
(

let uu____11403 = (

let uu____11408 = (unboxBool t1)
in (

let uu____11409 = (unboxBool t2)
in ((uu____11408), (uu____11409))))
in (mkOr uu____11403 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____11411; rng = uu____11412})::[]) -> begin
(

let uu____11428 = (unboxBool t1)
in (mkNot uu____11428 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11432; rng = uu____11433})::[]) when (

let uu____11449 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11449)) -> begin
(

let sz = (

let uu____11456 = (getBoxedInteger t0)
in (match (uu____11456) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11464 -> begin
(failwith "impossible")
end))
in (

let uu____11470 = (

let uu____11475 = (unboxBitVec sz t1)
in (

let uu____11476 = (unboxBitVec sz t2)
in ((uu____11475), (uu____11476))))
in (mkBvUlt uu____11470 t.rng)))
end
| App (Var ("Prims.equals"), (uu____11477)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11481; rng = uu____11482})::(uu____11483)::[]) when (

let uu____11499 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11499)) -> begin
(

let sz = (

let uu____11506 = (getBoxedInteger t0)
in (match (uu____11506) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11514 -> begin
(failwith "impossible")
end))
in (

let uu____11520 = (

let uu____11525 = (unboxBitVec sz t1)
in (

let uu____11526 = (unboxBitVec sz t2)
in ((uu____11525), (uu____11526))))
in (mkBvUlt uu____11520 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___126_11531 = (unboxBool t1)
in {tm = uu___126_11531.tm; freevars = uu___126_11531.freevars; rng = t.rng})
end
| uu____11532 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____11593 = (FStar_Options.unthrottle_inductives ())
in (match (uu____11593) with
| true -> begin
(mk_HasType v1 t)
end
| uu____11596 -> begin
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

let uu____11726 = (

let uu____11727 = (mkApp (("__uu__PartialApp"), ([])) t.rng)
in (mk_ApplyTT uu____11727 t t.rng))
in (FStar_All.pipe_right uu____11726 mk_Valid)))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____11745 = (

let uu____11753 = (

let uu____11756 = (mkInteger' i norng)
in (uu____11756)::[])
in (("FString_const"), (uu____11753)))
in (mkApp uu____11745 r)))


let mk_Precedes : term  ->  term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 x4 r -> (

let uu____11787 = (mkApp (("Prims.precedes"), ((x1)::(x2)::(x3)::(x4)::[])) r)
in (FStar_All.pipe_right uu____11787 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 r -> (mkApp (("LexCons"), ((x1)::(x2)::(x3)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____11832 -> begin
(

let uu____11834 = (

let uu____11842 = (

let uu____11845 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____11845)::[])
in (("SFuel"), (uu____11842)))
in (mkApp uu____11834 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____11893 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____11893))
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

let uu____11956 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____11956)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____11976 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____11976)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____11987 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____11987)))




