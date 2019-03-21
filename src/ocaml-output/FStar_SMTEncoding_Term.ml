
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


let uu___is_GenerateOptions : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GenerateOptions -> begin
true
end
| uu____1689 -> begin
false
end))


let uu___is_Hardcoded : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Hardcoded (_0) -> begin
true
end
| uu____1702 -> begin
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
| uu____1736 -> begin
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
| uu____1802 -> begin
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
| uu____1861 -> begin
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
| uu____1882 -> begin
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
| uu____1912 -> begin
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
| uu____1953 -> begin
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
| uu____1974 -> begin
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
| uu____2000 -> begin
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
| uu____2028 -> begin
false
end))


let uu___is_Pop : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____2039 -> begin
false
end))


let uu___is_CheckSat : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckSat -> begin
true
end
| uu____2050 -> begin
false
end))


let uu___is_GetUnsatCore : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetUnsatCore -> begin
true
end
| uu____2061 -> begin
false
end))


let uu___is_SetOption : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOption (_0) -> begin
true
end
| uu____2079 -> begin
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
| uu____2116 -> begin
false
end))


let uu___is_GetReasonUnknown : decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GetReasonUnknown -> begin
true
end
| uu____2127 -> begin
false
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> (Prims.op_Equality (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)))


let fv_sort : 'Auu____2162 'Auu____2163 . ('Auu____2162 * 'Auu____2163)  ->  'Auu____2163 = (fun x -> (FStar_Pervasives_Native.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x1), FreeV (y1)) -> begin
(fv_eq x1 y1)
end
| uu____2202 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun uu___119_2213 -> (match (uu___119_2213) with
| {tm = FreeV (x); freevars = uu____2215; rng = uu____2216} -> begin
(fv_sort x)
end
| uu____2232 -> begin
(failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun uu___120_2239 -> (match (uu___120_2239) with
| {tm = FreeV (fv); freevars = uu____2241; rng = uu____2242} -> begin
fv
end
| uu____2257 -> begin
(failwith "impossible")
end))


let rec freevars : term  ->  (Prims.string * sort) Prims.list = (fun t -> (match (t.tm) with
| Integer (uu____2279) -> begin
[]
end
| BoundV (uu____2286) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (uu____2309, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (uu____2320, uu____2321, uu____2322, uu____2323, t1, uu____2325) -> begin
(freevars t1)
end
| Labeled (t1, uu____2351, uu____2352) -> begin
(freevars t1)
end
| LblPos (t1, uu____2356) -> begin
(freevars t1)
end
| Let (es, body) -> begin
(FStar_List.collect freevars ((body)::es))
end))


let free_variables : term  ->  fvs = (fun t -> (

let uu____2376 = (FStar_ST.op_Bang t.freevars)
in (match (uu____2376) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
(

let fvs = (

let uu____2453 = (freevars t)
in (FStar_Util.remove_dups fv_eq uu____2453))
in ((FStar_ST.op_Colon_Equals t.freevars (FStar_Pervasives_Native.Some (fvs)));
fvs;
))
end)))


let rec assign_qids : decl  ->  unit = (fun d -> (

let in_terms = (fun nm t -> (

let set_qid = (fun qid n1 -> (

let uu____2584 = (FStar_ST.op_Bang qid)
in (match (uu____2584) with
| FStar_Pervasives_Native.Some (uu____2636) -> begin
n1
end
| FStar_Pervasives_Native.None -> begin
((

let uu____2641 = (

let uu____2645 = (

let uu____2647 = (

let uu____2649 = (FStar_Util.string_of_int n1)
in (Prims.strcat "." uu____2649))
in (Prims.strcat nm uu____2647))
in FStar_Pervasives_Native.Some (uu____2645))
in (FStar_ST.op_Colon_Equals qid uu____2641));
(n1 + (Prims.parse_int "1"));
)
end)))
in (

let rec aux = (fun n1 tx -> (match (tx.tm) with
| App (uu____2716, tms) -> begin
(FStar_List.fold_left aux n1 tms)
end
| Quant (uu____2723, uu____2724, uu____2725, uu____2726, scp, qid) -> begin
(

let nx = (set_qid qid n1)
in (aux nx scp))
end
| Let (tms, scp) -> begin
(

let nx = (FStar_List.fold_left aux n1 tms)
in (aux nx scp))
end
| Labeled (scp, uu____2798, uu____2799) -> begin
(aux n1 scp)
end
| LblPos (scp, uu____2803) -> begin
(aux n1 scp)
end
| uu____2806 -> begin
n1
end))
in (

let uu____2807 = (aux (Prims.parse_int "0") t)
in (FStar_All.pipe_right uu____2807 (fun a1 -> ()))))))
in (match (d) with
| DefineFun (nm, uu____2812, uu____2813, tm, uu____2815) -> begin
(in_terms (Prims.strcat "funqid_" nm) tm)
end
| Assume (a) -> begin
(in_terms a.assumption_name a.assumption_term)
end
| Module (uu____2824, ds) -> begin
(FStar_List.iter assign_qids ds)
end
| uu____2832 -> begin
()
end)))


let qop_to_string : qop  ->  Prims.string = (fun uu___121_2839 -> (match (uu___121_2839) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun uu___122_2849 -> (match (uu___122_2849) with
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

let uu____2884 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ zero_extend %s)" uu____2884))
end
| NatToBv (n1) -> begin
(

let uu____2889 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(_ int2bv %s)" uu____2889))
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___123_2903 -> (match (uu___123_2903) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i) -> begin
(

let uu____2913 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" uu____2913))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(

let uu____2933 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" uu____2933))
end
| FreeV (x) -> begin
(

let uu____2942 = (

let uu____2944 = (strSort (FStar_Pervasives_Native.snd x))
in (Prims.strcat ":" uu____2944))
in (Prims.strcat (FStar_Pervasives_Native.fst x) uu____2942))
end
| App (op, tms) -> begin
(

let uu____2955 = (

let uu____2957 = (op_to_string op)
in (

let uu____2959 = (

let uu____2961 = (

let uu____2963 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right uu____2963 (FStar_String.concat " ")))
in (Prims.strcat uu____2961 ")"))
in (Prims.strcat uu____2957 uu____2959)))
in (Prims.strcat "(" uu____2955))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____2980 = (hash_of_term t1)
in (

let uu____2982 = (

let uu____2984 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 uu____2984))
in (Prims.strcat uu____2980 uu____2982)))
end
| LblPos (t1, r) -> begin
(

let uu____2990 = (

let uu____2992 = (hash_of_term t1)
in (Prims.strcat uu____2992 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " uu____2990))
end
| Quant (qop, pats, wopt, sorts, body, uu____3002) -> begin
(

let uu____3027 = (

let uu____3029 = (

let uu____3031 = (

let uu____3033 = (

let uu____3035 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right uu____3035 (FStar_String.concat " ")))
in (

let uu____3045 = (

let uu____3047 = (

let uu____3049 = (hash_of_term body)
in (

let uu____3051 = (

let uu____3053 = (

let uu____3055 = (weightToSmt wopt)
in (

let uu____3057 = (

let uu____3059 = (

let uu____3061 = (

let uu____3063 = (FStar_All.pipe_right pats (FStar_List.map (fun pats1 -> (

let uu____3082 = (FStar_List.map hash_of_term pats1)
in (FStar_All.pipe_right uu____3082 (FStar_String.concat " "))))))
in (FStar_All.pipe_right uu____3063 (FStar_String.concat "; ")))
in (Prims.strcat uu____3061 "))"))
in (Prims.strcat " " uu____3059))
in (Prims.strcat uu____3055 uu____3057)))
in (Prims.strcat " " uu____3053))
in (Prims.strcat uu____3049 uu____3051)))
in (Prims.strcat ")(! " uu____3047))
in (Prims.strcat uu____3033 uu____3045)))
in (Prims.strcat " (" uu____3031))
in (Prims.strcat (qop_to_string qop) uu____3029))
in (Prims.strcat "(" uu____3027))
end
| Let (es, body) -> begin
(

let uu____3109 = (

let uu____3111 = (

let uu____3113 = (FStar_List.map hash_of_term es)
in (FStar_All.pipe_right uu____3113 (FStar_String.concat " ")))
in (

let uu____3123 = (

let uu____3125 = (

let uu____3127 = (hash_of_term body)
in (Prims.strcat uu____3127 ")"))
in (Prims.strcat ") " uu____3125))
in (Prims.strcat uu____3111 uu____3123)))
in (Prims.strcat "(let (" uu____3109))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mkBoxFunctions : Prims.string  ->  (Prims.string * Prims.string) = (fun s -> ((s), ((Prims.strcat s "_proj_0"))))


let boxIntFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxInt")


let boxBoolFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxBool")


let boxStringFun : (Prims.string * Prims.string) = (mkBoxFunctions "BoxString")


let boxBitVecFun : Prims.int  ->  (Prims.string * Prims.string) = (fun sz -> (

let uu____3219 = (

let uu____3221 = (FStar_Util.string_of_int sz)
in (Prims.strcat "BoxBitVec" uu____3221))
in (mkBoxFunctions uu____3219)))


let isInjective : Prims.string  ->  Prims.bool = (fun s -> (match (((FStar_String.length s) >= (Prims.parse_int "3"))) with
| true -> begin
((

let uu____3238 = (FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3"))
in (Prims.op_Equality uu____3238 "Box")) && (

let uu____3245 = (

let uu____3247 = (FStar_String.list_of_string s)
in (FStar_List.existsML (fun c -> (Prims.op_Equality c 46 (*.*))) uu____3247))
in (not (uu____3245))))
end
| uu____3257 -> begin
false
end))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (

let uu____3271 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {tm = t; freevars = uu____3271; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((TrueOp), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((FalseOp), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3348 = (

let uu____3349 = (FStar_Util.ensure_decimal i)
in Integer (uu____3349))
in (mk uu____3348 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____3364 = (FStar_Util.string_of_int i)
in (mkInteger uu____3364 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun uu____3434 r -> (match (uu____3434) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (TrueOp, uu____3464) -> begin
(mkFalse r)
end
| App (FalseOp, uu____3469) -> begin
(mkTrue r)
end
| uu____3474 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3490 r -> (match (uu____3490) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3498), uu____3499) -> begin
t2
end
| (uu____3504, App (TrueOp, uu____3505)) -> begin
t1
end
| (App (FalseOp, uu____3510), uu____3511) -> begin
(mkFalse r)
end
| (uu____3516, App (FalseOp, uu____3517)) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3534, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), uu____3543) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3550 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3570 r -> (match (uu____3570) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (TrueOp, uu____3578), uu____3579) -> begin
(mkTrue r)
end
| (uu____3584, App (TrueOp, uu____3585)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3590), uu____3591) -> begin
t2
end
| (uu____3596, App (FalseOp, uu____3597)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (uu____3614, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), uu____3623) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| uu____3630 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____3650 r -> (match (uu____3650) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (uu____3658, App (TrueOp, uu____3659)) -> begin
(mkTrue r)
end
| (App (FalseOp, uu____3664), uu____3665) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____3670), uu____3671) -> begin
t2
end
| (uu____3676, App (Imp, (t1')::(t2')::[])) -> begin
(

let uu____3681 = (

let uu____3688 = (

let uu____3691 = (mkAnd ((t1), (t1')) r)
in (uu____3691)::(t2')::[])
in ((Imp), (uu____3688)))
in (mkApp' uu____3681 r))
end
| uu____3694 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op uu____3719 r -> (match (uu____3719) with
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


let mkBvShl : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3929 r -> (match (uu____3929) with
| (t1, t2) -> begin
(

let uu____3938 = (

let uu____3945 = (

let uu____3948 = (

let uu____3951 = (mkNatToBv sz t2 r)
in (uu____3951)::[])
in (t1)::uu____3948)
in ((BvShl), (uu____3945)))
in (mkApp' uu____3938 r))
end))


let mkBvShr : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____3973 r -> (match (uu____3973) with
| (t1, t2) -> begin
(

let uu____3982 = (

let uu____3989 = (

let uu____3992 = (

let uu____3995 = (mkNatToBv sz t2 r)
in (uu____3995)::[])
in (t1)::uu____3992)
in ((BvShr), (uu____3989)))
in (mkApp' uu____3982 r))
end))


let mkBvUdiv : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4017 r -> (match (uu____4017) with
| (t1, t2) -> begin
(

let uu____4026 = (

let uu____4033 = (

let uu____4036 = (

let uu____4039 = (mkNatToBv sz t2 r)
in (uu____4039)::[])
in (t1)::uu____4036)
in ((BvUdiv), (uu____4033)))
in (mkApp' uu____4026 r))
end))


let mkBvMod : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4061 r -> (match (uu____4061) with
| (t1, t2) -> begin
(

let uu____4070 = (

let uu____4077 = (

let uu____4080 = (

let uu____4083 = (mkNatToBv sz t2 r)
in (uu____4083)::[])
in (t1)::uu____4080)
in ((BvMod), (uu____4077)))
in (mkApp' uu____4070 r))
end))


let mkBvMul : Prims.int  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun sz uu____4105 r -> (match (uu____4105) with
| (t1, t2) -> begin
(

let uu____4114 = (

let uu____4121 = (

let uu____4124 = (

let uu____4127 = (mkNatToBv sz t2 r)
in (uu____4127)::[])
in (t1)::uu____4124)
in ((BvMul), (uu____4121)))
in (mkApp' uu____4114 r))
end))


let mkBvUlt : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op BvUlt)


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (fun uu____4189 r -> (match (uu____4189) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (Var (f1), (s1)::[]), App (Var (f2), (s2)::[])) when ((Prims.op_Equality f1 f2) && (isInjective f1)) -> begin
(mk_bin_op Eq ((s1), (s2)) r)
end
| uu____4208 -> begin
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


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun uu____4435 r -> (match (uu____4435) with
| (t1, t2, t3) -> begin
(match (t1.tm) with
| App (TrueOp, uu____4446) -> begin
t2
end
| App (FalseOp, uu____4451) -> begin
t3
end
| uu____4456 -> begin
(match (((t2.tm), (t3.tm))) with
| (App (TrueOp, uu____4457), App (TrueOp, uu____4458)) -> begin
(mkTrue r)
end
| (App (TrueOp, uu____4467), uu____4468) -> begin
(

let uu____4473 = (

let uu____4478 = (mkNot t1 t1.rng)
in ((uu____4478), (t3)))
in (mkImp uu____4473 r))
end
| (uu____4479, App (TrueOp, uu____4480)) -> begin
(mkImp ((t1), (t2)) r)
end
| (uu____4485, uu____4486) -> begin
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
| Integer (uu____4542) -> begin
FStar_Pervasives_Native.None
end
| BoundV (uu____4544) -> begin
FStar_Pervasives_Native.None
end
| FreeV (uu____4546) -> begin
FStar_Pervasives_Native.None
end
| Let (tms, tm) -> begin
(aux_l ((tm)::tms))
end
| App (head1, terms) -> begin
(

let head_ok = (match (head1) with
| Var (uu____4567) -> begin
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
| BvUext (uu____4599) -> begin
false
end
| NatToBv (uu____4602) -> begin
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
| uu____4610 -> begin
(aux_l terms)
end))
end
| Labeled (t2, uu____4613, uu____4614) -> begin
(aux t2)
end
| Quant (uu____4617) -> begin
FStar_Pervasives_Native.Some (t1)
end
| LblPos (uu____4642) -> begin
FStar_Pervasives_Native.Some (t1)
end))
and aux_l = (fun ts -> (match (ts) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (t1)::ts1 -> begin
(

let uu____4657 = (aux t1)
in (match (uu____4657) with
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

let uu____4692 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "(BoundV %s)" uu____4692))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv))
end
| App (op, l) -> begin
(

let uu____4709 = (op_to_string op)
in (

let uu____4711 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" uu____4709 uu____4711)))
end
| Labeled (t1, r1, r2) -> begin
(

let uu____4719 = (print_smt_term t1)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 uu____4719))
end
| LblPos (t1, s) -> begin
(

let uu____4726 = (print_smt_term t1)
in (FStar_Util.format2 "(LblPos %s %s)" s uu____4726))
end
| Quant (qop, l, uu____4731, uu____4732, t1, uu____4734) -> begin
(

let uu____4759 = (print_smt_term_list_list l)
in (

let uu____4761 = (print_smt_term t1)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4759 uu____4761)))
end
| Let (es, body) -> begin
(

let uu____4770 = (print_smt_term_list es)
in (

let uu____4772 = (print_smt_term body)
in (FStar_Util.format2 "(let %s %s)" uu____4770 uu____4772)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (

let uu____4779 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right uu____4779 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l1 -> (

let uu____4806 = (

let uu____4808 = (

let uu____4810 = (print_smt_term_list l1)
in (Prims.strcat uu____4810 " ] "))
in (Prims.strcat "; [ " uu____4808))
in (Prims.strcat s uu____4806))) "" l))


let mkQuantQid : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string FStar_Syntax_Syntax.memo)  ->  term = (fun r check_pats uu____4855 -> (match (uu____4855) with
| (qop, pats, wopt, vars, body, qid) -> begin
(

let all_pats_ok = (fun pats1 -> (match ((not (check_pats))) with
| true -> begin
pats1
end
| uu____4934 -> begin
(

let uu____4936 = (FStar_Util.find_map pats1 (fun x -> (FStar_Util.find_map x check_pattern_ok)))
in (match (uu____4936) with
| FStar_Pervasives_Native.None -> begin
pats1
end
| FStar_Pervasives_Native.Some (p) -> begin
((

let uu____4951 = (

let uu____4957 = (

let uu____4959 = (print_smt_term p)
in (FStar_Util.format1 "Pattern (%s) contains illegal symbols; dropping it" uu____4959))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____4957)))
in (FStar_Errors.log_issue r uu____4951));
[];
)
end))
end))
in (match ((Prims.op_Equality (FStar_List.length vars) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____4968 -> begin
(match (body.tm) with
| App (TrueOp, uu____4970) -> begin
body
end
| uu____4975 -> begin
(

let uu____4976 = (

let uu____4977 = (

let uu____5002 = (all_pats_ok pats)
in ((qop), (uu____5002), (wopt), (vars), (body), (qid)))
in Quant (uu____4977))
in (mk uu____4976 r))
end)
end))
end))


let mkQuant : FStar_Range.range  ->  Prims.bool  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r check_pats uu____5076 -> (match (uu____5076) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5120 = (

let uu____5145 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((qop), (pats), (wopt), (vars), (body), (uu____5145)))
in (mkQuantQid r check_pats uu____5120))
end))


let mkLet : (term Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____5202 r -> (match (uu____5202) with
| (es, body) -> begin
(match ((Prims.op_Equality (FStar_List.length es) (Prims.parse_int "0"))) with
| true -> begin
body
end
| uu____5219 -> begin
(mk (Let (((es), (body)))) r)
end)
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of1 = (fun fv -> (

let uu____5252 = (FStar_Util.try_find_index (fv_eq fv) fvs)
in (match (uu____5252) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((nvars - (i + (Prims.parse_int "1"))))
end)))
in (

let rec aux = (fun ix t1 -> (

let uu____5279 = (FStar_ST.op_Bang t1.freevars)
in (match (uu____5279) with
| FStar_Pervasives_Native.Some ([]) -> begin
t1
end
| uu____5338 -> begin
(match (t1.tm) with
| Integer (uu____5348) -> begin
t1
end
| BoundV (uu____5350) -> begin
t1
end
| FreeV (x) -> begin
(

let uu____5358 = (index_of1 x)
in (match (uu____5358) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (i) -> begin
(mkBoundV (i + ix) t1.rng)
end))
end
| App (op, tms) -> begin
(

let uu____5372 = (

let uu____5379 = (FStar_List.map (aux ix) tms)
in ((op), (uu____5379)))
in (mkApp' uu____5372 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5389 = (

let uu____5390 = (

let uu____5398 = (aux ix t2)
in ((uu____5398), (r1), (r2)))
in Labeled (uu____5390))
in (mk uu____5389 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5404 = (

let uu____5405 = (

let uu____5411 = (aux ix t2)
in ((uu____5411), (r)))
in LblPos (uu____5405))
in (mk uu____5404 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, uu____5418) -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____5444 = (

let uu____5464 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n1)))))
in (

let uu____5485 = (aux (ix + n1) body)
in ((qop), (uu____5464), (wopt), (vars), (uu____5485))))
in (mkQuant t1.rng false uu____5444)))
end
| Let (es, body) -> begin
(

let uu____5506 = (FStar_List.fold_left (fun uu____5526 e -> (match (uu____5526) with
| (ix1, l) -> begin
(

let uu____5550 = (

let uu____5553 = (aux ix1 e)
in (uu____5553)::l)
in (((ix1 + (Prims.parse_int "1"))), (uu____5550)))
end)) ((ix), ([])) es)
in (match (uu____5506) with
| (ix1, es_rev) -> begin
(

let uu____5569 = uu____5506
in (

let uu____5577 = (

let uu____5584 = (aux ix1 body)
in (((FStar_List.rev es_rev)), (uu____5584)))
in (mkLet uu____5577 t1.rng)))
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
| Integer (uu____5621) -> begin
t1
end
| FreeV (uu____5623) -> begin
t1
end
| BoundV (i) -> begin
(match ((((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1))) with
| true -> begin
(FStar_List.nth tms1 (i - shift))
end
| uu____5633 -> begin
t1
end)
end
| App (op, tms2) -> begin
(

let uu____5641 = (

let uu____5648 = (FStar_List.map (aux shift) tms2)
in ((op), (uu____5648)))
in (mkApp' uu____5641 t1.rng))
end
| Labeled (t2, r1, r2) -> begin
(

let uu____5658 = (

let uu____5659 = (

let uu____5667 = (aux shift t2)
in ((uu____5667), (r1), (r2)))
in Labeled (uu____5659))
in (mk uu____5658 t2.rng))
end
| LblPos (t2, r) -> begin
(

let uu____5673 = (

let uu____5674 = (

let uu____5680 = (aux shift t2)
in ((uu____5680), (r)))
in LblPos (uu____5674))
in (mk uu____5673 t2.rng))
end
| Quant (qop, pats, wopt, vars, body, qid) -> begin
(

let m = (FStar_List.length vars)
in (

let shift1 = (shift + m)
in (

let uu____5719 = (

let uu____5744 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift1))))
in (

let uu____5761 = (aux shift1 body)
in ((qop), (uu____5744), (wopt), (vars), (uu____5761), (qid))))
in (mkQuantQid t1.rng false uu____5719))))
end
| Let (es, body) -> begin
(

let uu____5803 = (FStar_List.fold_left (fun uu____5823 e -> (match (uu____5823) with
| (ix, es1) -> begin
(

let uu____5847 = (

let uu____5850 = (aux shift e)
in (uu____5850)::es1)
in (((shift + (Prims.parse_int "1"))), (uu____5847)))
end)) ((shift), ([])) es)
in (match (uu____5803) with
| (shift1, es_rev) -> begin
(

let uu____5866 = (

let uu____5873 = (aux shift1 body)
in (((FStar_List.rev es_rev)), (uu____5873)))
in (mkLet uu____5866 t1.rng))
end))
end))
in (aux (Prims.parse_int "0") t)))))


let subst : term  ->  fv  ->  term  ->  term = (fun t fv s -> (

let uu____5893 = (abstr ((fv)::[]) t)
in (inst ((s)::[]) uu____5893)))


let mkQuant' : FStar_Range.range  ->  (qop * pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fv Prims.list * term)  ->  term = (fun r uu____5923 -> (match (uu____5923) with
| (qop, pats, wopt, vars, body) -> begin
(

let uu____5966 = (

let uu____5986 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (

let uu____6003 = (FStar_List.map fv_sort vars)
in (

let uu____6007 = (abstr vars body)
in ((qop), (uu____5986), (wopt), (uu____6003), (uu____6007)))))
in (mkQuant r true uu____5966))
end))


let mkForall : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6038 -> (match (uu____6038) with
| (pats, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkForall'' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * sort Prims.list * term)  ->  term = (fun r uu____6103 -> (match (uu____6103) with
| (pats, wopt, sorts, body) -> begin
(mkQuant r true ((Forall), (pats), (wopt), (sorts), (body)))
end))


let mkForall' : FStar_Range.range  ->  (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * fvs * term)  ->  term = (fun r uu____6178 -> (match (uu____6178) with
| (pats, wopt, vars, body) -> begin
(mkQuant' r ((Forall), (pats), (wopt), (vars), (body)))
end))


let mkExists : FStar_Range.range  ->  (pat Prims.list Prims.list * fvs * term)  ->  term = (fun r uu____6247 -> (match (uu____6247) with
| (pats, vars, body) -> begin
(mkQuant' r ((Exists), (pats), (FStar_Pervasives_Native.None), (vars), (body)))
end))


let mkLet' : ((fv * term) Prims.list * term)  ->  FStar_Range.range  ->  term = (fun uu____6304 r -> (match (uu____6304) with
| (bindings, body) -> begin
(

let uu____6330 = (FStar_List.split bindings)
in (match (uu____6330) with
| (vars, es) -> begin
(

let uu____6349 = (

let uu____6356 = (abstr vars body)
in ((es), (uu____6356)))
in (mkLet uu____6349 r))
end))
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let prrng : FStar_Range.range = FStar_Range.preludeRange


let mkDefineFun : (Prims.string * fv Prims.list * sort * term * caption)  ->  decl = (fun uu____6379 -> (match (uu____6379) with
| (nm, vars, s, tm, c) -> begin
(

let uu____6404 = (

let uu____6418 = (FStar_List.map fv_sort vars)
in (

let uu____6422 = (abstr vars tm)
in ((nm), (uu____6418), (s), (uu____6422), (c))))
in DefineFun (uu____6404))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (

let uu____6434 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" uu____6434)))


let fresh_token : FStar_Range.range  ->  (Prims.string * sort)  ->  Prims.int  ->  decl = (fun rng uu____6457 id1 -> (match (uu____6457) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (

let a = (

let uu____6473 = (

let uu____6474 = (

let uu____6479 = (mkInteger' id1 rng)
in (

let uu____6480 = (

let uu____6481 = (

let uu____6489 = (constr_id_of_sort sort)
in (

let uu____6491 = (

let uu____6494 = (mkApp ((tok_name), ([])) rng)
in (uu____6494)::[])
in ((uu____6489), (uu____6491))))
in (mkApp uu____6481 rng))
in ((uu____6479), (uu____6480))))
in (mkEq uu____6474 rng))
in (

let uu____6501 = (escape a_name)
in {assumption_term = uu____6473; assumption_caption = FStar_Pervasives_Native.Some ("fresh token"); assumption_name = uu____6501; assumption_fact_ids = []}))
in Assume (a)))
end))


let fresh_constructor : FStar_Range.range  ->  (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun rng uu____6527 -> (match (uu____6527) with
| (name, arg_sorts, sort, id1) -> begin
(

let id2 = (FStar_Util.string_of_int id1)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (

let uu____6567 = (

let uu____6573 = (

let uu____6575 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6575))
in ((uu____6573), (s)))
in (mkFreeV uu____6567 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (

let uu____6597 = (

let uu____6605 = (constr_id_of_sort sort)
in ((uu____6605), ((capp)::[])))
in (mkApp uu____6597 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (

let a = (

let uu____6614 = (

let uu____6615 = (

let uu____6626 = (

let uu____6627 = (

let uu____6632 = (mkInteger id2 norng)
in ((uu____6632), (cid_app)))
in (mkEq uu____6627 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6626)))
in (mkForall rng uu____6615))
in (

let uu____6641 = (escape a_name)
in {assumption_term = uu____6614; assumption_caption = FStar_Pervasives_Native.Some ("Constructor distinct"); assumption_name = uu____6641; assumption_fact_ids = []}))
in Assume (a))))))))
end))


let injective_constructor : FStar_Range.range  ->  (Prims.string * constructor_field Prims.list * sort)  ->  decls_t = (fun rng uu____6664 -> (match (uu____6664) with
| (name, fields, st) -> begin
(

let n_bvars = (FStar_List.length fields)
in (

let bvar_name = (fun i -> (

let uu____6696 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" uu____6696)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (

let uu____6735 = (

let uu____6741 = (bvar_name i)
in ((uu____6741), (s)))
in (mkFreeV uu____6735)))
in (

let bvars = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6774 -> (match (uu____6774) with
| (uu____6784, s, uu____6786) -> begin
(

let uu____6791 = (bvar i s)
in (uu____6791 norng))
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let uu____6813 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6851 -> (match (uu____6851) with
| (iname, isort, projectible) -> begin
(

let cproj_app = (mkApp ((iname), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((iname), ((st)::[]), (isort), (FStar_Pervasives_Native.Some ("Projector"))))
in (match (projectible) with
| true -> begin
(

let a = (

let uu____6884 = (

let uu____6885 = (

let uu____6896 = (

let uu____6897 = (

let uu____6902 = (

let uu____6903 = (bvar i isort)
in (uu____6903 norng))
in ((cproj_app), (uu____6902)))
in (mkEq uu____6897 norng))
in ((((capp)::[])::[]), (bvar_names), (uu____6896)))
in (mkForall rng uu____6885))
in (

let uu____6916 = (escape (Prims.strcat "projection_inverse_" iname))
in {assumption_term = uu____6884; assumption_caption = FStar_Pervasives_Native.Some ("Projection inverse"); assumption_name = uu____6916; assumption_fact_ids = []}))
in (proj_name)::(Assume (a))::[])
end
| uu____6921 -> begin
(proj_name)::[]
end)))
end))))
in (FStar_All.pipe_right uu____6813 FStar_List.flatten)))))))))
end))


let constructor_to_decl : FStar_Range.range  ->  constructor_t  ->  decls_t = (fun rng uu____6939 -> (match (uu____6939) with
| (name, fields, st, id1, injective) -> begin
(

let injective1 = (injective || true)
in (

let field_sorts = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7002 -> (match (uu____7002) with
| (uu____7011, sort, uu____7013) -> begin
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

let uu____7038 = (

let uu____7043 = (

let uu____7044 = (

let uu____7052 = (constr_id_of_sort st)
in ((uu____7052), ((xx)::[])))
in (mkApp uu____7044 norng))
in (

let uu____7057 = (

let uu____7058 = (FStar_Util.string_of_int id1)
in (mkInteger uu____7058 norng))
in ((uu____7043), (uu____7057))))
in (mkEq uu____7038 norng))
in (

let uu____7060 = (

let uu____7071 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7124 -> (match (uu____7124) with
| (proj, s, projectible) -> begin
(match (projectible) with
| true -> begin
(

let uu____7164 = (mkApp ((proj), ((xx)::[])) norng)
in ((uu____7164), ([])))
end
| uu____7180 -> begin
(

let fi = (

let uu____7188 = (

let uu____7190 = (FStar_Util.string_of_int i)
in (Prims.strcat "f_" uu____7190))
in ((uu____7188), (s)))
in (

let uu____7194 = (mkFreeV fi norng)
in ((uu____7194), ((fi)::[]))))
end)
end))))
in (FStar_All.pipe_right uu____7071 FStar_List.split))
in (match (uu____7060) with
| (proj_terms, ex_vars) -> begin
(

let uu____7246 = uu____7060
in (

let ex_vars1 = (FStar_List.flatten ex_vars)
in (

let disc_inv_body = (

let uu____7261 = (

let uu____7266 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (uu____7266)))
in (mkEq uu____7261 norng))
in (

let disc_inv_body1 = (match (ex_vars1) with
| [] -> begin
disc_inv_body
end
| uu____7271 -> begin
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
| uu____7296 -> begin
[]
end)
in (

let uu____7298 = (

let uu____7301 = (

let uu____7302 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (uu____7302))
in (uu____7301)::(cdecl)::(cid)::projs)
in (

let uu____7305 = (

let uu____7308 = (

let uu____7311 = (

let uu____7312 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (uu____7312))
in (uu____7311)::[])
in (FStar_List.append ((disc)::[]) uu____7308))
in (FStar_List.append uu____7298 uu____7305)))))))))
end))


let name_binders_inner : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun prefix_opt outer_names start sorts -> (

let uu____7396 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun uu____7460 s -> (match (uu____7460) with
| (names1, binders, n1) -> begin
(

let prefix1 = (match (s) with
| Term_sort -> begin
"@x"
end
| uu____7525 -> begin
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

let uu____7536 = (FStar_Util.string_of_int n1)
in (Prims.strcat prefix2 uu____7536))
in (

let names2 = (((nm), (s)))::names1
in (

let b = (

let uu____7554 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm uu____7554))
in ((names2), ((b)::binders), ((n1 + (Prims.parse_int "1")))))))))
end)) ((outer_names), ([]), (start))))
in (match (uu____7396) with
| (names1, binders, n1) -> begin
(

let uu____7624 = uu____7396
in ((names1), ((FStar_List.rev binders)), (n1)))
end)))


let name_macro_binders : sort Prims.list  ->  (fv Prims.list * Prims.string Prims.list) = (fun sorts -> (

let uu____7682 = (name_binders_inner (FStar_Pervasives_Native.Some ("__")) [] (Prims.parse_int "0") sorts)
in (match (uu____7682) with
| (names1, binders, n1) -> begin
(

let uu____7742 = uu____7682
in (((FStar_List.rev names1)), (binders)))
end)))


let termToSmt : Prims.bool  ->  Prims.string  ->  term  ->  Prims.string = (fun print_ranges enclosing_name t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (uu____7838); freevars = uu____7839; rng = uu____7840})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| uu____7858 -> begin
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

let uu____7935 = (FStar_List.nth names1 i)
in (FStar_All.pipe_right uu____7935 FStar_Pervasives_Native.fst))
end
| FreeV (x) -> begin
(FStar_Pervasives_Native.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(

let uu____7964 = (op_to_string op)
in (

let uu____7966 = (

let uu____7968 = (FStar_List.map (aux1 n1 names1) tms)
in (FStar_All.pipe_right uu____7968 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" uu____7964 uu____7966)))
end
| Labeled (t2, uu____7980, uu____7981) -> begin
(aux1 n1 names1 t2)
end
| LblPos (t2, s) -> begin
(

let uu____7988 = (aux1 n1 names1 t2)
in (FStar_Util.format2 "(! %s :lblpos %s)" uu____7988 s))
end
| Quant (qop, pats, wopt, sorts, body, qid) -> begin
(

let qidstr = (

let uu____8023 = (FStar_ST.op_Bang qid)
in (match (uu____8023) with
| FStar_Pervasives_Native.None -> begin
"no-qid"
end
| FStar_Pervasives_Native.Some (str) -> begin
str
end))
in (

let uu____8080 = (name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts)
in (match (uu____8080) with
| (names2, binders, n2) -> begin
(

let uu____8110 = uu____8080
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
| uu____8146 -> begin
(

let uu____8151 = (FStar_All.pipe_right pats1 (FStar_List.map (fun pats2 -> (

let uu____8170 = (

let uu____8172 = (FStar_List.map (fun p -> (

let uu____8180 = (aux1 n2 names2 p)
in (FStar_Util.format1 "%s" uu____8180))) pats2)
in (FStar_String.concat " " uu____8172))
in (FStar_Util.format1 "\n:pattern (%s)" uu____8170)))))
in (FStar_All.pipe_right uu____8151 (FStar_String.concat "\n")))
end)
in (

let res = (

let uu____8192 = (

let uu____8196 = (

let uu____8200 = (

let uu____8204 = (aux1 n2 names2 body)
in (

let uu____8206 = (

let uu____8210 = (weightToSmt wopt)
in (uu____8210)::(pats_str)::(qidstr)::[])
in (uu____8204)::uu____8206))
in (binders1)::uu____8200)
in ((qop_to_string qop))::uu____8196)
in (FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu____8192))
in ((

let uu____8221 = (

let uu____8223 = (

let uu____8225 = (FStar_ST.op_Bang qid)
in (FStar_Util.is_some uu____8225))
in (not (uu____8223)))
in (match (uu____8221) with
| true -> begin
(FStar_Util.print (Prims.strcat "Missing QID:\n" (Prims.strcat res "\n\n")) [])
end
| uu____8281 -> begin
()
end));
res;
))))))
end)))
end
| Let (es, body) -> begin
(

let uu____8289 = (FStar_List.fold_left (fun uu____8322 e -> (match (uu____8322) with
| (names0, binders, n0) -> begin
(

let nm = (

let uu____8365 = (FStar_Util.string_of_int n0)
in (Prims.strcat "@lb" uu____8365))
in (

let names01 = (((nm), (Term_sort)))::names0
in (

let b = (

let uu____8374 = (aux1 n1 names1 e)
in (FStar_Util.format2 "(%s %s)" nm uu____8374))
in ((names01), ((b)::binders), ((n0 + (Prims.parse_int "1")))))))
end)) ((names1), ([]), (n1)) es)
in (match (uu____8289) with
| (names2, binders, n2) -> begin
(

let uu____8408 = uu____8289
in (

let uu____8421 = (aux1 n2 names2 body)
in (FStar_Util.format2 "(let (%s)\n%s)" (FStar_String.concat " " binders) uu____8421)))
end))
end)))
and aux = (fun depth n1 names1 t1 -> (

let s = (aux' depth n1 names1 t1)
in (match (((print_ranges && (Prims.op_disEquality t1.rng norng)) && (Prims.op_disEquality t1.rng prrng))) with
| true -> begin
(

let uu____8438 = (FStar_Range.string_of_range t1.rng)
in (

let uu____8440 = (FStar_Range.string_of_use_range t1.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____8438 uu____8440 s)))
end
| uu____8443 -> begin
s
end)))
in (aux (Prims.parse_int "0") (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.bool  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun print_captions uu___124_8469 -> (match (uu___124_8469) with
| FStar_Pervasives_Native.Some (c) when print_captions -> begin
(

let c1 = (

let uu____8479 = (FStar_All.pipe_right (FStar_String.split ((10)::[]) c) (FStar_List.map FStar_Util.trim_string))
in (FStar_All.pipe_right uu____8479 (FStar_String.concat " ")))
in (Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")))
end
| uu____8501 -> begin
""
end))


let rec declToSmt' : Prims.string  ->  Prims.bool  ->  decl  ->  Prims.string = (fun z3options print_captions decl -> ((assign_qids decl);
(match (decl) with
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

let uu____8585 = (FStar_List.map (declToSmt' z3options print_captions) decls)
in (FStar_All.pipe_right uu____8585 (FStar_String.concat "\n")))
in (

let uu____8595 = (FStar_Options.keep_query_captions ())
in (match (uu____8595) with
| true -> begin
(

let uu____8599 = (FStar_Util.string_of_int (FStar_List.length decls))
in (

let uu____8601 = (FStar_Util.string_of_int (FStar_String.length res))
in (FStar_Util.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)" s res s uu____8599 uu____8601)))
end
| uu____8604 -> begin
res
end)))
end
| Caption (c) -> begin
(match (print_captions) with
| true -> begin
(

let uu____8610 = (

let uu____8612 = (FStar_All.pipe_right (FStar_Util.splitlines c) (FStar_List.map (fun s -> (Prims.strcat "; " (Prims.strcat s "\n")))))
in (FStar_All.pipe_right uu____8612 (FStar_String.concat "")))
in (Prims.strcat "\n" uu____8610))
end
| uu____8635 -> begin
""
end)
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (

let uu____8653 = (

let uu____8655 = (caption_to_string print_captions)
in (uu____8655 c))
in (

let uu____8664 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8653 f (FStar_String.concat " " l) uu____8664))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let uu____8679 = (name_macro_binders arg_sorts)
in (match (uu____8679) with
| (names1, binders) -> begin
(

let uu____8702 = uu____8679
in (

let body1 = (

let uu____8713 = (FStar_List.map (fun x -> (mkFreeV x norng)) names1)
in (inst uu____8713 body))
in (

let uu____8728 = (

let uu____8730 = (caption_to_string print_captions)
in (uu____8730 c))
in (

let uu____8739 = (strSort retsort)
in (

let uu____8741 = (

let uu____8743 = (escape f)
in (termToSmt print_captions uu____8743 body1))
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____8728 f (FStar_String.concat " " binders) uu____8739 uu____8741))))))
end))
end
| Assume (a) -> begin
(

let fact_ids_to_string = (fun ids -> (FStar_All.pipe_right ids (FStar_List.map (fun uu___125_8773 -> (match (uu___125_8773) with
| Name (n1) -> begin
(

let uu____8776 = (FStar_Ident.text_of_lid n1)
in (Prims.strcat "Name " uu____8776))
end
| Namespace (ns) -> begin
(

let uu____8780 = (FStar_Ident.text_of_lid ns)
in (Prims.strcat "Namespace " uu____8780))
end
| Tag (t) -> begin
(Prims.strcat "Tag " t)
end)))))
in (

let fids = (match (print_captions) with
| true -> begin
(

let uu____8790 = (

let uu____8792 = (fact_ids_to_string a.assumption_fact_ids)
in (FStar_String.concat "; " uu____8792))
in (FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8790))
end
| uu____8798 -> begin
""
end)
in (

let n1 = a.assumption_name
in (

let uu____8803 = (

let uu____8805 = (caption_to_string print_captions)
in (uu____8805 a.assumption_caption))
in (

let uu____8814 = (termToSmt print_captions n1 a.assumption_term)
in (FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8803 fids uu____8814 n1))))))
end
| Eval (t) -> begin
(

let uu____8818 = (termToSmt print_captions "eval" t)
in (FStar_Util.format1 "(eval %s)" uu____8818))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| RetainAssumptions (uu____8825) -> begin
""
end
| CheckSat -> begin
"(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
end
| GetUnsatCore -> begin
"(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
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

let uu____8847 = (FStar_Options.keep_query_captions ())
in (declToSmt' z3options uu____8847 decl)))
and declToSmt_no_caps : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (declToSmt' z3options false decl))
and declsToSmt : Prims.string  ->  decl Prims.list  ->  Prims.string = (fun z3options decls -> (

let uu____8860 = (FStar_List.map (declToSmt z3options) decls)
in (FStar_All.pipe_right uu____8860 (FStar_String.concat "\n"))))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (

let uu____8981 = (

let uu____8985 = (FStar_All.pipe_right constrs (FStar_List.collect (constructor_to_decl norng)))
in (FStar_All.pipe_right uu____8985 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right uu____8981 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let preludeDecls : decl Prims.list = (

let uu____9011 = (((("x"), (Term_sort))), ((("y"), (Term_sort))), ((("t"), (Term_sort))))
in (match (uu____9011) with
| (tmvarx, tmvary, tmvart) -> begin
(

let bovarb = (("b"), (Bool_sort))
in (

let flvarf = (("f"), (Fuel_sort))
in (

let uu____9105 = (((("t1"), (Term_sort))), ((("t2"), (Term_sort))), ((("x1"), (Term_sort))), ((("x2"), (Term_sort))), ((("y1"), (Term_sort))), ((("y2"), (Term_sort))))
in (match (uu____9105) with
| (t1, t2, x1, x2, y1, y2) -> begin
(

let uu____9258 = (((("x"), (Int_sort))), ((("y"), (Int_sort))))
in (match (uu____9258) with
| (intvarx, intvary) -> begin
(

let hastypez = (

let uu____9312 = (

let uu____9313 = (

let uu____9321 = (

let uu____9324 = (mkApp (("ZFuel"), ([])) prrng)
in (

let uu____9329 = (

let uu____9332 = (mkFreeV tmvarx prrng)
in (

let uu____9333 = (

let uu____9336 = (mkFreeV tmvart prrng)
in (uu____9336)::[])
in (uu____9332)::uu____9333))
in (uu____9324)::uu____9329))
in (("HasTypeFuel"), (uu____9321)))
in (mkApp uu____9313 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9312))
in (

let hastype = (

let uu____9342 = (

let uu____9343 = (

let uu____9351 = (

let uu____9354 = (mkApp (("MaxIFuel"), ([])) prrng)
in (

let uu____9359 = (

let uu____9362 = (mkFreeV tmvarx prrng)
in (

let uu____9363 = (

let uu____9366 = (mkFreeV tmvart prrng)
in (uu____9366)::[])
in (uu____9362)::uu____9363))
in (uu____9354)::uu____9359))
in (("HasTypeFuel"), (uu____9351)))
in (mkApp uu____9343 prrng))
in (abstr ((tmvarx)::(tmvart)::[]) uu____9342))
in (

let fuelirrelevance_pat = (

let uu____9372 = (

let uu____9380 = (

let uu____9383 = (

let uu____9384 = (

let uu____9392 = (

let uu____9395 = (mkFreeV flvarf prrng)
in (uu____9395)::[])
in (("SFuel"), (uu____9392)))
in (mkApp uu____9384 prrng))
in (

let uu____9400 = (

let uu____9403 = (mkFreeV tmvarx prrng)
in (

let uu____9404 = (

let uu____9407 = (mkFreeV tmvart prrng)
in (uu____9407)::[])
in (uu____9403)::uu____9404))
in (uu____9383)::uu____9400))
in (("HasTypeFuel"), (uu____9380)))
in (mkApp uu____9372 prrng))
in (

let fuelirrelevance = (

let uu____9413 = (

let uu____9424 = (

let uu____9425 = (

let uu____9430 = (

let uu____9431 = (

let uu____9439 = (

let uu____9442 = (mkFreeV tmvarx prrng)
in (

let uu____9443 = (

let uu____9446 = (mkFreeV tmvart prrng)
in (uu____9446)::[])
in (uu____9442)::uu____9443))
in (("HasTypeZ"), (uu____9439)))
in (mkApp uu____9431 prrng))
in ((fuelirrelevance_pat), (uu____9430)))
in (mkEq uu____9425 prrng))
in ((((fuelirrelevance_pat)::[])::[]), ((flvarf)::(tmvarx)::(tmvart)::[]), (uu____9424)))
in (mkForall prrng uu____9413))
in (

let nohoist_pat = (

let uu____9480 = (

let uu____9488 = (

let uu____9491 = (mkFreeV tmvart prrng)
in (

let uu____9492 = (

let uu____9495 = (mkFreeV bovarb prrng)
in (uu____9495)::[])
in (uu____9491)::uu____9492))
in (("NoHoist"), (uu____9488)))
in (mkApp uu____9480 prrng))
in (

let nohoist = (

let uu____9501 = (

let uu____9512 = (

let uu____9513 = (

let uu____9518 = (mkFreeV bovarb prrng)
in ((nohoist_pat), (uu____9518)))
in (mkEq uu____9513 prrng))
in ((((nohoist_pat)::[])::[]), ((tmvart)::(bovarb)::[]), (uu____9512)))
in (mkForall prrng uu____9501))
in (

let istyped = (

let uu____9543 = (

let uu____9544 = (

let uu____9555 = (

let uu____9556 = (

let uu____9564 = (

let uu____9567 = (mkFreeV tmvarx prrng)
in (

let uu____9568 = (

let uu____9571 = (mkFreeV tmvart prrng)
in (uu____9571)::[])
in (uu____9567)::uu____9568))
in (("HasTypeZ"), (uu____9564)))
in (mkApp uu____9556 prrng))
in (([]), ((tmvart)::[]), (uu____9555)))
in (mkExists prrng uu____9544))
in (abstr ((tmvarx)::[]) uu____9543))
in (

let validity_pat = (

let uu____9593 = (

let uu____9601 = (

let uu____9604 = (mkFreeV tmvart prrng)
in (uu____9604)::[])
in (("Valid"), (uu____9601)))
in (mkApp uu____9593 prrng))
in (

let validity = (

let uu____9610 = (

let uu____9621 = (

let uu____9622 = (

let uu____9627 = (

let uu____9628 = (

let uu____9639 = (

let uu____9640 = (

let uu____9648 = (

let uu____9651 = (mkFreeV tmvarx prrng)
in (

let uu____9652 = (

let uu____9655 = (mkFreeV tmvart prrng)
in (uu____9655)::[])
in (uu____9651)::uu____9652))
in (("HasType"), (uu____9648)))
in (mkApp uu____9640 prrng))
in (([]), ((tmvarx)::[]), (uu____9639)))
in (mkExists prrng uu____9628))
in ((uu____9627), (validity_pat)))
in (mkIff uu____9622 prrng))
in ((((validity_pat)::[])::[]), ((tmvart)::[]), (uu____9621)))
in (mkForall prrng uu____9610))
in (

let operator_pat = (fun nm -> (

let uu____9702 = (

let uu____9710 = (

let uu____9713 = (mkFreeV intvarx prrng)
in (

let uu____9714 = (

let uu____9717 = (mkFreeV intvary prrng)
in (uu____9717)::[])
in (uu____9713)::uu____9714))
in ((nm), (uu____9710)))
in (mkApp uu____9702 prrng)))
in (

let operator = (fun nm o -> (

let uu____9734 = (

let uu____9745 = (

let uu____9750 = (

let uu____9753 = (operator_pat nm)
in (uu____9753)::[])
in (uu____9750)::[])
in (

let uu____9758 = (

let uu____9759 = (

let uu____9764 = (operator_pat nm)
in (

let uu____9765 = (

let uu____9766 = (

let uu____9773 = (

let uu____9776 = (mkFreeV intvarx prrng)
in (

let uu____9777 = (

let uu____9780 = (mkFreeV intvary prrng)
in (uu____9780)::[])
in (uu____9776)::uu____9777))
in ((o), (uu____9773)))
in (mkApp' uu____9766 prrng))
in ((uu____9764), (uu____9765))))
in (mkEq uu____9759 prrng))
in ((uu____9745), ((intvarx)::(intvary)::[]), (uu____9758))))
in (mkForall prrng uu____9734)))
in (

let constrs = (FStar_All.pipe_right (((("FString_const"), (((("FString_const_proj_0"), (Int_sort), (true)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((((FStar_Pervasives_Native.fst boxIntFun)), (((((FStar_Pervasives_Native.snd boxIntFun)), (Int_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((((FStar_Pervasives_Native.fst boxBoolFun)), (((((FStar_Pervasives_Native.snd boxBoolFun)), (Bool_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((((FStar_Pervasives_Native.fst boxStringFun)), (((((FStar_Pervasives_Native.snd boxStringFun)), (String_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort), (true)))::((("LexCons_1"), (Term_sort), (true)))::((("LexCons_2"), (Term_sort), (true)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]) (FStar_List.collect (constructor_to_decl prrng)))
in (

let isprims = (

let uu____9912 = (

let uu____9913 = (

let uu____9921 = (

let uu____9924 = (mkFreeV tmvart prrng)
in (uu____9924)::[])
in (("is-LexCons"), (uu____9921)))
in (mkApp uu____9913 prrng))
in (abstr ((tmvart)::[]) uu____9912))
in (

let precedes_lext = (fun tm1 tm2 -> (

let lext = (mkApp (("Prims.lex_t"), ([])) prrng)
in (mkApp (("Prims.precedes"), ((lext)::(lext)::(tm1)::(tm2)::[])) prrng)))
in (

let lexicographic = (

let uu____9950 = (

let uu____9961 = (

let uu____9962 = (

let uu____9967 = (

let uu____9968 = (

let uu____9976 = (

let uu____9979 = (

let uu____9980 = (

let uu____9981 = (

let uu____9989 = (

let uu____9992 = (mkFreeV t1 prrng)
in (

let uu____9993 = (

let uu____9996 = (mkFreeV x1 prrng)
in (

let uu____9997 = (

let uu____10000 = (mkFreeV x2 prrng)
in (uu____10000)::[])
in (uu____9996)::uu____9997))
in (uu____9992)::uu____9993))
in (("LexCons"), (uu____9989)))
in (mkApp uu____9981 prrng))
in (

let uu____10005 = (

let uu____10006 = (

let uu____10014 = (

let uu____10017 = (mkFreeV t2 prrng)
in (

let uu____10018 = (

let uu____10021 = (mkFreeV y1 prrng)
in (

let uu____10022 = (

let uu____10025 = (mkFreeV y2 prrng)
in (uu____10025)::[])
in (uu____10021)::uu____10022))
in (uu____10017)::uu____10018))
in (("LexCons"), (uu____10014)))
in (mkApp uu____10006 prrng))
in (precedes_lext uu____9980 uu____10005)))
in (uu____9979)::[])
in (("Valid"), (uu____9976)))
in (mkApp uu____9968 prrng))
in (

let uu____10034 = (

let uu____10035 = (

let uu____10040 = (

let uu____10041 = (

let uu____10049 = (

let uu____10052 = (

let uu____10053 = (

let uu____10061 = (

let uu____10064 = (mkFreeV t1 prrng)
in (

let uu____10065 = (

let uu____10068 = (mkFreeV t2 prrng)
in (

let uu____10069 = (

let uu____10072 = (mkFreeV x1 prrng)
in (

let uu____10073 = (

let uu____10076 = (mkFreeV y1 prrng)
in (uu____10076)::[])
in (uu____10072)::uu____10073))
in (uu____10068)::uu____10069))
in (uu____10064)::uu____10065))
in (("Prims.precedes"), (uu____10061)))
in (mkApp uu____10053 prrng))
in (uu____10052)::[])
in (("Valid"), (uu____10049)))
in (mkApp uu____10041 prrng))
in (

let uu____10085 = (

let uu____10086 = (

let uu____10091 = (

let uu____10092 = (

let uu____10097 = (mkFreeV x1 prrng)
in (

let uu____10098 = (mkFreeV y1 prrng)
in ((uu____10097), (uu____10098))))
in (mkEq uu____10092 prrng))
in (

let uu____10099 = (

let uu____10100 = (

let uu____10108 = (

let uu____10111 = (

let uu____10112 = (mkFreeV x2 prrng)
in (

let uu____10113 = (mkFreeV y2 prrng)
in (precedes_lext uu____10112 uu____10113)))
in (uu____10111)::[])
in (("Valid"), (uu____10108)))
in (mkApp uu____10100 prrng))
in ((uu____10091), (uu____10099))))
in (mkAnd uu____10086 prrng))
in ((uu____10040), (uu____10085))))
in (mkOr uu____10035 prrng))
in ((uu____9967), (uu____10034))))
in (mkIff uu____9962 prrng))
in (([]), ((t1)::(t2)::(x1)::(x2)::(y1)::(y2)::[]), (uu____9961)))
in (mkForall prrng uu____9950))
in (

let precedes_pat = (

let uu____10160 = (

let uu____10168 = (

let uu____10171 = (mkFreeV t1 prrng)
in (

let uu____10172 = (

let uu____10175 = (mkFreeV t2 prrng)
in (

let uu____10176 = (

let uu____10179 = (mkFreeV x1 prrng)
in (

let uu____10180 = (

let uu____10183 = (mkFreeV x2 prrng)
in (uu____10183)::[])
in (uu____10179)::uu____10180))
in (uu____10175)::uu____10176))
in (uu____10171)::uu____10172))
in (("Prims.precedes"), (uu____10168)))
in (mkApp uu____10160 prrng))
in (

let precedes = (

let uu____10189 = (

let uu____10200 = (

let uu____10201 = (

let uu____10206 = (mkApp (("Valid"), ((precedes_pat)::[])) prrng)
in (

let uu____10211 = (

let uu____10212 = (

let uu____10220 = (

let uu____10223 = (

let uu____10224 = (mkFreeV x1 prrng)
in (

let uu____10225 = (mkFreeV x2 prrng)
in (precedes_lext uu____10224 uu____10225)))
in (uu____10223)::[])
in (("Valid"), (uu____10220)))
in (mkApp uu____10212 prrng))
in ((uu____10206), (uu____10211))))
in (mkIff uu____10201 prrng))
in ((((precedes_pat)::[])::[]), ((t1)::(t2)::(x1)::(x2)::[]), (uu____10200)))
in (mkForall prrng uu____10189))
in (

let rank_pat = (

let uu____10264 = (mkFreeV t1 prrng)
in (

let uu____10265 = (mkFreeV t2 prrng)
in (precedes_lext uu____10264 uu____10265)))
in (

let rank = (

let uu____10267 = (

let uu____10278 = (

let uu____10279 = (

let uu____10284 = (mkApp (("Valid"), ((rank_pat)::[])) prrng)
in (

let uu____10289 = (

let uu____10290 = (

let uu____10295 = (

let uu____10296 = (

let uu____10304 = (

let uu____10307 = (mkFreeV t1 prrng)
in (uu____10307)::[])
in (("Rank"), (uu____10304)))
in (mkApp uu____10296 prrng))
in (

let uu____10312 = (

let uu____10313 = (

let uu____10321 = (

let uu____10324 = (mkFreeV t2 prrng)
in (uu____10324)::[])
in (("Rank"), (uu____10321)))
in (mkApp uu____10313 prrng))
in ((uu____10295), (uu____10312))))
in (mkLT uu____10290 prrng))
in ((uu____10284), (uu____10289))))
in (mkIff uu____10279 prrng))
in ((((rank_pat)::[])::[]), ((t1)::(t2)::[]), (uu____10278)))
in (mkForall prrng uu____10267))
in (

let uu____10352 = (

let uu____10355 = (

let uu____10358 = (

let uu____10361 = (

let uu____10364 = (

let uu____10367 = (

let uu____10370 = (

let uu____10373 = (

let uu____10376 = (

let uu____10379 = (

let uu____10382 = (

let uu____10385 = (

let uu____10388 = (

let uu____10391 = (

let uu____10394 = (

let uu____10395 = (

let uu____10396 = (escape "fuel_irrelevance")
in {assumption_term = fuelirrelevance; assumption_caption = FStar_Pervasives_Native.Some ("Fuel irrelevance"); assumption_name = uu____10396; assumption_fact_ids = []})
in Assume (uu____10395))
in (

let uu____10401 = (

let uu____10404 = (

let uu____10407 = (

let uu____10408 = (

let uu____10409 = (escape "no_hoist")
in {assumption_term = nohoist; assumption_caption = FStar_Pervasives_Native.Some ("No-hoist"); assumption_name = uu____10409; assumption_fact_ids = []})
in Assume (uu____10408))
in (

let uu____10414 = (

let uu____10417 = (

let uu____10420 = (

let uu____10423 = (

let uu____10426 = (

let uu____10429 = (

let uu____10432 = (

let uu____10435 = (

let uu____10438 = (

let uu____10441 = (

let uu____10442 = (

let uu____10456 = (

let uu____10457 = (mkFreeV tmvarx prrng)
in (abstr ((tmvarx)::[]) uu____10457))
in (("Reify"), ((Term_sort)::[]), (Term_sort), (uu____10456), (FStar_Pervasives_Native.None)))
in DefineFun (uu____10442))
in (

let uu____10463 = (

let uu____10466 = (

let uu____10467 = (

let uu____10468 = (escape "validity")
in {assumption_term = validity; assumption_caption = FStar_Pervasives_Native.Some ("Validity"); assumption_name = uu____10468; assumption_fact_ids = []})
in Assume (uu____10467))
in (

let uu____10473 = (

let uu____10476 = (

let uu____10479 = (

let uu____10482 = (

let uu____10485 = (

let uu____10488 = (

let uu____10491 = (

let uu____10494 = (

let uu____10495 = (

let uu____10496 = (operator "_mul" Mul)
in (

let uu____10498 = (escape "arithmetic_multiplication")
in {assumption_term = uu____10496; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic multiplication"); assumption_name = uu____10498; assumption_fact_ids = []}))
in Assume (uu____10495))
in (

let uu____10503 = (

let uu____10506 = (

let uu____10507 = (

let uu____10508 = (operator "_div" Div)
in (

let uu____10510 = (escape "arithmetic_division")
in {assumption_term = uu____10508; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic division"); assumption_name = uu____10510; assumption_fact_ids = []}))
in Assume (uu____10507))
in (

let uu____10515 = (

let uu____10518 = (

let uu____10519 = (

let uu____10520 = (operator "_mod" Mod)
in (

let uu____10522 = (escape "arithmetic_modulus")
in {assumption_term = uu____10520; assumption_caption = FStar_Pervasives_Native.Some ("Arithmetic modulus"); assumption_name = uu____10522; assumption_fact_ids = []}))
in Assume (uu____10519))
in (uu____10518)::[])
in (uu____10506)::uu____10515))
in (uu____10494)::uu____10503))
in (DeclFun ((("__uu__PartialApp"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10491)
in (DeclFun ((("_mod"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10488)
in (DeclFun ((("_div"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10485)
in (DeclFun ((("_mul"), ((Int_sort)::(Int_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10482)
in (DeclFun ((("Range_const"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10479)
in (DeclFun ((("Prims.precedes"), ((Term_sort)::(Term_sort)::(Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10476)
in (uu____10466)::uu____10473))
in (uu____10441)::uu____10463))
in (DeclFun ((("Tm_uvar"), ((Int_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10438)
in (DeclFun ((("ConsFuel"), ((Fuel_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10435)
in (DeclFun ((("ConsTerm"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10432)
in (DeclFun ((("Closure"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10429)
in (DeclFun ((("Rank"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10426)
in (DeclFun ((("ApplyTT"), ((Term_sort)::(Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10423)
in (DeclFun ((("ApplyTF"), ((Term_sort)::(Fuel_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10420)
in (DefineFun ((("IsTyped"), ((Term_sort)::[]), (Bool_sort), (istyped), (FStar_Pervasives_Native.None))))::uu____10417)
in (uu____10407)::uu____10414))
in (DeclFun ((("NoHoist"), ((Term_sort)::(Bool_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10404)
in (uu____10394)::uu____10401))
in (DefineFun ((("HasType"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastype), (FStar_Pervasives_Native.None))))::uu____10391)
in (DefineFun ((("HasTypeZ"), ((Term_sort)::(Term_sort)::[]), (Bool_sort), (hastypez), (FStar_Pervasives_Native.None))))::uu____10388)
in (DeclFun ((("HasTypeFuel"), ((Fuel_sort)::(Term_sort)::(Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10385)
in (DeclFun ((("Valid"), ((Term_sort)::[]), (Bool_sort), (FStar_Pervasives_Native.None))))::uu____10382)
in (DeclFun ((("PreType"), ((Term_sort)::[]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10379)
in (DeclFun ((("MaxFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10376)
in (DeclFun ((("MaxIFuel"), ([]), (Fuel_sort), (FStar_Pervasives_Native.None))))::uu____10373)
in (FuelDeclaration)::uu____10370)
in (DeclFun ((("Term_constr_id"), ((Term_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10367)
in (SortDeclaration ("Term"))::uu____10364)
in (DeclFun ((("FString_constr_id"), ((String_sort)::[]), (Int_sort), (FStar_Pervasives_Native.None))))::uu____10361)
in (SortDeclaration ("FString"))::uu____10358)
in (GenerateOptions)::uu____10355)
in (

let uu____10649 = (

let uu____10652 = (

let uu____10655 = (

let uu____10658 = (

let uu____10661 = (

let uu____10662 = (

let uu____10663 = (escape "lexicographic_ordering")
in {assumption_term = lexicographic; assumption_caption = FStar_Pervasives_Native.Some ("Lexicographic ordering"); assumption_name = uu____10663; assumption_fact_ids = []})
in Assume (uu____10662))
in (

let uu____10668 = (

let uu____10671 = (

let uu____10672 = (

let uu____10673 = (escape "precedes_ordering")
in {assumption_term = precedes; assumption_caption = FStar_Pervasives_Native.Some ("Precedes ordering"); assumption_name = uu____10673; assumption_fact_ids = []})
in Assume (uu____10672))
in (

let uu____10678 = (

let uu____10681 = (

let uu____10682 = (

let uu____10683 = (escape "rank_ordering")
in {assumption_term = rank; assumption_caption = FStar_Pervasives_Native.Some ("Rank ordering"); assumption_name = uu____10683; assumption_fact_ids = []})
in Assume (uu____10682))
in (uu____10681)::[])
in (uu____10671)::uu____10678))
in (uu____10661)::uu____10668))
in (DeclFun ((("Prims.lex_t"), ([]), (Term_sort), (FStar_Pervasives_Native.None))))::uu____10658)
in (DefineFun ((("is-Prims.LexCons"), ((Term_sort)::[]), (Bool_sort), (isprims), (FStar_Pervasives_Native.None))))::uu____10655)
in (FStar_List.append constrs uu____10652))
in (FStar_List.append uu____10352 uu____10649))))))))))))))))))))))
end))
end))))
end))


let mkBvConstructor : Prims.int  ->  decls_t = (fun sz -> (

let uu____10708 = (

let uu____10709 = (

let uu____10711 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____10711))
in (

let uu____10720 = (

let uu____10723 = (

let uu____10724 = (

let uu____10726 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____10726))
in ((uu____10724), (BitVec_sort (sz)), (true)))
in (uu____10723)::[])
in ((uu____10709), (uu____10720), (Term_sort), (((Prims.parse_int "12") + sz)), (true))))
in (FStar_All.pipe_right uu____10708 (constructor_to_decl norng))))


let __range_c : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let mk_Range_const : unit  ->  term = (fun uu____10769 -> (

let i = (FStar_ST.op_Bang __range_c)
in ((

let uu____10794 = (

let uu____10796 = (FStar_ST.op_Bang __range_c)
in (uu____10796 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals __range_c uu____10794));
(

let uu____10841 = (

let uu____10849 = (

let uu____10852 = (mkInteger' i norng)
in (uu____10852)::[])
in (("Range_const"), (uu____10849)))
in (mkApp uu____10841 norng));
)))


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____10895 = (

let uu____10903 = (

let uu____10906 = (mkInteger' i norng)
in (uu____10906)::[])
in (("Tm_uvar"), (uu____10903)))
in (mkApp uu____10895 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let elim_box : Prims.bool  ->  Prims.string  ->  Prims.string  ->  term  ->  term = (fun cond u v1 t -> (match (t.tm) with
| App (Var (v'), (t1)::[]) when ((Prims.op_Equality v1 v') && cond) -> begin
t1
end
| uu____10949 -> begin
(mkApp ((u), ((t)::[])) t.rng)
end))


let maybe_elim_box : Prims.string  ->  Prims.string  ->  term  ->  term = (fun u v1 t -> (

let uu____10973 = (FStar_Options.smtencoding_elim_box ())
in (elim_box uu____10973 u v1 t)))


let boxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun) (FStar_Pervasives_Native.snd boxIntFun) t))


let unboxInt : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun) (FStar_Pervasives_Native.fst boxIntFun) t))


let boxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun) (FStar_Pervasives_Native.snd boxBoolFun) t))


let unboxBool : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun) (FStar_Pervasives_Native.fst boxBoolFun) t))


let boxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun) (FStar_Pervasives_Native.snd boxStringFun) t))


let unboxString : term  ->  term = (fun t -> (maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun) (FStar_Pervasives_Native.fst boxStringFun) t))


let boxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11048 = (

let uu____11050 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11050))
in (

let uu____11059 = (

let uu____11061 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11061))
in (elim_box true uu____11048 uu____11059 t))))


let unboxBitVec : Prims.int  ->  term  ->  term = (fun sz t -> (

let uu____11084 = (

let uu____11086 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.snd uu____11086))
in (

let uu____11095 = (

let uu____11097 = (boxBitVecFun sz)
in (FStar_Pervasives_Native.fst uu____11097))
in (elim_box true uu____11084 uu____11095 t))))


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
| uu____11120 -> begin
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
| uu____11134 -> begin
(FStar_Exn.raise FStar_Util.Impos)
end))


let getBoxedInteger : term  ->  Prims.int FStar_Pervasives_Native.option = (fun t -> (match (t.tm) with
| App (Var (s), (t2)::[]) when (Prims.op_Equality s (FStar_Pervasives_Native.fst boxIntFun)) -> begin
(match (t2.tm) with
| Integer (n1) -> begin
(

let uu____11160 = (FStar_Util.int_of_string n1)
in FStar_Pervasives_Native.Some (uu____11160))
end
| uu____11163 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____11165 -> begin
FStar_Pervasives_Native.None
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (uu____11183)::(t1)::(t2)::[]); freevars = uu____11186; rng = uu____11187})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (uu____11203)::(t1)::(t2)::[]); freevars = uu____11206; rng = uu____11207})::[]) -> begin
(

let uu____11223 = (mkEq ((t1), (t2)) norng)
in (mkNot uu____11223 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11226; rng = uu____11227})::[]) -> begin
(

let uu____11243 = (

let uu____11248 = (unboxInt t1)
in (

let uu____11249 = (unboxInt t2)
in ((uu____11248), (uu____11249))))
in (mkLTE uu____11243 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = uu____11252; rng = uu____11253})::[]) -> begin
(

let uu____11269 = (

let uu____11274 = (unboxInt t1)
in (

let uu____11275 = (unboxInt t2)
in ((uu____11274), (uu____11275))))
in (mkLT uu____11269 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = uu____11278; rng = uu____11279})::[]) -> begin
(

let uu____11295 = (

let uu____11300 = (unboxInt t1)
in (

let uu____11301 = (unboxInt t2)
in ((uu____11300), (uu____11301))))
in (mkGTE uu____11295 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = uu____11304; rng = uu____11305})::[]) -> begin
(

let uu____11321 = (

let uu____11326 = (unboxInt t1)
in (

let uu____11327 = (unboxInt t2)
in ((uu____11326), (uu____11327))))
in (mkGT uu____11321 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = uu____11330; rng = uu____11331})::[]) -> begin
(

let uu____11347 = (

let uu____11352 = (unboxBool t1)
in (

let uu____11353 = (unboxBool t2)
in ((uu____11352), (uu____11353))))
in (mkAnd uu____11347 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = uu____11356; rng = uu____11357})::[]) -> begin
(

let uu____11373 = (

let uu____11378 = (unboxBool t1)
in (

let uu____11379 = (unboxBool t2)
in ((uu____11378), (uu____11379))))
in (mkOr uu____11373 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t1)::[]); freevars = uu____11381; rng = uu____11382})::[]) -> begin
(

let uu____11398 = (unboxBool t1)
in (mkNot uu____11398 t1.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11402; rng = uu____11403})::[]) when (

let uu____11419 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11419)) -> begin
(

let sz = (

let uu____11426 = (getBoxedInteger t0)
in (match (uu____11426) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11434 -> begin
(failwith "impossible")
end))
in (

let uu____11440 = (

let uu____11445 = (unboxBitVec sz t1)
in (

let uu____11446 = (unboxBitVec sz t2)
in ((uu____11445), (uu____11446))))
in (mkBvUlt uu____11440 t.rng)))
end
| App (Var ("Prims.equals"), (uu____11447)::({tm = App (Var ("FStar.BV.bvult"), (t0)::(t1)::(t2)::[]); freevars = uu____11451; rng = uu____11452})::(uu____11453)::[]) when (

let uu____11469 = (getBoxedInteger t0)
in (FStar_Util.is_some uu____11469)) -> begin
(

let sz = (

let uu____11476 = (getBoxedInteger t0)
in (match (uu____11476) with
| FStar_Pervasives_Native.Some (sz) -> begin
sz
end
| uu____11484 -> begin
(failwith "impossible")
end))
in (

let uu____11490 = (

let uu____11495 = (unboxBitVec sz t1)
in (

let uu____11496 = (unboxBitVec sz t2)
in ((uu____11495), (uu____11496))))
in (mkBvUlt uu____11490 t.rng)))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let uu___126_11501 = (unboxBool t1)
in {tm = uu___126_11501.tm; freevars = uu___126_11501.freevars; rng = t.rng})
end
| uu____11502 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasType"), ((v1)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v1 t -> (mkApp (("HasTypeZ"), ((v1)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v1 -> (mkApp (("IsTyped"), ((v1)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v1 t -> (

let uu____11563 = (FStar_Options.unthrottle_inductives ())
in (match (uu____11563) with
| true -> begin
(mk_HasType v1 t)
end
| uu____11566 -> begin
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

let uu____11696 = (

let uu____11697 = (mkApp (("__uu__PartialApp"), ([])) t.rng)
in (mk_ApplyTT uu____11697 t t.rng))
in (FStar_All.pipe_right uu____11696 mk_Valid)))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (

let uu____11715 = (

let uu____11723 = (

let uu____11726 = (mkInteger' i norng)
in (uu____11726)::[])
in (("FString_const"), (uu____11723)))
in (mkApp uu____11715 r)))


let mk_Precedes : term  ->  term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 x4 r -> (

let uu____11757 = (mkApp (("Prims.precedes"), ((x1)::(x2)::(x3)::(x4)::[])) r)
in (FStar_All.pipe_right uu____11757 mk_Valid)))


let mk_LexCons : term  ->  term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 x3 r -> (mkApp (("LexCons"), ((x1)::(x2)::(x3)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
(mkApp (("ZFuel"), ([])) norng)
end
| uu____11802 -> begin
(

let uu____11804 = (

let uu____11812 = (

let uu____11815 = (n_fuel (n1 - (Prims.parse_int "1")))
in (uu____11815)::[])
in (("SFuel"), (uu____11812)))
in (mkApp uu____11804 norng))
end))


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term FStar_Pervasives_Native.option  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  term FStar_Pervasives_Native.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (FStar_Pervasives_Native.Some (p11), FStar_Pervasives_Native.Some (p21)) -> begin
(

let uu____11863 = (mkAnd ((p11), (p21)) r)
in FStar_Pervasives_Native.Some (uu____11863))
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

let uu____11926 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l uu____11926)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (

let uu____11946 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l uu____11946)))


let mk_haseq : term  ->  term = (fun t -> (

let uu____11957 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid uu____11957)))




