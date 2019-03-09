
open Prims
open FStar_Pervasives

let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____19 -> begin
i
end))

type pretty_alignment =
| PrettyLeft
| PrettyRight
| PrettyMark of Prims.string


let uu___is_PrettyLeft : pretty_alignment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PrettyLeft -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_PrettyRight : pretty_alignment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PrettyRight -> begin
true
end
| uu____47 -> begin
false
end))


let uu___is_PrettyMark : pretty_alignment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PrettyMark (_0) -> begin
true
end
| uu____60 -> begin
false
end))


let __proj__PrettyMark__item___0 : pretty_alignment  ->  Prims.string = (fun projectee -> (match (projectee) with
| PrettyMark (_0) -> begin
_0
end))


let prettyprint_table : pretty_alignment Prims.list  ->  Prims.string Prims.list Prims.list  ->  (Prims.string * Prims.int) = (fun fmt tab -> (

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____129 -> begin
i
end))
in (

let mark_split = (fun align s -> (match (align) with
| PrettyLeft -> begin
((""), (s))
end
| PrettyRight -> begin
((s), (""))
end
| PrettyMark (sep) -> begin
(

let spl = (FStar_Util.split s sep)
in (

let uu____168 = (

let uu____170 = (FStar_List.hd spl)
in (Prims.strcat uu____170 sep))
in (

let uu____173 = (

let uu____175 = (FStar_List.tl spl)
in (FStar_All.pipe_right uu____175 (FStar_String.concat sep)))
in ((uu____168), (uu____173)))))
end))
in (

let len = (fun align uu____213 s -> (match (uu____213) with
| (l, r) -> begin
(

let uu____240 = (mark_split align s)
in (match (uu____240) with
| (ls, rs) -> begin
(

let uu____259 = uu____240
in (

let uu____266 = (((FStar_String.length ls)), ((FStar_String.length rs)))
in (match (uu____266) with
| (lx, rx) -> begin
(

let uu____287 = uu____266
in (

let uu____294 = (max1 l lx)
in (

let uu____296 = (max1 r rx)
in ((uu____294), (uu____296)))))
end)))
end))
end))
in (

let rec maxlength = (fun fmt1 ln row -> (match (((fmt1), (ln), (row))) with
| ((fmt_hd)::fmt_tl, (ln_hd)::ln_tl, (row_hd)::row_tl) -> begin
(

let uu____417 = (len fmt_hd ln_hd row_hd)
in (

let uu____424 = (maxlength fmt_tl ln_tl row_tl)
in (uu____417)::uu____424))
end
| uu____439 -> begin
[]
end))
in (

let maxlength_init = (FStar_Common.tabulate (FStar_List.length fmt) (fun uu____481 -> (((Prims.parse_int "0")), ((Prims.parse_int "0")))))
in (

let maxlength_list = (FStar_List.fold_left (maxlength fmt) maxlength_init tab)
in (

let totallength = (FStar_List.fold_left (fun x uu____521 -> (match (uu____521) with
| (l, r) -> begin
((x + l) + r)
end)) (Prims.parse_int "0") maxlength_list)
in (

let enlarge = (fun uu____559 uu____560 -> (match (((uu____559), (uu____560))) with
| ((sl, sr), (l, r)) -> begin
(

let uu____611 = (FStar_Util.repeat (l - (FStar_String.length sl)) " ")
in (

let uu____614 = (

let uu____616 = (

let uu____618 = (FStar_Util.repeat (r - (FStar_String.length sr)) " ")
in (Prims.strcat sr uu____618))
in (Prims.strcat sl uu____616))
in (Prims.strcat uu____611 uu____614)))
end))
in (

let rec enlarge_row = (fun fmt1 ln row -> (match (((fmt1), (ln), (row))) with
| ((fmt_hd)::fmt_tl, ((ln_l, ln_r))::ln_tl, (row_hd)::row_tl) -> begin
(

let uu____727 = (mark_split fmt_hd row_hd)
in (match (uu____727) with
| (sl, sr) -> begin
(

let uu____743 = uu____727
in (

let uu____750 = (enlarge ((sl), (sr)) ((ln_l), (ln_r)))
in (

let uu____756 = (enlarge_row fmt_tl ln_tl row_tl)
in (uu____750)::uu____756)))
end))
end
| uu____761 -> begin
[]
end))
in (

let lines = (

let uu____786 = (FStar_List.map (enlarge_row fmt maxlength_list) tab)
in (FStar_All.pipe_right uu____786 (FStar_List.map (fun l -> (FStar_String.concat "  " l)))))
in (

let totallength1 = (FStar_List.fold_left (fun x s -> (max1 x (FStar_String.length s))) (Prims.parse_int "0") lines)
in (

let uu____827 = (FStar_All.pipe_right lines (FStar_String.concat "\n"))
in ((uu____827), (totallength1)))))))))))))))

type query_info =
{query_info_name : Prims.string; query_info_index : Prims.int; query_info_range : FStar_Range.range}


let __proj__Mkquery_info__item__query_info_name : query_info  ->  Prims.string = (fun projectee -> (match (projectee) with
| {query_info_name = query_info_name; query_info_index = query_info_index; query_info_range = query_info_range} -> begin
query_info_name
end))


let __proj__Mkquery_info__item__query_info_index : query_info  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_info_name = query_info_name; query_info_index = query_info_index; query_info_range = query_info_range} -> begin
query_info_index
end))


let __proj__Mkquery_info__item__query_info_range : query_info  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {query_info_name = query_info_name; query_info_index = query_info_index; query_info_range = query_info_range} -> begin
query_info_range
end))


type qiprofile_map =
(Prims.int * Prims.int * Prims.int) FStar_Util.psmap

type quantifier_info =
{quantifier_info_query : query_info; quantifier_info_quantifier : FStar_SMTEncoding_Term.term; quantifier_info_context : FStar_SMTEncoding_Term.term}


let __proj__Mkquantifier_info__item__quantifier_info_query : quantifier_info  ->  query_info = (fun projectee -> (match (projectee) with
| {quantifier_info_query = quantifier_info_query; quantifier_info_quantifier = quantifier_info_quantifier; quantifier_info_context = quantifier_info_context} -> begin
quantifier_info_query
end))


let __proj__Mkquantifier_info__item__quantifier_info_quantifier : quantifier_info  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {quantifier_info_query = quantifier_info_query; quantifier_info_quantifier = quantifier_info_quantifier; quantifier_info_context = quantifier_info_context} -> begin
quantifier_info_quantifier
end))


let __proj__Mkquantifier_info__item__quantifier_info_context : quantifier_info  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {quantifier_info_query = quantifier_info_query; quantifier_info_quantifier = quantifier_info_quantifier; quantifier_info_context = quantifier_info_context} -> begin
quantifier_info_context
end))

type qiprofile =
{qiprofile_id : Prims.string; qiprofile_quantifiers : quantifier_info Prims.list; qiprofile_instances : Prims.int; qiprofile_generation : Prims.int; qiprofile_cost : Prims.int}


let __proj__Mkqiprofile__item__qiprofile_id : qiprofile  ->  Prims.string = (fun projectee -> (match (projectee) with
| {qiprofile_id = qiprofile_id; qiprofile_quantifiers = qiprofile_quantifiers; qiprofile_instances = qiprofile_instances; qiprofile_generation = qiprofile_generation; qiprofile_cost = qiprofile_cost} -> begin
qiprofile_id
end))


let __proj__Mkqiprofile__item__qiprofile_quantifiers : qiprofile  ->  quantifier_info Prims.list = (fun projectee -> (match (projectee) with
| {qiprofile_id = qiprofile_id; qiprofile_quantifiers = qiprofile_quantifiers; qiprofile_instances = qiprofile_instances; qiprofile_generation = qiprofile_generation; qiprofile_cost = qiprofile_cost} -> begin
qiprofile_quantifiers
end))


let __proj__Mkqiprofile__item__qiprofile_instances : qiprofile  ->  Prims.int = (fun projectee -> (match (projectee) with
| {qiprofile_id = qiprofile_id; qiprofile_quantifiers = qiprofile_quantifiers; qiprofile_instances = qiprofile_instances; qiprofile_generation = qiprofile_generation; qiprofile_cost = qiprofile_cost} -> begin
qiprofile_instances
end))


let __proj__Mkqiprofile__item__qiprofile_generation : qiprofile  ->  Prims.int = (fun projectee -> (match (projectee) with
| {qiprofile_id = qiprofile_id; qiprofile_quantifiers = qiprofile_quantifiers; qiprofile_instances = qiprofile_instances; qiprofile_generation = qiprofile_generation; qiprofile_cost = qiprofile_cost} -> begin
qiprofile_generation
end))


let __proj__Mkqiprofile__item__qiprofile_cost : qiprofile  ->  Prims.int = (fun projectee -> (match (projectee) with
| {qiprofile_id = qiprofile_id; qiprofile_quantifiers = qiprofile_quantifiers; qiprofile_instances = qiprofile_instances; qiprofile_generation = qiprofile_generation; qiprofile_cost = qiprofile_cost} -> begin
qiprofile_cost
end))


let query_name : query_info  ->  Prims.string = (fun q -> (

let fn = (FStar_Range.file_of_range q.query_info_range)
in (

let rg = (

let uu____1083 = ((Prims.op_Equality (FStar_String.length fn) (Prims.parse_int "0")) || (

let uu____1088 = (FStar_Util.char_at fn (Prims.parse_int "0"))
in (Prims.op_Equality uu____1088 60 (*<*))))
in (match (uu____1083) with
| true -> begin
""
end
| uu____1096 -> begin
(

let s1 = (

let uu____1100 = (FStar_All.pipe_right q.query_info_range FStar_Range.end_of_range)
in (FStar_All.pipe_right uu____1100 FStar_Range.string_of_pos))
in (

let s2 = (

let uu____1104 = (FStar_All.pipe_right q.query_info_range FStar_Range.end_of_range)
in (FStar_All.pipe_right uu____1104 FStar_Range.string_of_pos))
in (FStar_Util.format " (%s-%s)" ((s1)::(s2)::[]))))
end))
in (

let uu____1110 = (

let uu____1112 = (

let uu____1114 = (

let uu____1116 = (FStar_Util.string_of_int q.query_info_index)
in (Prims.strcat uu____1116 (Prims.strcat ") from " (Prims.strcat fn rg))))
in (Prims.strcat " , " uu____1114))
in (Prims.strcat q.query_info_name uu____1112))
in (Prims.strcat "(" uu____1110)))))


let quantifier_file : quantifier_info  ->  Prims.string = (fun q -> (FStar_Range.file_of_range q.quantifier_info_quantifier.FStar_SMTEncoding_Term.rng))


let quantifier_module : quantifier_info  ->  Prims.string = (fun q -> (

let fn = (quantifier_file q)
in (

let uu____1139 = ((Prims.op_Equality (FStar_String.length fn) (Prims.parse_int "0")) || (

let uu____1144 = (FStar_Util.char_at fn (Prims.parse_int "0"))
in (Prims.op_Equality uu____1144 60 (*<*))))
in (match (uu____1139) with
| true -> begin
fn
end
| uu____1151 -> begin
(FStar_Parser_Dep.module_name_of_file fn)
end))))


let quantifier_range : quantifier_info  ->  Prims.string = (fun q -> (

let fn = (quantifier_file q)
in (

let uu____1163 = ((Prims.op_Equality (FStar_String.length fn) (Prims.parse_int "0")) || (

let uu____1168 = (FStar_Util.char_at fn (Prims.parse_int "0"))
in (Prims.op_Equality uu____1168 60 (*<*))))
in (match (uu____1163) with
| true -> begin
""
end
| uu____1176 -> begin
(

let s1 = (

let uu____1180 = (FStar_All.pipe_right q.quantifier_info_quantifier.FStar_SMTEncoding_Term.rng FStar_Range.end_of_range)
in (FStar_All.pipe_right uu____1180 FStar_Range.string_of_pos))
in (

let s2 = (

let uu____1184 = (FStar_All.pipe_right q.quantifier_info_quantifier.FStar_SMTEncoding_Term.rng FStar_Range.end_of_range)
in (FStar_All.pipe_right uu____1184 FStar_Range.string_of_pos))
in (FStar_Util.format "(%s-%s)" ((s1)::(s2)::[]))))
end))))


let parse_qiprofile : Prims.string  ->  qiprofile_map = (fun s -> (

let parse_line = (fun line -> (match ((FStar_Util.starts_with line "[quantifier_instances]")) with
| true -> begin
(

let uu____1236 = (

let uu____1240 = (

let uu____1244 = (FStar_Util.substring_from line (Prims.parse_int "22"))
in (FStar_Util.split uu____1244 ":"))
in (FStar_All.pipe_right uu____1240 (FStar_List.map FStar_Util.trim_string)))
in (match (uu____1236) with
| (id1)::(inst1)::(gen1)::(cost)::[] -> begin
(

let uu____1283 = (

let uu____1296 = (FStar_Util.int_of_string inst1)
in (

let uu____1298 = (FStar_Util.int_of_string gen1)
in (

let uu____1300 = (FStar_Util.int_of_string cost)
in ((id1), (uu____1296), (uu____1298), (uu____1300)))))
in FStar_Pervasives_Native.Some (uu____1283))
end
| uu____1318 -> begin
(failwith "could not parse quantifier instantiation info")
end))
end
| uu____1337 -> begin
FStar_Pervasives_Native.None
end))
in (

let comp = (fun uu____1385 uu____1386 -> (match (((uu____1385), (uu____1386))) with
| ((qid1, inst1, gen1, cost1), (qid2, inst2, gen2, cost2)) -> begin
(FStar_Util.compare qid1 qid2)
end))
in (

let conflate = (fun l -> (

let rec aux = (fun qid inst1 gen1 cost l1 o -> (match (l1) with
| [] -> begin
(FStar_List.rev ((((qid), (inst1), (gen1), (cost)))::o))
end
| ((hd_qid, hd_inst, hd_gen, hd_cost))::tl1 -> begin
(match ((Prims.op_Equality hd_qid qid)) with
| true -> begin
(

let uu____1765 = (max gen1 hd_gen)
in (

let uu____1767 = (max cost hd_cost)
in (aux qid (inst1 + hd_inst) uu____1765 uu____1767 tl1 o)))
end
| uu____1769 -> begin
(aux hd_qid hd_inst hd_gen hd_cost tl1 ((((qid), (inst1), (gen1), (cost)))::o))
end)
end))
in (match (l) with
| [] -> begin
[]
end
| ((qid, inst1, gen1, cost))::tl1 -> begin
(aux qid inst1 gen1 cost l [])
end)))
in (

let add1 = (fun o uu____1898 -> (match (uu____1898) with
| (qid, inst1, gen1, cost) -> begin
(FStar_Util.psmap_add o qid ((inst1), (gen1), (cost)))
end))
in (

let uu____1935 = (

let uu____1950 = (

let uu____1965 = (

let uu____1980 = (

let uu____1997 = (FStar_All.pipe_right (FStar_String.split ((10)::[]) s) (FStar_List.map FStar_Util.trim_string))
in (FStar_All.pipe_right uu____1997 (FStar_List.map parse_line)))
in (FStar_All.pipe_right uu____1980 FStar_Util.collect_some))
in (FStar_All.pipe_right uu____1965 (FStar_Util.sort_with comp)))
in (FStar_All.pipe_right uu____1950 conflate))
in (

let uu____2156 = (

let uu____2175 = (FStar_Util.psmap_empty ())
in (FStar_List.fold_left add1 uu____2175))
in (FStar_All.pipe_right uu____1935 uu____2156))))))))


let rec extract_quantifiers_from_decls : query_info  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.string * quantifier_info) Prims.list = (fun query decl -> (

let from_term = (fun context tm0 -> (

let rec aux = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____2298, tms) -> begin
(

let uu____2304 = (FStar_List.map aux tms)
in (FStar_List.flatten uu____2304))
end
| FStar_SMTEncoding_Term.Quant (uu____2326, uu____2327, uu____2328, uu____2329, t, qid) -> begin
(

let uu____2356 = (FStar_ST.op_Bang qid)
in (match (uu____2356) with
| FStar_Pervasives_Native.Some (id1) -> begin
(

let uu____2417 = (aux t)
in (((id1), ({quantifier_info_query = query; quantifier_info_quantifier = tm; quantifier_info_context = context})))::uu____2417)
end
| FStar_Pervasives_Native.None -> begin
(failwith "No QID found")
end))
end
| FStar_SMTEncoding_Term.Let (tms, t) -> begin
(

let uu____2446 = (aux t)
in (

let uu____2454 = (FStar_List.collect aux tms)
in (FStar_List.append uu____2446 uu____2454)))
end
| FStar_SMTEncoding_Term.Labeled (t, uu____2473, uu____2474) -> begin
(aux t)
end
| FStar_SMTEncoding_Term.LblPos (t, uu____2478) -> begin
(aux t)
end
| uu____2481 -> begin
[]
end))
in (aux tm0)))
in (match (decl) with
| FStar_SMTEncoding_Term.DefineFun (nm, args, ret1, tm, uu____2498) -> begin
(from_term tm tm)
end
| FStar_SMTEncoding_Term.Assume (a) -> begin
(from_term a.FStar_SMTEncoding_Term.assumption_term a.FStar_SMTEncoding_Term.assumption_term)
end
| FStar_SMTEncoding_Term.Module (s, ds) -> begin
(extract_quantifiers ((query), (ds)))
end
| uu____2516 -> begin
[]
end)))
and extract_quantifiers : (query_info * FStar_SMTEncoding_Term.decl Prims.list)  ->  (Prims.string * quantifier_info) Prims.list = (fun uu____2522 -> (match (uu____2522) with
| (query, decls) -> begin
(FStar_List.fold_left (fun l d -> (

let uu____2568 = (extract_quantifiers_from_decls query d)
in (FStar_List.append uu____2568 l))) [] decls)
end))


let profile_quantifiers : (query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list  ->  Prims.string  ->  qiprofile FStar_Util.psmap = (fun queries qiprofile_output -> (

let comp = (fun uu____2639 uu____2640 -> (match (((uu____2639), (uu____2640))) with
| ((id1, q1), (id2, q2)) -> begin
(FStar_Util.compare id1 id2)
end))
in (

let conflate = (fun l -> (

let rec aux = (fun i id1 ls o -> (match (i) with
| ((idx, qinfo))::tl1 -> begin
(match ((Prims.op_Equality id1 idx)) with
| true -> begin
(aux tl1 id1 ((qinfo)::ls) o)
end
| uu____2824 -> begin
(aux tl1 idx ((qinfo)::[]) ((((id1), ((FStar_List.rev ls))))::o))
end)
end
| [] -> begin
(((id1), ((FStar_List.rev ls))))::o
end))
in (match (l) with
| [] -> begin
[]
end
| ((s, q))::tl1 -> begin
(

let uu____2889 = (aux tl1 s ((q)::[]) [])
in (FStar_List.rev uu____2889))
end)))
in (

let remove_duplicates = (fun l -> (

let equal_range = (fun q1 q2 -> ((

let uu____2944 = (quantifier_file q1)
in (

let uu____2946 = (quantifier_file q2)
in (Prims.op_Equality uu____2944 uu____2946))) && (

let uu____2951 = (quantifier_range q1)
in (

let uu____2953 = (quantifier_range q2)
in (Prims.op_Equality uu____2951 uu____2953)))))
in (

let rec rm = (fun q i o -> (match (i) with
| (hd1)::tl1 -> begin
(

let uu____2988 = (

let uu____2991 = (equal_range hd1 q)
in (match (uu____2991) with
| true -> begin
o
end
| uu____2996 -> begin
(hd1)::o
end))
in (rm q tl1 uu____2988))
end
| [] -> begin
(FStar_List.rev o)
end))
in (

let rec aux = (fun i o -> (match (i) with
| (hd1)::tl1 -> begin
(

let uu____3025 = (rm hd1 i [])
in (aux uu____3025 ((hd1)::o)))
end
| [] -> begin
(FStar_List.rev o)
end))
in (aux l [])))))
in (

let qip = (parse_qiprofile qiprofile_output)
in (

let insert = (fun o uu____3050 -> (match (uu____3050) with
| (id1, info) -> begin
(

let uu____3072 = (

let uu____3082 = (FStar_Util.psmap_try_find qip id1)
in (match (uu____3082) with
| FStar_Pervasives_Native.None -> begin
(((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end))
in (match (uu____3072) with
| (inst1, gen1, cost) -> begin
(

let uu____3157 = uu____3072
in (

let value = {qiprofile_id = id1; qiprofile_quantifiers = info; qiprofile_instances = inst1; qiprofile_generation = gen1; qiprofile_cost = cost}
in (FStar_Util.psmap_add o id1 value)))
end))
end))
in (

let uu____3168 = (

let uu____3178 = (

let uu____3188 = (

let uu____3196 = (FStar_List.collect extract_quantifiers queries)
in (FStar_All.pipe_right uu____3196 (FStar_Util.sort_with comp)))
in (FStar_All.pipe_right uu____3188 conflate))
in (FStar_All.pipe_right uu____3178 (FStar_List.map (fun uu____3286 -> (match (uu____3286) with
| (s, q) -> begin
(

let uu____3309 = (remove_duplicates q)
in ((s), (uu____3309)))
end)))))
in (

let uu____3315 = (

let uu____3331 = (FStar_Util.psmap_empty ())
in (FStar_List.fold_left insert uu____3331))
in (FStar_All.pipe_right uu____3168 uu____3315)))))))))


let tabular_profile : qiprofile FStar_Util.psmap  ->  Prims.string Prims.list Prims.list = (fun q -> (

let comp = (fun uu____3396 uu____3397 -> (match (((uu____3396), (uu____3397))) with
| ((i1, q1), (i2, q2)) -> begin
(match ((i1 < i2)) with
| true -> begin
(Prims.parse_int "1")
end
| uu____3451 -> begin
(match ((i1 > i2)) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____3456 -> begin
(Prims.parse_int "0")
end)
end)
end))
in (

let qid_to_tail_rows = (fun info -> (

let uu____3471 = (

let uu____3475 = (

let uu____3479 = (quantifier_module info)
in (

let uu____3481 = (

let uu____3485 = (quantifier_file info)
in (

let uu____3487 = (

let uu____3491 = (quantifier_range info)
in (uu____3491)::[])
in (uu____3485)::uu____3487))
in (uu____3479)::uu____3481))
in ("")::uu____3475)
in ("")::uu____3471))
in (

let qid_to_rows = (fun o k -> (

let prof = (

let uu____3535 = (FStar_Util.psmap_try_find q k)
in (FStar_Util.must uu____3535))
in (match ((prof.qiprofile_instances > (Prims.parse_int "0"))) with
| true -> begin
(match (prof.qiprofile_quantifiers) with
| [] -> begin
(failwith "QID not found")
end
| (hd1)::tl1 -> begin
(

let uu____3560 = (

let uu____3566 = (

let uu____3570 = (

let uu____3574 = (FStar_Util.string_of_int prof.qiprofile_instances)
in (

let uu____3576 = (

let uu____3580 = (quantifier_module hd1)
in (

let uu____3582 = (

let uu____3586 = (quantifier_file hd1)
in (

let uu____3588 = (

let uu____3592 = (quantifier_range hd1)
in (uu____3592)::[])
in (uu____3586)::uu____3588))
in (uu____3580)::uu____3582))
in (uu____3574)::uu____3576))
in (prof.qiprofile_id)::uu____3570)
in (

let uu____3600 = (FStar_List.map qid_to_tail_rows tl1)
in (uu____3566)::uu____3600))
in (FStar_List.append o uu____3560))
end)
end
| uu____3615 -> begin
o
end)))
in (

let uu____3617 = (

let uu____3621 = (

let uu____3630 = (FStar_Util.psmap_fold q (fun k v1 acc -> (((v1.qiprofile_instances), (k)))::acc) [])
in (FStar_All.pipe_right uu____3630 (FStar_Util.sort_with comp)))
in (FStar_All.pipe_right uu____3621 (FStar_List.map (fun uu____3719 -> (match (uu____3719) with
| (i, q1) -> begin
q1
end)))))
in (FStar_All.pipe_right uu____3617 (FStar_List.fold_left qid_to_rows [])))))))


let qiprofile_analysis : (query_info * FStar_SMTEncoding_Term.decls_t) Prims.list  ->  Prims.string  ->  unit = (fun queries qiprofile_output -> (match (queries) with
| [] -> begin
()
end
| uu____3783 -> begin
(

let q = (profile_quantifiers queries qiprofile_output)
in (

let tab = (tabular_profile q)
in (

let fmt = (PrettyRight)::(PrettyRight)::(PrettyLeft)::(PrettyRight)::(PrettyLeft)::[]
in (

let uu____3804 = (prettyprint_table fmt tab)
in (match (uu____3804) with
| (content_string, content_length) -> begin
(

let uu____3817 = uu____3804
in (

let uu____3824 = (

let headers = (FStar_All.pipe_right queries (FStar_List.map (fun uu____3856 -> (match (uu____3856) with
| (q1, ds) -> begin
(query_name q1)
end))))
in (

let uu____3870 = (FStar_List.fold_left (fun x s -> (max x (FStar_String.length s))) (Prims.parse_int "0") headers)
in (((FStar_String.concat "\n" headers)), (uu____3870))))
in (match (uu____3824) with
| (header_string, header_length) -> begin
(

let uu____3890 = uu____3824
in (

let line = (

let uu____3899 = (max content_length header_length)
in (FStar_Util.repeat uu____3899 "-"))
in (FStar_Util.print (Prims.strcat line (Prims.strcat "\n" (Prims.strcat header_string (Prims.strcat "\n" (Prims.strcat line (Prims.strcat "\n" (Prims.strcat content_string (Prims.strcat "\n" (Prims.strcat line "\n\n"))))))))) [])))
end)))
end)))))
end))




