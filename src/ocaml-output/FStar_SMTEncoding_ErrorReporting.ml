
open Prims
open FStar_Pervasives
exception Not_a_wp_implication of (Prims.string)


let uu___is_Not_a_wp_implication : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____13) -> begin
true
end
| uu____16 -> begin
false
end))


let __proj__Not_a_wp_implication__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____27) -> begin
uu____27
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____85 uu____86 -> (match (((uu____85), (uu____86))) with
| (((uu____136, uu____137, r1), uu____139), ((uu____140, uu____141, r2), uu____143)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____220 uu____221 -> (match (((uu____220), (uu____221))) with
| ((uu____251, m1, r1), (uu____254, m2, r2)) -> begin
((Prims.op_Equality r1 r2) && (Prims.op_Equality m1 m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string FStar_Pervasives_Native.option * FStar_Range.range) Prims.list


let fresh_label : Prims.string  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun message range t -> (

let l = ((FStar_Util.incr ctr);
(

let uu____354 = (

let uu____356 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____356))
in (FStar_Util.format1 "label_%s" uu____354));
)
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt1 = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt1)))))))))


let label_goals : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (labels * FStar_SMTEncoding_Term.term) = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (FStar_Pervasives_Native.None, uu____477) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____485)) -> begin
(Prims.op_Equality nm nm')
end
| (uu____494, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____505, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____507)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____519 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____543 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____553; FStar_SMTEncoding_Term.rng = uu____554})::[])::[], iopt, uu____556, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____559; FStar_SMTEncoding_Term.rng = uu____560}, uu____561) -> begin
true
end
| uu____610 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____622 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____652 = (f ())
in ((true), (uu____652)))
end)
in (match (uu____622) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " (Prims.strcat msg_prefix (Prims.strcat " :: " msg)))
end
| uu____704 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu____708 = (

let uu____710 = (FStar_Range.use_range rng)
in (

let uu____711 = (FStar_Range.use_range r1)
in (FStar_Range.rng_included uu____710 uu____711)))
in (match (uu____708) with
| true -> begin
rng
end
| uu____713 -> begin
(

let uu____715 = (FStar_Range.def_range rng)
in (FStar_Range.set_def_range r1 uu____715))
end))
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____770) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____774) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____778) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____792) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in (FStar_All.try_with (fun uu___270_839 -> (match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____858; FStar_SMTEncoding_Term.rng = rng}, uu____860) -> begin
(

let post_name = (

let uu____898 = (

let uu____900 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____900))
in (Prims.strcat "^^post_condition_" uu____898))
in (

let names1 = (

let uu____913 = (FStar_List.map (fun s -> (

let uu____929 = (

let uu____931 = (

let uu____933 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____933))
in (Prims.strcat "^^" uu____931))
in ((uu____929), (s)))) sorts)
in (((post_name), (post)))::uu____913)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____953 = (

let uu____958 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____959 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____958), (uu____959))))
in (match (uu____953) with
| (lhs1, rhs1) -> begin
(

let uu____968 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____986 = (FStar_Util.prefix clauses_lhs)
in (match (uu____986) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____1016; FStar_SMTEncoding_Term.rng = rng_ens}, uu____1018) -> begin
(

let uu____1054 = (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1)
in (match (uu____1054) with
| true -> begin
(

let uu____1064 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____1064) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____1108 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____1114 = (

let uu____1115 = (

let uu____1140 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in (

let uu____1143 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____1140), (uu____1143))))
in FStar_SMTEncoding_Term.Quant (uu____1115))
in (FStar_SMTEncoding_Term.mk uu____1114 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____1188 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____1188))))))
end))
end
| uu____1191 -> begin
(

let uu____1193 = (

let uu____1194 = (

let uu____1196 = (

let uu____1198 = (

let uu____1200 = (FStar_SMTEncoding_Term.print_smt_term post1)
in (Prims.strcat "  ... " uu____1200))
in (Prims.strcat post_name uu____1198))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____1196))
in Not_a_wp_implication (uu____1194))
in (FStar_Exn.raise uu____1193))
end))
end
| uu____1210 -> begin
(

let uu____1211 = (

let uu____1212 = (

let uu____1214 = (

let uu____1216 = (

let uu____1218 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____1218))
in (Prims.strcat post_name uu____1216))
in (Prims.strcat "Ensures clause doesn\'t have the expected shape for post-condition " uu____1214))
in Not_a_wp_implication (uu____1212))
in (FStar_Exn.raise uu____1211))
end)
end))
end
| uu____1228 -> begin
(

let uu____1229 = (

let uu____1230 = (

let uu____1232 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____1232))
in Not_a_wp_implication (uu____1230))
in (FStar_Exn.raise uu____1229))
end)
in (match (uu____968) with
| (labels1, lhs2) -> begin
(

let uu____1253 = (

let uu____1260 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1260) with
| (labels2, rhs2) -> begin
(

let uu____1280 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____1280)))
end))
in (match (uu____1253) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____1296 = (

let uu____1297 = (

let uu____1298 = (

let uu____1323 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body), (uu____1323)))
in FStar_SMTEncoding_Term.Quant (uu____1298))
in (FStar_SMTEncoding_Term.mk uu____1297 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1296))))
end))
end))
end)))))
end
| uu____1367 -> begin
(

let uu____1368 = (

let uu____1370 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____1370))
in (fallback uu____1368))
end)
end)) (fun uu___269_1375 -> (match (uu___269_1375) with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end))))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____1392; FStar_SMTEncoding_Term.rng = rng}, uu____1394) when (is_a_named_continuation lhs) -> begin
(

let uu____1426 = (FStar_Util.prefix sorts)
in (match (uu____1426) with
| (sorts', post) -> begin
(

let new_post_name = (

let uu____1447 = (

let uu____1449 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1449))
in (Prims.strcat "^^post_condition_" uu____1447))
in (

let names1 = (

let uu____1462 = (FStar_List.map (fun s -> (

let uu____1478 = (

let uu____1480 = (

let uu____1482 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1482))
in (Prims.strcat "^^" uu____1480))
in ((uu____1478), (s)))) sorts')
in (FStar_List.append uu____1462 ((((new_post_name), (post)))::[])))
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____1512 = (

let uu____1517 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1518 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1517), (uu____1518))))
in (match (uu____1512) with
| (lhs1, rhs1) -> begin
(

let uu____1527 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1566; FStar_SMTEncoding_Term.rng = uu____1567})::[])::[], iopt, sorts1, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l0)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1572; FStar_SMTEncoding_Term.rng = uu____1573}, uu____1574) -> begin
(

let uu____1622 = (is_a_post_condition (FStar_Pervasives_Native.Some (new_post_name)) r1)
in (match (uu____1622) with
| true -> begin
(

let uu____1632 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 l0)
in (match (uu____1632) with
| (labels2, l) -> begin
(

let uu____1651 = (

let uu____1652 = (

let uu____1653 = (

let uu____1678 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((l)::(r1)::[])))))
in (

let uu____1681 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts1), (uu____1678), (uu____1681))))
in FStar_SMTEncoding_Term.Quant (uu____1653))
in (FStar_SMTEncoding_Term.mk uu____1652 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1651)))
end))
end
| uu____1731 -> begin
((labels1), (tm))
end))
end
| uu____1735 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1527) with
| (labels1, lhs_conjs) -> begin
(

let uu____1754 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (new_post_name)) labels1 rhs1)
in (match (uu____1754) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1775 = (

let uu____1776 = (

let uu____1781 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1781), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1776 rng))
in (FStar_All.pipe_right uu____1775 (FStar_SMTEncoding_Term.abstr names1)))
in (

let q2 = (

let uu____1783 = (

let uu____1784 = (

let uu____1809 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), (sorts), (body), (uu____1809)))
in FStar_SMTEncoding_Term.Quant (uu____1784))
in (FStar_SMTEncoding_Term.mk uu____1783 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (q2))))
end))
end))
end)))))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1860 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1860) with
| (labels1, rhs1) -> begin
(

let uu____1879 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1879)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1887 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1887) with
| (labels1, conjuncts2) -> begin
(

let uu____1914 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1914)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1922 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1922) with
| (labels1, q12) -> begin
(

let uu____1941 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1941) with
| (labels2, q21) -> begin
(

let uu____1960 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1960)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1963, uu____1964, uu____1965, uu____1966, uu____1967) -> begin
(

let uu____1992 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1992) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____2007) -> begin
(

let uu____2012 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2012) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____2027) -> begin
(

let uu____2032 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2032) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____2047), uu____2048) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____2056) -> begin
(

let uu____2062 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2062) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____2077) -> begin
(

let uu____2082 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2082) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____2097) -> begin
(

let uu____2102 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2102) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____2117) -> begin
(

let uu____2122 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2122) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____2137) -> begin
(

let uu____2142 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2142) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____2157) -> begin
(

let uu____2162 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2162) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____2177) -> begin
(

let uu____2182 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2182) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____2197) -> begin
(

let uu____2202 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2202) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____2217) -> begin
(

let uu____2222 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2222) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____2237) -> begin
(

let uu____2242 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2242) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____2257), uu____2258) -> begin
(

let uu____2264 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2264) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____2279) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____2291) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____2303) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____2315) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____2327) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____2339) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____2351) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____2363) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____2375) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAdd, uu____2387) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvSub, uu____2399) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____2411) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____2423) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____2435) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____2447) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____2459) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____2471), uu____2472) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____2485) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____2497), uu____2498) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____2511) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____2523) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body, uu____2539) -> begin
(

let uu____2564 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2564) with
| (labels1, body1) -> begin
(

let uu____2583 = (

let uu____2584 = (

let uu____2585 = (

let uu____2610 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1), (uu____2610)))
in FStar_SMTEncoding_Term.Quant (uu____2585))
in (FStar_SMTEncoding_Term.mk uu____2584 q1.FStar_SMTEncoding_Term.rng))
in ((labels1), (uu____2583)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____2660 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2660) with
| (labels1, body1) -> begin
(

let uu____2679 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2679)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Z3.z3result)  ->  unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____2719 -> (

let msg = (

let uu____2722 = (

let uu____2724 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____2724))
in (

let uu____2725 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____2728 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____2734 -> begin
"error"
end) uu____2722 uu____2725 uu____2728))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____2754 -> (match (uu____2754) with
| ((uu____2767, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2783 = (FStar_Range.string_of_range r)
in (FStar_Util.print1 "OK: proof obligation at %s was proven in isolation\n" uu____2783))
end
| uu____2786 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Warning_HintFailedToReplayProof), ((Prims.strcat "Hint failed to replay this sub-proof: " msg))))
end
| uu____2791 -> begin
(

let uu____2793 = (

let uu____2799 = (

let uu____2801 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "XX: proof obligation at %s failed\n\t%s\n" uu____2801 msg))
in ((FStar_Errors.Error_ProofObligationFailed), (uu____2799)))
in (FStar_Errors.log_issue r uu____2793))
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2874 -> (match (uu____2874) with
| (l, uu____2888, uu____2889) -> begin
(

let a = (

let uu____2903 = (

let uu____2904 = (

let uu____2909 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2909), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2904))
in {FStar_SMTEncoding_Term.assumption_term = uu____2903; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2979 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2996 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2979 uu____2996)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____3023 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____3023));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let result = (askZ3 decls)
in (match (result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____3056) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____3057 -> begin
(linear_check eliminated ((hd1)::errors) tl1)
end)));
)
end);
))
in ((print_banner ());
(FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))));
(

let res = (linear_check [] [] all_labels)
in ((FStar_Util.print_string "\n");
(FStar_All.pipe_right res (FStar_List.iter print_result));
(

let uu____3106 = (FStar_Util.for_all FStar_Pervasives_Native.snd res)
in (match (uu____3106) with
| true -> begin
(FStar_Util.print_string "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n")
end
| uu____3130 -> begin
()
end));
));
))))))




