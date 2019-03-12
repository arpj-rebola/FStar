
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____38 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___149_62 -> (match (uu___149_62) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____84 = (FStar_Options.debug_any ())
in (match (uu____84) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____90 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____93 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____99)::q -> begin
(aux q)
end
| uu____106 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____112 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____130 -> (

let run_proc_result = (FStar_All.try_with (fun uu___154_147 -> (match (()) with
| () -> begin
(

let uu____151 = (

let uu____153 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____153 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____151))
end)) (fun uu___153_162 -> FStar_Pervasives_Native.None))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (out) -> begin
(

let uu____185 = (parse_z3_version_lines out)
in (match (uu____185) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : unit  ->  unit = (fun uu____216 -> (

let uu____217 = (

let uu____219 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____219)))
in (match (uu____217) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____266 = (z3hash_warning_message ())
in (match (uu____266) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (e, msg) -> begin
(

let msg1 = (FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg "Please download the version of Z3 corresponding to your platform from:" _z3url "and add the bin/ subdirectory into your PATH")
in (FStar_Errors.log_issue FStar_Range.dummyRange ((e), (msg1))))
end));
)
end
| uu____294 -> begin
()
end)))


let ini_params : unit  ->  Prims.string Prims.list = (fun uu____304 -> ((check_z3hash ());
(

let args = (

let uu____313 = (

let uu____317 = (

let uu____321 = (

let uu____323 = (

let uu____325 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____325))
in (FStar_Util.format1 "smt.random_seed=%s" uu____323))
in (uu____321)::[])
in ("-in")::uu____317)
in ("-smt2")::uu____313)
in (

let opts = (FStar_Options.z3_cliopt ())
in (

let qi = (

let uu____342 = (FStar_Options.report_qi ())
in (match (uu____342) with
| true -> begin
("smt.qi.profile=true")::[]
end
| uu____351 -> begin
[]
end))
in (

let proof = (

let uu____358 = (FStar_Options.smt_proof ())
in (match (uu____358) with
| true -> begin
("proof=true")::[]
end
| uu____367 -> begin
[]
end))
in (FStar_List.append args (FStar_List.append opts (FStar_List.append qi proof)))))));
))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list FStar_Pervasives_Native.option


type refutation =
Prims.string Prims.list FStar_Pervasives_Native.option

type z3status =
| UNSAT of (unsat_core * refutation)
| SAT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| UNKNOWN of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| TIMEOUT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| KILLED


let uu___is_UNSAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
true
end
| uu____445 -> begin
false
end))


let __proj__UNSAT__item___0 : z3status  ->  (unsat_core * refutation) = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
_0
end))


let uu___is_SAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
true
end
| uu____484 -> begin
false
end))


let __proj__SAT__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
_0
end))


let uu___is_UNKNOWN : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
true
end
| uu____532 -> begin
false
end))


let __proj__UNKNOWN__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
_0
end))


let uu___is_TIMEOUT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
true
end
| uu____580 -> begin
false
end))


let __proj__TIMEOUT__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
_0
end))


let uu___is_KILLED : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| KILLED -> begin
true
end
| uu____620 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___150_631 -> (match (uu___150_631) with
| SAT (uu____633) -> begin
"sat"
end
| UNSAT (uu____642) -> begin
"unsat"
end
| UNKNOWN (uu____648) -> begin
"unknown"
end
| TIMEOUT (uu____657) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(

let uu____685 = (status_tag s)
in ((uu____685), ([])))
end
| UNSAT (uu____690) -> begin
(

let uu____695 = (status_tag s)
in ((uu____695), ([])))
end
| SAT (errs, msg) -> begin
(

let uu____708 = (

let uu____710 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____710 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____708), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____731 = (

let uu____733 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____733 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____731), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____754 = (

let uu____756 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____756 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____754), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____775 -> (

let uu____777 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____777 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let filter1 = (

let uu____796 = (FStar_Options.report_qi ())
in (match (uu____796) with
| true -> begin
(fun s -> (not ((FStar_Util.starts_with s "[quantifier_instances]"))))
end
| uu____807 -> begin
(fun s -> true)
end))
in (

let uu____812 = (FStar_Options.z3_exe ())
in (

let uu____814 = (ini_params ())
in (FStar_Util.start_process id1 uu____812 uu____814 (fun s -> (Prims.op_Equality s "Done!")) filter1)))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  Prims.string; restart : unit  ->  unit; kill : unit  ->  Prims.string; store : FStar_SMTEncoding_Analysis.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit; extract : unit  ->  (FStar_SMTEncoding_Analysis.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
restart
end))


let __proj__Mkbgproc__item__kill : bgproc  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
kill
end))


let __proj__Mkbgproc__item__store : bgproc  ->  FStar_SMTEncoding_Analysis.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
store
end))


let __proj__Mkbgproc__item__extract : bgproc  ->  unit  ->  (FStar_SMTEncoding_Analysis.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
extract
end))

type query_log =
{get_module_name : unit  ->  Prims.string; set_module_name : Prims.string  ->  unit; write_to_log : Prims.string  ->  unit; close_log : unit  ->  unit; log_file_name : unit  ->  Prims.string}


let __proj__Mkquery_log__item__get_module_name : query_log  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name} -> begin
get_module_name
end))


let __proj__Mkquery_log__item__set_module_name : query_log  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name} -> begin
set_module_name
end))


let __proj__Mkquery_log__item__write_to_log : query_log  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name} -> begin
write_to_log
end))


let __proj__Mkquery_log__item__close_log : query_log  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name} -> begin
close_log
end))


let __proj__Mkquery_log__item__log_file_name : query_log  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name} -> begin
log_file_name
end))


let query_logging : query_log = (

let query_number = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let log_file_opt = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let current_file_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_module_name = (fun n1 -> (FStar_ST.op_Colon_Equals current_module_name (FStar_Pervasives_Native.Some (n1))))
in (

let get_module_name = (fun uu____1629 -> (

let uu____1631 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1631) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1694 -> (

let uu____1695 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1695) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1753 = (

let uu____1762 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1837 -> (match (uu____1837) with
| (m, uu____1846) -> begin
(Prims.op_Equality n1 m)
end)) uu____1762))
in (match (uu____1753) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1860 = (

let uu____1869 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1869)
in (FStar_ST.op_Colon_Equals used_file_names uu____1860));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____2001, k) -> begin
((

let uu____2014 = (

let uu____2023 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____2023)
in (FStar_ST.op_Colon_Equals used_file_names uu____2014));
(

let uu____2155 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____2155));
)
end))
in (

let file_name1 = (FStar_Util.format1 "queries-%s.smt2" file_name)
in ((FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (file_name1)));
(

let fh = (FStar_Util.open_file_for_writing file_name1)
in ((FStar_ST.op_Colon_Equals log_file_opt (FStar_Pervasives_Native.Some (fh)));
fh;
));
)))
end)))
in (

let get_log_file = (fun uu____2263 -> (

let uu____2264 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2264) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2321 = (get_log_file ())
in (FStar_Util.append_to_file uu____2321 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2332 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2332) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2387 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2387) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_Util.format1 "queries-%s" n1)
end))
in ((FStar_Util.mkdir true dir_name);
(FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (dir_name)));
dir_name;
))
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end))
in (

let qnum = (FStar_ST.op_Bang query_number)
in ((

let uu____2546 = (

let uu____2548 = (FStar_ST.op_Bang query_number)
in (uu____2548 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2546));
(

let file_name = (

let uu____2639 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2639))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2652 = (

let uu____2654 = (FStar_Options.n_cores ())
in (uu____2654 > (Prims.parse_int "1")))
in (match (uu____2652) with
| true -> begin
(write_to_new_log str)
end
| uu____2658 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2665 -> (

let uu____2666 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2666) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2767 -> (

let uu____2769 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2769) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))))))


let bg_z3_proc : bgproc FStar_ST.ref = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let the_queries = (FStar_Util.mk_ref [])
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____2884 -> (

let uu____2885 = (

let uu____2887 = ((FStar_Util.incr ctr);
(

let uu____2923 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2923 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2887))
in (new_z3proc uu____2885))))
in (

let z3proc = (fun uu____2976 -> ((

let uu____2978 = (

let uu____2980 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2980 FStar_Pervasives_Native.None))
in (match (uu____2978) with
| true -> begin
((

let uu____3032 = (

let uu____3035 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3035))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3032));
(FStar_ST.op_Colon_Equals the_queries []);
)
end
| uu____3144 -> begin
()
end));
(

let uu____3146 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____3146));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____3213 -> "\nkilled\n")
in (

let uu____3215 = (z3proc ())
in (FStar_Util.ask_process uu____3215 input kill_handler))))
in (

let refresh = (fun uu____3222 -> (

let extra = (

let uu____3226 = (z3proc ())
in (FStar_Util.kill_process uu____3226))
in ((

let uu____3228 = (

let uu____3231 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3231))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3228));
(FStar_ST.op_Colon_Equals the_queries []);
(query_logging.close_log ());
extra;
)))
in (

let kill = (fun uu____3348 -> (

let uu____3350 = (

let uu____3352 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.is_some uu____3352))
in (match (uu____3350) with
| true -> begin
(

let extra = (

let uu____3404 = (z3proc ())
in (FStar_Util.kill_process uu____3404))
in ((FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_queries []);
extra;
))
end
| uu____3516 -> begin
""
end)))
in (

let restart = (fun uu____3524 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____3572 = (

let uu____3575 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3575))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3572));
))
in (

let store = (fun info decls -> (

let uu____3636 = (

let uu____3645 = (FStar_ST.op_Bang the_queries)
in (FStar_List.append uu____3645 ((((info), (decls)))::[])))
in (FStar_ST.op_Colon_Equals the_queries uu____3636)))
in (

let extract = (fun uu____3801 -> (FStar_ST.op_Bang the_queries))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart); kill = (FStar_Util.with_monitor x kill); store = store; extract = extract}))))))))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


let at_log_file : unit  ->  Prims.string = (fun uu____3910 -> (

let uu____3912 = (FStar_Options.log_queries ())
in (match (uu____3912) with
| true -> begin
(

let uu____3916 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____3916))
end
| uu____3919 -> begin
""
end)))


type smt_output_section =
Prims.string Prims.list

type smt_output =
{smt_result : smt_output_section; smt_reason_unknown : smt_output_section FStar_Pervasives_Native.option; smt_unsat_core : smt_output_section FStar_Pervasives_Native.option; smt_statistics : smt_output_section FStar_Pervasives_Native.option; smt_labels : smt_output_section FStar_Pervasives_Native.option; smt_refutation : smt_output_section FStar_Pervasives_Native.option}


let __proj__Mksmt_output__item__smt_result : smt_output  ->  smt_output_section = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_result
end))


let __proj__Mksmt_output__item__smt_reason_unknown : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_reason_unknown
end))


let __proj__Mksmt_output__item__smt_unsat_core : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_unsat_core
end))


let __proj__Mksmt_output__item__smt_statistics : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_statistics
end))


let __proj__Mksmt_output__item__smt_labels : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_labels
end))


let __proj__Mksmt_output__item__smt_refutation : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation} -> begin
smt_refutation
end))


let smt_output_sections : FStar_Range.range  ->  Prims.string Prims.list  ->  smt_output = (fun r lines -> (

let rec until = (fun tag lines1 -> (match (lines1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (l)::lines2 -> begin
(match ((Prims.op_Equality tag l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines2)))
end
| uu____4226 -> begin
(

let uu____4228 = (until tag lines2)
in (FStar_Util.map_opt uu____4228 (fun uu____4264 -> (match (uu____4264) with
| (until_tag, rest) -> begin
(((l)::until_tag), (rest))
end))))
end)
end))
in (

let start_tag = (fun tag -> (Prims.strcat "<" (Prims.strcat tag ">")))
in (

let end_tag = (fun tag -> (Prims.strcat "</" (Prims.strcat tag ">")))
in (

let find_section = (fun tag lines1 -> (

let uu____4371 = (until (start_tag tag) lines1)
in (match (uu____4371) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____4441 = (until (end_tag tag) suffix)
in (match (uu____4441) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____4526 = (find_section "result" lines)
in (match (uu____4526) with
| (result_opt, lines1) -> begin
(

let uu____4549 = uu____4526
in (

let result = (FStar_Util.must result_opt)
in (

let uu____4560 = (find_section "reason-unknown" lines1)
in (match (uu____4560) with
| (reason_unknown, lines2) -> begin
(

let uu____4583 = uu____4560
in (

let uu____4593 = (find_section "unsat-core" lines2)
in (match (uu____4593) with
| (unsat_core, lines3) -> begin
(

let uu____4616 = uu____4593
in (

let uu____4626 = (

let uu____4636 = (FStar_Options.smt_proof ())
in (match (uu____4636) with
| true -> begin
(find_section "proof" lines3)
end
| uu____4649 -> begin
((FStar_Pervasives_Native.None), (lines3))
end))
in (match (uu____4626) with
| (refutation, lines4) -> begin
(

let uu____4668 = uu____4626
in (

let uu____4678 = (find_section "statistics" lines4)
in (match (uu____4678) with
| (statistics, lines5) -> begin
(

let uu____4701 = uu____4678
in (

let uu____4711 = (find_section "labels" lines5)
in (match (uu____4711) with
| (labels, lines6) -> begin
(

let uu____4734 = uu____4711
in (

let remaining = (

let uu____4748 = (until "Done!" lines6)
in (match (uu____4748) with
| FStar_Pervasives_Native.None -> begin
lines6
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(FStar_List.append prefix1 suffix)
end))
in ((match (remaining) with
| [] -> begin
()
end
| uu____4802 -> begin
(

let uu____4806 = (

let uu____4812 = (FStar_Util.format1 "Unexpected additional output from Z3: %s\n" (FStar_String.concat "\n" remaining))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4812)))
in (FStar_Errors.log_issue r uu____4806))
end);
(

let uu____4817 = (FStar_Util.must result_opt)
in {smt_result = uu____4817; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels; smt_refutation = refutation});
)))
end)))
end)))
end)))
end)))
end))))
end)))))))


let doZ3Exe : FStar_SMTEncoding_Analysis.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun info decls fresh input label_messages -> (

let r = info.FStar_SMTEncoding_Analysis.query_info_range
in (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split ((10)::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let smt_output = (smt_output_sections r lines)
in (

let unsat_core = (match (smt_output.smt_unsat_core) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let s1 = (FStar_Util.trim_string (FStar_String.concat " " s))
in (

let s2 = (FStar_Util.substring s1 (Prims.parse_int "1") ((FStar_String.length s1) - (Prims.parse_int "2")))
in (match ((FStar_Util.starts_with s2 "error")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4910 -> begin
(

let uu____4912 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4912))
end)))
end)
in (

let unsat_proof = smt_output.smt_refutation
in (

let labels = (match (smt_output.smt_labels) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lines1) -> begin
(

let rec lblnegs = (fun lines2 -> (match (lines2) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____4958 = (lblnegs rest)
in (lname)::uu____4958)
end
| (lname)::(uu____4964)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4974 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____5003 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____5062 -> (match (uu____5062) with
| (m, uu____5077, uu____5078) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____5003) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r1) -> begin
(((lbl), (msg), (r1)))::[]
end)))))))
end)
in (

let statistics = (

let statistics = (FStar_Util.smap_create (Prims.parse_int "0"))
in (match (smt_output.smt_statistics) with
| FStar_Pervasives_Native.None -> begin
statistics
end
| FStar_Pervasives_Native.Some (lines1) -> begin
(

let parse_line = (fun line -> (

let pline = (FStar_Util.split (FStar_Util.trim_string line) ":")
in (match (pline) with
| ("(")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____5241 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| ("")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____5270 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____5273 -> begin
()
end)))
in ((FStar_List.iter parse_line lines1);
statistics;
))
end))
in (

let reason_unknown = (FStar_Util.map_opt smt_output.smt_reason_unknown (fun x -> (

let ru = (FStar_String.concat " " x)
in (match ((FStar_Util.starts_with ru "(:reason-unknown \"")) with
| true -> begin
(

let reason = (FStar_Util.substring_from ru (FStar_String.length "(:reason-unknown \""))
in (

let res = (FStar_String.substring reason (Prims.parse_int "0") ((FStar_String.length reason) - (Prims.parse_int "2")))
in res))
end
| uu____5302 -> begin
ru
end))))
in (

let status = ((

let uu____5306 = (FStar_Options.debug_any ())
in (match (uu____5306) with
| true -> begin
(

let uu____5309 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____5309))
end
| uu____5314 -> begin
()
end));
(match (smt_output.smt_result) with
| ("unsat")::[] -> begin
UNSAT (((unsat_core), (unsat_proof)))
end
| ("sat")::[] -> begin
SAT (((labels), (reason_unknown)))
end
| ("unknown")::[] -> begin
UNKNOWN (((labels), (reason_unknown)))
end
| ("timeout")::[] -> begin
TIMEOUT (((labels), (reason_unknown)))
end
| ("killed")::[] -> begin
((

let uu____5341 = (

let uu____5346 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5346.restart)
in (uu____5341 ()));
KILLED;
)
end
| uu____5366 -> begin
(

let uu____5367 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____5367))
end);
)
in ((status), (statistics)))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let uu____5375 = (tid ())
in (

let uu____5377 = (FStar_Options.z3_exe ())
in (

let uu____5379 = (ini_params ())
in (FStar_Util.run_process uu____5375 uu____5377 uu____5379 (FStar_Pervasives_Native.Some (input))))))
end
| uu____5384 -> begin
(

let uu____5386 = (

let uu____5393 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5393.ask)
in (uu____5386 input))
end)
in (

let uu____5413 = (parse (FStar_Util.trim_string stdout1))
in (match (uu____5413) with
| (status, statistics) -> begin
(

let uu____5424 = uu____5413
in ((

let uu____5430 = (FStar_Options.report_qi ())
in (match (uu____5430) with
| true -> begin
(match (status) with
| UNSAT (uu____5433, uu____5434) -> begin
(match (fresh) with
| true -> begin
(failwith "Option --report_qi is incompatible with multi-core solving")
end
| uu____5437 -> begin
(

let uu____5439 = (

let uu____5450 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5450.store)
in (uu____5439 info decls))
end)
end
| uu____5470 -> begin
()
end)
end
| uu____5471 -> begin
()
end));
((status), (statistics));
))
end))))))


let z3_options : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n(set-option :model true)\n(set-option :smt.case_split 3)\n(set-option :smt.relevancy 2)\n")


let set_z3_options : Prims.string  ->  unit = (fun opts -> (FStar_ST.op_Colon_Equals z3_options opts))

type 'a job_t =
{job : unit  ->  'a; callback : 'a  ->  unit}


let __proj__Mkjob_t__item__job : 'a . 'a job_t  ->  unit  ->  'a = (fun projectee -> (match (projectee) with
| {job = job; callback = callback} -> begin
job
end))


let __proj__Mkjob_t__item__callback : 'a . 'a job_t  ->  'a  ->  unit = (fun projectee -> (match (projectee) with
| {job = job; callback = callback} -> begin
callback
end))

type z3result =
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option; z3result_query_decls : FStar_SMTEncoding_Term.decl Prims.list}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls} -> begin
z3result_query_hash
end))


let __proj__Mkz3result__item__z3result_query_decls : z3result  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls} -> begin
z3result_query_decls
end))


type z3job =
z3result job_t


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let z3_job : FStar_SMTEncoding_Analysis.query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun r fresh label_messages input decls qhash uu____5804 -> (

let start = (FStar_Util.now ())
in (

let uu____5813 = (FStar_All.try_with (fun uu___156_5823 -> (match (()) with
| () -> begin
(doZ3Exe r decls fresh input label_messages)
end)) (fun uu___155_5831 -> if (

let uu____5836 = (FStar_Options.trace_error ())
in (not (uu____5836))) then begin
(Obj.magic ((Obj.repr ((

let uu____5839 = (

let uu____5848 = (

let uu____5861 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5861.extract)
in (uu____5848 ()))
in (FStar_All.pipe_left (fun a1 -> ()) uu____5839));
(

let uu____5890 = (

let uu____5892 = (

let uu____5898 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5898.refresh)
in (uu____5892 ()))
in (FStar_All.pipe_left (fun a2 -> ()) uu____5890));
(FStar_Exn.raise uu___155_5831);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____5813) with
| (status, statistics) -> begin
(

let uu____5925 = uu____5813
in (

let uu____5930 = (

let uu____5936 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5936))
in (match (uu____5930) with
| (uu____5937, elapsed_time) -> begin
(

let uu____5941 = uu____5930
in (

let ds = (

let uu____5950 = (FStar_Options.smt_proof ())
in (match (uu____5950) with
| true -> begin
decls
end
| uu____5955 -> begin
[]
end))
in {z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash; z3result_query_decls = ds}))
end)))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____5987 -> (

let j = (

let uu____5989 = (FStar_ST.op_Bang job_queue)
in (match (uu____5989) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::tl1 -> begin
((FStar_ST.op_Colon_Equals job_queue tl1);
hd1;
)
end))
in ((FStar_Util.incr pending_jobs);
(FStar_Util.monitor_exit job_queue);
(run_job j);
(FStar_Util.with_monitor job_queue (fun uu____6057 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____6059 -> (

let uu____6060 = (FStar_ST.op_Bang running)
in if uu____6060 then begin
(

let rec aux = (fun uu____6088 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____6094 = (FStar_ST.op_Bang job_queue)
in (match (uu____6094) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____6127 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____6131 = (j.job ())
in (FStar_All.pipe_left j.callback uu____6131)))


let kill : unit  ->  unit = (fun uu____6137 -> ((FStar_Util.print "[FINISH]\n" []);
(

let uu____6141 = (

let uu____6143 = (FStar_Options.n_cores ())
in (uu____6143 < (Prims.parse_int "2")))
in (match (uu____6141) with
| true -> begin
(

let uu____6147 = (

let uu____6149 = (

let uu____6155 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6155.kill)
in (uu____6149 ()))
in (FStar_All.pipe_left (fun a3 -> ()) uu____6147))
end
| uu____6176 -> begin
()
end));
))


let init : unit  ->  unit = (fun uu____6183 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____6222 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____6226 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____6240 -> ((

let uu____6242 = (

let uu____6245 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____6245 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____6242));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____6303 -> (

let rec aux = (fun uu____6309 -> (

let uu____6310 = (FStar_Util.with_monitor job_queue (fun uu____6328 -> (

let uu____6329 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____6352 = (

let uu____6353 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____6353))
in ((uu____6329), (uu____6352))))) ())
in (match (uu____6310) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____6417 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (

let uu____6421 = (

let uu____6423 = (FStar_Options.n_cores ())
in (uu____6423 > (Prims.parse_int "1")))
in (match (uu____6421) with
| true -> begin
(aux ())
end
| uu____6427 -> begin
(kill ())
end))))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let stack_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let stack_delta : FStar_SMTEncoding_Term.decls_t FStar_ST.ref = (FStar_Util.mk_ref [])


let incremental_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6470 -> (FStar_ST.op_Bang stack_delta))


let cummulative_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6495 -> (

let uu____6496 = (

let uu____6501 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.rev uu____6501))
in (FStar_List.flatten uu____6496)))


let clear_scope : unit  ->  unit = (fun uu____6532 -> (FStar_ST.op_Colon_Equals stack_delta []))


let get_scope : unit  ->  scope_t = (fun uu____6557 -> (FStar_ST.op_Bang stack_scope))


let reset_scope : unit  ->  unit = (fun uu____6582 -> (

let uu____6583 = (cummulative_scope ())
in (FStar_ST.op_Colon_Equals stack_delta uu____6583)))


let add_to_scopes : FStar_SMTEncoding_Term.decls_t  ->  unit = (fun decls -> ((

let uu____6610 = (FStar_ST.op_Bang stack_scope)
in (match (uu____6610) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals stack_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6661 -> begin
(failwith "Impossible")
end));
(

let uu____6663 = (

let uu____6664 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6664 decls))
in (FStar_ST.op_Colon_Equals stack_delta uu____6663));
))


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6716 -> ((

let uu____6718 = (

let uu____6719 = (FStar_ST.op_Bang stack_scope)
in ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])::uu____6719)
in (FStar_ST.op_Colon_Equals stack_scope uu____6718));
(

let uu____6764 = (

let uu____6765 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6765 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6764));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6817 -> ((

let uu____6819 = (

let uu____6820 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.tl uu____6820))
in (FStar_ST.op_Colon_Equals stack_scope uu____6819));
(

let uu____6865 = (

let uu____6866 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6866 ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6865));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push stack_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____6945 -> (pop msg)) stack_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___151_6958 -> (match (uu___151_6958) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6961 -> begin
()
end))));
(add_to_scopes decls);
))


let refresh : unit  ->  unit = (fun uu____6967 -> (

let uu____6968 = (

let uu____6970 = (FStar_Options.n_cores ())
in (uu____6970 < (Prims.parse_int "2")))
in (match (uu____6968) with
| true -> begin
(

let query_data = (

let uu____6983 = (

let uu____6996 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6996.extract)
in (uu____6983 ()))
in (

let qip_output = (

let uu____7018 = (

let uu____7024 = (FStar_ST.op_Bang bg_z3_proc)
in uu____7024.refresh)
in (uu____7018 ()))
in ((reset_scope ());
(

let uu____7045 = (FStar_Options.report_qi ())
in (match (uu____7045) with
| true -> begin
(FStar_SMTEncoding_Analysis.qiprofile_analysis query_data qip_output)
end
| uu____7048 -> begin
()
end));
)))
end
| uu____7050 -> begin
()
end)))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (FStar_ST.op_Bang z3_options)
in (

let uu____7101 = (

let uu____7110 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____7110) with
| true -> begin
(

let uu____7121 = (

let uu____7132 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___152_7160 -> (match (uu___152_7160) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____7163 -> begin
false
end))))
in (FStar_All.pipe_right uu____7132 FStar_Option.get))
in (match (uu____7121) with
| (prefix1, check_sat, suffix) -> begin
(

let uu____7216 = uu____7121
in (

let pp = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options))
in (

let suffix1 = (check_sat)::suffix
in (

let ps_lines = (pp prefix1)
in (

let ss_lines = (pp suffix1)
in (

let ps = (FStar_String.concat "\n" ps_lines)
in (

let ss = (FStar_String.concat "\n" ss_lines)
in (

let hs = (

let uu____7257 = (FStar_Options.keep_query_captions ())
in (match (uu____7257) with
| true -> begin
(

let uu____7261 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____7261 (FStar_String.concat "\n")))
end
| uu____7276 -> begin
ps
end))
in (

let uu____7278 = (

let uu____7282 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____7282))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____7278)))))))))))
end))
end
| uu____7290 -> begin
(

let uu____7292 = (

let uu____7294 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____7294 (FStar_String.concat "\n")))
in ((uu____7292), (FStar_Pervasives_Native.None)))
end))
in (match (uu____7101) with
| (r, hash) -> begin
(

let uu____7327 = uu____7101
in ((

let uu____7337 = (FStar_Options.log_queries ())
in (match (uu____7337) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____7340 -> begin
()
end));
((r), (hash));
))
end))))


type cb =
z3result  ->  unit


let cache_hit : FStar_SMTEncoding_Analysis.query_info  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  FStar_SMTEncoding_Term.decls_t  ->  Prims.bool = (fun r cache qhash cb decls -> (

let uu____7393 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____7393) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash; z3result_query_decls = []}
in ((cb result);
true;
));
))
end
| uu____7425 -> begin
false
end)
end
| uu____7430 -> begin
false
end)))


let ask_1_core : FStar_SMTEncoding_Analysis.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry cb -> (

let cumm_theory = (

let uu____7490 = (FStar_Options.report_qi ())
in (match (uu____7490) with
| true -> begin
(

let uu____7493 = (cummulative_scope ())
in (FStar_List.append uu____7493 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
end
| uu____7496 -> begin
[]
end))
in (

let incr_theory = (

let uu____7499 = (incremental_scope ())
in (FStar_List.append uu____7499 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in ((clear_scope ());
(

let uu____7503 = (filter_theory incr_theory)
in (match (uu____7503) with
| (incr_theory1, used_unsat_core) -> begin
(

let uu____7513 = uu____7503
in (

let uu____7519 = (mk_input incr_theory1)
in (match (uu____7519) with
| (input, qhash) -> begin
(

let uu____7538 = uu____7519
in (

let uu____7547 = (

let uu____7549 = (cache_hit r cache qhash cb cumm_theory)
in (not (uu____7549)))
in (match (uu____7547) with
| true -> begin
(run_job {job = (z3_job r false label_messages input cumm_theory qhash); callback = cb})
end
| uu____7557 -> begin
()
end)))
end)))
end));
))))


let ask_n_cores : FStar_SMTEncoding_Analysis.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

let theory = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.flatten (FStar_List.rev s))
end
| FStar_Pervasives_Native.None -> begin
((clear_scope ());
(cummulative_scope ());
)
end)
in (

let uu____7629 = (filter_theory theory)
in (match (uu____7629) with
| (theory1, used_unsat_core) -> begin
(

let uu____7639 = uu____7629
in (

let uu____7645 = (mk_input theory1)
in (match (uu____7645) with
| (input, qhash) -> begin
(

let cumm_theory = (

let uu____7665 = (FStar_Options.report_qi ())
in (match (uu____7665) with
| true -> begin
theory1
end
| uu____7668 -> begin
[]
end))
in (

let uu____7670 = (

let uu____7672 = (cache_hit r cache qhash cb theory1)
in (not (uu____7672)))
in (match (uu____7670) with
| true -> begin
(enqueue {job = (z3_job r true label_messages input cumm_theory qhash); callback = cb})
end
| uu____7680 -> begin
()
end)))
end)))
end))))


let ask : FStar_SMTEncoding_Analysis.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter1 cache label_messages qry scope cb -> (

let uu____7749 = (

let uu____7751 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7751 (Prims.parse_int "1")))
in (match (uu____7749) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb)
end
| uu____7758 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




