
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

let proof = (

let uu____342 = (FStar_Options.analyze_proof ())
in (match (uu____342) with
| true -> begin
("proof=true")::("smt.qi.profile=true")::[]
end
| uu____353 -> begin
[]
end))
in (FStar_List.append args (FStar_List.append opts proof)))));
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
| uu____430 -> begin
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
| uu____469 -> begin
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
| uu____517 -> begin
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
| uu____565 -> begin
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
| uu____605 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___150_616 -> (match (uu___150_616) with
| SAT (uu____618) -> begin
"sat"
end
| UNSAT (uu____627) -> begin
"unsat"
end
| UNKNOWN (uu____633) -> begin
"unknown"
end
| TIMEOUT (uu____642) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(

let uu____670 = (status_tag s)
in ((uu____670), ([])))
end
| UNSAT (uu____675) -> begin
(

let uu____680 = (status_tag s)
in ((uu____680), ([])))
end
| SAT (errs, msg) -> begin
(

let uu____693 = (

let uu____695 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____695 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____693), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____716 = (

let uu____718 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____718 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____716), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____739 = (

let uu____741 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____741 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____739), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____760 -> (

let uu____762 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____762 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let filter1 = (

let uu____781 = (FStar_Options.analyze_proof ())
in (match (uu____781) with
| true -> begin
(fun s -> (not ((FStar_Util.starts_with s "[quantifier_instances]"))))
end
| uu____792 -> begin
(fun s -> true)
end))
in (

let uu____797 = (FStar_Options.z3_exe ())
in (

let uu____799 = (ini_params ())
in (FStar_Util.start_process id1 uu____797 uu____799 (fun s -> (Prims.op_Equality s "Done!")) filter1)))))

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

let get_module_name = (fun uu____1614 -> (

let uu____1616 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1616) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1679 -> (

let uu____1680 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1680) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1738 = (

let uu____1747 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1822 -> (match (uu____1822) with
| (m, uu____1831) -> begin
(Prims.op_Equality n1 m)
end)) uu____1747))
in (match (uu____1738) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1845 = (

let uu____1854 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1854)
in (FStar_ST.op_Colon_Equals used_file_names uu____1845));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1986, k) -> begin
((

let uu____1999 = (

let uu____2008 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____2008)
in (FStar_ST.op_Colon_Equals used_file_names uu____1999));
(

let uu____2140 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____2140));
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

let get_log_file = (fun uu____2248 -> (

let uu____2249 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2249) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2306 = (get_log_file ())
in (FStar_Util.append_to_file uu____2306 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2317 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2317) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2372 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2372) with
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

let uu____2531 = (

let uu____2533 = (FStar_ST.op_Bang query_number)
in (uu____2533 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2531));
(

let file_name = (

let uu____2624 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2624))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2637 = (

let uu____2639 = (FStar_Options.n_cores ())
in (uu____2639 > (Prims.parse_int "1")))
in (match (uu____2637) with
| true -> begin
(write_to_new_log str)
end
| uu____2643 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2650 -> (

let uu____2651 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2651) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2752 -> (

let uu____2754 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2754) with
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
in (fun uu____2869 -> (

let uu____2870 = (

let uu____2872 = ((FStar_Util.incr ctr);
(

let uu____2908 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2908 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2872))
in (new_z3proc uu____2870))))
in (

let z3proc = (fun uu____2961 -> ((

let uu____2963 = (

let uu____2965 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2965 FStar_Pervasives_Native.None))
in (match (uu____2963) with
| true -> begin
((

let uu____3017 = (

let uu____3020 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3020))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3017));
(FStar_ST.op_Colon_Equals the_queries []);
)
end
| uu____3129 -> begin
()
end));
(

let uu____3131 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____3131));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____3198 -> "\nkilled\n")
in (

let uu____3200 = (z3proc ())
in (FStar_Util.ask_process uu____3200 input kill_handler))))
in (

let refresh = (fun uu____3207 -> (

let extra = (

let uu____3211 = (z3proc ())
in (FStar_Util.kill_process uu____3211))
in ((

let uu____3213 = (

let uu____3216 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3216))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3213));
(FStar_ST.op_Colon_Equals the_queries []);
(query_logging.close_log ());
extra;
)))
in (

let kill = (fun uu____3333 -> (

let uu____3335 = (

let uu____3337 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.is_some uu____3337))
in (match (uu____3335) with
| true -> begin
(

let extra = (

let uu____3389 = (z3proc ())
in (FStar_Util.kill_process uu____3389))
in ((FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_queries []);
extra;
))
end
| uu____3501 -> begin
""
end)))
in (

let restart = (fun uu____3509 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____3557 = (

let uu____3560 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3560))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3557));
))
in (

let store = (fun info decls -> (

let uu____3621 = (

let uu____3630 = (FStar_ST.op_Bang the_queries)
in (FStar_List.append uu____3630 ((((info), (decls)))::[])))
in (FStar_ST.op_Colon_Equals the_queries uu____3621)))
in (

let extract = (fun uu____3786 -> (FStar_ST.op_Bang the_queries))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart); kill = (FStar_Util.with_monitor x kill); store = store; extract = extract}))))))))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


let at_log_file : unit  ->  Prims.string = (fun uu____3895 -> (

let uu____3897 = (FStar_Options.log_queries ())
in (match (uu____3897) with
| true -> begin
(

let uu____3901 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____3901))
end
| uu____3904 -> begin
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
| uu____4211 -> begin
(

let uu____4213 = (until tag lines2)
in (FStar_Util.map_opt uu____4213 (fun uu____4249 -> (match (uu____4249) with
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

let uu____4356 = (until (start_tag tag) lines1)
in (match (uu____4356) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____4426 = (until (end_tag tag) suffix)
in (match (uu____4426) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____4511 = (find_section "result" lines)
in (match (uu____4511) with
| (result_opt, lines1) -> begin
(

let uu____4534 = uu____4511
in (

let result = (FStar_Util.must result_opt)
in (

let uu____4545 = (find_section "reason-unknown" lines1)
in (match (uu____4545) with
| (reason_unknown, lines2) -> begin
(

let uu____4568 = uu____4545
in (

let uu____4578 = (find_section "unsat-core" lines2)
in (match (uu____4578) with
| (unsat_core, lines3) -> begin
(

let uu____4601 = uu____4578
in (

let uu____4611 = (

let uu____4621 = (FStar_Options.analyze_proof ())
in (match (uu____4621) with
| true -> begin
(find_section "proof" lines3)
end
| uu____4634 -> begin
((FStar_Pervasives_Native.None), (lines3))
end))
in (match (uu____4611) with
| (refutation, lines4) -> begin
(

let uu____4653 = uu____4611
in (

let uu____4663 = (find_section "statistics" lines4)
in (match (uu____4663) with
| (statistics, lines5) -> begin
(

let uu____4686 = uu____4663
in (

let uu____4696 = (find_section "labels" lines5)
in (match (uu____4696) with
| (labels, lines6) -> begin
(

let uu____4719 = uu____4696
in (

let remaining = (

let uu____4733 = (until "Done!" lines6)
in (match (uu____4733) with
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
| uu____4787 -> begin
(

let uu____4791 = (

let uu____4797 = (FStar_Util.format1 "Unexpected additional output from Z3: %s\n" (FStar_String.concat "\n" remaining))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4797)))
in (FStar_Errors.log_issue r uu____4791))
end);
(

let uu____4802 = (FStar_Util.must result_opt)
in {smt_result = uu____4802; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels; smt_refutation = refutation});
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
| uu____4895 -> begin
(

let uu____4897 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4897))
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

let uu____4943 = (lblnegs rest)
in (lname)::uu____4943)
end
| (lname)::(uu____4949)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4959 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4988 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____5047 -> (match (uu____5047) with
| (m, uu____5062, uu____5063) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____4988) with
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
| uu____5226 -> begin
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
| uu____5255 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____5258 -> begin
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
| uu____5287 -> begin
ru
end))))
in (

let status = ((

let uu____5291 = (FStar_Options.debug_any ())
in (match (uu____5291) with
| true -> begin
(

let uu____5294 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____5294))
end
| uu____5299 -> begin
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

let uu____5326 = (

let uu____5331 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5331.restart)
in (uu____5326 ()));
KILLED;
)
end
| uu____5351 -> begin
(

let uu____5352 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____5352))
end);
)
in ((status), (statistics)))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let uu____5360 = (tid ())
in (

let uu____5362 = (FStar_Options.z3_exe ())
in (

let uu____5364 = (ini_params ())
in (FStar_Util.run_process uu____5360 uu____5362 uu____5364 (FStar_Pervasives_Native.Some (input))))))
end
| uu____5369 -> begin
(

let uu____5371 = (

let uu____5378 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5378.ask)
in (uu____5371 input))
end)
in (

let uu____5398 = (parse (FStar_Util.trim_string stdout1))
in (match (uu____5398) with
| (status, statistics) -> begin
(

let uu____5409 = uu____5398
in ((

let uu____5415 = (FStar_Options.analyze_proof ())
in (match (uu____5415) with
| true -> begin
(match (status) with
| UNSAT (uu____5418, uu____5419) -> begin
(match (fresh) with
| true -> begin
(failwith "Option --analyze_proof is incompatible with multi-core solving")
end
| uu____5422 -> begin
(

let uu____5424 = (

let uu____5435 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5435.store)
in (uu____5424 info decls))
end)
end
| uu____5455 -> begin
()
end)
end
| uu____5456 -> begin
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
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash} -> begin
z3result_query_hash
end))


type z3job =
z3result job_t


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let z3_job : FStar_SMTEncoding_Analysis.query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun r fresh label_messages input decls qhash uu____5749 -> (

let start = (FStar_Util.now ())
in (

let uu____5758 = (FStar_All.try_with (fun uu___156_5768 -> (match (()) with
| () -> begin
(doZ3Exe r decls fresh input label_messages)
end)) (fun uu___155_5776 -> if (

let uu____5781 = (FStar_Options.trace_error ())
in (not (uu____5781))) then begin
(Obj.magic ((Obj.repr ((

let uu____5784 = (

let uu____5793 = (

let uu____5806 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5806.extract)
in (uu____5793 ()))
in (FStar_All.pipe_left (fun a1 -> ()) uu____5784));
(

let uu____5835 = (

let uu____5837 = (

let uu____5843 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5843.refresh)
in (uu____5837 ()))
in (FStar_All.pipe_left (fun a2 -> ()) uu____5835));
(FStar_Exn.raise uu___155_5776);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____5758) with
| (status, statistics) -> begin
(

let uu____5870 = uu____5758
in (

let uu____5875 = (

let uu____5881 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5881))
in (match (uu____5875) with
| (uu____5882, elapsed_time) -> begin
(

let uu____5886 = uu____5875
in {z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash})
end)))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____5922 -> (

let j = (

let uu____5924 = (FStar_ST.op_Bang job_queue)
in (match (uu____5924) with
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
(FStar_Util.with_monitor job_queue (fun uu____5992 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____5994 -> (

let uu____5995 = (FStar_ST.op_Bang running)
in if uu____5995 then begin
(

let rec aux = (fun uu____6023 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____6029 = (FStar_ST.op_Bang job_queue)
in (match (uu____6029) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____6062 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____6066 = (j.job ())
in (FStar_All.pipe_left j.callback uu____6066)))


let kill : unit  ->  unit = (fun uu____6072 -> ((FStar_Util.print "[FINISH]\n" []);
(

let uu____6076 = (

let uu____6078 = (FStar_Options.n_cores ())
in (uu____6078 < (Prims.parse_int "2")))
in (match (uu____6076) with
| true -> begin
(

let uu____6082 = (

let uu____6084 = (

let uu____6090 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6090.kill)
in (uu____6084 ()))
in (FStar_All.pipe_left (fun a3 -> ()) uu____6082))
end
| uu____6111 -> begin
()
end));
))


let init : unit  ->  unit = (fun uu____6118 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____6157 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____6161 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____6175 -> ((

let uu____6177 = (

let uu____6180 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____6180 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____6177));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____6238 -> (

let rec aux = (fun uu____6244 -> (

let uu____6245 = (FStar_Util.with_monitor job_queue (fun uu____6263 -> (

let uu____6264 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____6287 = (

let uu____6288 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____6288))
in ((uu____6264), (uu____6287))))) ())
in (match (uu____6245) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____6352 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (

let uu____6356 = (

let uu____6358 = (FStar_Options.n_cores ())
in (uu____6358 > (Prims.parse_int "1")))
in (match (uu____6356) with
| true -> begin
(aux ())
end
| uu____6362 -> begin
(kill ())
end))))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let stack_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let stack_delta : FStar_SMTEncoding_Term.decls_t FStar_ST.ref = (FStar_Util.mk_ref [])


let incremental_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6405 -> (FStar_ST.op_Bang stack_delta))


let cummulative_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6430 -> (

let uu____6431 = (

let uu____6436 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.rev uu____6436))
in (FStar_List.flatten uu____6431)))


let clear_scope : unit  ->  unit = (fun uu____6467 -> (FStar_ST.op_Colon_Equals stack_delta []))


let get_scope : unit  ->  scope_t = (fun uu____6492 -> (FStar_ST.op_Bang stack_scope))


let reset_scope : unit  ->  unit = (fun uu____6517 -> (

let uu____6518 = (cummulative_scope ())
in (FStar_ST.op_Colon_Equals stack_delta uu____6518)))


let add_to_scopes : FStar_SMTEncoding_Term.decls_t  ->  unit = (fun decls -> ((

let uu____6545 = (FStar_ST.op_Bang stack_scope)
in (match (uu____6545) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals stack_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6596 -> begin
(failwith "Impossible")
end));
(

let uu____6598 = (

let uu____6599 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6599 decls))
in (FStar_ST.op_Colon_Equals stack_delta uu____6598));
))


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6651 -> ((

let uu____6653 = (

let uu____6654 = (FStar_ST.op_Bang stack_scope)
in ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])::uu____6654)
in (FStar_ST.op_Colon_Equals stack_scope uu____6653));
(

let uu____6699 = (

let uu____6700 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6700 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6699));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6752 -> ((

let uu____6754 = (

let uu____6755 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.tl uu____6755))
in (FStar_ST.op_Colon_Equals stack_scope uu____6754));
(

let uu____6800 = (

let uu____6801 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6801 ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6800));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push stack_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____6880 -> (pop msg)) stack_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___151_6893 -> (match (uu___151_6893) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6896 -> begin
()
end))));
(add_to_scopes decls);
))


let refresh : unit  ->  unit = (fun uu____6902 -> (

let uu____6903 = (

let uu____6905 = (FStar_Options.n_cores ())
in (uu____6905 < (Prims.parse_int "2")))
in (match (uu____6903) with
| true -> begin
(

let query_data = (

let uu____6918 = (

let uu____6931 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6931.extract)
in (uu____6918 ()))
in (

let qip_output = (

let uu____6953 = (

let uu____6959 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6959.refresh)
in (uu____6953 ()))
in ((reset_scope ());
(

let uu____6980 = (FStar_Options.analyze_proof ())
in (match (uu____6980) with
| true -> begin
(FStar_SMTEncoding_Analysis.qiprofile_analysis query_data qip_output)
end
| uu____6983 -> begin
()
end));
)))
end
| uu____6985 -> begin
()
end)))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (FStar_ST.op_Bang z3_options)
in (

let uu____7036 = (

let uu____7045 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____7045) with
| true -> begin
(

let uu____7056 = (

let uu____7067 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___152_7095 -> (match (uu___152_7095) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____7098 -> begin
false
end))))
in (FStar_All.pipe_right uu____7067 FStar_Option.get))
in (match (uu____7056) with
| (prefix1, check_sat, suffix) -> begin
(

let uu____7151 = uu____7056
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

let uu____7192 = (FStar_Options.keep_query_captions ())
in (match (uu____7192) with
| true -> begin
(

let uu____7196 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____7196 (FStar_String.concat "\n")))
end
| uu____7211 -> begin
ps
end))
in (

let uu____7213 = (

let uu____7217 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____7217))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____7213)))))))))))
end))
end
| uu____7225 -> begin
(

let uu____7227 = (

let uu____7229 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____7229 (FStar_String.concat "\n")))
in ((uu____7227), (FStar_Pervasives_Native.None)))
end))
in (match (uu____7036) with
| (r, hash) -> begin
(

let uu____7262 = uu____7036
in ((

let uu____7272 = (FStar_Options.log_queries ())
in (match (uu____7272) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____7275 -> begin
()
end));
((r), (hash));
))
end))))


type cb =
z3result  ->  unit


let cache_hit : FStar_SMTEncoding_Analysis.query_info  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  FStar_SMTEncoding_Term.decls_t  ->  Prims.bool = (fun r cache qhash cb decls -> (

let uu____7328 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____7328) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash}
in ((cb result);
true;
));
))
end
| uu____7360 -> begin
false
end)
end
| uu____7365 -> begin
false
end)))


let ask_1_core : FStar_SMTEncoding_Analysis.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry cb -> (

let cumm_theory = (

let uu____7425 = (FStar_Options.analyze_proof ())
in (match (uu____7425) with
| true -> begin
(

let uu____7428 = (cummulative_scope ())
in (FStar_List.append uu____7428 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
end
| uu____7431 -> begin
[]
end))
in (

let incr_theory = (

let uu____7434 = (incremental_scope ())
in (FStar_List.append uu____7434 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in ((clear_scope ());
(

let uu____7438 = (filter_theory incr_theory)
in (match (uu____7438) with
| (incr_theory1, used_unsat_core) -> begin
(

let uu____7448 = uu____7438
in (

let uu____7454 = (mk_input incr_theory1)
in (match (uu____7454) with
| (input, qhash) -> begin
(

let uu____7473 = uu____7454
in (

let uu____7482 = (

let uu____7484 = (cache_hit r cache qhash cb cumm_theory)
in (not (uu____7484)))
in (match (uu____7482) with
| true -> begin
(run_job {job = (z3_job r false label_messages input cumm_theory qhash); callback = cb})
end
| uu____7492 -> begin
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

let uu____7564 = (filter_theory theory)
in (match (uu____7564) with
| (theory1, used_unsat_core) -> begin
(

let uu____7574 = uu____7564
in (

let uu____7580 = (mk_input theory1)
in (match (uu____7580) with
| (input, qhash) -> begin
(

let cumm_theory = (

let uu____7600 = (FStar_Options.analyze_proof ())
in (match (uu____7600) with
| true -> begin
theory1
end
| uu____7603 -> begin
[]
end))
in (

let uu____7605 = (

let uu____7607 = (cache_hit r cache qhash cb theory1)
in (not (uu____7607)))
in (match (uu____7605) with
| true -> begin
(enqueue {job = (z3_job r true label_messages input cumm_theory qhash); callback = cb})
end
| uu____7615 -> begin
()
end)))
end)))
end))))


let ask : FStar_SMTEncoding_Analysis.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter1 cache label_messages qry scope cb -> (

let uu____7684 = (

let uu____7686 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7686 (Prims.parse_int "1")))
in (match (uu____7684) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb)
end
| uu____7693 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




