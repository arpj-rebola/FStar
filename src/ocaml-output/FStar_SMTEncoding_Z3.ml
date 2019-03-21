
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

let uu____309 = (

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

let uu____334 = (

let uu____338 = (FStar_Options.z3_cliopt ())
in (

let uu____342 = (

let uu____346 = (FStar_Options.report_qi ())
in (match (uu____346) with
| true -> begin
("smt.qi.profile=true")::[]
end
| uu____355 -> begin
[]
end))
in (FStar_List.append uu____338 uu____342)))
in (FStar_List.append uu____309 uu____334)));
))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list FStar_Pervasives_Native.option

type z3status =
| UNSAT of unsat_core
| SAT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| UNKNOWN of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| TIMEOUT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| KILLED


let uu___is_UNSAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
true
end
| uu____419 -> begin
false
end))


let __proj__UNSAT__item___0 : z3status  ->  unsat_core = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
_0
end))


let uu___is_SAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
true
end
| uu____446 -> begin
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
| uu____494 -> begin
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
| uu____542 -> begin
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
| uu____582 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___150_593 -> (match (uu___150_593) with
| SAT (uu____595) -> begin
"sat"
end
| UNSAT (uu____604) -> begin
"unsat"
end
| UNKNOWN (uu____606) -> begin
"unknown"
end
| TIMEOUT (uu____615) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(

let uu____643 = (status_tag s)
in ((uu____643), ([])))
end
| UNSAT (uu____648) -> begin
(

let uu____649 = (status_tag s)
in ((uu____649), ([])))
end
| SAT (errs, msg) -> begin
(

let uu____662 = (

let uu____664 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____664 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____662), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____685 = (

let uu____687 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____687 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____685), (errs)))
end
| TIMEOUT (errs, msg) -> begin
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
end))


let tid : unit  ->  Prims.string = (fun uu____729 -> (

let uu____731 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____731 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let filter1 = (

let uu____750 = (FStar_Options.report_qi ())
in (match (uu____750) with
| true -> begin
(fun s -> (not ((FStar_Util.starts_with s "[quantifier_instances]"))))
end
| uu____761 -> begin
(fun s -> true)
end))
in (

let uu____766 = (FStar_Options.z3_exe ())
in (

let uu____768 = (ini_params ())
in (FStar_Util.start_process id1 uu____766 uu____768 (fun s -> (Prims.op_Equality s "Done!")) filter1)))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  Prims.string; restart : unit  ->  unit; kill : unit  ->  Prims.string; store : FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit; extract : unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list}


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


let __proj__Mkbgproc__item__store : bgproc  ->  FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
store
end))


let __proj__Mkbgproc__item__extract : bgproc  ->  unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
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

let get_module_name = (fun uu____1583 -> (

let uu____1585 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1585) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1648 -> (

let uu____1649 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1649) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1707 = (

let uu____1716 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1791 -> (match (uu____1791) with
| (m, uu____1800) -> begin
(Prims.op_Equality n1 m)
end)) uu____1716))
in (match (uu____1707) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1814 = (

let uu____1823 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1823)
in (FStar_ST.op_Colon_Equals used_file_names uu____1814));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1955, k) -> begin
((

let uu____1968 = (

let uu____1977 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1977)
in (FStar_ST.op_Colon_Equals used_file_names uu____1968));
(

let uu____2109 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____2109));
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

let get_log_file = (fun uu____2217 -> (

let uu____2218 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2218) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2275 = (get_log_file ())
in (FStar_Util.append_to_file uu____2275 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2286 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2286) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2341 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2341) with
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

let uu____2500 = (

let uu____2502 = (FStar_ST.op_Bang query_number)
in (uu____2502 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2500));
(

let file_name = (

let uu____2593 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2593))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2606 = (

let uu____2608 = (FStar_Options.n_cores ())
in (uu____2608 > (Prims.parse_int "1")))
in (match (uu____2606) with
| true -> begin
(write_to_new_log str)
end
| uu____2612 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2619 -> (

let uu____2620 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2620) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2721 -> (

let uu____2723 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2723) with
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
in (fun uu____2838 -> (

let uu____2839 = (

let uu____2841 = ((FStar_Util.incr ctr);
(

let uu____2877 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2877 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2841))
in (new_z3proc uu____2839))))
in (

let z3proc = (fun uu____2930 -> ((

let uu____2932 = (

let uu____2934 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2934 FStar_Pervasives_Native.None))
in (match (uu____2932) with
| true -> begin
((

let uu____2986 = (

let uu____2989 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2989))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2986));
(FStar_ST.op_Colon_Equals the_queries []);
)
end
| uu____3098 -> begin
()
end));
(

let uu____3100 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____3100));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____3167 -> "\nkilled\n")
in (

let uu____3169 = (z3proc ())
in (FStar_Util.ask_process uu____3169 input kill_handler))))
in (

let refresh = (fun uu____3176 -> (

let extra = (

let uu____3180 = (z3proc ())
in (FStar_Util.kill_process uu____3180))
in ((

let uu____3182 = (

let uu____3185 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3185))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3182));
(FStar_ST.op_Colon_Equals the_queries []);
(query_logging.close_log ());
extra;
)))
in (

let kill = (fun uu____3302 -> (

let uu____3304 = (

let uu____3306 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.is_some uu____3306))
in (match (uu____3304) with
| true -> begin
(

let extra = (

let uu____3358 = (z3proc ())
in (FStar_Util.kill_process uu____3358))
in ((FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_queries []);
extra;
))
end
| uu____3470 -> begin
""
end)))
in (

let restart = (fun uu____3478 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____3526 = (

let uu____3529 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3529))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3526));
))
in (

let store = (fun info decls -> (

let uu____3590 = (

let uu____3599 = (FStar_ST.op_Bang the_queries)
in (FStar_List.append uu____3599 ((((info), (decls)))::[])))
in (FStar_ST.op_Colon_Equals the_queries uu____3590)))
in (

let extract = (fun uu____3755 -> (FStar_ST.op_Bang the_queries))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart); kill = (FStar_Util.with_monitor x kill); store = store; extract = extract}))))))))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


let at_log_file : unit  ->  Prims.string = (fun uu____3864 -> (

let uu____3866 = (FStar_Options.log_queries ())
in (match (uu____3866) with
| true -> begin
(

let uu____3870 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____3870))
end
| uu____3873 -> begin
""
end)))


type smt_output_section =
Prims.string Prims.list

type smt_output =
{smt_result : smt_output_section; smt_reason_unknown : smt_output_section FStar_Pervasives_Native.option; smt_unsat_core : smt_output_section FStar_Pervasives_Native.option; smt_statistics : smt_output_section FStar_Pervasives_Native.option; smt_labels : smt_output_section FStar_Pervasives_Native.option}


let __proj__Mksmt_output__item__smt_result : smt_output  ->  smt_output_section = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_result
end))


let __proj__Mksmt_output__item__smt_reason_unknown : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_reason_unknown
end))


let __proj__Mksmt_output__item__smt_unsat_core : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_unsat_core
end))


let __proj__Mksmt_output__item__smt_statistics : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_statistics
end))


let __proj__Mksmt_output__item__smt_labels : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_labels
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
| uu____4132 -> begin
(

let uu____4134 = (until tag lines2)
in (FStar_Util.map_opt uu____4134 (fun uu____4170 -> (match (uu____4170) with
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

let uu____4277 = (until (start_tag tag) lines1)
in (match (uu____4277) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____4347 = (until (end_tag tag) suffix)
in (match (uu____4347) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____4432 = (find_section "result" lines)
in (match (uu____4432) with
| (result_opt, lines1) -> begin
(

let uu____4455 = uu____4432
in (

let result = (FStar_Util.must result_opt)
in (

let uu____4466 = (find_section "reason-unknown" lines1)
in (match (uu____4466) with
| (reason_unknown, lines2) -> begin
(

let uu____4489 = uu____4466
in (

let uu____4499 = (find_section "unsat-core" lines2)
in (match (uu____4499) with
| (unsat_core, lines3) -> begin
(

let uu____4522 = uu____4499
in (

let uu____4532 = (find_section "statistics" lines3)
in (match (uu____4532) with
| (statistics, lines4) -> begin
(

let uu____4555 = uu____4532
in (

let uu____4565 = (find_section "labels" lines4)
in (match (uu____4565) with
| (labels, lines5) -> begin
(

let uu____4588 = uu____4565
in (

let remaining = (

let uu____4602 = (until "Done!" lines5)
in (match (uu____4602) with
| FStar_Pervasives_Native.None -> begin
lines5
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(FStar_List.append prefix1 suffix)
end))
in ((match (remaining) with
| [] -> begin
()
end
| uu____4656 -> begin
(

let uu____4660 = (

let uu____4666 = (FStar_Util.format1 "Unexpected additional output from Z3: %s\n" (FStar_String.concat "\n" remaining))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4666)))
in (FStar_Errors.log_issue r uu____4660))
end);
(

let uu____4671 = (FStar_Util.must result_opt)
in {smt_result = uu____4671; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
)))
end)))
end)))
end)))
end))))
end)))))))


let doZ3Exe : FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun info decls fresh input label_messages -> (

let r = info.FStar_SMTEncoding_QIReport.query_info_range
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
| uu____4764 -> begin
(

let uu____4766 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4766))
end)))
end)
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

let uu____4811 = (lblnegs rest)
in (lname)::uu____4811)
end
| (lname)::(uu____4817)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4827 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4856 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____4915 -> (match (uu____4915) with
| (m, uu____4930, uu____4931) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____4856) with
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
| uu____5094 -> begin
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
| uu____5123 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____5126 -> begin
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
| uu____5155 -> begin
ru
end))))
in (

let status = ((

let uu____5159 = (FStar_Options.debug_any ())
in (match (uu____5159) with
| true -> begin
(

let uu____5162 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____5162))
end
| uu____5167 -> begin
()
end));
(match (smt_output.smt_result) with
| ("unsat")::[] -> begin
UNSAT (unsat_core)
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

let uu____5194 = (

let uu____5199 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5199.restart)
in (uu____5194 ()));
KILLED;
)
end
| uu____5219 -> begin
(

let uu____5220 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____5220))
end);
)
in ((status), (statistics))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let uu____5228 = (tid ())
in (

let uu____5230 = (FStar_Options.z3_exe ())
in (

let uu____5232 = (ini_params ())
in (FStar_Util.run_process uu____5228 uu____5230 uu____5232 (FStar_Pervasives_Native.Some (input))))))
end
| uu____5237 -> begin
(

let uu____5239 = (

let uu____5246 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5246.ask)
in (uu____5239 input))
end)
in (

let uu____5266 = (parse (FStar_Util.trim_string stdout1))
in (match (uu____5266) with
| (status, statistics) -> begin
(

let uu____5277 = uu____5266
in ((

let uu____5283 = (FStar_Options.report_qi ())
in (match (uu____5283) with
| true -> begin
(match (status) with
| UNSAT (uu____5286) -> begin
(match (fresh) with
| true -> begin
(failwith "Option --report_qi is incompatible with multi-core solving")
end
| uu____5289 -> begin
(

let uu____5291 = (

let uu____5302 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5302.store)
in (uu____5291 info decls))
end)
end
| uu____5322 -> begin
()
end)
end
| uu____5323 -> begin
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


let z3_job : FStar_SMTEncoding_QIReport.query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun r fresh label_messages input decls qhash uu____5656 -> (

let start = (FStar_Util.now ())
in (

let uu____5665 = (FStar_All.try_with (fun uu___156_5675 -> (match (()) with
| () -> begin
(doZ3Exe r decls fresh input label_messages)
end)) (fun uu___155_5683 -> if (

let uu____5688 = (FStar_Options.trace_error ())
in (not (uu____5688))) then begin
(Obj.magic ((Obj.repr ((

let uu____5691 = (

let uu____5700 = (

let uu____5713 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5713.extract)
in (uu____5700 ()))
in (FStar_All.pipe_left (fun a1 -> ()) uu____5691));
(

let uu____5742 = (

let uu____5744 = (

let uu____5750 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5750.refresh)
in (uu____5744 ()))
in (FStar_All.pipe_left (fun a2 -> ()) uu____5742));
(FStar_Exn.raise uu___155_5683);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____5665) with
| (status, statistics) -> begin
(

let uu____5777 = uu____5665
in (

let uu____5782 = (

let uu____5788 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5788))
in (match (uu____5782) with
| (uu____5789, elapsed_time) -> begin
(

let uu____5793 = uu____5782
in {z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash; z3result_query_decls = decls})
end)))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____5829 -> (

let j = (

let uu____5831 = (FStar_ST.op_Bang job_queue)
in (match (uu____5831) with
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
(FStar_Util.with_monitor job_queue (fun uu____5899 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____5901 -> (

let uu____5902 = (FStar_ST.op_Bang running)
in if uu____5902 then begin
(

let rec aux = (fun uu____5930 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____5936 = (FStar_ST.op_Bang job_queue)
in (match (uu____5936) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____5969 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____5973 = (j.job ())
in (FStar_All.pipe_left j.callback uu____5973)))


let kill : unit  ->  unit = (fun uu____5979 -> (

let uu____5980 = (

let uu____5982 = (FStar_Options.n_cores ())
in (uu____5982 < (Prims.parse_int "2")))
in (match (uu____5980) with
| true -> begin
(

let uu____5986 = (

let uu____5988 = (

let uu____5994 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5994.kill)
in (uu____5988 ()))
in (FStar_All.pipe_left (fun a3 -> ()) uu____5986))
end
| uu____6015 -> begin
()
end)))


let init : unit  ->  unit = (fun uu____6022 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____6061 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____6065 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____6079 -> ((

let uu____6081 = (

let uu____6084 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____6084 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____6081));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____6142 -> (

let rec aux = (fun uu____6148 -> (

let uu____6149 = (FStar_Util.with_monitor job_queue (fun uu____6167 -> (

let uu____6168 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____6191 = (

let uu____6192 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____6192))
in ((uu____6168), (uu____6191))))) ())
in (match (uu____6149) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____6256 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (

let uu____6260 = (

let uu____6262 = (FStar_Options.n_cores ())
in (uu____6262 > (Prims.parse_int "1")))
in (match (uu____6260) with
| true -> begin
(aux ())
end
| uu____6266 -> begin
(kill ())
end))))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let stack_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let stack_delta : FStar_SMTEncoding_Term.decls_t FStar_ST.ref = (FStar_Util.mk_ref [])


let incremental_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6309 -> (FStar_ST.op_Bang stack_delta))


let cummulative_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____6334 -> (

let uu____6335 = (

let uu____6340 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.rev uu____6340))
in (FStar_List.flatten uu____6335)))


let clear_scope : unit  ->  unit = (fun uu____6371 -> (FStar_ST.op_Colon_Equals stack_delta []))


let get_scope : unit  ->  scope_t = (fun uu____6396 -> (FStar_ST.op_Bang stack_scope))


let reset_scope : unit  ->  unit = (fun uu____6421 -> (

let uu____6422 = (cummulative_scope ())
in (FStar_ST.op_Colon_Equals stack_delta uu____6422)))


let add_to_scopes : FStar_SMTEncoding_Term.decls_t  ->  unit = (fun decls -> ((

let uu____6449 = (FStar_ST.op_Bang stack_scope)
in (match (uu____6449) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals stack_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6500 -> begin
(failwith "Impossible")
end));
(

let uu____6502 = (

let uu____6503 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6503 decls))
in (FStar_ST.op_Colon_Equals stack_delta uu____6502));
))


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6555 -> ((

let uu____6557 = (

let uu____6558 = (FStar_ST.op_Bang stack_scope)
in ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])::uu____6558)
in (FStar_ST.op_Colon_Equals stack_scope uu____6557));
(

let uu____6603 = (

let uu____6604 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6604 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6603));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6656 -> ((

let uu____6658 = (

let uu____6659 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.tl uu____6659))
in (FStar_ST.op_Colon_Equals stack_scope uu____6658));
(

let uu____6704 = (

let uu____6705 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6705 ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6704));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push stack_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____6784 -> (pop msg)) stack_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___151_6797 -> (match (uu___151_6797) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6800 -> begin
()
end))));
(add_to_scopes decls);
))


let refresh : unit  ->  unit = (fun uu____6806 -> (

let uu____6807 = (

let uu____6809 = (FStar_Options.n_cores ())
in (uu____6809 < (Prims.parse_int "2")))
in (match (uu____6807) with
| true -> begin
(

let query_data = (

let uu____6822 = (

let uu____6835 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6835.extract)
in (uu____6822 ()))
in (

let qip_output = (

let uu____6857 = (

let uu____6863 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6863.refresh)
in (uu____6857 ()))
in ((reset_scope ());
(

let uu____6884 = (FStar_Options.report_qi ())
in (match (uu____6884) with
| true -> begin
(FStar_SMTEncoding_QIReport.qiprofile_analysis query_data qip_output)
end
| uu____6887 -> begin
()
end));
)))
end
| uu____6889 -> begin
()
end)))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (FStar_ST.op_Bang z3_options)
in (

let uu____6940 = (

let uu____6949 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____6949) with
| true -> begin
(

let uu____6960 = (

let uu____6971 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___152_6999 -> (match (uu___152_6999) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____7002 -> begin
false
end))))
in (FStar_All.pipe_right uu____6971 FStar_Option.get))
in (match (uu____6960) with
| (prefix1, check_sat, suffix) -> begin
(

let uu____7055 = uu____6960
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

let uu____7096 = (FStar_Options.keep_query_captions ())
in (match (uu____7096) with
| true -> begin
(

let uu____7100 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____7100 (FStar_String.concat "\n")))
end
| uu____7115 -> begin
ps
end))
in (

let uu____7117 = (

let uu____7121 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____7121))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____7117)))))))))))
end))
end
| uu____7129 -> begin
(

let uu____7131 = (

let uu____7133 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____7133 (FStar_String.concat "\n")))
in ((uu____7131), (FStar_Pervasives_Native.None)))
end))
in (match (uu____6940) with
| (r, hash) -> begin
(

let uu____7166 = uu____6940
in ((

let uu____7176 = (FStar_Options.log_queries ())
in (match (uu____7176) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____7179 -> begin
()
end));
((r), (hash));
))
end))))


type cb =
z3result  ->  unit


let cache_hit : FStar_SMTEncoding_QIReport.query_info  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  FStar_SMTEncoding_Term.decls_t  ->  Prims.bool = (fun r cache qhash cb decls -> (

let uu____7232 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____7232) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (FStar_Pervasives_Native.None); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash; z3result_query_decls = []}
in ((cb result);
true;
));
))
end
| uu____7261 -> begin
false
end)
end
| uu____7266 -> begin
false
end)))


let ask_1_core : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry cb -> (

let cumm_theory = (

let uu____7326 = (FStar_Options.report_qi ())
in (match (uu____7326) with
| true -> begin
(

let uu____7329 = (cummulative_scope ())
in (FStar_List.append uu____7329 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
end
| uu____7332 -> begin
[]
end))
in (

let incr_theory = (

let uu____7335 = (incremental_scope ())
in (FStar_List.append uu____7335 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in ((clear_scope ());
(

let uu____7339 = (filter_theory incr_theory)
in (match (uu____7339) with
| (incr_theory1, used_unsat_core) -> begin
(

let uu____7349 = uu____7339
in (

let uu____7355 = (mk_input incr_theory1)
in (match (uu____7355) with
| (input, qhash) -> begin
(

let uu____7374 = uu____7355
in (

let uu____7383 = (

let uu____7385 = (cache_hit r cache qhash cb cumm_theory)
in (not (uu____7385)))
in (match (uu____7383) with
| true -> begin
(run_job {job = (z3_job r false label_messages input cumm_theory qhash); callback = cb})
end
| uu____7393 -> begin
()
end)))
end)))
end));
))))


let ask_n_cores : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

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

let uu____7465 = (filter_theory theory)
in (match (uu____7465) with
| (theory1, used_unsat_core) -> begin
(

let uu____7475 = uu____7465
in (

let uu____7481 = (mk_input theory1)
in (match (uu____7481) with
| (input, qhash) -> begin
(

let cumm_theory = (

let uu____7501 = (FStar_Options.report_qi ())
in (match (uu____7501) with
| true -> begin
theory1
end
| uu____7504 -> begin
[]
end))
in (

let uu____7506 = (

let uu____7508 = (cache_hit r cache qhash cb theory1)
in (not (uu____7508)))
in (match (uu____7506) with
| true -> begin
(enqueue {job = (z3_job r true label_messages input cumm_theory qhash); callback = cb})
end
| uu____7516 -> begin
()
end)))
end)))
end))))


let ask : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter1 cache label_messages qry scope cb -> (

let uu____7585 = (

let uu____7587 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7587 (Prims.parse_int "1")))
in (match (uu____7585) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb)
end
| uu____7594 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




