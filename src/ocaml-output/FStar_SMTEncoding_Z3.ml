
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

let rec aux = (fun uu___123_62 -> (match (uu___123_62) with
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

let run_proc_result = (FStar_All.try_with (fun uu___128_147 -> (match (()) with
| () -> begin
(

let uu____151 = (

let uu____153 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____153 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____151))
end)) (fun uu___127_162 -> FStar_Pervasives_Native.None))
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

type qi_info =
{instances : Prims.int; max_generation : Prims.int; max_cost : Prims.int}


let __proj__Mkqi_info__item__instances : qi_info  ->  Prims.int = (fun projectee -> (match (projectee) with
| {instances = instances; max_generation = max_generation; max_cost = max_cost} -> begin
instances
end))


let __proj__Mkqi_info__item__max_generation : qi_info  ->  Prims.int = (fun projectee -> (match (projectee) with
| {instances = instances; max_generation = max_generation; max_cost = max_cost} -> begin
max_generation
end))


let __proj__Mkqi_info__item__max_cost : qi_info  ->  Prims.int = (fun projectee -> (match (projectee) with
| {instances = instances; max_generation = max_generation; max_cost = max_cost} -> begin
max_cost
end))


type qi_profile =
qi_info FStar_Util.psmap


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___124_678 -> (match (uu___124_678) with
| SAT (uu____680) -> begin
"sat"
end
| UNSAT (uu____689) -> begin
"unsat"
end
| UNKNOWN (uu____695) -> begin
"unknown"
end
| TIMEOUT (uu____704) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(

let uu____732 = (status_tag s)
in ((uu____732), ([])))
end
| UNSAT (uu____737) -> begin
(

let uu____742 = (status_tag s)
in ((uu____742), ([])))
end
| SAT (errs, msg) -> begin
(

let uu____755 = (

let uu____757 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____757 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____755), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____778 = (

let uu____780 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____780 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____778), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____801 = (

let uu____803 = (status_tag s)
in (FStar_Util.format2 "%s%s" uu____803 (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end)))
in ((uu____801), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____822 -> (

let uu____824 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____824 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let permissive = (FStar_Options.analyze_proof ())
in (

let uu____838 = (FStar_Options.z3_exe ())
in (

let uu____840 = (ini_params ())
in (FStar_Util.start_process id1 uu____838 uu____840 permissive (fun s -> (Prims.op_Equality s "Done!")))))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  Prims.string; restart : unit  ->  unit}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
restart
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

let get_module_name = (fun uu____1340 -> (

let uu____1342 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1342) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1405 -> (

let uu____1406 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1406) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1464 = (

let uu____1473 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1548 -> (match (uu____1548) with
| (m, uu____1557) -> begin
(Prims.op_Equality n1 m)
end)) uu____1473))
in (match (uu____1464) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1571 = (

let uu____1580 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1580)
in (FStar_ST.op_Colon_Equals used_file_names uu____1571));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1712, k) -> begin
((

let uu____1725 = (

let uu____1734 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1734)
in (FStar_ST.op_Colon_Equals used_file_names uu____1725));
(

let uu____1866 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1866));
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

let get_log_file = (fun uu____1974 -> (

let uu____1975 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1975) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2032 = (get_log_file ())
in (FStar_Util.append_to_file uu____2032 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2043 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2043) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2098 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2098) with
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

let uu____2257 = (

let uu____2259 = (FStar_ST.op_Bang query_number)
in (uu____2259 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2257));
(

let file_name = (

let uu____2350 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2350))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2363 = (

let uu____2365 = (FStar_Options.n_cores ())
in (uu____2365 > (Prims.parse_int "1")))
in (match (uu____2363) with
| true -> begin
(write_to_new_log str)
end
| uu____2369 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2376 -> (

let uu____2377 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2377) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2478 -> (

let uu____2480 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2480) with
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

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____2570 -> (

let uu____2571 = (

let uu____2573 = ((FStar_Util.incr ctr);
(

let uu____2609 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2609 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2573))
in (new_z3proc uu____2571))))
in (

let z3proc = (fun uu____2662 -> ((

let uu____2664 = (

let uu____2666 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2666 FStar_Pervasives_Native.None))
in (match (uu____2664) with
| true -> begin
(

let uu____2717 = (

let uu____2720 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2720))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2717))
end
| uu____2766 -> begin
()
end));
(

let uu____2768 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2768));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____2835 -> "\nkilled\n")
in (

let uu____2837 = (z3proc ())
in (FStar_Util.ask_process uu____2837 input kill_handler))))
in (

let refresh = (fun uu____2844 -> (

let out = (

let uu____2848 = (z3proc ())
in (FStar_Util.kill_process uu____2848))
in ((

let uu____2850 = (

let uu____2853 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2853))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2850));
(query_logging.close_log ());
out;
)))
in (

let restart = (fun uu____2905 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2953 = (

let uu____2956 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2956))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2953));
))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart)}))))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


let at_log_file : unit  ->  Prims.string = (fun uu____3042 -> (

let uu____3044 = (FStar_Options.log_queries ())
in (match (uu____3044) with
| true -> begin
(

let uu____3048 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____3048))
end
| uu____3051 -> begin
""
end)))


type smt_output_section =
Prims.string Prims.list

type smt_output =
{smt_result : smt_output_section; smt_reason_unknown : smt_output_section FStar_Pervasives_Native.option; smt_unsat_core : smt_output_section FStar_Pervasives_Native.option; smt_statistics : smt_output_section FStar_Pervasives_Native.option; smt_labels : smt_output_section FStar_Pervasives_Native.option; smt_refutation : smt_output_section FStar_Pervasives_Native.option; smt_qiprofile : smt_output_section FStar_Pervasives_Native.option}


let __proj__Mksmt_output__item__smt_result : smt_output  ->  smt_output_section = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_result
end))


let __proj__Mksmt_output__item__smt_reason_unknown : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_reason_unknown
end))


let __proj__Mksmt_output__item__smt_unsat_core : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_unsat_core
end))


let __proj__Mksmt_output__item__smt_statistics : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_statistics
end))


let __proj__Mksmt_output__item__smt_labels : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_labels
end))


let __proj__Mksmt_output__item__smt_refutation : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_refutation
end))


let __proj__Mksmt_output__item__smt_qiprofile : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels; smt_refutation = smt_refutation; smt_qiprofile = smt_qiprofile} -> begin
smt_qiprofile
end))


let parse_qi_info : Prims.string  ->  (Prims.string * qi_info) = (fun line -> (

let uu____3321 = (

let uu____3325 = (

let uu____3329 = (FStar_Util.substring_from line (Prims.parse_int "22"))
in (FStar_Util.split uu____3329 ":"))
in (FStar_All.pipe_right uu____3325 (FStar_List.map FStar_Util.trim_string)))
in (match (uu____3321) with
| (id1)::(inst1)::(gen1)::(cost)::[] -> begin
(

let uu____3359 = (

let uu____3360 = (FStar_Util.int_of_string inst1)
in (

let uu____3362 = (FStar_Util.int_of_string gen1)
in (

let uu____3364 = (FStar_Util.int_of_string cost)
in {instances = uu____3360; max_generation = uu____3362; max_cost = uu____3364})))
in ((id1), (uu____3359)))
end
| uu____3367 -> begin
(failwith "could not parse quantifier instantiation info")
end)))


let smt_output_sections : FStar_Range.range  ->  Prims.string Prims.list  ->  smt_output = (fun r output_lines -> (

let rec until = (fun tag lines -> (match (lines) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (l)::lines1 -> begin
(match ((Prims.op_Equality tag l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines1)))
end
| uu____3486 -> begin
(

let uu____3488 = (until tag lines1)
in (FStar_Util.map_opt uu____3488 (fun uu____3524 -> (match (uu____3524) with
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

let find_section = (fun tag lines -> (

let uu____3631 = (until (start_tag tag) lines)
in (match (uu____3631) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3701 = (until (end_tag tag) suffix)
in (match (uu____3701) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3786 = (

let uu____3796 = (FStar_Options.analyze_proof ())
in (match (uu____3796) with
| true -> begin
(

let uu____3808 = (FStar_List.partition (fun x -> (FStar_Util.starts_with x "[quantifier_instances]")) output_lines)
in (match (uu____3808) with
| (u, v1) -> begin
((FStar_Pervasives_Native.Some (u)), (v1))
end))
end
| uu____3852 -> begin
((FStar_Pervasives_Native.None), (output_lines))
end))
in (match (uu____3786) with
| (qilines, lines) -> begin
(

let uu____3871 = uu____3786
in (

let uu____3881 = (find_section "result" lines)
in (match (uu____3881) with
| (result_opt, lines1) -> begin
(

let uu____3904 = uu____3881
in (

let result = (FStar_Util.must result_opt)
in (

let uu____3915 = (find_section "reason-unknown" lines1)
in (match (uu____3915) with
| (reason_unknown, lines2) -> begin
(

let uu____3938 = uu____3915
in (

let uu____3948 = (find_section "unsat-core" lines2)
in (match (uu____3948) with
| (unsat_core, lines3) -> begin
(

let uu____3971 = uu____3948
in (

let uu____3981 = (

let uu____3991 = (FStar_Options.analyze_proof ())
in (match (uu____3991) with
| true -> begin
(find_section "proof" lines3)
end
| uu____4004 -> begin
((FStar_Pervasives_Native.None), (lines3))
end))
in (match (uu____3981) with
| (refutation, lines4) -> begin
(

let uu____4023 = uu____3981
in (

let uu____4033 = (find_section "statistics" lines4)
in (match (uu____4033) with
| (statistics, lines5) -> begin
(

let uu____4056 = uu____4033
in (

let uu____4066 = (find_section "labels" lines5)
in (match (uu____4066) with
| (labels, lines6) -> begin
(

let uu____4089 = uu____4066
in (

let remaining = (

let uu____4103 = (until "Done!" lines6)
in (match (uu____4103) with
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
| uu____4157 -> begin
(

let uu____4161 = (

let uu____4167 = (FStar_Util.format1 "Unexpected additional output from Z3: %s\n" (FStar_String.concat "\n" remaining))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4167)))
in (FStar_Errors.log_issue r uu____4161))
end);
(

let uu____4172 = (FStar_Util.must result_opt)
in {smt_result = uu____4172; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels; smt_refutation = refutation; smt_qiprofile = qilines});
)))
end)))
end)))
end)))
end)))
end))))
end)))
end)))))))


let doZ3Exe : FStar_Range.range  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics * qi_profile) = (fun r fresh input label_messages -> (

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
| uu____4260 -> begin
(

let uu____4262 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4262))
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

let uu____4308 = (lblnegs rest)
in (lname)::uu____4308)
end
| (lname)::(uu____4314)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4324 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4353 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____4412 -> (match (uu____4412) with
| (m, uu____4427, uu____4428) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____4353) with
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
| uu____4591 -> begin
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
| uu____4620 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____4623 -> begin
()
end)))
in ((FStar_List.iter parse_line lines1);
statistics;
))
end))
in (

let qiprofile = (match (smt_output.smt_qiprofile) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.psmap_empty ())
end
| FStar_Pervasives_Native.Some (lines1) -> begin
(

let qips = (FStar_List.map parse_qi_info lines1)
in (

let uu____4645 = (FStar_Util.psmap_empty ())
in (FStar_List.fold_left (fun x uu____4656 -> (match (uu____4656) with
| (y, z) -> begin
(FStar_Util.psmap_add x y z)
end)) uu____4645 qips)))
end)
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
| uu____4689 -> begin
ru
end))))
in (

let status = ((

let uu____4693 = (FStar_Options.debug_any ())
in (match (uu____4693) with
| true -> begin
(

let uu____4696 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____4696))
end
| uu____4701 -> begin
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

let uu____4728 = (

let uu____4733 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4733.restart)
in (uu____4728 ()));
KILLED;
)
end
| uu____4753 -> begin
(

let uu____4754 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____4754))
end);
)
in ((status), (statistics), (qiprofile))))))))))))
in (

let stdout1 = (

let uu____4763 = (FStar_Options.analyze_proof ())
in (match (uu____4763) with
| true -> begin
(

let askout = (

let uu____4769 = (

let uu____4776 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4776.ask)
in (uu____4769 input))
in (

let refreshout = (

let uu____4798 = (

let uu____4804 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4804.refresh)
in (uu____4798 ()))
in (Prims.strcat askout (Prims.strcat "\n" refreshout))))
end
| uu____4825 -> begin
(match (fresh) with
| true -> begin
(

let uu____4829 = (tid ())
in (

let uu____4831 = (FStar_Options.z3_exe ())
in (

let uu____4833 = (ini_params ())
in (FStar_Util.run_process uu____4829 uu____4831 uu____4833 (FStar_Pervasives_Native.Some (input))))))
end
| uu____4838 -> begin
(

let uu____4840 = (

let uu____4847 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4847.ask)
in (uu____4840 input))
end)
end))
in (parse (FStar_Util.trim_string stdout1)))))


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

type z3result =
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_qiprofile : qi_profile; z3result_query_hash : Prims.string FStar_Pervasives_Native.option; z3result_query_decls : FStar_SMTEncoding_Term.decl Prims.list; z3result_query_info : query_info}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_qiprofile : z3result  ->  qi_profile = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_qiprofile
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_query_hash
end))


let __proj__Mkz3result__item__z3result_query_decls : z3result  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_query_decls
end))


let __proj__Mkz3result__item__z3result_query_info : z3result  ->  query_info = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_qiprofile = z3result_qiprofile; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_query_info = z3result_query_info} -> begin
z3result_query_info
end))


type z3job =
z3result job_t


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let z3_job : query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun r fresh label_messages input decls qhash uu____5310 -> (

let start = (FStar_Util.now ())
in (

let uu____5319 = (FStar_All.try_with (fun uu___130_5333 -> (match (()) with
| () -> begin
(doZ3Exe r.query_info_range fresh input label_messages)
end)) (fun uu___129_5342 -> if (

let uu____5349 = (FStar_Options.trace_error ())
in (not (uu____5349))) then begin
(Obj.magic ((Obj.repr ((

let uu____5352 = (

let uu____5354 = (

let uu____5360 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5360.refresh)
in (uu____5354 ()))
in (FStar_All.pipe_left (fun a1 -> ()) uu____5352));
(FStar_Exn.raise uu___129_5342);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____5319) with
| (status, statistics, qiprofile) -> begin
(

let uu____5390 = uu____5319
in (

let uu____5397 = (

let uu____5403 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5403))
in (match (uu____5397) with
| (uu____5404, elapsed_time) -> begin
(

let uu____5408 = uu____5397
in {z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_qiprofile = qiprofile; z3result_query_hash = qhash; z3result_query_decls = decls; z3result_query_info = r})
end)))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____5444 -> (

let j = (

let uu____5446 = (FStar_ST.op_Bang job_queue)
in (match (uu____5446) with
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
(FStar_Util.with_monitor job_queue (fun uu____5514 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____5516 -> (

let uu____5517 = (FStar_ST.op_Bang running)
in if uu____5517 then begin
(

let rec aux = (fun uu____5545 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____5551 = (FStar_ST.op_Bang job_queue)
in (match (uu____5551) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____5584 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____5588 = (j.job ())
in (FStar_All.pipe_left j.callback uu____5588)))


let init : unit  ->  unit = (fun uu____5594 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____5633 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____5637 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____5651 -> ((

let uu____5653 = (

let uu____5656 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____5656 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____5653));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____5714 -> (

let rec aux = (fun uu____5720 -> (

let uu____5721 = (FStar_Util.with_monitor job_queue (fun uu____5739 -> (

let uu____5740 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____5763 = (

let uu____5764 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____5764))
in ((uu____5740), (uu____5763))))) ())
in (match (uu____5721) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____5828 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let stack_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let stack_delta : FStar_SMTEncoding_Term.decls_t FStar_ST.ref = (FStar_Util.mk_ref [])


let incremental_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____5873 -> (FStar_ST.op_Bang stack_delta))


let cummulative_scope : unit  ->  FStar_SMTEncoding_Term.decls_t = (fun uu____5898 -> (

let uu____5899 = (

let uu____5904 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.rev uu____5904))
in (FStar_List.flatten uu____5899)))


let clear_scope : unit  ->  unit = (fun uu____5935 -> (FStar_ST.op_Colon_Equals stack_delta []))


let get_scope : unit  ->  scope_t = (fun uu____5960 -> (FStar_ST.op_Bang stack_scope))


let reset_scope : unit  ->  unit = (fun uu____5985 -> (

let uu____5986 = (cummulative_scope ())
in (FStar_ST.op_Colon_Equals stack_delta uu____5986)))


let add_to_scopes : FStar_SMTEncoding_Term.decls_t  ->  unit = (fun decls -> ((

let uu____6013 = (FStar_ST.op_Bang stack_scope)
in (match (uu____6013) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals stack_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6064 -> begin
(failwith "Impossible")
end));
(

let uu____6066 = (

let uu____6067 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6067 decls))
in (FStar_ST.op_Colon_Equals stack_delta uu____6066));
))


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6119 -> ((

let uu____6121 = (

let uu____6122 = (FStar_ST.op_Bang stack_scope)
in ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])::uu____6122)
in (FStar_ST.op_Colon_Equals stack_scope uu____6121));
(

let uu____6167 = (

let uu____6168 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6168 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6167));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____6220 -> ((

let uu____6222 = (

let uu____6223 = (FStar_ST.op_Bang stack_scope)
in (FStar_List.tl uu____6223))
in (FStar_ST.op_Colon_Equals stack_scope uu____6222));
(

let uu____6268 = (

let uu____6269 = (FStar_ST.op_Bang stack_delta)
in (FStar_List.append uu____6269 ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals stack_delta uu____6268));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push stack_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____6348 -> (pop msg)) stack_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___125_6361 -> (match (uu___125_6361) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6364 -> begin
()
end))));
(add_to_scopes decls);
))


let refresh : unit  ->  unit = (fun uu____6370 -> ((

let uu____6372 = (

let uu____6374 = (FStar_Options.n_cores ())
in (uu____6374 < (Prims.parse_int "2")))
in (match (uu____6372) with
| true -> begin
(

let uu____6378 = (

let uu____6380 = (

let uu____6386 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6386.refresh)
in (uu____6380 ()))
in (FStar_All.pipe_left (fun a2 -> ()) uu____6378))
end
| uu____6407 -> begin
()
end));
(reset_scope ());
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (FStar_ST.op_Bang z3_options)
in (

let uu____6458 = (

let uu____6467 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____6467) with
| true -> begin
(

let uu____6478 = (

let uu____6489 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___126_6517 -> (match (uu___126_6517) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____6520 -> begin
false
end))))
in (FStar_All.pipe_right uu____6489 FStar_Option.get))
in (match (uu____6478) with
| (prefix1, check_sat, suffix) -> begin
(

let uu____6573 = uu____6478
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

let uu____6614 = (FStar_Options.keep_query_captions ())
in (match (uu____6614) with
| true -> begin
(

let uu____6618 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____6618 (FStar_String.concat "\n")))
end
| uu____6633 -> begin
ps
end))
in (

let uu____6635 = (

let uu____6639 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____6639))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____6635)))))))))))
end))
end
| uu____6647 -> begin
(

let uu____6649 = (

let uu____6651 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____6651 (FStar_String.concat "\n")))
in ((uu____6649), (FStar_Pervasives_Native.None)))
end))
in (match (uu____6458) with
| (r, hash) -> begin
(

let uu____6684 = uu____6458
in ((

let uu____6694 = (FStar_Options.log_queries ())
in (match (uu____6694) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____6697 -> begin
()
end));
((r), (hash));
))
end))))


type cb =
z3result  ->  unit


let cache_hit : query_info  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  FStar_SMTEncoding_Term.decls_t  ->  Prims.bool = (fun r cache qhash cb decls -> (

let uu____6750 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____6750) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = (

let uu____6772 = (FStar_Util.psmap_empty ())
in {z3result_status = UNSAT (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_qiprofile = uu____6772; z3result_query_hash = qhash; z3result_query_decls = decls; z3result_query_info = r})
in ((cb result);
true;
));
))
end
| uu____6783 -> begin
false
end)
end
| uu____6788 -> begin
false
end)))


let ask_1_core : query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry cb -> (

let cumm_theory = (

let uu____6848 = (cummulative_scope ())
in (FStar_List.append uu____6848 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let incr_theory = (

let uu____6852 = (incremental_scope ())
in (FStar_List.append uu____6852 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in ((

let uu____6856 = (FStar_Options.analyze_proof ())
in (match (uu____6856) with
| true -> begin
(reset_scope ())
end
| uu____6859 -> begin
(clear_scope ())
end));
(

let uu____6861 = (filter_theory incr_theory)
in (match (uu____6861) with
| (incr_theory1, used_unsat_core) -> begin
(

let uu____6871 = uu____6861
in (

let uu____6877 = (mk_input incr_theory1)
in (match (uu____6877) with
| (input, qhash) -> begin
(

let uu____6896 = uu____6877
in (

let uu____6905 = (

let uu____6907 = (cache_hit r cache qhash cb cumm_theory)
in (not (uu____6907)))
in (match (uu____6905) with
| true -> begin
(run_job {job = (z3_job r false label_messages input cumm_theory qhash); callback = cb})
end
| uu____6915 -> begin
()
end)))
end)))
end));
))))


let ask_n_cores : query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

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

let uu____6987 = (filter_theory theory)
in (match (uu____6987) with
| (theory1, used_unsat_core) -> begin
(

let uu____6997 = uu____6987
in (

let uu____7003 = (mk_input theory1)
in (match (uu____7003) with
| (input, qhash) -> begin
(

let uu____7022 = (

let uu____7024 = (cache_hit r cache qhash cb theory1)
in (not (uu____7024)))
in (match (uu____7022) with
| true -> begin
(enqueue {job = (z3_job r true label_messages input theory1 qhash); callback = cb})
end
| uu____7032 -> begin
()
end))
end)))
end))))


let ask : query_info  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter1 cache label_messages qry scope cb -> (

let uu____7101 = (

let uu____7103 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7103 (Prims.parse_int "1")))
in (match (uu____7101) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb)
end
| uu____7110 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




