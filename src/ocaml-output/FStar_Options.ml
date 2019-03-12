
open Prims
open FStar_Pervasives

let debug_embedding : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let eager_embedding : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of Prims.string


let uu___is_Low : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Low -> begin
true
end
| uu____71 -> begin
false
end))


let uu___is_Medium : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Medium -> begin
true
end
| uu____82 -> begin
false
end))


let uu___is_High : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| High -> begin
true
end
| uu____93 -> begin
false
end))


let uu___is_Extreme : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Extreme -> begin
true
end
| uu____104 -> begin
false
end))


let uu___is_Other : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
true
end
| uu____117 -> begin
false
end))


let __proj__Other__item___0 : debug_level_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
_0
end))

type option_val =
| Bool of Prims.bool
| String of Prims.string
| Path of Prims.string
| Int of Prims.int
| List of option_val Prims.list
| Unset


let uu___is_Bool : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
true
end
| uu____172 -> begin
false
end))


let __proj__Bool__item___0 : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
_0
end))


let uu___is_String : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String (_0) -> begin
true
end
| uu____196 -> begin
false
end))


let __proj__String__item___0 : option_val  ->  Prims.string = (fun projectee -> (match (projectee) with
| String (_0) -> begin
_0
end))


let uu___is_Path : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Path (_0) -> begin
true
end
| uu____220 -> begin
false
end))


let __proj__Path__item___0 : option_val  ->  Prims.string = (fun projectee -> (match (projectee) with
| Path (_0) -> begin
_0
end))


let uu___is_Int : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
true
end
| uu____244 -> begin
false
end))


let __proj__Int__item___0 : option_val  ->  Prims.int = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
_0
end))


let uu___is_List : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| List (_0) -> begin
true
end
| uu____269 -> begin
false
end))


let __proj__List__item___0 : option_val  ->  option_val Prims.list = (fun projectee -> (match (projectee) with
| List (_0) -> begin
_0
end))


let uu___is_Unset : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unset -> begin
true
end
| uu____294 -> begin
false
end))


let mk_bool : Prims.bool  ->  option_val = (fun _0_1 -> Bool (_0_1))


let mk_string : Prims.string  ->  option_val = (fun _0_2 -> String (_0_2))


let mk_path : Prims.string  ->  option_val = (fun _0_3 -> Path (_0_3))


let mk_int : Prims.int  ->  option_val = (fun _0_4 -> Int (_0_4))


let mk_list : option_val Prims.list  ->  option_val = (fun _0_5 -> List (_0_5))

type options =
| Set
| Reset
| Restore


let uu___is_Set : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Set -> begin
true
end
| uu____336 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____347 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____358 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : unit  ->  Prims.bool = (fun uu____383 -> (FStar_ST.op_Bang __unit_tests__))


let __set_unit_tests : unit  ->  unit = (fun uu____410 -> (FStar_ST.op_Colon_Equals __unit_tests__ true))


let __clear_unit_tests : unit  ->  unit = (fun uu____438 -> (FStar_ST.op_Colon_Equals __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___80_467 -> (match (uu___80_467) with
| Bool (b) -> begin
b
end
| uu____471 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___81_480 -> (match (uu___81_480) with
| Int (b) -> begin
b
end
| uu____484 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___82_493 -> (match (uu___82_493) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____499 -> begin
(failwith "Impos: expected String")
end))


let as_list' : option_val  ->  option_val Prims.list = (fun uu___83_509 -> (match (uu___83_509) with
| List (ts) -> begin
ts
end
| uu____515 -> begin
(failwith "Impos: expected List")
end))


let as_list : 'Auu____526 . (option_val  ->  'Auu____526)  ->  option_val  ->  'Auu____526 Prims.list = (fun as_t x -> (

let uu____544 = (as_list' x)
in (FStar_All.pipe_right uu____544 (FStar_List.map as_t))))


let as_option : 'Auu____558 . (option_val  ->  'Auu____558)  ->  option_val  ->  'Auu____558 FStar_Pervasives_Native.option = (fun as_t uu___84_573 -> (match (uu___84_573) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____577 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____577))
end))


let as_comma_string_list : option_val  ->  Prims.string Prims.list = (fun uu___85_586 -> (match (uu___85_586) with
| List (ls) -> begin
(

let uu____593 = (FStar_List.map (fun l -> (

let uu____605 = (as_string l)
in (FStar_Util.split uu____605 ","))) ls)
in (FStar_All.pipe_left FStar_List.flatten uu____593))
end
| uu____617 -> begin
(failwith "Impos: expected String (comma list)")
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : unit  ->  optionstate = (fun uu____653 -> (

let uu____654 = (

let uu____657 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____657))
in (FStar_List.hd uu____654)))


let pop : unit  ->  unit = (fun uu____696 -> (

let uu____697 = (FStar_ST.op_Bang fstar_options)
in (match (uu____697) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____732)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____740)::tl1 -> begin
(FStar_ST.op_Colon_Equals fstar_options tl1)
end)))


let push : unit  ->  unit = (fun uu____782 -> (

let uu____783 = (

let uu____788 = (

let uu____791 = (

let uu____794 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____794))
in (FStar_List.map FStar_Util.smap_copy uu____791))
in (

let uu____828 = (FStar_ST.op_Bang fstar_options)
in (uu____788)::uu____828))
in (FStar_ST.op_Colon_Equals fstar_options uu____783)))


let internal_pop : unit  ->  Prims.bool = (fun uu____895 -> (

let curstack = (

let uu____899 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____899))
in (match (curstack) with
| [] -> begin
(failwith "impossible: empty current option stack")
end
| (uu____936)::[] -> begin
false
end
| (uu____938)::tl1 -> begin
((

let uu____943 = (

let uu____948 = (

let uu____953 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.tl uu____953))
in (tl1)::uu____948)
in (FStar_ST.op_Colon_Equals fstar_options uu____943));
true;
)
end)))


let internal_push : unit  ->  unit = (fun uu____1022 -> (

let curstack = (

let uu____1026 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____1026))
in (

let stack' = (

let uu____1063 = (

let uu____1064 = (FStar_List.hd curstack)
in (FStar_Util.smap_copy uu____1064))
in (uu____1063)::curstack)
in (

let uu____1067 = (

let uu____1072 = (

let uu____1077 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.tl uu____1077))
in (stack')::uu____1072)
in (FStar_ST.op_Colon_Equals fstar_options uu____1067)))))


let set : optionstate  ->  unit = (fun o -> (

let uu____1146 = (FStar_ST.op_Bang fstar_options)
in (match (uu____1146) with
| [] -> begin
(failwith "set on empty option stack")
end
| ([])::uu____1181 -> begin
(failwith "set on empty current option stack")
end
| ((uu____1189)::tl1)::os -> begin
(FStar_ST.op_Colon_Equals fstar_options (((o)::tl1)::os))
end)))


let snapshot : unit  ->  (Prims.int * unit) = (fun uu____1239 -> (FStar_Common.snapshot push fstar_options ()))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop fstar_options depth))


let set_option : Prims.string  ->  option_val  ->  unit = (fun k v1 -> (

let uu____1269 = (peek ())
in (FStar_Util.smap_add uu____1269 k v1)))


let set_option' : (Prims.string * option_val)  ->  unit = (fun uu____1282 -> (match (uu____1282) with
| (k, v1) -> begin
(set_option k v1)
end))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  unit = (fun filename -> (

let uu____1321 = (

let uu____1325 = (FStar_ST.op_Bang light_off_files)
in (filename)::uu____1325)
in (FStar_ST.op_Colon_Equals light_off_files uu____1321)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("__temp_fast_implicits"), (Bool (false))))::((("abort_on"), (Int ((Prims.parse_int "0")))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("already_cached"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("cache_dir"), (Unset)))::((("cache_off"), (Bool (false))))::((("cmi"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("defensive"), (String ("no"))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("eager_subtyping"), (Bool (false))))::((("expose_interfaces"), (Bool (false))))::((("extract"), (Unset)))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("full_context_dependency"), (Bool (true))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("print"), (Bool (false))))::((("print_in_place"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("keep_query_captions"), (Bool (true))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_smt"), (Bool (false))))::((("no_plugins"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("normalize_pure_terms_for_extraction"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("tactics_failhard"), (Bool (false))))::((("tactics_info"), (Bool (false))))::((("tactic_raw_binders"), (Bool (false))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("tcnorm"), (Bool (true))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("use_hint_hashes"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("vcgen.optimize_bind_as_seq"), (Unset)))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("use_two_phase_tc"), (Bool (true))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::((("__tactics_nbe"), (Bool (false))))::((("warn_error"), (String (""))))::((("use_extracted_interfaces"), (Bool (false))))::((("use_nbe"), (Bool (false))))::((("report_qi"), (Bool (false))))::((("smt_proof"), (Bool (false))))::[]


let init : unit  ->  unit = (fun uu____2235 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : unit  ->  unit = (fun uu____2255 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options (((o)::[])::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____2328 = (

let uu____2331 = (peek ())
in (FStar_Util.smap_try_find uu____2331 s))
in (match (uu____2328) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____2344 . Prims.string  ->  (option_val  ->  'Auu____2344)  ->  'Auu____2344 = (fun s c -> (

let uu____2362 = (get_option s)
in (c uu____2362)))


let get_abort_on : unit  ->  Prims.int = (fun uu____2369 -> (lookup_opt "abort_on" as_int))


let get_admit_smt_queries : unit  ->  Prims.bool = (fun uu____2378 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2389 -> (lookup_opt "admit_except" (as_option as_string)))


let get_already_cached : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2405 -> (lookup_opt "already_cached" (as_option (as_list as_string))))


let get_cache_checked_modules : unit  ->  Prims.bool = (fun uu____2422 -> (lookup_opt "cache_checked_modules" as_bool))


let get_cache_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2433 -> (lookup_opt "cache_dir" (as_option as_string)))


let get_cache_off : unit  ->  Prims.bool = (fun uu____2445 -> (lookup_opt "cache_off" as_bool))


let get_cmi : unit  ->  Prims.bool = (fun uu____2454 -> (lookup_opt "cmi" as_bool))


let get_codegen : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2465 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : unit  ->  Prims.string Prims.list = (fun uu____2479 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : unit  ->  Prims.string Prims.list = (fun uu____2493 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : unit  ->  Prims.string Prims.list = (fun uu____2507 -> (lookup_opt "debug_level" as_comma_string_list))


let get_defensive : unit  ->  Prims.string = (fun uu____2518 -> (lookup_opt "defensive" as_string))


let get_dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2529 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : unit  ->  Prims.bool = (fun uu____2541 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : unit  ->  Prims.bool = (fun uu____2550 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : unit  ->  Prims.bool = (fun uu____2559 -> (lookup_opt "doc" as_bool))


let get_dump_module : unit  ->  Prims.string Prims.list = (fun uu____2570 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_subtyping : unit  ->  Prims.bool = (fun uu____2582 -> (lookup_opt "eager_subtyping" as_bool))


let get_expose_interfaces : unit  ->  Prims.bool = (fun uu____2591 -> (lookup_opt "expose_interfaces" as_bool))


let get_extract : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2604 -> (lookup_opt "extract" (as_option (as_list as_string))))


let get_extract_module : unit  ->  Prims.string Prims.list = (fun uu____2623 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : unit  ->  Prims.string Prims.list = (fun uu____2637 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : unit  ->  Prims.bool = (fun uu____2649 -> (lookup_opt "fs_typ_app" as_bool))


let get_hide_uvar_nums : unit  ->  Prims.bool = (fun uu____2658 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : unit  ->  Prims.bool = (fun uu____2667 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2678 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : unit  ->  Prims.bool = (fun uu____2690 -> (lookup_opt "in" as_bool))


let get_ide : unit  ->  Prims.bool = (fun uu____2699 -> (lookup_opt "ide" as_bool))


let get_include : unit  ->  Prims.string Prims.list = (fun uu____2710 -> (lookup_opt "include" (as_list as_string)))


let get_print : unit  ->  Prims.bool = (fun uu____2722 -> (lookup_opt "print" as_bool))


let get_print_in_place : unit  ->  Prims.bool = (fun uu____2731 -> (lookup_opt "print_in_place" as_bool))


let get_initial_fuel : unit  ->  Prims.int = (fun uu____2740 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : unit  ->  Prims.int = (fun uu____2749 -> (lookup_opt "initial_ifuel" as_int))


let get_keep_query_captions : unit  ->  Prims.bool = (fun uu____2758 -> (lookup_opt "keep_query_captions" as_bool))


let get_lax : unit  ->  Prims.bool = (fun uu____2767 -> (lookup_opt "lax" as_bool))


let get_load : unit  ->  Prims.string Prims.list = (fun uu____2778 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : unit  ->  Prims.bool = (fun uu____2790 -> (lookup_opt "log_queries" as_bool))


let get_log_types : unit  ->  Prims.bool = (fun uu____2799 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : unit  ->  Prims.int = (fun uu____2808 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : unit  ->  Prims.int = (fun uu____2817 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : unit  ->  Prims.int = (fun uu____2826 -> (lookup_opt "min_fuel" as_int))


let get_MLish : unit  ->  Prims.bool = (fun uu____2835 -> (lookup_opt "MLish" as_bool))


let get_n_cores : unit  ->  Prims.int = (fun uu____2844 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : unit  ->  Prims.bool = (fun uu____2853 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : unit  ->  Prims.string Prims.list = (fun uu____2864 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : unit  ->  Prims.bool = (fun uu____2876 -> (lookup_opt "no_location_info" as_bool))


let get_no_plugins : unit  ->  Prims.bool = (fun uu____2885 -> (lookup_opt "no_plugins" as_bool))


let get_no_smt : unit  ->  Prims.bool = (fun uu____2894 -> (lookup_opt "no_smt" as_bool))


let get_normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____2903 -> (lookup_opt "normalize_pure_terms_for_extraction" as_bool))


let get_odir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2914 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : unit  ->  Prims.bool = (fun uu____2926 -> (lookup_opt "ugly" as_bool))


let get_prims : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2937 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : unit  ->  Prims.bool = (fun uu____2949 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : unit  ->  Prims.bool = (fun uu____2958 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : unit  ->  Prims.bool = (fun uu____2967 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : unit  ->  Prims.bool = (fun uu____2976 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : unit  ->  Prims.bool = (fun uu____2985 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : unit  ->  Prims.bool = (fun uu____2994 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : unit  ->  Prims.bool = (fun uu____3003 -> (lookup_opt "prn" as_bool))


let get_query_stats : unit  ->  Prims.bool = (fun uu____3012 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : unit  ->  Prims.bool = (fun uu____3021 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3032 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_silent : unit  ->  Prims.bool = (fun uu____3044 -> (lookup_opt "silent" as_bool))


let get_smt : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3055 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____3067 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : unit  ->  Prims.string = (fun uu____3076 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : unit  ->  Prims.string = (fun uu____3085 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_tactic_raw_binders : unit  ->  Prims.bool = (fun uu____3094 -> (lookup_opt "tactic_raw_binders" as_bool))


let get_tactics_failhard : unit  ->  Prims.bool = (fun uu____3103 -> (lookup_opt "tactics_failhard" as_bool))


let get_tactics_info : unit  ->  Prims.bool = (fun uu____3112 -> (lookup_opt "tactics_info" as_bool))


let get_tactic_trace : unit  ->  Prims.bool = (fun uu____3121 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : unit  ->  Prims.int = (fun uu____3130 -> (lookup_opt "tactic_trace_d" as_int))


let get_tactics_nbe : unit  ->  Prims.bool = (fun uu____3139 -> (lookup_opt "__tactics_nbe" as_bool))


let get_tcnorm : unit  ->  Prims.bool = (fun uu____3148 -> (lookup_opt "tcnorm" as_bool))


let get_timing : unit  ->  Prims.bool = (fun uu____3157 -> (lookup_opt "timing" as_bool))


let get_trace_error : unit  ->  Prims.bool = (fun uu____3166 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : unit  ->  Prims.bool = (fun uu____3175 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____3184 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____3193 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : unit  ->  Prims.bool = (fun uu____3202 -> (lookup_opt "use_hints" as_bool))


let get_use_hint_hashes : unit  ->  Prims.bool = (fun uu____3211 -> (lookup_opt "use_hint_hashes" as_bool))


let get_use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3222 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : unit  ->  Prims.bool = (fun uu____3234 -> (

let uu____3235 = (lookup_opt "no_tactics" as_bool)
in (not (uu____3235))))


let get_using_facts_from : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____3249 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_vcgen_optimize_bind_as_seq : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3268 -> (lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)))


let get_verify_module : unit  ->  Prims.string Prims.list = (fun uu____3282 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : unit  ->  Prims.string Prims.list = (fun uu____3296 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : unit  ->  Prims.bool = (fun uu____3308 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : unit  ->  Prims.bool = (fun uu____3317 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : unit  ->  Prims.string Prims.list = (fun uu____3328 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : unit  ->  Prims.bool = (fun uu____3340 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : unit  ->  Prims.int = (fun uu____3349 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : unit  ->  Prims.int = (fun uu____3358 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : unit  ->  Prims.int = (fun uu____3367 -> (lookup_opt "z3seed" as_int))


let get_use_two_phase_tc : unit  ->  Prims.bool = (fun uu____3376 -> (lookup_opt "use_two_phase_tc" as_bool))


let get_no_positivity : unit  ->  Prims.bool = (fun uu____3385 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____3394 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let get_warn_error : unit  ->  Prims.string = (fun uu____3403 -> (lookup_opt "warn_error" as_string))


let get_use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____3412 -> (lookup_opt "use_extracted_interfaces" as_bool))


let get_use_nbe : unit  ->  Prims.bool = (fun uu____3421 -> (lookup_opt "use_nbe" as_bool))


let get_report_qi : unit  ->  Prims.bool = (fun uu____3430 -> (lookup_opt "report_qi" as_bool))


let get_smt_proof : unit  ->  Prims.bool = (fun uu____3439 -> (lookup_opt "smt_proof" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___86_3448 -> (match (uu___86_3448) with
| "Low" -> begin
Low
end
| "Medium" -> begin
Medium
end
| "High" -> begin
High
end
| "Extreme" -> begin
Extreme
end
| s -> begin
Other (s)
end))


let one_debug_level_geq : debug_level_t  ->  debug_level_t  ->  Prims.bool = (fun l1 l2 -> (match (l1) with
| Other (uu____3469) -> begin
(Prims.op_Equality l1 l2)
end
| Low -> begin
(Prims.op_Equality l1 l2)
end
| Medium -> begin
((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium))
end
| High -> begin
(((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium)) || (Prims.op_Equality l2 High))
end
| Extreme -> begin
((((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium)) || (Prims.op_Equality l2 High)) || (Prims.op_Equality l2 Extreme))
end))


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (

let uu____3478 = (get_debug_level ())
in (FStar_All.pipe_right uu____3478 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "<not set>")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : unit  ->  unit = (fun uu____3644 -> (

let uu____3645 = (

let uu____3647 = (FStar_ST.op_Bang _version)
in (

let uu____3670 = (FStar_ST.op_Bang _platform)
in (

let uu____3693 = (FStar_ST.op_Bang _compiler)
in (

let uu____3716 = (FStar_ST.op_Bang _date)
in (

let uu____3739 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3647 uu____3670 uu____3693 uu____3716 uu____3739))))))
in (FStar_Util.print_string uu____3645)))


let display_usage_aux : 'Auu____3770 'Auu____3771 . ('Auu____3770 * Prims.string * 'Auu____3771 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____3826 -> (match (uu____3826) with
| (uu____3839, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____3858 = (

let uu____3860 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____3860))
in (FStar_Util.print_string uu____3858))
end
| uu____3863 -> begin
(

let uu____3865 = (

let uu____3867 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____3867 doc))
in (FStar_Util.print_string uu____3865))
end)
end
| FStar_Getopt.OneArg (uu____3870, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____3885 = (

let uu____3887 = (FStar_Util.colorize_bold flag)
in (

let uu____3889 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____3887 uu____3889)))
in (FStar_Util.print_string uu____3885))
end
| uu____3892 -> begin
(

let uu____3894 = (

let uu____3896 = (FStar_Util.colorize_bold flag)
in (

let uu____3898 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____3896 uu____3898 doc)))
in (FStar_Util.print_string uu____3894))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____3933 = o
in (match (uu____3933) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____3975 -> (

let uu____3976 = (f ())
in (set_option name uu____3976)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____3997 = (f x)
in (set_option name uu____3997)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____4024 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____4024))
in (mk_list ((value)::prev_values))))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let uu____4050 = (

let uu____4053 = (lookup_opt name as_list')
in (FStar_List.append uu____4053 ((value)::[])))
in (mk_list uu____4050)))


let accumulate_string : 'Auu____4067 . Prims.string  ->  ('Auu____4067  ->  Prims.string)  ->  'Auu____4067  ->  unit = (fun name post_processor value -> (

let uu____4092 = (

let uu____4093 = (

let uu____4094 = (post_processor value)
in (mk_string uu____4094))
in (accumulated_option name uu____4093))
in (set_option name uu____4092)))


let add_extract_module : Prims.string  ->  unit = (fun s -> (accumulate_string "extract_module" FStar_String.lowercase s))


let add_extract_namespace : Prims.string  ->  unit = (fun s -> (accumulate_string "extract_namespace" FStar_String.lowercase s))


let add_verify_module : Prims.string  ->  unit = (fun s -> (accumulate_string "verify_module" FStar_String.lowercase s))

type opt_type =
| Const of option_val
| IntStr of Prims.string
| BoolStr
| PathStr of Prims.string
| SimpleStr of Prims.string
| EnumStr of Prims.string Prims.list
| OpenEnumStr of (Prims.string Prims.list * Prims.string)
| PostProcessed of ((option_val  ->  option_val) * opt_type)
| Accumulated of opt_type
| ReverseAccumulated of opt_type
| WithSideEffect of ((unit  ->  unit) * opt_type)


let uu___is_Const : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____4216 -> begin
false
end))


let __proj__Const__item___0 : opt_type  ->  option_val = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
_0
end))


let uu___is_IntStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IntStr (_0) -> begin
true
end
| uu____4237 -> begin
false
end))


let __proj__IntStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| IntStr (_0) -> begin
_0
end))


let uu___is_BoolStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BoolStr -> begin
true
end
| uu____4259 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____4272 -> begin
false
end))


let __proj__PathStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
_0
end))


let uu___is_SimpleStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SimpleStr (_0) -> begin
true
end
| uu____4296 -> begin
false
end))


let __proj__SimpleStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| SimpleStr (_0) -> begin
_0
end))


let uu___is_EnumStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EnumStr (_0) -> begin
true
end
| uu____4322 -> begin
false
end))


let __proj__EnumStr__item___0 : opt_type  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| EnumStr (_0) -> begin
_0
end))


let uu___is_OpenEnumStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OpenEnumStr (_0) -> begin
true
end
| uu____4359 -> begin
false
end))


let __proj__OpenEnumStr__item___0 : opt_type  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| OpenEnumStr (_0) -> begin
_0
end))


let uu___is_PostProcessed : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PostProcessed (_0) -> begin
true
end
| uu____4410 -> begin
false
end))


let __proj__PostProcessed__item___0 : opt_type  ->  ((option_val  ->  option_val) * opt_type) = (fun projectee -> (match (projectee) with
| PostProcessed (_0) -> begin
_0
end))


let uu___is_Accumulated : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Accumulated (_0) -> begin
true
end
| uu____4451 -> begin
false
end))


let __proj__Accumulated__item___0 : opt_type  ->  opt_type = (fun projectee -> (match (projectee) with
| Accumulated (_0) -> begin
_0
end))


let uu___is_ReverseAccumulated : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ReverseAccumulated (_0) -> begin
true
end
| uu____4471 -> begin
false
end))


let __proj__ReverseAccumulated__item___0 : opt_type  ->  opt_type = (fun projectee -> (match (projectee) with
| ReverseAccumulated (_0) -> begin
_0
end))


let uu___is_WithSideEffect : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
true
end
| uu____4498 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((unit  ->  unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4542) -> begin
true
end
| uu____4545 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4556) -> begin
uu____4556
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___91_4580 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____4582) -> begin
(

let uu____4584 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____4584) with
| FStar_Pervasives_Native.Some (v1) -> begin
(mk_int v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____4592 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____4599 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____4606 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in (mk_bool uu____4592))
end
| PathStr (uu____4609) -> begin
(mk_path str_val)
end
| SimpleStr (uu____4611) -> begin
(mk_string str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
(mk_string str_val)
end
| uu____4619 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____4621) -> begin
(mk_string str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____4638 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____4638))
end
| Accumulated (elem_spec) -> begin
(

let v1 = (parse_opt_val opt_name elem_spec str_val)
in (accumulated_option opt_name v1))
end
| ReverseAccumulated (elem_spec) -> begin
(

let v1 = (parse_opt_val opt_name elem_spec str_val)
in (reverse_accumulated_option opt_name v1))
end
| WithSideEffect (side_effect, elem_spec) -> begin
((side_effect ());
(parse_opt_val opt_name elem_spec str_val);
)
end)
end)) (fun uu___90_4655 -> (match (uu___90_4655) with
| InvalidArgument (opt_name1) -> begin
(

let uu____4658 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____4658))
end))))


let rec desc_of_opt_type : opt_type  ->  Prims.string FStar_Pervasives_Native.option = (fun typ -> (

let desc_of_enum = (fun cases -> FStar_Pervasives_Native.Some ((Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]"))))
in (match (typ) with
| Const (c) -> begin
FStar_Pervasives_Native.None
end
| IntStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| BoolStr -> begin
(desc_of_enum (("true")::("false")::[]))
end
| PathStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| SimpleStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| EnumStr (strs) -> begin
(desc_of_enum strs)
end
| OpenEnumStr (strs, desc) -> begin
(desc_of_enum (FStar_List.append strs ((desc)::[])))
end
| PostProcessed (uu____4728, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____4738, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____4769 = (desc_of_opt_type typ)
in (match (uu____4769) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____4777 -> (parser "")))
end
| FStar_Pervasives_Native.Some (desc) -> begin
FStar_Getopt.OneArg (((parser), (desc)))
end))))


let pp_validate_dir : option_val  ->  option_val = (fun p -> (

let pp = (as_string p)
in ((FStar_Util.mkdir false pp);
p;
)))


let pp_lowercase : option_val  ->  option_val = (fun s -> (

let uu____4803 = (

let uu____4805 = (as_string s)
in (FStar_String.lowercase uu____4805))
in (mk_string uu____4803)))


let abort_counter : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let rec specs_with_types : unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____4862 -> (

let uu____4876 = (

let uu____4890 = (

let uu____4904 = (

let uu____4918 = (

let uu____4932 = (

let uu____4944 = (

let uu____4945 = (mk_bool true)
in Const (uu____4945))
in ((FStar_Getopt.noshort), ("cache_checked_modules"), (uu____4944), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))
in (

let uu____4952 = (

let uu____4966 = (

let uu____4980 = (

let uu____4992 = (

let uu____4993 = (mk_bool true)
in Const (uu____4993))
in ((FStar_Getopt.noshort), ("cache_off"), (uu____4992), ("Do not read or write any .checked files")))
in (

let uu____5000 = (

let uu____5014 = (

let uu____5026 = (

let uu____5027 = (mk_bool true)
in Const (uu____5027))
in ((FStar_Getopt.noshort), ("cmi"), (uu____5026), ("Inline across module interfaces during extraction (aka. cross-module inlining)")))
in (

let uu____5034 = (

let uu____5048 = (

let uu____5062 = (

let uu____5076 = (

let uu____5090 = (

let uu____5104 = (

let uu____5118 = (

let uu____5132 = (

let uu____5144 = (

let uu____5145 = (mk_bool true)
in Const (uu____5145))
in ((FStar_Getopt.noshort), ("detail_errors"), (uu____5144), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))
in (

let uu____5152 = (

let uu____5166 = (

let uu____5178 = (

let uu____5179 = (mk_bool true)
in Const (uu____5179))
in ((FStar_Getopt.noshort), ("detail_hint_replay"), (uu____5178), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))
in (

let uu____5186 = (

let uu____5200 = (

let uu____5212 = (

let uu____5213 = (mk_bool true)
in Const (uu____5213))
in ((FStar_Getopt.noshort), ("doc"), (uu____5212), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))
in (

let uu____5220 = (

let uu____5234 = (

let uu____5248 = (

let uu____5260 = (

let uu____5261 = (mk_bool true)
in Const (uu____5261))
in ((FStar_Getopt.noshort), ("eager_inference"), (uu____5260), ("Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))
in (

let uu____5268 = (

let uu____5282 = (

let uu____5294 = (

let uu____5295 = (mk_bool true)
in Const (uu____5295))
in ((FStar_Getopt.noshort), ("eager_subtyping"), (uu____5294), ("Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")))
in (

let uu____5302 = (

let uu____5316 = (

let uu____5330 = (

let uu____5344 = (

let uu____5358 = (

let uu____5370 = (

let uu____5371 = (mk_bool true)
in Const (uu____5371))
in ((FStar_Getopt.noshort), ("expose_interfaces"), (uu____5370), ("Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")))
in (

let uu____5378 = (

let uu____5392 = (

let uu____5404 = (

let uu____5405 = (mk_bool true)
in Const (uu____5405))
in ((FStar_Getopt.noshort), ("hide_uvar_nums"), (uu____5404), ("Don\'t print unification variable numbers")))
in (

let uu____5412 = (

let uu____5426 = (

let uu____5440 = (

let uu____5452 = (

let uu____5453 = (mk_bool true)
in Const (uu____5453))
in ((FStar_Getopt.noshort), ("hint_info"), (uu____5452), ("Print information regarding hints (deprecated; use --query_stats instead)")))
in (

let uu____5460 = (

let uu____5474 = (

let uu____5486 = (

let uu____5487 = (mk_bool true)
in Const (uu____5487))
in ((FStar_Getopt.noshort), ("in"), (uu____5486), ("Legacy interactive mode; reads input from stdin")))
in (

let uu____5494 = (

let uu____5508 = (

let uu____5520 = (

let uu____5521 = (mk_bool true)
in Const (uu____5521))
in ((FStar_Getopt.noshort), ("ide"), (uu____5520), ("JSON-based interactive mode for IDEs")))
in (

let uu____5528 = (

let uu____5542 = (

let uu____5556 = (

let uu____5568 = (

let uu____5569 = (mk_bool true)
in Const (uu____5569))
in ((FStar_Getopt.noshort), ("print"), (uu____5568), ("Parses and prettyprints the files included on the command line")))
in (

let uu____5576 = (

let uu____5590 = (

let uu____5602 = (

let uu____5603 = (mk_bool true)
in Const (uu____5603))
in ((FStar_Getopt.noshort), ("print_in_place"), (uu____5602), ("Parses and prettyprints in place the files included on the command line")))
in (

let uu____5610 = (

let uu____5624 = (

let uu____5638 = (

let uu____5652 = (

let uu____5666 = (

let uu____5678 = (

let uu____5679 = (mk_bool true)
in Const (uu____5679))
in ((FStar_Getopt.noshort), ("lax"), (uu____5678), ("Run the lax-type checker only (admit all verification conditions)")))
in (

let uu____5686 = (

let uu____5700 = (

let uu____5714 = (

let uu____5726 = (

let uu____5727 = (mk_bool true)
in Const (uu____5727))
in ((FStar_Getopt.noshort), ("log_types"), (uu____5726), ("Print types computed for data/val/let-bindings")))
in (

let uu____5734 = (

let uu____5748 = (

let uu____5760 = (

let uu____5761 = (mk_bool true)
in Const (uu____5761))
in ((FStar_Getopt.noshort), ("log_queries"), (uu____5760), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))
in (

let uu____5768 = (

let uu____5782 = (

let uu____5796 = (

let uu____5810 = (

let uu____5824 = (

let uu____5836 = (

let uu____5837 = (mk_bool true)
in Const (uu____5837))
in ((FStar_Getopt.noshort), ("MLish"), (uu____5836), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))
in (

let uu____5844 = (

let uu____5858 = (

let uu____5872 = (

let uu____5884 = (

let uu____5885 = (mk_bool true)
in Const (uu____5885))
in ((FStar_Getopt.noshort), ("no_default_includes"), (uu____5884), ("Ignore the default module search paths")))
in (

let uu____5892 = (

let uu____5906 = (

let uu____5920 = (

let uu____5932 = (

let uu____5933 = (mk_bool true)
in Const (uu____5933))
in ((FStar_Getopt.noshort), ("no_location_info"), (uu____5932), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))
in (

let uu____5940 = (

let uu____5954 = (

let uu____5966 = (

let uu____5967 = (mk_bool true)
in Const (uu____5967))
in ((FStar_Getopt.noshort), ("no_smt"), (uu____5966), ("Do not send any queries to the SMT solver, and fail on them instead")))
in (

let uu____5974 = (

let uu____5988 = (

let uu____6000 = (

let uu____6001 = (mk_bool true)
in Const (uu____6001))
in ((FStar_Getopt.noshort), ("normalize_pure_terms_for_extraction"), (uu____6000), ("Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")))
in (

let uu____6008 = (

let uu____6022 = (

let uu____6036 = (

let uu____6050 = (

let uu____6062 = (

let uu____6063 = (mk_bool true)
in Const (uu____6063))
in ((FStar_Getopt.noshort), ("print_bound_var_types"), (uu____6062), ("Print the types of bound variables")))
in (

let uu____6070 = (

let uu____6084 = (

let uu____6096 = (

let uu____6097 = (mk_bool true)
in Const (uu____6097))
in ((FStar_Getopt.noshort), ("print_effect_args"), (uu____6096), ("Print inferred predicate transformers for all computation types")))
in (

let uu____6104 = (

let uu____6118 = (

let uu____6130 = (

let uu____6131 = (mk_bool true)
in Const (uu____6131))
in ((FStar_Getopt.noshort), ("print_full_names"), (uu____6130), ("Print full names of variables")))
in (

let uu____6138 = (

let uu____6152 = (

let uu____6164 = (

let uu____6165 = (mk_bool true)
in Const (uu____6165))
in ((FStar_Getopt.noshort), ("print_implicits"), (uu____6164), ("Print implicit arguments")))
in (

let uu____6172 = (

let uu____6186 = (

let uu____6198 = (

let uu____6199 = (mk_bool true)
in Const (uu____6199))
in ((FStar_Getopt.noshort), ("print_universes"), (uu____6198), ("Print universes")))
in (

let uu____6206 = (

let uu____6220 = (

let uu____6232 = (

let uu____6233 = (mk_bool true)
in Const (uu____6233))
in ((FStar_Getopt.noshort), ("print_z3_statistics"), (uu____6232), ("Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")))
in (

let uu____6240 = (

let uu____6254 = (

let uu____6266 = (

let uu____6267 = (mk_bool true)
in Const (uu____6267))
in ((FStar_Getopt.noshort), ("prn"), (uu____6266), ("Print full names (deprecated; use --print_full_names instead)")))
in (

let uu____6274 = (

let uu____6288 = (

let uu____6300 = (

let uu____6301 = (mk_bool true)
in Const (uu____6301))
in ((FStar_Getopt.noshort), ("query_stats"), (uu____6300), ("Print SMT query statistics")))
in (

let uu____6308 = (

let uu____6322 = (

let uu____6334 = (

let uu____6335 = (mk_bool true)
in Const (uu____6335))
in ((FStar_Getopt.noshort), ("record_hints"), (uu____6334), ("Record a database of hints for efficient proof replay")))
in (

let uu____6342 = (

let uu____6356 = (

let uu____6370 = (

let uu____6382 = (

let uu____6383 = (mk_bool true)
in Const (uu____6383))
in ((FStar_Getopt.noshort), ("silent"), (uu____6382), ("Disable all non-critical output")))
in (

let uu____6390 = (

let uu____6404 = (

let uu____6418 = (

let uu____6432 = (

let uu____6446 = (

let uu____6460 = (

let uu____6472 = (

let uu____6473 = (mk_bool true)
in Const (uu____6473))
in ((FStar_Getopt.noshort), ("tactic_raw_binders"), (uu____6472), ("Do not use the lexical scope of tactics to improve binder names")))
in (

let uu____6480 = (

let uu____6494 = (

let uu____6506 = (

let uu____6507 = (mk_bool true)
in Const (uu____6507))
in ((FStar_Getopt.noshort), ("tactics_failhard"), (uu____6506), ("Do not recover from metaprogramming errors, and abort if one occurs")))
in (

let uu____6514 = (

let uu____6528 = (

let uu____6540 = (

let uu____6541 = (mk_bool true)
in Const (uu____6541))
in ((FStar_Getopt.noshort), ("tactics_info"), (uu____6540), ("Print some rough information on tactics, such as the time they take to run")))
in (

let uu____6548 = (

let uu____6562 = (

let uu____6574 = (

let uu____6575 = (mk_bool true)
in Const (uu____6575))
in ((FStar_Getopt.noshort), ("tactic_trace"), (uu____6574), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))
in (

let uu____6582 = (

let uu____6596 = (

let uu____6610 = (

let uu____6622 = (

let uu____6623 = (mk_bool true)
in Const (uu____6623))
in ((FStar_Getopt.noshort), ("__tactics_nbe"), (uu____6622), ("Use NBE to evaluate metaprograms (experimental)")))
in (

let uu____6630 = (

let uu____6644 = (

let uu____6658 = (

let uu____6670 = (

let uu____6671 = (mk_bool true)
in Const (uu____6671))
in ((FStar_Getopt.noshort), ("timing"), (uu____6670), ("Print the time it takes to verify each top-level definition")))
in (

let uu____6678 = (

let uu____6692 = (

let uu____6704 = (

let uu____6705 = (mk_bool true)
in Const (uu____6705))
in ((FStar_Getopt.noshort), ("trace_error"), (uu____6704), ("Don\'t print an error message; show an exception trace instead")))
in (

let uu____6712 = (

let uu____6726 = (

let uu____6738 = (

let uu____6739 = (mk_bool true)
in Const (uu____6739))
in ((FStar_Getopt.noshort), ("ugly"), (uu____6738), ("Emit output formatted for debugging")))
in (

let uu____6746 = (

let uu____6760 = (

let uu____6772 = (

let uu____6773 = (mk_bool true)
in Const (uu____6773))
in ((FStar_Getopt.noshort), ("unthrottle_inductives"), (uu____6772), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))
in (

let uu____6780 = (

let uu____6794 = (

let uu____6806 = (

let uu____6807 = (mk_bool true)
in Const (uu____6807))
in ((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (uu____6806), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))
in (

let uu____6814 = (

let uu____6828 = (

let uu____6840 = (

let uu____6841 = (mk_bool true)
in Const (uu____6841))
in ((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (uu____6840), ("Use equality constraints when comparing higher-order types (Temporary)")))
in (

let uu____6848 = (

let uu____6862 = (

let uu____6874 = (

let uu____6875 = (mk_bool true)
in Const (uu____6875))
in ((FStar_Getopt.noshort), ("use_hints"), (uu____6874), ("Use a previously recorded hints database for proof replay")))
in (

let uu____6882 = (

let uu____6896 = (

let uu____6908 = (

let uu____6909 = (mk_bool true)
in Const (uu____6909))
in ((FStar_Getopt.noshort), ("use_hint_hashes"), (uu____6908), ("Admit queries if their hash matches the hash recorded in the hints database")))
in (

let uu____6916 = (

let uu____6930 = (

let uu____6944 = (

let uu____6956 = (

let uu____6957 = (mk_bool true)
in Const (uu____6957))
in ((FStar_Getopt.noshort), ("no_plugins"), (uu____6956), ("Do not run plugins natively and interpret them as usual instead")))
in (

let uu____6964 = (

let uu____6978 = (

let uu____6990 = (

let uu____6991 = (mk_bool true)
in Const (uu____6991))
in ((FStar_Getopt.noshort), ("no_tactics"), (uu____6990), ("Do not run the tactic engine before discharging a VC")))
in (

let uu____6998 = (

let uu____7012 = (

let uu____7026 = (

let uu____7040 = (

let uu____7054 = (

let uu____7066 = (

let uu____7067 = (mk_bool true)
in Const (uu____7067))
in ((FStar_Getopt.noshort), ("__temp_fast_implicits"), (uu____7066), ("Don\'t use this option yet")))
in (

let uu____7074 = (

let uu____7088 = (

let uu____7100 = (

let uu____7101 = (

let uu____7109 = (

let uu____7110 = (mk_bool true)
in Const (uu____7110))
in (((fun uu____7117 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____7109)))
in WithSideEffect (uu____7101))
in ((118 (*v*)), ("version"), (uu____7100), ("Display version number")))
in (

let uu____7126 = (

let uu____7140 = (

let uu____7152 = (

let uu____7153 = (mk_bool true)
in Const (uu____7153))
in ((FStar_Getopt.noshort), ("warn_default_effects"), (uu____7152), ("Warn when (a -> b) is desugared to (a -> Tot b)")))
in (

let uu____7160 = (

let uu____7174 = (

let uu____7188 = (

let uu____7200 = (

let uu____7201 = (mk_bool true)
in Const (uu____7201))
in ((FStar_Getopt.noshort), ("z3refresh"), (uu____7200), ("Restart Z3 after each query; useful for ensuring proof robustness")))
in (

let uu____7208 = (

let uu____7222 = (

let uu____7236 = (

let uu____7250 = (

let uu____7264 = (

let uu____7278 = (

let uu____7290 = (

let uu____7291 = (mk_bool true)
in Const (uu____7291))
in ((FStar_Getopt.noshort), ("__no_positivity"), (uu____7290), ("Don\'t check positivity of inductive types")))
in (

let uu____7298 = (

let uu____7312 = (

let uu____7324 = (

let uu____7325 = (mk_bool true)
in Const (uu____7325))
in ((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (uu____7324), ("Do not eta-expand coertions in generated OCaml")))
in (

let uu____7332 = (

let uu____7346 = (

let uu____7360 = (

let uu____7374 = (

let uu____7388 = (

let uu____7400 = (

let uu____7401 = (

let uu____7409 = (

let uu____7410 = (mk_bool true)
in Const (uu____7410))
in (((fun uu____7416 -> (FStar_ST.op_Colon_Equals debug_embedding true))), (uu____7409)))
in WithSideEffect (uu____7401))
in ((FStar_Getopt.noshort), ("__debug_embedding"), (uu____7400), ("Debug messages for embeddings/unembeddings of natively compiled terms")))
in (

let uu____7444 = (

let uu____7458 = (

let uu____7470 = (

let uu____7471 = (

let uu____7479 = (

let uu____7480 = (mk_bool true)
in Const (uu____7480))
in (((fun uu____7486 -> (FStar_ST.op_Colon_Equals eager_embedding true))), (uu____7479)))
in WithSideEffect (uu____7471))
in ((FStar_Getopt.noshort), ("eager_embedding"), (uu____7470), ("Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")))
in (

let uu____7514 = (

let uu____7528 = (

let uu____7540 = (

let uu____7541 = (

let uu____7549 = (

let uu____7550 = (mk_bool true)
in Const (uu____7550))
in (((fun uu____7557 -> ((

let uu____7559 = (specs ())
in (display_usage_aux uu____7559));
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____7549)))
in WithSideEffect (uu____7541))
in ((104 (*h*)), ("help"), (uu____7540), ("Display this information")))
in (

let uu____7583 = (

let uu____7597 = (

let uu____7609 = (

let uu____7610 = (mk_bool true)
in Const (uu____7610))
in ((FStar_Getopt.noshort), ("report_qi"), (uu____7609), ("Generates a quantifier instantiation report every time Z3 is closed")))
in (

let uu____7617 = (

let uu____7631 = (

let uu____7643 = (

let uu____7644 = (mk_bool true)
in Const (uu____7644))
in ((FStar_Getopt.noshort), ("smt_proof"), (uu____7643), ("Extracts an SMT proof from Z3")))
in (uu____7631)::[])
in (uu____7597)::uu____7617))
in (uu____7528)::uu____7583))
in (uu____7458)::uu____7514))
in (uu____7388)::uu____7444))
in (((FStar_Getopt.noshort), ("use_nbe"), (BoolStr), ("Use normalization by evaluation as the default normalization srategy (default \'false\')")))::uu____7374)
in (((FStar_Getopt.noshort), ("use_extracted_interfaces"), (BoolStr), ("Extract interfaces from the dependencies and use them for verification (default \'false\')")))::uu____7360)
in (((FStar_Getopt.noshort), ("warn_error"), (SimpleStr ("")), ("The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")))::uu____7346)
in (uu____7312)::uu____7332))
in (uu____7278)::uu____7298))
in (((FStar_Getopt.noshort), ("use_two_phase_tc"), (BoolStr), ("Use the two phase typechecker (default \'true\')")))::uu____7264)
in (((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::uu____7250)
in (((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::uu____7236)
in (((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::uu____7222)
in (uu____7188)::uu____7208))
in (((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::uu____7174)
in (uu____7140)::uu____7160))
in (uu____7088)::uu____7126))
in (uu____7054)::uu____7074))
in (((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::uu____7040)
in (((FStar_Getopt.noshort), ("vcgen.optimize_bind_as_seq"), (EnumStr (("off")::("without_type")::("with_type")::[])), ("\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")))::uu____7026)
in (((FStar_Getopt.noshort), ("using_facts_from"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | fact id)\'"))), ("\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the \'+\' is optional: --using_facts_from \'FStar.List\' is equivalent to --using_facts_from \'+FStar.List\'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")))::uu____7012)
in (uu____6978)::uu____6998))
in (uu____6944)::uu____6964))
in (((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::uu____6930)
in (uu____6896)::uu____6916))
in (uu____6862)::uu____6882))
in (uu____6828)::uu____6848))
in (uu____6794)::uu____6814))
in (uu____6760)::uu____6780))
in (uu____6726)::uu____6746))
in (uu____6692)::uu____6712))
in (uu____6658)::uu____6678))
in (((FStar_Getopt.noshort), ("tcnorm"), (BoolStr), ("Attempt to normalize definitions marked as tcnorm (default \'true\')")))::uu____6644)
in (uu____6610)::uu____6630))
in (((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::uu____6596)
in (uu____6562)::uu____6582))
in (uu____6528)::uu____6548))
in (uu____6494)::uu____6514))
in (uu____6460)::uu____6480))
in (((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::uu____6446)
in (((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::uu____6432)
in (((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::uu____6418)
in (((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::uu____6404)
in (uu____6370)::uu____6390))
in (((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::uu____6356)
in (uu____6322)::uu____6342))
in (uu____6288)::uu____6308))
in (uu____6254)::uu____6274))
in (uu____6220)::uu____6240))
in (uu____6186)::uu____6206))
in (uu____6152)::uu____6172))
in (uu____6118)::uu____6138))
in (uu____6084)::uu____6104))
in (uu____6050)::uu____6070))
in (((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::uu____6036)
in (((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::uu____6022)
in (uu____5988)::uu____6008))
in (uu____5954)::uu____5974))
in (uu____5920)::uu____5940))
in (((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Deprecated: use --extract instead; Do not extract code from this module")))::uu____5906)
in (uu____5872)::uu____5892))
in (((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::uu____5858)
in (uu____5824)::uu____5844))
in (((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::uu____5810)
in (((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::uu____5796)
in (((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::uu____5782)
in (uu____5748)::uu____5768))
in (uu____5714)::uu____5734))
in (((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::uu____5700)
in (uu____5666)::uu____5686))
in (((FStar_Getopt.noshort), ("keep_query_captions"), (BoolStr), ("Retain comments in the logged SMT queries (requires --log_queries; default true)")))::uu____5652)
in (((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::uu____5638)
in (((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::uu____5624)
in (uu____5590)::uu____5610))
in (uu____5556)::uu____5576))
in (((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::uu____5542)
in (uu____5508)::uu____5528))
in (uu____5474)::uu____5494))
in (uu____5440)::uu____5460))
in (((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::uu____5426)
in (uu____5392)::uu____5412))
in (uu____5358)::uu____5378))
in (((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Deprecated: use --extract instead; Only extract modules in the specified namespace")))::uu____5344)
in (((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")))::uu____5330)
in (((FStar_Getopt.noshort), ("extract"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the \'+\' is optional: --extract \'+A\' and --extract \'A\' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract \'A B\'.")))::uu____5316)
in (uu____5282)::uu____5302))
in (uu____5248)::uu____5268))
in (((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::uu____5234)
in (uu____5200)::uu____5220))
in (uu____5166)::uu____5186))
in (uu____5132)::uu____5152))
in (((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::("full")::("raw")::[])), ("Output the transitive closure of the full dependency graph in three formats:\n\t \'graph\': a format suitable the \'dot\' tool from \'GraphViz\'\n\t \'full\': a format suitable for \'make\', including dependences for producing .ml and .krml files\n\t \'make\': (deprecated) a format suitable for \'make\', including only dependences among source files")))::uu____5118)
in (((FStar_Getopt.noshort), ("defensive"), (EnumStr (("no")::("warn")::("fail")::[])), ("Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif \'no\', no checks are performed\n\t\tif \'warn\', checks are performed and raise a warning when they fail\n\t\tif \'fail\', like \'warn\', but the compiler aborts instead of issuing a warning\n\t\t(default \'no\')")))::uu____5104)
in (((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::uu____5090)
in (((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::uu____5076)
in (((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::uu____5062)
in (((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::("Plugin")::[])), ("Generate code for further compilation to executable code, or build a compiler plugin")))::uu____5048)
in (uu____5014)::uu____5034))
in (uu____4980)::uu____5000))
in (((FStar_Getopt.noshort), ("cache_dir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Read and write .checked and .checked.lax in directory <dir>")))::uu____4966)
in (uu____4932)::uu____4952))
in (((FStar_Getopt.noshort), ("already_cached"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")))::uu____4918)
in (((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("[symbol|(symbol, id)]")), ("Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\' or --admit_except FStar.Fin.pigeonhole)")))::uu____4904)
in (((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::uu____4890)
in (((FStar_Getopt.noshort), ("abort_on"), (PostProcessed ((((fun uu___87_9170 -> (match (uu___87_9170) with
| Int (x) -> begin
((FStar_ST.op_Colon_Equals abort_counter x);
Int (x);
)
end
| x -> begin
(failwith "?")
end))), (IntStr ("non-negative integer"))))), ("Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")))::uu____4876))
and specs : unit  ->  FStar_Getopt.opt Prims.list = (fun uu____9199 -> (

let uu____9202 = (specs_with_types ())
in (FStar_List.map (fun uu____9233 -> (match (uu____9233) with
| (short, long, typ, doc) -> begin
(

let uu____9255 = (

let uu____9269 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____9269), (doc)))
in (mk_spec uu____9255))
end)) uu____9202)))


let settable : Prims.string  ->  Prims.bool = (fun uu___88_9284 -> (match (uu___88_9284) with
| "abort_on" -> begin
true
end
| "admit_smt_queries" -> begin
true
end
| "admit_except" -> begin
true
end
| "debug" -> begin
true
end
| "debug_level" -> begin
true
end
| "defensive" -> begin
true
end
| "detail_errors" -> begin
true
end
| "detail_hint_replay" -> begin
true
end
| "eager_inference" -> begin
true
end
| "eager_subtyping" -> begin
true
end
| "hide_uvar_nums" -> begin
true
end
| "hint_info" -> begin
true
end
| "hint_file" -> begin
true
end
| "initial_fuel" -> begin
true
end
| "initial_ifuel" -> begin
true
end
| "lax" -> begin
true
end
| "load" -> begin
true
end
| "log_types" -> begin
true
end
| "log_queries" -> begin
true
end
| "max_fuel" -> begin
true
end
| "max_ifuel" -> begin
true
end
| "min_fuel" -> begin
true
end
| "no_smt" -> begin
true
end
| "__no_positivity" -> begin
true
end
| "ugly" -> begin
true
end
| "print_bound_var_types" -> begin
true
end
| "print_effect_args" -> begin
true
end
| "print_full_names" -> begin
true
end
| "print_implicits" -> begin
true
end
| "print_universes" -> begin
true
end
| "print_z3_statistics" -> begin
true
end
| "prn" -> begin
true
end
| "query_stats" -> begin
true
end
| "silent" -> begin
true
end
| "smtencoding.elim_box" -> begin
true
end
| "smtencoding.nl_arith_repr" -> begin
true
end
| "smtencoding.l_arith_repr" -> begin
true
end
| "timing" -> begin
true
end
| "trace_error" -> begin
true
end
| "unthrottle_inductives" -> begin
true
end
| "use_eq_at_higher_order" -> begin
true
end
| "no_plugins" -> begin
true
end
| "no_tactics" -> begin
true
end
| "normalize_pure_terms_for_extraction" -> begin
true
end
| "tactic_raw_binders" -> begin
true
end
| "tactics_failhard" -> begin
true
end
| "tactics_info" -> begin
true
end
| "tactic_trace" -> begin
true
end
| "tactic_trace_d" -> begin
true
end
| "tcnorm" -> begin
true
end
| "__tactics_nbe" -> begin
true
end
| "__temp_fast_implicits" -> begin
true
end
| "__temp_no_proj" -> begin
true
end
| "reuse_hint_for" -> begin
true
end
| "warn_error" -> begin
true
end
| "z3rlimit_factor" -> begin
true
end
| "z3rlimit" -> begin
true
end
| "z3refresh" -> begin
true
end
| "use_two_phase_tc" -> begin
true
end
| "vcgen.optimize_bind_as_seq" -> begin
true
end
| uu____9407 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")) || (Prims.op_Equality s "using_facts_from")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____9506 -> (match (uu____9506) with
| (uu____9521, x, uu____9523, uu____9524) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____9599 -> (match (uu____9599) with
| (uu____9614, x, uu____9616, uu____9617) -> begin
(resettable x)
end))))


let display_usage : unit  ->  unit = (fun uu____9633 -> (

let uu____9634 = (specs ())
in (display_usage_aux uu____9634)))


let fstar_bin_directory : Prims.string = (FStar_Util.get_exec_dir ())

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____9666) -> begin
true
end
| uu____9669 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____9680) -> begin
uu____9680
end))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs1 = (match (o) with
| Set -> begin
settable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_All.try_with (fun uu___93_9701 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____9705 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___92_9715 -> (match (uu___92_9715) with
| File_argument (s1) -> begin
(

let uu____9718 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____9718))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____9754 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____9760 = (

let uu____9764 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____9764 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____9760))))
in (

let uu____9821 = (

let uu____9825 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9825))
in ((res), (uu____9821)))))


let file_list : unit  ->  Prims.string Prims.list = (fun uu____9867 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____9907 -> begin
(init ())
end);
(

let r = (

let uu____9910 = (specs ())
in (FStar_Getopt.parse_cmdline uu____9910 (fun x -> ())))
in ((

let uu____9917 = (

let uu____9923 = (

let uu____9924 = (FStar_List.map mk_string old_verify_module)
in List (uu____9924))
in (("verify_module"), (uu____9923)))
in (set_option' uu____9917));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____9943 = (

let uu____9945 = (

let uu____9947 = (

let uu____9949 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____9949))
in ((FStar_String.length f1) - uu____9947))
in (uu____9945 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____9943))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____9962 = (get_lax ())
in (match (uu____9962) with
| true -> begin
false
end
| uu____9967 -> begin
(

let l = (get_verify_module ())
in (FStar_List.contains (FStar_String.lowercase m) l))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____9983 = (module_name_of_file_name fn)
in (should_verify uu____9983)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____9994 = (get___temp_no_proj ())
in (FStar_List.contains m uu____9994)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____10008 = (should_verify m)
in (match (uu____10008) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____10014 -> begin
false
end)))


let include_path : unit  ->  Prims.string Prims.list = (fun uu____10025 -> (

let cache_dir = (

let uu____10030 = (get_cache_dir ())
in (match (uu____10030) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (c) -> begin
(c)::[]
end))
in (

let uu____10044 = (get_no_default_includes ())
in (match (uu____10044) with
| true -> begin
(

let uu____10050 = (get_include ())
in (FStar_List.append cache_dir uu____10050))
end
| uu____10055 -> begin
(

let lib_paths = (

let uu____10061 = (FStar_Util.expand_environment_variable "FSTAR_LIB")
in (match (uu____10061) with
| FStar_Pervasives_Native.None -> begin
(

let fstar_home = (Prims.strcat fstar_bin_directory "/..")
in (

let defs = universe_include_path_base_dirs
in (

let uu____10077 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat fstar_home x))))
in (FStar_All.pipe_right uu____10077 (FStar_List.filter FStar_Util.file_exists)))))
end
| FStar_Pervasives_Native.Some (s) -> begin
(s)::[]
end))
in (

let uu____10104 = (

let uu____10108 = (

let uu____10112 = (get_include ())
in (FStar_List.append uu____10112 ((".")::[])))
in (FStar_List.append lib_paths uu____10108))
in (FStar_List.append cache_dir uu____10104)))
end))))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (

let file_map = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun filename -> (

let uu____10139 = (FStar_Util.smap_try_find file_map filename)
in (match (uu____10139) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| FStar_Pervasives_Native.None -> begin
(

let result = (FStar_All.try_with (fun uu___95_10161 -> (match (()) with
| () -> begin
(

let uu____10165 = (FStar_Util.is_path_absolute filename)
in (match (uu____10165) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____10176 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10179 -> begin
(

let uu____10181 = (

let uu____10185 = (include_path ())
in (FStar_List.rev uu____10185))
in (FStar_Util.find_map uu____10181 (fun p -> (

let path = (match ((Prims.op_Equality p ".")) with
| true -> begin
filename
end
| uu____10202 -> begin
(FStar_Util.join_paths p filename)
end)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____10209 -> begin
FStar_Pervasives_Native.None
end)))))
end))
end)) (fun uu___94_10213 -> FStar_Pervasives_Native.None))
in (match (result) with
| FStar_Pervasives_Native.None -> begin
result
end
| FStar_Pervasives_Native.Some (f) -> begin
((FStar_Util.smap_add file_map filename f);
result;
)
end))
end))))


let prims : unit  ->  Prims.string = (fun uu____10233 -> (

let uu____10234 = (get_prims ())
in (match (uu____10234) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____10243 = (find_file filename)
in (match (uu____10243) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10252 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10252))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : unit  ->  Prims.string = (fun uu____10265 -> (

let uu____10266 = (prims ())
in (FStar_Util.basename uu____10266)))


let pervasives : unit  ->  Prims.string = (fun uu____10274 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____10278 = (find_file filename)
in (match (uu____10278) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10287 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10287))
end))))


let pervasives_basename : unit  ->  Prims.string = (fun uu____10297 -> (

let uu____10298 = (pervasives ())
in (FStar_Util.basename uu____10298)))


let pervasives_native_basename : unit  ->  Prims.string = (fun uu____10306 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____10310 = (find_file filename)
in (match (uu____10310) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10319 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10319))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____10332 = (get_odir ())
in (match (uu____10332) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Util.join_paths x fname)
end)))


let prepend_cache_dir : Prims.string  ->  Prims.string = (fun fpath -> (

let uu____10350 = (get_cache_dir ())
in (match (uu____10350) with
| FStar_Pervasives_Native.None -> begin
fpath
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____10359 = (FStar_Util.basename fpath)
in (FStar_Util.join_paths x uu____10359))
end)))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split ((46 (*.*))::[]) text))


let parse_settings : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun ns -> (

let cache = (FStar_Util.smap_create (Prims.parse_int "31"))
in (

let with_cache = (fun f s -> (

let uu____10481 = (FStar_Util.smap_try_find cache s)
in (match (uu____10481) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (f s)
in ((FStar_Util.smap_add cache s res);
res;
))
end)))
in (

let parse_one_setting = (fun s -> (match ((Prims.op_Equality s "*")) with
| true -> begin
(([]), (true))
end
| uu____10600 -> begin
(match ((FStar_Util.starts_with s "-")) with
| true -> begin
(

let path = (

let uu____10616 = (FStar_Util.substring_from s (Prims.parse_int "1"))
in (path_of_text uu____10616))
in ((path), (false)))
end
| uu____10624 -> begin
(

let s1 = (match ((FStar_Util.starts_with s "+")) with
| true -> begin
(FStar_Util.substring_from s (Prims.parse_int "1"))
end
| uu____10632 -> begin
s
end)
in (((path_of_text s1)), (true)))
end)
end))
in (

let uu____10639 = (FStar_All.pipe_right ns (FStar_List.collect (fun s -> (

let s1 = (FStar_Util.trim_string s)
in (match ((Prims.op_Equality s1 "")) with
| true -> begin
[]
end
| uu____10699 -> begin
(with_cache (fun s2 -> (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_List.map parse_one_setting))) s1)
end)))))
in (FStar_All.pipe_right uu____10639 FStar_List.rev))))))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____10765 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____10765 (FStar_List.contains s))))


let __temp_fast_implicits : unit  ->  Prims.bool = (fun uu____10780 -> (lookup_opt "__temp_fast_implicits" as_bool))


let admit_smt_queries : unit  ->  Prims.bool = (fun uu____10789 -> (get_admit_smt_queries ()))


let admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____10798 -> (get_admit_except ()))


let cache_checked_modules : unit  ->  Prims.bool = (fun uu____10805 -> (get_cache_checked_modules ()))


let cache_off : unit  ->  Prims.bool = (fun uu____10812 -> (get_cache_off ()))


let cmi : unit  ->  Prims.bool = (fun uu____10819 -> (get_cmi ()))

type codegen_t =
| OCaml
| FSharp
| Kremlin
| Plugin


let uu___is_OCaml : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OCaml -> begin
true
end
| uu____10829 -> begin
false
end))


let uu___is_FSharp : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSharp -> begin
true
end
| uu____10840 -> begin
false
end))


let uu___is_Kremlin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kremlin -> begin
true
end
| uu____10851 -> begin
false
end))


let uu___is_Plugin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Plugin -> begin
true
end
| uu____10862 -> begin
false
end))


let codegen : unit  ->  codegen_t FStar_Pervasives_Native.option = (fun uu____10871 -> (

let uu____10872 = (get_codegen ())
in (FStar_Util.map_opt uu____10872 (fun uu___89_10878 -> (match (uu___89_10878) with
| "OCaml" -> begin
OCaml
end
| "FSharp" -> begin
FSharp
end
| "Kremlin" -> begin
Kremlin
end
| "Plugin" -> begin
Plugin
end
| uu____10884 -> begin
(failwith "Impossible")
end)))))


let codegen_libs : unit  ->  Prims.string Prims.list Prims.list = (fun uu____10897 -> (

let uu____10898 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____10898 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : unit  ->  Prims.bool = (fun uu____10924 -> (

let uu____10925 = (get_debug ())
in (Prims.op_disEquality uu____10925 [])))


let debug_module : Prims.string  ->  Prims.bool = (fun modul -> (

let uu____10942 = (get_debug ())
in (FStar_All.pipe_right uu____10942 (FStar_List.contains modul))))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____10967 = (get_debug ())
in (FStar_All.pipe_right uu____10967 (FStar_List.contains modul))) && (debug_level_geq level)))


let defensive : unit  ->  Prims.bool = (fun uu____10982 -> (

let uu____10983 = (get_defensive ())
in (Prims.op_disEquality uu____10983 "no")))


let defensive_fail : unit  ->  Prims.bool = (fun uu____10993 -> (

let uu____10994 = (get_defensive ())
in (Prims.op_Equality uu____10994 "fail")))


let dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11006 -> (get_dep ()))


let detail_errors : unit  ->  Prims.bool = (fun uu____11013 -> (get_detail_errors ()))


let detail_hint_replay : unit  ->  Prims.bool = (fun uu____11020 -> (get_detail_hint_replay ()))


let doc : unit  ->  Prims.bool = (fun uu____11027 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____11037 = (get_dump_module ())
in (FStar_All.pipe_right uu____11037 (FStar_List.contains s))))


let eager_subtyping : unit  ->  Prims.bool = (fun uu____11052 -> (get_eager_subtyping ()))


let expose_interfaces : unit  ->  Prims.bool = (fun uu____11059 -> (get_expose_interfaces ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____11069 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____11069)))


let full_context_dependency : unit  ->  Prims.bool = (fun uu____11105 -> true)


let hide_uvar_nums : unit  ->  Prims.bool = (fun uu____11113 -> (get_hide_uvar_nums ()))


let hint_info : unit  ->  Prims.bool = (fun uu____11120 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11129 -> (get_hint_file ()))


let ide : unit  ->  Prims.bool = (fun uu____11136 -> (get_ide ()))


let print : unit  ->  Prims.bool = (fun uu____11143 -> (get_print ()))


let print_in_place : unit  ->  Prims.bool = (fun uu____11150 -> (get_print_in_place ()))


let initial_fuel : unit  ->  Prims.int = (fun uu____11157 -> (

let uu____11158 = (get_initial_fuel ())
in (

let uu____11160 = (get_max_fuel ())
in (Prims.min uu____11158 uu____11160))))


let initial_ifuel : unit  ->  Prims.int = (fun uu____11168 -> (

let uu____11169 = (get_initial_ifuel ())
in (

let uu____11171 = (get_max_ifuel ())
in (Prims.min uu____11169 uu____11171))))


let interactive : unit  ->  Prims.bool = (fun uu____11179 -> ((get_in ()) || (get_ide ())))


let lax : unit  ->  Prims.bool = (fun uu____11186 -> (get_lax ()))


let load : unit  ->  Prims.string Prims.list = (fun uu____11195 -> (get_load ()))


let legacy_interactive : unit  ->  Prims.bool = (fun uu____11202 -> (get_in ()))


let log_queries : unit  ->  Prims.bool = (fun uu____11209 -> (get_log_queries ()))


let keep_query_captions : unit  ->  Prims.bool = (fun uu____11216 -> ((log_queries ()) && (get_keep_query_captions ())))


let log_types : unit  ->  Prims.bool = (fun uu____11223 -> (get_log_types ()))


let max_fuel : unit  ->  Prims.int = (fun uu____11230 -> (get_max_fuel ()))


let max_ifuel : unit  ->  Prims.int = (fun uu____11237 -> (get_max_ifuel ()))


let min_fuel : unit  ->  Prims.int = (fun uu____11244 -> (get_min_fuel ()))


let ml_ish : unit  ->  Prims.bool = (fun uu____11251 -> (get_MLish ()))


let set_ml_ish : unit  ->  unit = (fun uu____11257 -> (set_option "MLish" (Bool (true))))


let n_cores : unit  ->  Prims.int = (fun uu____11266 -> (get_n_cores ()))


let no_default_includes : unit  ->  Prims.bool = (fun uu____11273 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let s1 = (FStar_String.lowercase s)
in (

let uu____11285 = (get_no_extract ())
in (FStar_All.pipe_right uu____11285 (FStar_Util.for_some (fun f -> (Prims.op_Equality (FStar_String.lowercase f) s1)))))))


let normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____11304 -> (get_normalize_pure_terms_for_extraction ()))


let no_location_info : unit  ->  Prims.bool = (fun uu____11311 -> (get_no_location_info ()))


let no_plugins : unit  ->  Prims.bool = (fun uu____11318 -> (get_no_plugins ()))


let no_smt : unit  ->  Prims.bool = (fun uu____11325 -> (get_no_smt ()))


let output_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11334 -> (get_odir ()))


let ugly : unit  ->  Prims.bool = (fun uu____11341 -> (get_ugly ()))


let print_bound_var_types : unit  ->  Prims.bool = (fun uu____11348 -> (get_print_bound_var_types ()))


let print_effect_args : unit  ->  Prims.bool = (fun uu____11355 -> (get_print_effect_args ()))


let print_implicits : unit  ->  Prims.bool = (fun uu____11362 -> (get_print_implicits ()))


let print_real_names : unit  ->  Prims.bool = (fun uu____11369 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : unit  ->  Prims.bool = (fun uu____11376 -> (get_print_universes ()))


let print_z3_statistics : unit  ->  Prims.bool = (fun uu____11383 -> ((get_print_z3_statistics ()) || (get_query_stats ())))


let query_stats : unit  ->  Prims.bool = (fun uu____11390 -> (get_query_stats ()))


let record_hints : unit  ->  Prims.bool = (fun uu____11397 -> (get_record_hints ()))


let reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11406 -> (get_reuse_hint_for ()))


let silent : unit  ->  Prims.bool = (fun uu____11413 -> (get_silent ()))


let smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____11420 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : unit  ->  Prims.bool = (fun uu____11427 -> (

let uu____11428 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11428 "native")))


let smtencoding_nl_arith_wrapped : unit  ->  Prims.bool = (fun uu____11438 -> (

let uu____11439 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11439 "wrapped")))


let smtencoding_nl_arith_default : unit  ->  Prims.bool = (fun uu____11449 -> (

let uu____11450 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11450 "boxwrap")))


let smtencoding_l_arith_native : unit  ->  Prims.bool = (fun uu____11460 -> (

let uu____11461 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____11461 "native")))


let smtencoding_l_arith_default : unit  ->  Prims.bool = (fun uu____11471 -> (

let uu____11472 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____11472 "boxwrap")))


let tactic_raw_binders : unit  ->  Prims.bool = (fun uu____11482 -> (get_tactic_raw_binders ()))


let tactics_failhard : unit  ->  Prims.bool = (fun uu____11489 -> (get_tactics_failhard ()))


let tactics_info : unit  ->  Prims.bool = (fun uu____11496 -> (get_tactics_info ()))


let tactic_trace : unit  ->  Prims.bool = (fun uu____11503 -> (get_tactic_trace ()))


let tactic_trace_d : unit  ->  Prims.int = (fun uu____11510 -> (get_tactic_trace_d ()))


let tactics_nbe : unit  ->  Prims.bool = (fun uu____11517 -> (get_tactics_nbe ()))


let tcnorm : unit  ->  Prims.bool = (fun uu____11524 -> (get_tcnorm ()))


let timing : unit  ->  Prims.bool = (fun uu____11531 -> (get_timing ()))


let trace_error : unit  ->  Prims.bool = (fun uu____11538 -> (get_trace_error ()))


let unthrottle_inductives : unit  ->  Prims.bool = (fun uu____11545 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____11552 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____11559 -> (get_use_eq_at_higher_order ()))


let use_hints : unit  ->  Prims.bool = (fun uu____11566 -> (get_use_hints ()))


let use_hint_hashes : unit  ->  Prims.bool = (fun uu____11573 -> (get_use_hint_hashes ()))


let use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11582 -> (get_use_native_tactics ()))


let use_tactics : unit  ->  Prims.bool = (fun uu____11589 -> (get_use_tactics ()))


let using_facts_from : unit  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun uu____11605 -> (

let uu____11606 = (get_using_facts_from ())
in (match (uu____11606) with
| FStar_Pervasives_Native.None -> begin
((([]), (true)))::[]
end
| FStar_Pervasives_Native.Some (ns) -> begin
(parse_settings ns)
end)))


let vcgen_optimize_bind_as_seq : unit  ->  Prims.bool = (fun uu____11660 -> (

let uu____11661 = (get_vcgen_optimize_bind_as_seq ())
in (FStar_Option.isSome uu____11661)))


let vcgen_decorate_with_type : unit  ->  Prims.bool = (fun uu____11672 -> (

let uu____11673 = (get_vcgen_optimize_bind_as_seq ())
in (match (uu____11673) with
| FStar_Pervasives_Native.Some ("with_type") -> begin
true
end
| uu____11681 -> begin
false
end)))


let warn_default_effects : unit  ->  Prims.bool = (fun uu____11692 -> (get_warn_default_effects ()))


let z3_exe : unit  ->  Prims.string = (fun uu____11699 -> (

let uu____11700 = (get_smt ())
in (match (uu____11700) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : unit  ->  Prims.string Prims.list = (fun uu____11718 -> (get_z3cliopt ()))


let z3_refresh : unit  ->  Prims.bool = (fun uu____11725 -> (get_z3refresh ()))


let z3_rlimit : unit  ->  Prims.int = (fun uu____11732 -> (get_z3rlimit ()))


let z3_rlimit_factor : unit  ->  Prims.int = (fun uu____11739 -> (get_z3rlimit_factor ()))


let z3_seed : unit  ->  Prims.int = (fun uu____11746 -> (get_z3seed ()))


let use_two_phase_tc : unit  ->  Prims.bool = (fun uu____11753 -> ((get_use_two_phase_tc ()) && (

let uu____11755 = (lax ())
in (not (uu____11755)))))


let no_positivity : unit  ->  Prims.bool = (fun uu____11763 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____11770 -> (get_ml_no_eta_expand_coertions ()))


let warn_error : unit  ->  Prims.string = (fun uu____11777 -> (get_warn_error ()))


let use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____11784 -> (get_use_extracted_interfaces ()))


let use_nbe : unit  ->  Prims.bool = (fun uu____11791 -> (get_use_nbe ()))


let report_qi : unit  ->  Prims.bool = (fun uu____11798 -> (get_report_qi ()))


let smt_proof : unit  ->  Prims.bool = (fun uu____11805 -> (get_smt_proof ()))


let with_saved_options : 'a . (unit  ->  'a)  ->  'a = (fun f -> (

let uu____11822 = (

let uu____11824 = (trace_error ())
in (not (uu____11824)))
in (match (uu____11822) with
| true -> begin
((push ());
(

let r = (FStar_All.try_with (fun uu___97_11839 -> (match (()) with
| () -> begin
(

let uu____11844 = (f ())
in FStar_Util.Inr (uu____11844))
end)) (fun uu___96_11846 -> FStar_Util.Inl (uu___96_11846)))
in ((pop ());
(match (r) with
| FStar_Util.Inr (v1) -> begin
v1
end
| FStar_Util.Inl (ex) -> begin
(FStar_Exn.raise ex)
end);
));
)
end
| uu____11854 -> begin
((push ());
(

let retv = (f ())
in ((pop ());
retv;
));
)
end)))


let module_matches_namespace_filter : Prims.string  ->  Prims.string Prims.list  ->  Prims.bool = (fun m filter1 -> (

let m1 = (FStar_String.lowercase m)
in (

let setting = (parse_settings filter1)
in (

let m_components = (path_of_text m1)
in (

let rec matches_path = (fun m_components1 path -> (match (((m_components1), (path))) with
| (uu____11927, []) -> begin
true
end
| ((m2)::ms, (p)::ps) -> begin
((Prims.op_Equality m2 (FStar_String.lowercase p)) && (matches_path ms ps))
end
| uu____11960 -> begin
false
end))
in (

let uu____11972 = (FStar_All.pipe_right setting (FStar_Util.try_find (fun uu____12014 -> (match (uu____12014) with
| (path, uu____12025) -> begin
(matches_path m_components path)
end))))
in (match (uu____11972) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____12044, flag) -> begin
flag
end)))))))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> (

let m1 = (FStar_String.lowercase m)
in (

let uu____12073 = (get_extract ())
in (match (uu____12073) with
| FStar_Pervasives_Native.Some (extract_setting) -> begin
((

let uu____12088 = (

let uu____12104 = (get_no_extract ())
in (

let uu____12108 = (get_extract_namespace ())
in (

let uu____12112 = (get_extract_module ())
in ((uu____12104), (uu____12108), (uu____12112)))))
in (match (uu____12088) with
| ([], [], []) -> begin
()
end
| uu____12137 -> begin
(failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module")
end));
(module_matches_namespace_filter m1 extract_setting);
)
end
| FStar_Pervasives_Native.None -> begin
(

let should_extract_namespace = (fun m2 -> (

let uu____12166 = (get_extract_namespace ())
in (match (uu____12166) with
| [] -> begin
false
end
| ns -> begin
(FStar_All.pipe_right ns (FStar_Util.for_some (fun n1 -> (FStar_Util.starts_with m2 (FStar_String.lowercase n1)))))
end)))
in (

let should_extract_module = (fun m2 -> (

let uu____12194 = (get_extract_module ())
in (match (uu____12194) with
| [] -> begin
false
end
| l -> begin
(FStar_All.pipe_right l (FStar_Util.for_some (fun n1 -> (Prims.op_Equality (FStar_String.lowercase n1) m2))))
end)))
in ((

let uu____12216 = (no_extract m1)
in (not (uu____12216))) && (

let uu____12219 = (

let uu____12230 = (get_extract_namespace ())
in (

let uu____12234 = (get_extract_module ())
in ((uu____12230), (uu____12234))))
in (match (uu____12219) with
| ([], []) -> begin
true
end
| uu____12254 -> begin
((should_extract_namespace m1) || (should_extract_module m1))
end)))))
end))))


let should_be_already_cached : Prims.string  ->  Prims.bool = (fun m -> (

let uu____12274 = (get_already_cached ())
in (match (uu____12274) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (already_cached_setting) -> begin
(module_matches_namespace_filter m already_cached_setting)
end)))




