
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


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("__temp_fast_implicits"), (Bool (false))))::((("abort_on"), (Int ((Prims.parse_int "0")))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("already_cached"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("cache_dir"), (Unset)))::((("cache_off"), (Bool (false))))::((("cmi"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("defensive"), (String ("no"))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("eager_subtyping"), (Bool (false))))::((("expose_interfaces"), (Bool (false))))::((("extract"), (Unset)))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("full_context_dependency"), (Bool (true))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("print"), (Bool (false))))::((("print_in_place"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("keep_query_captions"), (Bool (true))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_smt"), (Bool (false))))::((("no_plugins"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("normalize_pure_terms_for_extraction"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("tactics_failhard"), (Bool (false))))::((("tactics_info"), (Bool (false))))::((("tactic_raw_binders"), (Bool (false))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("tcnorm"), (Bool (true))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("use_hint_hashes"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("vcgen.optimize_bind_as_seq"), (Unset)))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("use_two_phase_tc"), (Bool (true))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::((("__tactics_nbe"), (Bool (false))))::((("warn_error"), (String (""))))::((("use_extracted_interfaces"), (Bool (false))))::((("use_nbe"), (Bool (false))))::((("report_qi"), (Bool (false))))::[]


let init : unit  ->  unit = (fun uu____2227 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : unit  ->  unit = (fun uu____2247 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options (((o)::[])::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____2320 = (

let uu____2323 = (peek ())
in (FStar_Util.smap_try_find uu____2323 s))
in (match (uu____2320) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____2336 . Prims.string  ->  (option_val  ->  'Auu____2336)  ->  'Auu____2336 = (fun s c -> (

let uu____2354 = (get_option s)
in (c uu____2354)))


let get_abort_on : unit  ->  Prims.int = (fun uu____2361 -> (lookup_opt "abort_on" as_int))


let get_admit_smt_queries : unit  ->  Prims.bool = (fun uu____2370 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2381 -> (lookup_opt "admit_except" (as_option as_string)))


let get_already_cached : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2397 -> (lookup_opt "already_cached" (as_option (as_list as_string))))


let get_cache_checked_modules : unit  ->  Prims.bool = (fun uu____2414 -> (lookup_opt "cache_checked_modules" as_bool))


let get_cache_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2425 -> (lookup_opt "cache_dir" (as_option as_string)))


let get_cache_off : unit  ->  Prims.bool = (fun uu____2437 -> (lookup_opt "cache_off" as_bool))


let get_cmi : unit  ->  Prims.bool = (fun uu____2446 -> (lookup_opt "cmi" as_bool))


let get_codegen : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2457 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : unit  ->  Prims.string Prims.list = (fun uu____2471 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : unit  ->  Prims.string Prims.list = (fun uu____2485 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : unit  ->  Prims.string Prims.list = (fun uu____2499 -> (lookup_opt "debug_level" as_comma_string_list))


let get_defensive : unit  ->  Prims.string = (fun uu____2510 -> (lookup_opt "defensive" as_string))


let get_dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2521 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : unit  ->  Prims.bool = (fun uu____2533 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : unit  ->  Prims.bool = (fun uu____2542 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : unit  ->  Prims.bool = (fun uu____2551 -> (lookup_opt "doc" as_bool))


let get_dump_module : unit  ->  Prims.string Prims.list = (fun uu____2562 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_subtyping : unit  ->  Prims.bool = (fun uu____2574 -> (lookup_opt "eager_subtyping" as_bool))


let get_expose_interfaces : unit  ->  Prims.bool = (fun uu____2583 -> (lookup_opt "expose_interfaces" as_bool))


let get_extract : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2596 -> (lookup_opt "extract" (as_option (as_list as_string))))


let get_extract_module : unit  ->  Prims.string Prims.list = (fun uu____2615 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : unit  ->  Prims.string Prims.list = (fun uu____2629 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : unit  ->  Prims.bool = (fun uu____2641 -> (lookup_opt "fs_typ_app" as_bool))


let get_hide_uvar_nums : unit  ->  Prims.bool = (fun uu____2650 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : unit  ->  Prims.bool = (fun uu____2659 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2670 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : unit  ->  Prims.bool = (fun uu____2682 -> (lookup_opt "in" as_bool))


let get_ide : unit  ->  Prims.bool = (fun uu____2691 -> (lookup_opt "ide" as_bool))


let get_include : unit  ->  Prims.string Prims.list = (fun uu____2702 -> (lookup_opt "include" (as_list as_string)))


let get_print : unit  ->  Prims.bool = (fun uu____2714 -> (lookup_opt "print" as_bool))


let get_print_in_place : unit  ->  Prims.bool = (fun uu____2723 -> (lookup_opt "print_in_place" as_bool))


let get_initial_fuel : unit  ->  Prims.int = (fun uu____2732 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : unit  ->  Prims.int = (fun uu____2741 -> (lookup_opt "initial_ifuel" as_int))


let get_keep_query_captions : unit  ->  Prims.bool = (fun uu____2750 -> (lookup_opt "keep_query_captions" as_bool))


let get_lax : unit  ->  Prims.bool = (fun uu____2759 -> (lookup_opt "lax" as_bool))


let get_load : unit  ->  Prims.string Prims.list = (fun uu____2770 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : unit  ->  Prims.bool = (fun uu____2782 -> (lookup_opt "log_queries" as_bool))


let get_log_types : unit  ->  Prims.bool = (fun uu____2791 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : unit  ->  Prims.int = (fun uu____2800 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : unit  ->  Prims.int = (fun uu____2809 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : unit  ->  Prims.int = (fun uu____2818 -> (lookup_opt "min_fuel" as_int))


let get_MLish : unit  ->  Prims.bool = (fun uu____2827 -> (lookup_opt "MLish" as_bool))


let get_n_cores : unit  ->  Prims.int = (fun uu____2836 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : unit  ->  Prims.bool = (fun uu____2845 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : unit  ->  Prims.string Prims.list = (fun uu____2856 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : unit  ->  Prims.bool = (fun uu____2868 -> (lookup_opt "no_location_info" as_bool))


let get_no_plugins : unit  ->  Prims.bool = (fun uu____2877 -> (lookup_opt "no_plugins" as_bool))


let get_no_smt : unit  ->  Prims.bool = (fun uu____2886 -> (lookup_opt "no_smt" as_bool))


let get_normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____2895 -> (lookup_opt "normalize_pure_terms_for_extraction" as_bool))


let get_odir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2906 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : unit  ->  Prims.bool = (fun uu____2918 -> (lookup_opt "ugly" as_bool))


let get_prims : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2929 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : unit  ->  Prims.bool = (fun uu____2941 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : unit  ->  Prims.bool = (fun uu____2950 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : unit  ->  Prims.bool = (fun uu____2959 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : unit  ->  Prims.bool = (fun uu____2968 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : unit  ->  Prims.bool = (fun uu____2977 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : unit  ->  Prims.bool = (fun uu____2986 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : unit  ->  Prims.bool = (fun uu____2995 -> (lookup_opt "prn" as_bool))


let get_query_stats : unit  ->  Prims.bool = (fun uu____3004 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : unit  ->  Prims.bool = (fun uu____3013 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3024 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_silent : unit  ->  Prims.bool = (fun uu____3036 -> (lookup_opt "silent" as_bool))


let get_smt : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3047 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____3059 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : unit  ->  Prims.string = (fun uu____3068 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : unit  ->  Prims.string = (fun uu____3077 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_tactic_raw_binders : unit  ->  Prims.bool = (fun uu____3086 -> (lookup_opt "tactic_raw_binders" as_bool))


let get_tactics_failhard : unit  ->  Prims.bool = (fun uu____3095 -> (lookup_opt "tactics_failhard" as_bool))


let get_tactics_info : unit  ->  Prims.bool = (fun uu____3104 -> (lookup_opt "tactics_info" as_bool))


let get_tactic_trace : unit  ->  Prims.bool = (fun uu____3113 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : unit  ->  Prims.int = (fun uu____3122 -> (lookup_opt "tactic_trace_d" as_int))


let get_tactics_nbe : unit  ->  Prims.bool = (fun uu____3131 -> (lookup_opt "__tactics_nbe" as_bool))


let get_tcnorm : unit  ->  Prims.bool = (fun uu____3140 -> (lookup_opt "tcnorm" as_bool))


let get_timing : unit  ->  Prims.bool = (fun uu____3149 -> (lookup_opt "timing" as_bool))


let get_trace_error : unit  ->  Prims.bool = (fun uu____3158 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : unit  ->  Prims.bool = (fun uu____3167 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____3176 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____3185 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : unit  ->  Prims.bool = (fun uu____3194 -> (lookup_opt "use_hints" as_bool))


let get_use_hint_hashes : unit  ->  Prims.bool = (fun uu____3203 -> (lookup_opt "use_hint_hashes" as_bool))


let get_use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3214 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : unit  ->  Prims.bool = (fun uu____3226 -> (

let uu____3227 = (lookup_opt "no_tactics" as_bool)
in (not (uu____3227))))


let get_using_facts_from : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____3241 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_vcgen_optimize_bind_as_seq : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3260 -> (lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)))


let get_verify_module : unit  ->  Prims.string Prims.list = (fun uu____3274 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : unit  ->  Prims.string Prims.list = (fun uu____3288 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : unit  ->  Prims.bool = (fun uu____3300 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : unit  ->  Prims.bool = (fun uu____3309 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : unit  ->  Prims.string Prims.list = (fun uu____3320 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : unit  ->  Prims.bool = (fun uu____3332 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : unit  ->  Prims.int = (fun uu____3341 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : unit  ->  Prims.int = (fun uu____3350 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : unit  ->  Prims.int = (fun uu____3359 -> (lookup_opt "z3seed" as_int))


let get_use_two_phase_tc : unit  ->  Prims.bool = (fun uu____3368 -> (lookup_opt "use_two_phase_tc" as_bool))


let get_no_positivity : unit  ->  Prims.bool = (fun uu____3377 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____3386 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let get_warn_error : unit  ->  Prims.string = (fun uu____3395 -> (lookup_opt "warn_error" as_string))


let get_use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____3404 -> (lookup_opt "use_extracted_interfaces" as_bool))


let get_use_nbe : unit  ->  Prims.bool = (fun uu____3413 -> (lookup_opt "use_nbe" as_bool))


let get_report_qi : unit  ->  Prims.bool = (fun uu____3422 -> (lookup_opt "report_qi" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___86_3431 -> (match (uu___86_3431) with
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
| Other (uu____3452) -> begin
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

let uu____3461 = (get_debug_level ())
in (FStar_All.pipe_right uu____3461 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "<not set>")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : unit  ->  unit = (fun uu____3627 -> (

let uu____3628 = (

let uu____3630 = (FStar_ST.op_Bang _version)
in (

let uu____3653 = (FStar_ST.op_Bang _platform)
in (

let uu____3676 = (FStar_ST.op_Bang _compiler)
in (

let uu____3699 = (FStar_ST.op_Bang _date)
in (

let uu____3722 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3630 uu____3653 uu____3676 uu____3699 uu____3722))))))
in (FStar_Util.print_string uu____3628)))


let display_usage_aux : 'Auu____3753 'Auu____3754 . ('Auu____3753 * Prims.string * 'Auu____3754 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____3809 -> (match (uu____3809) with
| (uu____3822, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____3841 = (

let uu____3843 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____3843))
in (FStar_Util.print_string uu____3841))
end
| uu____3846 -> begin
(

let uu____3848 = (

let uu____3850 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____3850 doc))
in (FStar_Util.print_string uu____3848))
end)
end
| FStar_Getopt.OneArg (uu____3853, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____3868 = (

let uu____3870 = (FStar_Util.colorize_bold flag)
in (

let uu____3872 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____3870 uu____3872)))
in (FStar_Util.print_string uu____3868))
end
| uu____3875 -> begin
(

let uu____3877 = (

let uu____3879 = (FStar_Util.colorize_bold flag)
in (

let uu____3881 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____3879 uu____3881 doc)))
in (FStar_Util.print_string uu____3877))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____3916 = o
in (match (uu____3916) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____3958 -> (

let uu____3959 = (f ())
in (set_option name uu____3959)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____3980 = (f x)
in (set_option name uu____3980)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____4007 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____4007))
in (mk_list ((value)::prev_values))))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let uu____4033 = (

let uu____4036 = (lookup_opt name as_list')
in (FStar_List.append uu____4036 ((value)::[])))
in (mk_list uu____4033)))


let accumulate_string : 'Auu____4050 . Prims.string  ->  ('Auu____4050  ->  Prims.string)  ->  'Auu____4050  ->  unit = (fun name post_processor value -> (

let uu____4075 = (

let uu____4076 = (

let uu____4077 = (post_processor value)
in (mk_string uu____4077))
in (accumulated_option name uu____4076))
in (set_option name uu____4075)))


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
| uu____4199 -> begin
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
| uu____4220 -> begin
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
| uu____4242 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____4255 -> begin
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
| uu____4279 -> begin
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
| uu____4305 -> begin
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
| uu____4342 -> begin
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
| uu____4393 -> begin
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
| uu____4434 -> begin
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
| uu____4454 -> begin
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
| uu____4481 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((unit  ->  unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4525) -> begin
true
end
| uu____4528 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4539) -> begin
uu____4539
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___91_4563 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____4565) -> begin
(

let uu____4567 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____4567) with
| FStar_Pervasives_Native.Some (v1) -> begin
(mk_int v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____4575 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____4582 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____4589 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in (mk_bool uu____4575))
end
| PathStr (uu____4592) -> begin
(mk_path str_val)
end
| SimpleStr (uu____4594) -> begin
(mk_string str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
(mk_string str_val)
end
| uu____4602 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____4604) -> begin
(mk_string str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____4621 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____4621))
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
end)) (fun uu___90_4638 -> (match (uu___90_4638) with
| InvalidArgument (opt_name1) -> begin
(

let uu____4641 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____4641))
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
| PostProcessed (uu____4711, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____4721, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____4752 = (desc_of_opt_type typ)
in (match (uu____4752) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____4760 -> (parser "")))
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

let uu____4786 = (

let uu____4788 = (as_string s)
in (FStar_String.lowercase uu____4788))
in (mk_string uu____4786)))


let abort_counter : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let rec specs_with_types : unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____4845 -> (

let uu____4859 = (

let uu____4873 = (

let uu____4887 = (

let uu____4901 = (

let uu____4915 = (

let uu____4927 = (

let uu____4928 = (mk_bool true)
in Const (uu____4928))
in ((FStar_Getopt.noshort), ("cache_checked_modules"), (uu____4927), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))
in (

let uu____4935 = (

let uu____4949 = (

let uu____4963 = (

let uu____4975 = (

let uu____4976 = (mk_bool true)
in Const (uu____4976))
in ((FStar_Getopt.noshort), ("cache_off"), (uu____4975), ("Do not read or write any .checked files")))
in (

let uu____4983 = (

let uu____4997 = (

let uu____5009 = (

let uu____5010 = (mk_bool true)
in Const (uu____5010))
in ((FStar_Getopt.noshort), ("cmi"), (uu____5009), ("Inline across module interfaces during extraction (aka. cross-module inlining)")))
in (

let uu____5017 = (

let uu____5031 = (

let uu____5045 = (

let uu____5059 = (

let uu____5073 = (

let uu____5087 = (

let uu____5101 = (

let uu____5115 = (

let uu____5127 = (

let uu____5128 = (mk_bool true)
in Const (uu____5128))
in ((FStar_Getopt.noshort), ("detail_errors"), (uu____5127), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))
in (

let uu____5135 = (

let uu____5149 = (

let uu____5161 = (

let uu____5162 = (mk_bool true)
in Const (uu____5162))
in ((FStar_Getopt.noshort), ("detail_hint_replay"), (uu____5161), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))
in (

let uu____5169 = (

let uu____5183 = (

let uu____5195 = (

let uu____5196 = (mk_bool true)
in Const (uu____5196))
in ((FStar_Getopt.noshort), ("doc"), (uu____5195), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))
in (

let uu____5203 = (

let uu____5217 = (

let uu____5231 = (

let uu____5243 = (

let uu____5244 = (mk_bool true)
in Const (uu____5244))
in ((FStar_Getopt.noshort), ("eager_inference"), (uu____5243), ("Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))
in (

let uu____5251 = (

let uu____5265 = (

let uu____5277 = (

let uu____5278 = (mk_bool true)
in Const (uu____5278))
in ((FStar_Getopt.noshort), ("eager_subtyping"), (uu____5277), ("Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")))
in (

let uu____5285 = (

let uu____5299 = (

let uu____5313 = (

let uu____5327 = (

let uu____5341 = (

let uu____5353 = (

let uu____5354 = (mk_bool true)
in Const (uu____5354))
in ((FStar_Getopt.noshort), ("expose_interfaces"), (uu____5353), ("Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")))
in (

let uu____5361 = (

let uu____5375 = (

let uu____5387 = (

let uu____5388 = (mk_bool true)
in Const (uu____5388))
in ((FStar_Getopt.noshort), ("hide_uvar_nums"), (uu____5387), ("Don\'t print unification variable numbers")))
in (

let uu____5395 = (

let uu____5409 = (

let uu____5423 = (

let uu____5435 = (

let uu____5436 = (mk_bool true)
in Const (uu____5436))
in ((FStar_Getopt.noshort), ("hint_info"), (uu____5435), ("Print information regarding hints (deprecated; use --query_stats instead)")))
in (

let uu____5443 = (

let uu____5457 = (

let uu____5469 = (

let uu____5470 = (mk_bool true)
in Const (uu____5470))
in ((FStar_Getopt.noshort), ("in"), (uu____5469), ("Legacy interactive mode; reads input from stdin")))
in (

let uu____5477 = (

let uu____5491 = (

let uu____5503 = (

let uu____5504 = (mk_bool true)
in Const (uu____5504))
in ((FStar_Getopt.noshort), ("ide"), (uu____5503), ("JSON-based interactive mode for IDEs")))
in (

let uu____5511 = (

let uu____5525 = (

let uu____5539 = (

let uu____5551 = (

let uu____5552 = (mk_bool true)
in Const (uu____5552))
in ((FStar_Getopt.noshort), ("print"), (uu____5551), ("Parses and prettyprints the files included on the command line")))
in (

let uu____5559 = (

let uu____5573 = (

let uu____5585 = (

let uu____5586 = (mk_bool true)
in Const (uu____5586))
in ((FStar_Getopt.noshort), ("print_in_place"), (uu____5585), ("Parses and prettyprints in place the files included on the command line")))
in (

let uu____5593 = (

let uu____5607 = (

let uu____5621 = (

let uu____5635 = (

let uu____5649 = (

let uu____5661 = (

let uu____5662 = (mk_bool true)
in Const (uu____5662))
in ((FStar_Getopt.noshort), ("lax"), (uu____5661), ("Run the lax-type checker only (admit all verification conditions)")))
in (

let uu____5669 = (

let uu____5683 = (

let uu____5697 = (

let uu____5709 = (

let uu____5710 = (mk_bool true)
in Const (uu____5710))
in ((FStar_Getopt.noshort), ("log_types"), (uu____5709), ("Print types computed for data/val/let-bindings")))
in (

let uu____5717 = (

let uu____5731 = (

let uu____5743 = (

let uu____5744 = (mk_bool true)
in Const (uu____5744))
in ((FStar_Getopt.noshort), ("log_queries"), (uu____5743), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))
in (

let uu____5751 = (

let uu____5765 = (

let uu____5779 = (

let uu____5793 = (

let uu____5807 = (

let uu____5819 = (

let uu____5820 = (mk_bool true)
in Const (uu____5820))
in ((FStar_Getopt.noshort), ("MLish"), (uu____5819), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))
in (

let uu____5827 = (

let uu____5841 = (

let uu____5855 = (

let uu____5867 = (

let uu____5868 = (mk_bool true)
in Const (uu____5868))
in ((FStar_Getopt.noshort), ("no_default_includes"), (uu____5867), ("Ignore the default module search paths")))
in (

let uu____5875 = (

let uu____5889 = (

let uu____5903 = (

let uu____5915 = (

let uu____5916 = (mk_bool true)
in Const (uu____5916))
in ((FStar_Getopt.noshort), ("no_location_info"), (uu____5915), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))
in (

let uu____5923 = (

let uu____5937 = (

let uu____5949 = (

let uu____5950 = (mk_bool true)
in Const (uu____5950))
in ((FStar_Getopt.noshort), ("no_smt"), (uu____5949), ("Do not send any queries to the SMT solver, and fail on them instead")))
in (

let uu____5957 = (

let uu____5971 = (

let uu____5983 = (

let uu____5984 = (mk_bool true)
in Const (uu____5984))
in ((FStar_Getopt.noshort), ("normalize_pure_terms_for_extraction"), (uu____5983), ("Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")))
in (

let uu____5991 = (

let uu____6005 = (

let uu____6019 = (

let uu____6033 = (

let uu____6045 = (

let uu____6046 = (mk_bool true)
in Const (uu____6046))
in ((FStar_Getopt.noshort), ("print_bound_var_types"), (uu____6045), ("Print the types of bound variables")))
in (

let uu____6053 = (

let uu____6067 = (

let uu____6079 = (

let uu____6080 = (mk_bool true)
in Const (uu____6080))
in ((FStar_Getopt.noshort), ("print_effect_args"), (uu____6079), ("Print inferred predicate transformers for all computation types")))
in (

let uu____6087 = (

let uu____6101 = (

let uu____6113 = (

let uu____6114 = (mk_bool true)
in Const (uu____6114))
in ((FStar_Getopt.noshort), ("print_full_names"), (uu____6113), ("Print full names of variables")))
in (

let uu____6121 = (

let uu____6135 = (

let uu____6147 = (

let uu____6148 = (mk_bool true)
in Const (uu____6148))
in ((FStar_Getopt.noshort), ("print_implicits"), (uu____6147), ("Print implicit arguments")))
in (

let uu____6155 = (

let uu____6169 = (

let uu____6181 = (

let uu____6182 = (mk_bool true)
in Const (uu____6182))
in ((FStar_Getopt.noshort), ("print_universes"), (uu____6181), ("Print universes")))
in (

let uu____6189 = (

let uu____6203 = (

let uu____6215 = (

let uu____6216 = (mk_bool true)
in Const (uu____6216))
in ((FStar_Getopt.noshort), ("print_z3_statistics"), (uu____6215), ("Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")))
in (

let uu____6223 = (

let uu____6237 = (

let uu____6249 = (

let uu____6250 = (mk_bool true)
in Const (uu____6250))
in ((FStar_Getopt.noshort), ("prn"), (uu____6249), ("Print full names (deprecated; use --print_full_names instead)")))
in (

let uu____6257 = (

let uu____6271 = (

let uu____6283 = (

let uu____6284 = (mk_bool true)
in Const (uu____6284))
in ((FStar_Getopt.noshort), ("query_stats"), (uu____6283), ("Print SMT query statistics")))
in (

let uu____6291 = (

let uu____6305 = (

let uu____6317 = (

let uu____6318 = (mk_bool true)
in Const (uu____6318))
in ((FStar_Getopt.noshort), ("record_hints"), (uu____6317), ("Record a database of hints for efficient proof replay")))
in (

let uu____6325 = (

let uu____6339 = (

let uu____6353 = (

let uu____6365 = (

let uu____6366 = (mk_bool true)
in Const (uu____6366))
in ((FStar_Getopt.noshort), ("silent"), (uu____6365), ("Disable all non-critical output")))
in (

let uu____6373 = (

let uu____6387 = (

let uu____6401 = (

let uu____6415 = (

let uu____6429 = (

let uu____6443 = (

let uu____6455 = (

let uu____6456 = (mk_bool true)
in Const (uu____6456))
in ((FStar_Getopt.noshort), ("tactic_raw_binders"), (uu____6455), ("Do not use the lexical scope of tactics to improve binder names")))
in (

let uu____6463 = (

let uu____6477 = (

let uu____6489 = (

let uu____6490 = (mk_bool true)
in Const (uu____6490))
in ((FStar_Getopt.noshort), ("tactics_failhard"), (uu____6489), ("Do not recover from metaprogramming errors, and abort if one occurs")))
in (

let uu____6497 = (

let uu____6511 = (

let uu____6523 = (

let uu____6524 = (mk_bool true)
in Const (uu____6524))
in ((FStar_Getopt.noshort), ("tactics_info"), (uu____6523), ("Print some rough information on tactics, such as the time they take to run")))
in (

let uu____6531 = (

let uu____6545 = (

let uu____6557 = (

let uu____6558 = (mk_bool true)
in Const (uu____6558))
in ((FStar_Getopt.noshort), ("tactic_trace"), (uu____6557), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))
in (

let uu____6565 = (

let uu____6579 = (

let uu____6593 = (

let uu____6605 = (

let uu____6606 = (mk_bool true)
in Const (uu____6606))
in ((FStar_Getopt.noshort), ("__tactics_nbe"), (uu____6605), ("Use NBE to evaluate metaprograms (experimental)")))
in (

let uu____6613 = (

let uu____6627 = (

let uu____6641 = (

let uu____6653 = (

let uu____6654 = (mk_bool true)
in Const (uu____6654))
in ((FStar_Getopt.noshort), ("timing"), (uu____6653), ("Print the time it takes to verify each top-level definition")))
in (

let uu____6661 = (

let uu____6675 = (

let uu____6687 = (

let uu____6688 = (mk_bool true)
in Const (uu____6688))
in ((FStar_Getopt.noshort), ("trace_error"), (uu____6687), ("Don\'t print an error message; show an exception trace instead")))
in (

let uu____6695 = (

let uu____6709 = (

let uu____6721 = (

let uu____6722 = (mk_bool true)
in Const (uu____6722))
in ((FStar_Getopt.noshort), ("ugly"), (uu____6721), ("Emit output formatted for debugging")))
in (

let uu____6729 = (

let uu____6743 = (

let uu____6755 = (

let uu____6756 = (mk_bool true)
in Const (uu____6756))
in ((FStar_Getopt.noshort), ("unthrottle_inductives"), (uu____6755), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))
in (

let uu____6763 = (

let uu____6777 = (

let uu____6789 = (

let uu____6790 = (mk_bool true)
in Const (uu____6790))
in ((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (uu____6789), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))
in (

let uu____6797 = (

let uu____6811 = (

let uu____6823 = (

let uu____6824 = (mk_bool true)
in Const (uu____6824))
in ((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (uu____6823), ("Use equality constraints when comparing higher-order types (Temporary)")))
in (

let uu____6831 = (

let uu____6845 = (

let uu____6857 = (

let uu____6858 = (mk_bool true)
in Const (uu____6858))
in ((FStar_Getopt.noshort), ("use_hints"), (uu____6857), ("Use a previously recorded hints database for proof replay")))
in (

let uu____6865 = (

let uu____6879 = (

let uu____6891 = (

let uu____6892 = (mk_bool true)
in Const (uu____6892))
in ((FStar_Getopt.noshort), ("use_hint_hashes"), (uu____6891), ("Admit queries if their hash matches the hash recorded in the hints database")))
in (

let uu____6899 = (

let uu____6913 = (

let uu____6927 = (

let uu____6939 = (

let uu____6940 = (mk_bool true)
in Const (uu____6940))
in ((FStar_Getopt.noshort), ("no_plugins"), (uu____6939), ("Do not run plugins natively and interpret them as usual instead")))
in (

let uu____6947 = (

let uu____6961 = (

let uu____6973 = (

let uu____6974 = (mk_bool true)
in Const (uu____6974))
in ((FStar_Getopt.noshort), ("no_tactics"), (uu____6973), ("Do not run the tactic engine before discharging a VC")))
in (

let uu____6981 = (

let uu____6995 = (

let uu____7009 = (

let uu____7023 = (

let uu____7037 = (

let uu____7049 = (

let uu____7050 = (mk_bool true)
in Const (uu____7050))
in ((FStar_Getopt.noshort), ("__temp_fast_implicits"), (uu____7049), ("Don\'t use this option yet")))
in (

let uu____7057 = (

let uu____7071 = (

let uu____7083 = (

let uu____7084 = (

let uu____7092 = (

let uu____7093 = (mk_bool true)
in Const (uu____7093))
in (((fun uu____7100 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____7092)))
in WithSideEffect (uu____7084))
in ((118 (*v*)), ("version"), (uu____7083), ("Display version number")))
in (

let uu____7109 = (

let uu____7123 = (

let uu____7135 = (

let uu____7136 = (mk_bool true)
in Const (uu____7136))
in ((FStar_Getopt.noshort), ("warn_default_effects"), (uu____7135), ("Warn when (a -> b) is desugared to (a -> Tot b)")))
in (

let uu____7143 = (

let uu____7157 = (

let uu____7171 = (

let uu____7183 = (

let uu____7184 = (mk_bool true)
in Const (uu____7184))
in ((FStar_Getopt.noshort), ("z3refresh"), (uu____7183), ("Restart Z3 after each query; useful for ensuring proof robustness")))
in (

let uu____7191 = (

let uu____7205 = (

let uu____7219 = (

let uu____7233 = (

let uu____7247 = (

let uu____7261 = (

let uu____7273 = (

let uu____7274 = (mk_bool true)
in Const (uu____7274))
in ((FStar_Getopt.noshort), ("__no_positivity"), (uu____7273), ("Don\'t check positivity of inductive types")))
in (

let uu____7281 = (

let uu____7295 = (

let uu____7307 = (

let uu____7308 = (mk_bool true)
in Const (uu____7308))
in ((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (uu____7307), ("Do not eta-expand coertions in generated OCaml")))
in (

let uu____7315 = (

let uu____7329 = (

let uu____7343 = (

let uu____7357 = (

let uu____7371 = (

let uu____7383 = (

let uu____7384 = (

let uu____7392 = (

let uu____7393 = (mk_bool true)
in Const (uu____7393))
in (((fun uu____7399 -> (FStar_ST.op_Colon_Equals debug_embedding true))), (uu____7392)))
in WithSideEffect (uu____7384))
in ((FStar_Getopt.noshort), ("__debug_embedding"), (uu____7383), ("Debug messages for embeddings/unembeddings of natively compiled terms")))
in (

let uu____7427 = (

let uu____7441 = (

let uu____7453 = (

let uu____7454 = (

let uu____7462 = (

let uu____7463 = (mk_bool true)
in Const (uu____7463))
in (((fun uu____7469 -> (FStar_ST.op_Colon_Equals eager_embedding true))), (uu____7462)))
in WithSideEffect (uu____7454))
in ((FStar_Getopt.noshort), ("eager_embedding"), (uu____7453), ("Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")))
in (

let uu____7497 = (

let uu____7511 = (

let uu____7523 = (

let uu____7524 = (

let uu____7532 = (

let uu____7533 = (mk_bool true)
in Const (uu____7533))
in (((fun uu____7540 -> ((

let uu____7542 = (specs ())
in (display_usage_aux uu____7542));
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____7532)))
in WithSideEffect (uu____7524))
in ((104 (*h*)), ("help"), (uu____7523), ("Display this information")))
in (

let uu____7566 = (

let uu____7580 = (

let uu____7592 = (

let uu____7593 = (mk_bool true)
in Const (uu____7593))
in ((FStar_Getopt.noshort), ("report_qi"), (uu____7592), ("Generates a quantifier instantiation report every time Z3 is closed")))
in (uu____7580)::[])
in (uu____7511)::uu____7566))
in (uu____7441)::uu____7497))
in (uu____7371)::uu____7427))
in (((FStar_Getopt.noshort), ("use_nbe"), (BoolStr), ("Use normalization by evaluation as the default normalization srategy (default \'false\')")))::uu____7357)
in (((FStar_Getopt.noshort), ("use_extracted_interfaces"), (BoolStr), ("Extract interfaces from the dependencies and use them for verification (default \'false\')")))::uu____7343)
in (((FStar_Getopt.noshort), ("warn_error"), (SimpleStr ("")), ("The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")))::uu____7329)
in (uu____7295)::uu____7315))
in (uu____7261)::uu____7281))
in (((FStar_Getopt.noshort), ("use_two_phase_tc"), (BoolStr), ("Use the two phase typechecker (default \'true\')")))::uu____7247)
in (((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::uu____7233)
in (((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::uu____7219)
in (((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::uu____7205)
in (uu____7171)::uu____7191))
in (((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::uu____7157)
in (uu____7123)::uu____7143))
in (uu____7071)::uu____7109))
in (uu____7037)::uu____7057))
in (((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::uu____7023)
in (((FStar_Getopt.noshort), ("vcgen.optimize_bind_as_seq"), (EnumStr (("off")::("without_type")::("with_type")::[])), ("\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")))::uu____7009)
in (((FStar_Getopt.noshort), ("using_facts_from"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | fact id)\'"))), ("\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the \'+\' is optional: --using_facts_from \'FStar.List\' is equivalent to --using_facts_from \'+FStar.List\'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")))::uu____6995)
in (uu____6961)::uu____6981))
in (uu____6927)::uu____6947))
in (((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::uu____6913)
in (uu____6879)::uu____6899))
in (uu____6845)::uu____6865))
in (uu____6811)::uu____6831))
in (uu____6777)::uu____6797))
in (uu____6743)::uu____6763))
in (uu____6709)::uu____6729))
in (uu____6675)::uu____6695))
in (uu____6641)::uu____6661))
in (((FStar_Getopt.noshort), ("tcnorm"), (BoolStr), ("Attempt to normalize definitions marked as tcnorm (default \'true\')")))::uu____6627)
in (uu____6593)::uu____6613))
in (((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::uu____6579)
in (uu____6545)::uu____6565))
in (uu____6511)::uu____6531))
in (uu____6477)::uu____6497))
in (uu____6443)::uu____6463))
in (((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::uu____6429)
in (((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::uu____6415)
in (((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::uu____6401)
in (((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::uu____6387)
in (uu____6353)::uu____6373))
in (((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::uu____6339)
in (uu____6305)::uu____6325))
in (uu____6271)::uu____6291))
in (uu____6237)::uu____6257))
in (uu____6203)::uu____6223))
in (uu____6169)::uu____6189))
in (uu____6135)::uu____6155))
in (uu____6101)::uu____6121))
in (uu____6067)::uu____6087))
in (uu____6033)::uu____6053))
in (((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::uu____6019)
in (((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::uu____6005)
in (uu____5971)::uu____5991))
in (uu____5937)::uu____5957))
in (uu____5903)::uu____5923))
in (((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Deprecated: use --extract instead; Do not extract code from this module")))::uu____5889)
in (uu____5855)::uu____5875))
in (((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::uu____5841)
in (uu____5807)::uu____5827))
in (((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::uu____5793)
in (((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::uu____5779)
in (((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::uu____5765)
in (uu____5731)::uu____5751))
in (uu____5697)::uu____5717))
in (((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::uu____5683)
in (uu____5649)::uu____5669))
in (((FStar_Getopt.noshort), ("keep_query_captions"), (BoolStr), ("Retain comments in the logged SMT queries (requires --log_queries; default true)")))::uu____5635)
in (((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::uu____5621)
in (((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::uu____5607)
in (uu____5573)::uu____5593))
in (uu____5539)::uu____5559))
in (((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::uu____5525)
in (uu____5491)::uu____5511))
in (uu____5457)::uu____5477))
in (uu____5423)::uu____5443))
in (((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::uu____5409)
in (uu____5375)::uu____5395))
in (uu____5341)::uu____5361))
in (((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Deprecated: use --extract instead; Only extract modules in the specified namespace")))::uu____5327)
in (((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")))::uu____5313)
in (((FStar_Getopt.noshort), ("extract"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the \'+\' is optional: --extract \'+A\' and --extract \'A\' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract \'A B\'.")))::uu____5299)
in (uu____5265)::uu____5285))
in (uu____5231)::uu____5251))
in (((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::uu____5217)
in (uu____5183)::uu____5203))
in (uu____5149)::uu____5169))
in (uu____5115)::uu____5135))
in (((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::("full")::("raw")::[])), ("Output the transitive closure of the full dependency graph in three formats:\n\t \'graph\': a format suitable the \'dot\' tool from \'GraphViz\'\n\t \'full\': a format suitable for \'make\', including dependences for producing .ml and .krml files\n\t \'make\': (deprecated) a format suitable for \'make\', including only dependences among source files")))::uu____5101)
in (((FStar_Getopt.noshort), ("defensive"), (EnumStr (("no")::("warn")::("fail")::[])), ("Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif \'no\', no checks are performed\n\t\tif \'warn\', checks are performed and raise a warning when they fail\n\t\tif \'fail\', like \'warn\', but the compiler aborts instead of issuing a warning\n\t\t(default \'no\')")))::uu____5087)
in (((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::uu____5073)
in (((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::uu____5059)
in (((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::uu____5045)
in (((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::("Plugin")::[])), ("Generate code for further compilation to executable code, or build a compiler plugin")))::uu____5031)
in (uu____4997)::uu____5017))
in (uu____4963)::uu____4983))
in (((FStar_Getopt.noshort), ("cache_dir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Read and write .checked and .checked.lax in directory <dir>")))::uu____4949)
in (uu____4915)::uu____4935))
in (((FStar_Getopt.noshort), ("already_cached"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")))::uu____4901)
in (((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("[symbol|(symbol, id)]")), ("Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\' or --admit_except FStar.Fin.pigeonhole)")))::uu____4887)
in (((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::uu____4873)
in (((FStar_Getopt.noshort), ("abort_on"), (PostProcessed ((((fun uu___87_9108 -> (match (uu___87_9108) with
| Int (x) -> begin
((FStar_ST.op_Colon_Equals abort_counter x);
Int (x);
)
end
| x -> begin
(failwith "?")
end))), (IntStr ("non-negative integer"))))), ("Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")))::uu____4859))
and specs : unit  ->  FStar_Getopt.opt Prims.list = (fun uu____9137 -> (

let uu____9140 = (specs_with_types ())
in (FStar_List.map (fun uu____9171 -> (match (uu____9171) with
| (short, long, typ, doc) -> begin
(

let uu____9193 = (

let uu____9207 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____9207), (doc)))
in (mk_spec uu____9193))
end)) uu____9140)))


let settable : Prims.string  ->  Prims.bool = (fun uu___88_9222 -> (match (uu___88_9222) with
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
| uu____9345 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")) || (Prims.op_Equality s "using_facts_from")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____9444 -> (match (uu____9444) with
| (uu____9459, x, uu____9461, uu____9462) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____9537 -> (match (uu____9537) with
| (uu____9552, x, uu____9554, uu____9555) -> begin
(resettable x)
end))))


let display_usage : unit  ->  unit = (fun uu____9571 -> (

let uu____9572 = (specs ())
in (display_usage_aux uu____9572)))


let fstar_bin_directory : Prims.string = (FStar_Util.get_exec_dir ())

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____9604) -> begin
true
end
| uu____9607 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____9618) -> begin
uu____9618
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
in (FStar_All.try_with (fun uu___93_9639 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____9643 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___92_9653 -> (match (uu___92_9653) with
| File_argument (s1) -> begin
(

let uu____9656 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____9656))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____9692 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____9698 = (

let uu____9702 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____9702 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____9698))))
in (

let uu____9759 = (

let uu____9763 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9763))
in ((res), (uu____9759)))))


let file_list : unit  ->  Prims.string Prims.list = (fun uu____9805 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____9845 -> begin
(init ())
end);
(

let r = (

let uu____9848 = (specs ())
in (FStar_Getopt.parse_cmdline uu____9848 (fun x -> ())))
in ((

let uu____9855 = (

let uu____9861 = (

let uu____9862 = (FStar_List.map mk_string old_verify_module)
in List (uu____9862))
in (("verify_module"), (uu____9861)))
in (set_option' uu____9855));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____9881 = (

let uu____9883 = (

let uu____9885 = (

let uu____9887 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____9887))
in ((FStar_String.length f1) - uu____9885))
in (uu____9883 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____9881))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____9900 = (get_lax ())
in (match (uu____9900) with
| true -> begin
false
end
| uu____9905 -> begin
(

let l = (get_verify_module ())
in (FStar_List.contains (FStar_String.lowercase m) l))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____9921 = (module_name_of_file_name fn)
in (should_verify uu____9921)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____9932 = (get___temp_no_proj ())
in (FStar_List.contains m uu____9932)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____9946 = (should_verify m)
in (match (uu____9946) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____9952 -> begin
false
end)))


let include_path : unit  ->  Prims.string Prims.list = (fun uu____9963 -> (

let cache_dir = (

let uu____9968 = (get_cache_dir ())
in (match (uu____9968) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (c) -> begin
(c)::[]
end))
in (

let uu____9982 = (get_no_default_includes ())
in (match (uu____9982) with
| true -> begin
(

let uu____9988 = (get_include ())
in (FStar_List.append cache_dir uu____9988))
end
| uu____9993 -> begin
(

let lib_paths = (

let uu____9999 = (FStar_Util.expand_environment_variable "FSTAR_LIB")
in (match (uu____9999) with
| FStar_Pervasives_Native.None -> begin
(

let fstar_home = (Prims.strcat fstar_bin_directory "/..")
in (

let defs = universe_include_path_base_dirs
in (

let uu____10015 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat fstar_home x))))
in (FStar_All.pipe_right uu____10015 (FStar_List.filter FStar_Util.file_exists)))))
end
| FStar_Pervasives_Native.Some (s) -> begin
(s)::[]
end))
in (

let uu____10042 = (

let uu____10046 = (

let uu____10050 = (get_include ())
in (FStar_List.append uu____10050 ((".")::[])))
in (FStar_List.append lib_paths uu____10046))
in (FStar_List.append cache_dir uu____10042)))
end))))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (

let file_map = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun filename -> (

let uu____10077 = (FStar_Util.smap_try_find file_map filename)
in (match (uu____10077) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| FStar_Pervasives_Native.None -> begin
(

let result = (FStar_All.try_with (fun uu___95_10099 -> (match (()) with
| () -> begin
(

let uu____10103 = (FStar_Util.is_path_absolute filename)
in (match (uu____10103) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____10114 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10117 -> begin
(

let uu____10119 = (

let uu____10123 = (include_path ())
in (FStar_List.rev uu____10123))
in (FStar_Util.find_map uu____10119 (fun p -> (

let path = (match ((Prims.op_Equality p ".")) with
| true -> begin
filename
end
| uu____10140 -> begin
(FStar_Util.join_paths p filename)
end)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____10147 -> begin
FStar_Pervasives_Native.None
end)))))
end))
end)) (fun uu___94_10151 -> FStar_Pervasives_Native.None))
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


let prims : unit  ->  Prims.string = (fun uu____10171 -> (

let uu____10172 = (get_prims ())
in (match (uu____10172) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____10181 = (find_file filename)
in (match (uu____10181) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10190 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10190))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : unit  ->  Prims.string = (fun uu____10203 -> (

let uu____10204 = (prims ())
in (FStar_Util.basename uu____10204)))


let pervasives : unit  ->  Prims.string = (fun uu____10212 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____10216 = (find_file filename)
in (match (uu____10216) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10225 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10225))
end))))


let pervasives_basename : unit  ->  Prims.string = (fun uu____10235 -> (

let uu____10236 = (pervasives ())
in (FStar_Util.basename uu____10236)))


let pervasives_native_basename : unit  ->  Prims.string = (fun uu____10244 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____10248 = (find_file filename)
in (match (uu____10248) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10257 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____10257))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____10270 = (get_odir ())
in (match (uu____10270) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Util.join_paths x fname)
end)))


let prepend_cache_dir : Prims.string  ->  Prims.string = (fun fpath -> (

let uu____10288 = (get_cache_dir ())
in (match (uu____10288) with
| FStar_Pervasives_Native.None -> begin
fpath
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____10297 = (FStar_Util.basename fpath)
in (FStar_Util.join_paths x uu____10297))
end)))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split ((46 (*.*))::[]) text))


let parse_settings : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun ns -> (

let cache = (FStar_Util.smap_create (Prims.parse_int "31"))
in (

let with_cache = (fun f s -> (

let uu____10419 = (FStar_Util.smap_try_find cache s)
in (match (uu____10419) with
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
| uu____10538 -> begin
(match ((FStar_Util.starts_with s "-")) with
| true -> begin
(

let path = (

let uu____10554 = (FStar_Util.substring_from s (Prims.parse_int "1"))
in (path_of_text uu____10554))
in ((path), (false)))
end
| uu____10562 -> begin
(

let s1 = (match ((FStar_Util.starts_with s "+")) with
| true -> begin
(FStar_Util.substring_from s (Prims.parse_int "1"))
end
| uu____10570 -> begin
s
end)
in (((path_of_text s1)), (true)))
end)
end))
in (

let uu____10577 = (FStar_All.pipe_right ns (FStar_List.collect (fun s -> (

let s1 = (FStar_Util.trim_string s)
in (match ((Prims.op_Equality s1 "")) with
| true -> begin
[]
end
| uu____10637 -> begin
(with_cache (fun s2 -> (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_List.map parse_one_setting))) s1)
end)))))
in (FStar_All.pipe_right uu____10577 FStar_List.rev))))))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____10703 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____10703 (FStar_List.contains s))))


let __temp_fast_implicits : unit  ->  Prims.bool = (fun uu____10718 -> (lookup_opt "__temp_fast_implicits" as_bool))


let admit_smt_queries : unit  ->  Prims.bool = (fun uu____10727 -> (get_admit_smt_queries ()))


let admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____10736 -> (get_admit_except ()))


let cache_checked_modules : unit  ->  Prims.bool = (fun uu____10743 -> (get_cache_checked_modules ()))


let cache_off : unit  ->  Prims.bool = (fun uu____10750 -> (get_cache_off ()))


let cmi : unit  ->  Prims.bool = (fun uu____10757 -> (get_cmi ()))

type codegen_t =
| OCaml
| FSharp
| Kremlin
| Plugin


let uu___is_OCaml : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OCaml -> begin
true
end
| uu____10767 -> begin
false
end))


let uu___is_FSharp : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSharp -> begin
true
end
| uu____10778 -> begin
false
end))


let uu___is_Kremlin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kremlin -> begin
true
end
| uu____10789 -> begin
false
end))


let uu___is_Plugin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Plugin -> begin
true
end
| uu____10800 -> begin
false
end))


let codegen : unit  ->  codegen_t FStar_Pervasives_Native.option = (fun uu____10809 -> (

let uu____10810 = (get_codegen ())
in (FStar_Util.map_opt uu____10810 (fun uu___89_10816 -> (match (uu___89_10816) with
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
| uu____10822 -> begin
(failwith "Impossible")
end)))))


let codegen_libs : unit  ->  Prims.string Prims.list Prims.list = (fun uu____10835 -> (

let uu____10836 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____10836 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : unit  ->  Prims.bool = (fun uu____10862 -> (

let uu____10863 = (get_debug ())
in (Prims.op_disEquality uu____10863 [])))


let debug_module : Prims.string  ->  Prims.bool = (fun modul -> (

let uu____10880 = (get_debug ())
in (FStar_All.pipe_right uu____10880 (FStar_List.contains modul))))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____10905 = (get_debug ())
in (FStar_All.pipe_right uu____10905 (FStar_List.contains modul))) && (debug_level_geq level)))


let defensive : unit  ->  Prims.bool = (fun uu____10920 -> (

let uu____10921 = (get_defensive ())
in (Prims.op_disEquality uu____10921 "no")))


let defensive_fail : unit  ->  Prims.bool = (fun uu____10931 -> (

let uu____10932 = (get_defensive ())
in (Prims.op_Equality uu____10932 "fail")))


let dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____10944 -> (get_dep ()))


let detail_errors : unit  ->  Prims.bool = (fun uu____10951 -> (get_detail_errors ()))


let detail_hint_replay : unit  ->  Prims.bool = (fun uu____10958 -> (get_detail_hint_replay ()))


let doc : unit  ->  Prims.bool = (fun uu____10965 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____10975 = (get_dump_module ())
in (FStar_All.pipe_right uu____10975 (FStar_List.contains s))))


let eager_subtyping : unit  ->  Prims.bool = (fun uu____10990 -> (get_eager_subtyping ()))


let expose_interfaces : unit  ->  Prims.bool = (fun uu____10997 -> (get_expose_interfaces ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____11007 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____11007)))


let full_context_dependency : unit  ->  Prims.bool = (fun uu____11043 -> true)


let hide_uvar_nums : unit  ->  Prims.bool = (fun uu____11051 -> (get_hide_uvar_nums ()))


let hint_info : unit  ->  Prims.bool = (fun uu____11058 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11067 -> (get_hint_file ()))


let ide : unit  ->  Prims.bool = (fun uu____11074 -> (get_ide ()))


let print : unit  ->  Prims.bool = (fun uu____11081 -> (get_print ()))


let print_in_place : unit  ->  Prims.bool = (fun uu____11088 -> (get_print_in_place ()))


let initial_fuel : unit  ->  Prims.int = (fun uu____11095 -> (

let uu____11096 = (get_initial_fuel ())
in (

let uu____11098 = (get_max_fuel ())
in (Prims.min uu____11096 uu____11098))))


let initial_ifuel : unit  ->  Prims.int = (fun uu____11106 -> (

let uu____11107 = (get_initial_ifuel ())
in (

let uu____11109 = (get_max_ifuel ())
in (Prims.min uu____11107 uu____11109))))


let interactive : unit  ->  Prims.bool = (fun uu____11117 -> ((get_in ()) || (get_ide ())))


let lax : unit  ->  Prims.bool = (fun uu____11124 -> (get_lax ()))


let load : unit  ->  Prims.string Prims.list = (fun uu____11133 -> (get_load ()))


let legacy_interactive : unit  ->  Prims.bool = (fun uu____11140 -> (get_in ()))


let log_queries : unit  ->  Prims.bool = (fun uu____11147 -> (get_log_queries ()))


let keep_query_captions : unit  ->  Prims.bool = (fun uu____11154 -> ((log_queries ()) && (get_keep_query_captions ())))


let log_types : unit  ->  Prims.bool = (fun uu____11161 -> (get_log_types ()))


let max_fuel : unit  ->  Prims.int = (fun uu____11168 -> (get_max_fuel ()))


let max_ifuel : unit  ->  Prims.int = (fun uu____11175 -> (get_max_ifuel ()))


let min_fuel : unit  ->  Prims.int = (fun uu____11182 -> (get_min_fuel ()))


let ml_ish : unit  ->  Prims.bool = (fun uu____11189 -> (get_MLish ()))


let set_ml_ish : unit  ->  unit = (fun uu____11195 -> (set_option "MLish" (Bool (true))))


let n_cores : unit  ->  Prims.int = (fun uu____11204 -> (get_n_cores ()))


let no_default_includes : unit  ->  Prims.bool = (fun uu____11211 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let s1 = (FStar_String.lowercase s)
in (

let uu____11223 = (get_no_extract ())
in (FStar_All.pipe_right uu____11223 (FStar_Util.for_some (fun f -> (Prims.op_Equality (FStar_String.lowercase f) s1)))))))


let normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____11242 -> (get_normalize_pure_terms_for_extraction ()))


let no_location_info : unit  ->  Prims.bool = (fun uu____11249 -> (get_no_location_info ()))


let no_plugins : unit  ->  Prims.bool = (fun uu____11256 -> (get_no_plugins ()))


let no_smt : unit  ->  Prims.bool = (fun uu____11263 -> (get_no_smt ()))


let output_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11272 -> (get_odir ()))


let ugly : unit  ->  Prims.bool = (fun uu____11279 -> (get_ugly ()))


let print_bound_var_types : unit  ->  Prims.bool = (fun uu____11286 -> (get_print_bound_var_types ()))


let print_effect_args : unit  ->  Prims.bool = (fun uu____11293 -> (get_print_effect_args ()))


let print_implicits : unit  ->  Prims.bool = (fun uu____11300 -> (get_print_implicits ()))


let print_real_names : unit  ->  Prims.bool = (fun uu____11307 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : unit  ->  Prims.bool = (fun uu____11314 -> (get_print_universes ()))


let print_z3_statistics : unit  ->  Prims.bool = (fun uu____11321 -> ((get_print_z3_statistics ()) || (get_query_stats ())))


let query_stats : unit  ->  Prims.bool = (fun uu____11328 -> (get_query_stats ()))


let record_hints : unit  ->  Prims.bool = (fun uu____11335 -> (get_record_hints ()))


let reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11344 -> (get_reuse_hint_for ()))


let silent : unit  ->  Prims.bool = (fun uu____11351 -> (get_silent ()))


let smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____11358 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : unit  ->  Prims.bool = (fun uu____11365 -> (

let uu____11366 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11366 "native")))


let smtencoding_nl_arith_wrapped : unit  ->  Prims.bool = (fun uu____11376 -> (

let uu____11377 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11377 "wrapped")))


let smtencoding_nl_arith_default : unit  ->  Prims.bool = (fun uu____11387 -> (

let uu____11388 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____11388 "boxwrap")))


let smtencoding_l_arith_native : unit  ->  Prims.bool = (fun uu____11398 -> (

let uu____11399 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____11399 "native")))


let smtencoding_l_arith_default : unit  ->  Prims.bool = (fun uu____11409 -> (

let uu____11410 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____11410 "boxwrap")))


let tactic_raw_binders : unit  ->  Prims.bool = (fun uu____11420 -> (get_tactic_raw_binders ()))


let tactics_failhard : unit  ->  Prims.bool = (fun uu____11427 -> (get_tactics_failhard ()))


let tactics_info : unit  ->  Prims.bool = (fun uu____11434 -> (get_tactics_info ()))


let tactic_trace : unit  ->  Prims.bool = (fun uu____11441 -> (get_tactic_trace ()))


let tactic_trace_d : unit  ->  Prims.int = (fun uu____11448 -> (get_tactic_trace_d ()))


let tactics_nbe : unit  ->  Prims.bool = (fun uu____11455 -> (get_tactics_nbe ()))


let tcnorm : unit  ->  Prims.bool = (fun uu____11462 -> (get_tcnorm ()))


let timing : unit  ->  Prims.bool = (fun uu____11469 -> (get_timing ()))


let trace_error : unit  ->  Prims.bool = (fun uu____11476 -> (get_trace_error ()))


let unthrottle_inductives : unit  ->  Prims.bool = (fun uu____11483 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____11490 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____11497 -> (get_use_eq_at_higher_order ()))


let use_hints : unit  ->  Prims.bool = (fun uu____11504 -> (get_use_hints ()))


let use_hint_hashes : unit  ->  Prims.bool = (fun uu____11511 -> (get_use_hint_hashes ()))


let use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____11520 -> (get_use_native_tactics ()))


let use_tactics : unit  ->  Prims.bool = (fun uu____11527 -> (get_use_tactics ()))


let using_facts_from : unit  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun uu____11543 -> (

let uu____11544 = (get_using_facts_from ())
in (match (uu____11544) with
| FStar_Pervasives_Native.None -> begin
((([]), (true)))::[]
end
| FStar_Pervasives_Native.Some (ns) -> begin
(parse_settings ns)
end)))


let vcgen_optimize_bind_as_seq : unit  ->  Prims.bool = (fun uu____11598 -> (

let uu____11599 = (get_vcgen_optimize_bind_as_seq ())
in (FStar_Option.isSome uu____11599)))


let vcgen_decorate_with_type : unit  ->  Prims.bool = (fun uu____11610 -> (

let uu____11611 = (get_vcgen_optimize_bind_as_seq ())
in (match (uu____11611) with
| FStar_Pervasives_Native.Some ("with_type") -> begin
true
end
| uu____11619 -> begin
false
end)))


let warn_default_effects : unit  ->  Prims.bool = (fun uu____11630 -> (get_warn_default_effects ()))


let z3_exe : unit  ->  Prims.string = (fun uu____11637 -> (

let uu____11638 = (get_smt ())
in (match (uu____11638) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : unit  ->  Prims.string Prims.list = (fun uu____11656 -> (get_z3cliopt ()))


let z3_refresh : unit  ->  Prims.bool = (fun uu____11663 -> (get_z3refresh ()))


let z3_rlimit : unit  ->  Prims.int = (fun uu____11670 -> (get_z3rlimit ()))


let z3_rlimit_factor : unit  ->  Prims.int = (fun uu____11677 -> (get_z3rlimit_factor ()))


let z3_seed : unit  ->  Prims.int = (fun uu____11684 -> (get_z3seed ()))


let use_two_phase_tc : unit  ->  Prims.bool = (fun uu____11691 -> ((get_use_two_phase_tc ()) && (

let uu____11693 = (lax ())
in (not (uu____11693)))))


let no_positivity : unit  ->  Prims.bool = (fun uu____11701 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____11708 -> (get_ml_no_eta_expand_coertions ()))


let warn_error : unit  ->  Prims.string = (fun uu____11715 -> (get_warn_error ()))


let use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____11722 -> (get_use_extracted_interfaces ()))


let use_nbe : unit  ->  Prims.bool = (fun uu____11729 -> (get_use_nbe ()))


let report_qi : unit  ->  Prims.bool = (fun uu____11736 -> (get_report_qi ()))


let with_saved_options : 'a . (unit  ->  'a)  ->  'a = (fun f -> (

let uu____11753 = (

let uu____11755 = (trace_error ())
in (not (uu____11755)))
in (match (uu____11753) with
| true -> begin
((push ());
(

let r = (FStar_All.try_with (fun uu___97_11770 -> (match (()) with
| () -> begin
(

let uu____11775 = (f ())
in FStar_Util.Inr (uu____11775))
end)) (fun uu___96_11777 -> FStar_Util.Inl (uu___96_11777)))
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
| uu____11785 -> begin
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
| (uu____11858, []) -> begin
true
end
| ((m2)::ms, (p)::ps) -> begin
((Prims.op_Equality m2 (FStar_String.lowercase p)) && (matches_path ms ps))
end
| uu____11891 -> begin
false
end))
in (

let uu____11903 = (FStar_All.pipe_right setting (FStar_Util.try_find (fun uu____11945 -> (match (uu____11945) with
| (path, uu____11956) -> begin
(matches_path m_components path)
end))))
in (match (uu____11903) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____11975, flag) -> begin
flag
end)))))))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> (

let m1 = (FStar_String.lowercase m)
in (

let uu____12004 = (get_extract ())
in (match (uu____12004) with
| FStar_Pervasives_Native.Some (extract_setting) -> begin
((

let uu____12019 = (

let uu____12035 = (get_no_extract ())
in (

let uu____12039 = (get_extract_namespace ())
in (

let uu____12043 = (get_extract_module ())
in ((uu____12035), (uu____12039), (uu____12043)))))
in (match (uu____12019) with
| ([], [], []) -> begin
()
end
| uu____12068 -> begin
(failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module")
end));
(module_matches_namespace_filter m1 extract_setting);
)
end
| FStar_Pervasives_Native.None -> begin
(

let should_extract_namespace = (fun m2 -> (

let uu____12097 = (get_extract_namespace ())
in (match (uu____12097) with
| [] -> begin
false
end
| ns -> begin
(FStar_All.pipe_right ns (FStar_Util.for_some (fun n1 -> (FStar_Util.starts_with m2 (FStar_String.lowercase n1)))))
end)))
in (

let should_extract_module = (fun m2 -> (

let uu____12125 = (get_extract_module ())
in (match (uu____12125) with
| [] -> begin
false
end
| l -> begin
(FStar_All.pipe_right l (FStar_Util.for_some (fun n1 -> (Prims.op_Equality (FStar_String.lowercase n1) m2))))
end)))
in ((

let uu____12147 = (no_extract m1)
in (not (uu____12147))) && (

let uu____12150 = (

let uu____12161 = (get_extract_namespace ())
in (

let uu____12165 = (get_extract_module ())
in ((uu____12161), (uu____12165))))
in (match (uu____12150) with
| ([], []) -> begin
true
end
| uu____12185 -> begin
((should_extract_namespace m1) || (should_extract_module m1))
end)))))
end))))


let should_be_already_cached : Prims.string  ->  Prims.bool = (fun m -> (

let uu____12205 = (get_already_cached ())
in (match (uu____12205) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (already_cached_setting) -> begin
(module_matches_namespace_filter m already_cached_setting)
end)))




