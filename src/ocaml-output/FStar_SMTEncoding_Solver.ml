
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____60 = (FStar_Options.record_hints ())
in (match (uu____60) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____88 -> begin
()
end));
(

let uu____90 = (FStar_Options.use_hints ())
in (match (uu____90) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____97 = (FStar_Options.hint_file ())
in (match (uu____97) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____106 = (FStar_Util.read_hints val_filename)
in (match (uu____106) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____113 = (FStar_Options.hint_info ())
in (match (uu____113) with
| true -> begin
(

let uu____116 = (

let uu____118 = (FStar_Options.hint_file ())
in (match (uu____118) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____128 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____138 -> begin
"invalid; using potentially stale hints"
end) uu____116))
end
| uu____141 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____166 = (FStar_Options.hint_info ())
in (match (uu____166) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____170 -> begin
()
end))
end))))
end
| uu____172 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____183 = (FStar_Options.record_hints ())
in (match (uu____183) with
| true -> begin
(

let hints = (

let uu____187 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____187))
in (

let hints_db = (

let uu____214 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____214; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____220 = (FStar_Options.hint_file ())
in (match (uu____220) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____229 -> begin
()
end));
(FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None);
(FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None);
))


let with_hints_db : 'a . Prims.string  ->  (unit  ->  'a)  ->  'a = (fun fname f -> ((initialize_hints_db fname);
(

let result = (f ())
in ((finalize_hints_db fname);
result;
));
))


let filter_using_facts_from : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decls_t = (fun e theory -> (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____337 -> begin
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun uu___375_345 -> (match (uu___375_345) with
| FStar_SMTEncoding_Term.Name (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____348 -> begin
false
end)))) || (

let uu____351 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____351)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (

let keep_decl = (fun uu___376_371 -> (match (uu___376_371) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(matches_fact_ids include_assumption_names a)
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
true;
)
end
| FStar_SMTEncoding_Term.Module (uu____386) -> begin
(failwith "Solver.fs::keep_decl should never have been called with a Module decl")
end
| uu____396 -> begin
true
end))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____413 = (FStar_All.pipe_right decls (FStar_List.filter keep_decl))
in (FStar_All.pipe_right uu____413 (fun decls1 -> (FStar_SMTEncoding_Term.Module (((name), (decls1))))::out)))
end
| uu____431 -> begin
(

let uu____432 = (keep_decl d)
in (match (uu____432) with
| true -> begin
(d)::out
end
| uu____435 -> begin
out
end))
end)) [] theory_rev)))
in pruned_theory))))


let rec filter_assertions_with_stats : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool * Prims.int * Prims.int) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____478 = (filter_using_facts_from e theory)
in ((uu____478), (false), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let theory_rev = (FStar_List.rev theory)
in (

let uu____493 = (

let uu____502 = (

let uu____513 = (

let uu____516 = (

let uu____517 = (

let uu____519 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____519))
in FStar_SMTEncoding_Term.Caption (uu____517))
in (uu____516)::[])
in ((uu____513), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (FStar_List.fold_left (fun uu____549 d -> (match (uu____549) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____610 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____628 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____643 = (FStar_All.pipe_right decls (filter_assertions_with_stats e (FStar_Pervasives_Native.Some (core1))))
in (FStar_All.pipe_right uu____643 (fun uu____701 -> (match (uu____701) with
| (decls1, uu____726, r, p) -> begin
(((FStar_SMTEncoding_Term.Module (((name), (decls1))))::theory1), ((n_retained + r)), ((n_pruned + p)))
end))))
end
| uu____746 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) uu____502 theory_rev))
in (match (uu____493) with
| (theory', n_retained, n_pruned) -> begin
(

let uu____769 = uu____493
in ((theory'), (true), (n_retained), (n_pruned)))
end)))
end))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun e core theory -> (

let uu____808 = (filter_assertions_with_stats e core theory)
in (match (uu____808) with
| (theory1, b, uu____827, uu____828) -> begin
((theory1), (b))
end)))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun e x -> (

let uu____857 = (filter_using_facts_from e x)
in ((uu____857), (false))))

type errors =
{error_reason : Prims.string; error_fuel : Prims.int; error_ifuel : Prims.int; error_hint : Prims.string Prims.list FStar_Pervasives_Native.option; error_messages : (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list}


let __proj__Mkerrors__item__error_reason : errors  ->  Prims.string = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_reason
end))


let __proj__Mkerrors__item__error_fuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_fuel
end))


let __proj__Mkerrors__item__error_ifuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_ifuel
end))


let __proj__Mkerrors__item__error_hint : errors  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_hint
end))


let __proj__Mkerrors__item__error_messages : errors  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_messages
end))


let error_to_short_string : errors  ->  Prims.string = (fun err -> (

let uu____1084 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____1086 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason uu____1084 uu____1086 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"with hint"
end
| uu____1095 -> begin
""
end)))))

type query_settings =
{query_env : FStar_TypeChecker_Env.env; query_decl : FStar_SMTEncoding_Term.decl; query_name : Prims.string; query_index : Prims.int; query_range : FStar_Range.range; query_fuel : Prims.int; query_ifuel : Prims.int; query_rlimit : Prims.int; query_hint : FStar_SMTEncoding_Z3.unsat_core; query_errors : errors Prims.list; query_all_labels : FStar_SMTEncoding_Term.error_labels; query_suffix : FStar_SMTEncoding_Term.decl Prims.list; query_hash : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkquery_settings__item__query_env : query_settings  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_env
end))


let __proj__Mkquery_settings__item__query_decl : query_settings  ->  FStar_SMTEncoding_Term.decl = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_decl
end))


let __proj__Mkquery_settings__item__query_name : query_settings  ->  Prims.string = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_name
end))


let __proj__Mkquery_settings__item__query_index : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_index
end))


let __proj__Mkquery_settings__item__query_range : query_settings  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_range
end))


let __proj__Mkquery_settings__item__query_fuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_fuel
end))


let __proj__Mkquery_settings__item__query_ifuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_ifuel
end))


let __proj__Mkquery_settings__item__query_rlimit : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_rlimit
end))


let __proj__Mkquery_settings__item__query_hint : query_settings  ->  FStar_SMTEncoding_Z3.unsat_core = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_hint
end))


let __proj__Mkquery_settings__item__query_errors : query_settings  ->  errors Prims.list = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_errors
end))


let __proj__Mkquery_settings__item__query_all_labels : query_settings  ->  FStar_SMTEncoding_Term.error_labels = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_all_labels
end))


let __proj__Mkquery_settings__item__query_suffix : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_suffix
end))


let __proj__Mkquery_settings__item__query_hash : query_settings  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_hash
end))


let settings_to_info : query_settings  ->  FStar_SMTEncoding_Analysis.query_info = (fun s -> {FStar_SMTEncoding_Analysis.query_info_name = s.query_name; FStar_SMTEncoding_Analysis.query_info_index = s.query_index; FStar_SMTEncoding_Analysis.query_info_range = s.query_range})


let with_fuel_and_diagnostics : query_settings  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decls_t = (fun settings label_assumptions -> (

let n1 = settings.query_fuel
in (

let i = settings.query_ifuel
in (

let rlimit = settings.query_rlimit
in (

let uu____1625 = (

let uu____1628 = (

let uu____1629 = (

let uu____1631 = (FStar_Util.string_of_int n1)
in (

let uu____1633 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1631 uu____1633)))
in FStar_SMTEncoding_Term.Caption (uu____1629))
in (

let uu____1636 = (

let uu____1639 = (

let uu____1640 = (

let uu____1648 = (

let uu____1649 = (

let uu____1654 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1659 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1654), (uu____1659))))
in (FStar_SMTEncoding_Util.mkEq uu____1649))
in ((uu____1648), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1640))
in (

let uu____1663 = (

let uu____1666 = (

let uu____1667 = (

let uu____1675 = (

let uu____1676 = (

let uu____1681 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1686 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1681), (uu____1686))))
in (FStar_SMTEncoding_Util.mkEq uu____1676))
in ((uu____1675), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1667))
in (uu____1666)::(settings.query_decl)::[])
in (uu____1639)::uu____1663))
in (uu____1628)::uu____1636))
in (

let uu____1690 = (

let uu____1693 = (

let uu____1696 = (

let uu____1699 = (

let uu____1700 = (

let uu____1707 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1707)))
in FStar_SMTEncoding_Term.SetOption (uu____1700))
in (uu____1699)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[])
in (

let uu____1712 = (

let uu____1715 = (

let uu____1718 = ((FStar_Options.record_hints ()) || (FStar_Options.analyze_proof ()))
in (match (uu____1718) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____1723 -> begin
[]
end))
in (

let uu____1725 = (

let uu____1728 = (

let uu____1731 = (FStar_Options.analyze_proof ())
in (match (uu____1731) with
| true -> begin
(FStar_SMTEncoding_Term.GetProof)::[]
end
| uu____1736 -> begin
[]
end))
in (

let uu____1738 = (

let uu____1741 = (

let uu____1744 = (FStar_Options.print_z3_statistics ())
in (match (uu____1744) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1749 -> begin
[]
end))
in (FStar_List.append uu____1741 settings.query_suffix))
in (FStar_List.append uu____1728 uu____1738)))
in (FStar_List.append uu____1715 uu____1725)))
in (FStar_List.append uu____1696 uu____1712)))
in (FStar_List.append label_assumptions uu____1693))
in (FStar_List.append uu____1625 uu____1690)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let get_hint_for : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1781 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1781) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___377_1814 -> (match (uu___377_1814) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1822 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1825 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1843) -> begin
FStar_Pervasives_Native.None
end
| uu____1848 -> begin
(

let uu____1849 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1849) with
| (msg, error_labels) -> begin
(

let err = (

let uu____1862 = (FStar_List.map (fun uu____1890 -> (match (uu____1890) with
| (uu____1905, x, y) -> begin
((FStar_Errors.Error_Z3SolverError), (x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1862})
in FStar_Pervasives_Native.Some (err))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3r -> (

let uu____1922 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____1922) with
| true -> begin
(match (z3r.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1925) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1945 = (settings_to_info settings)
in (

let uu____1946 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask uu____1945 (filter_assertions settings.query_env settings.query_hint) settings.query_hash settings.query_all_labels uu____1946 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))))));
(

let uu____1996 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1996));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____2045 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err -> (match (err.error_messages) with
| [] -> begin
false
end
| uu____2076 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____2099 = (find_localized_errors errs)
in (FStar_Option.isSome uu____2099)))


let report_errors : query_settings  ->  unit = (fun settings -> ((

let uu____2109 = (find_localized_errors settings.query_errors)
in (match (uu____2109) with
| FStar_Pervasives_Native.Some (err) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____2119 = (

let uu____2121 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2121))
in (FStar_Errors.diag settings.query_range uu____2119)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____2126 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____2139 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2139)))))
in (FStar_All.pipe_right uu____2126 (FStar_String.concat "; ")))
in (

let uu____2147 = (

let uu____2157 = (

let uu____2165 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((FStar_Errors.Error_UnknownFatal_AssertionFailure), (uu____2165), (settings.query_range)))
in (uu____2157)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____2147)))
end));
(

let uu____2183 = ((FStar_Options.detail_errors ()) && (

let uu____2186 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____2186 (Prims.parse_int "1"))))
in (match (uu____2183) with
| true -> begin
(

let initial_fuel1 = (

let uu___378_2192 = settings
in (

let uu____2193 = (FStar_Options.initial_fuel ())
in (

let uu____2195 = (FStar_Options.initial_ifuel ())
in {query_env = uu___378_2192.query_env; query_decl = uu___378_2192.query_decl; query_name = uu___378_2192.query_name; query_index = uu___378_2192.query_index; query_range = uu___378_2192.query_range; query_fuel = uu____2193; query_ifuel = uu____2195; query_rlimit = uu___378_2192.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___378_2192.query_errors; query_all_labels = uu___378_2192.query_all_labels; query_suffix = uu___378_2192.query_suffix; query_hash = uu___378_2192.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____2214 = (settings_to_info settings)
in (

let uu____2215 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask uu____2214 (filter_facts_without_core settings.query_env) settings.query_hash settings.query_all_labels uu____2215 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))))));
(

let uu____2265 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____2265));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____2314 -> begin
()
end));
))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2327 = ((FStar_Options.hint_info ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____2327) with
| true -> begin
(

let uu____2330 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____2330) with
| (status_string, errs) -> begin
(

let uu____2346 = uu____2330
in (

let tag = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2357) -> begin
"succeeded"
end
| uu____2363 -> begin
(Prims.strcat "failed {reason-unknown=" (Prims.strcat status_string "}"))
end)
in (

let range = (

let uu____2368 = (

let uu____2370 = (FStar_Range.string_of_range settings.query_range)
in (

let uu____2372 = (

let uu____2374 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____2374 ")"))
in (Prims.strcat uu____2370 uu____2372)))
in (Prims.strcat "(" uu____2368))
in (

let used_hint_tag = (

let uu____2380 = (used_hint settings)
in (match (uu____2380) with
| true -> begin
" (with hint)"
end
| uu____2385 -> begin
""
end))
in (

let stats = (

let uu____2390 = (FStar_Options.print_z3_statistics ())
in (match (uu____2390) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____2424 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____2424 "}"))))
end
| uu____2429 -> begin
""
end))
in ((

let uu____2433 = (

let uu____2437 = (

let uu____2441 = (

let uu____2445 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____2447 = (

let uu____2451 = (

let uu____2455 = (

let uu____2459 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____2461 = (

let uu____2465 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____2467 = (

let uu____2471 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____2473 = (

let uu____2477 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____2477)::(stats)::[])
in (uu____2471)::uu____2473))
in (uu____2465)::uu____2467))
in (uu____2459)::uu____2461))
in (used_hint_tag)::uu____2455)
in (tag)::uu____2451)
in (uu____2445)::uu____2447))
in (settings.query_name)::uu____2441)
in (range)::uu____2437)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____2433));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____2512 -> (match (uu____2512) with
| (uu____2520, msg, range1) -> begin
(

let tag1 = (

let uu____2527 = (used_hint settings)
in (match (uu____2527) with
| true -> begin
"(Hint-replay failed): "
end
| uu____2532 -> begin
""
end))
in (FStar_Errors.log_issue range1 ((FStar_Errors.Warning_HitReplayFailed), ((Prims.strcat tag1 msg)))))
end))));
))))))
end))
end
| uu____2536 -> begin
()
end)))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2549 = (

let uu____2551 = (FStar_Options.record_hints ())
in (not (uu____2551)))
in (match (uu____2549) with
| true -> begin
()
end
| uu____2554 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core1, proof) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____2580 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____2588 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____2588) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____2644 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None, uu____2648) -> begin
(

let uu____2652 = (

let uu____2653 = (get_hint_for settings.query_name settings.query_index)
in (FStar_Option.get uu____2653))
in (store_hint uu____2652))
end
| FStar_SMTEncoding_Z3.UNSAT (unsat_core, uu____2657) -> begin
(

let uu____2658 = (used_hint settings)
in (match (uu____2658) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____2661 -> begin
(store_hint (mk_hint unsat_core))
end))
end
| uu____2663 -> begin
()
end)))
end)))


let process_result : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings result -> ((

let uu____2680 = ((used_hint settings) && (

let uu____2683 = (FStar_Options.z3_refresh ())
in (not (uu____2683))))
in (match (uu____2680) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2686 -> begin
()
end));
(

let errs = (query_errors settings result)
in ((query_info settings result);
(record_hint settings result);
(detail_hint_replay settings result);
errs;
));
))


let fold_queries : query_settings Prims.list  ->  (query_settings  ->  (FStar_SMTEncoding_Z3.z3result  ->  unit)  ->  unit)  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option)  ->  (errors Prims.list  ->  unit)  ->  unit = (fun qs ask1 f report1 -> (

let rec aux = (fun acc qs1 -> (match (qs1) with
| [] -> begin
(report1 acc)
end
| (q)::qs2 -> begin
(ask1 q (fun res -> (

let uu____2783 = (f q res)
in (match (uu____2783) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (errs) -> begin
(aux ((errs)::acc) qs2)
end))))
end))
in (aux [] qs)))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decls_t  ->  unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____2814 = (

let uu____2821 = (match (env.FStar_TypeChecker_Env.qtbl_name_and_index) with
| (uu____2834, FStar_Pervasives_Native.None) -> begin
(failwith "No query name set!")
end
| (uu____2860, FStar_Pervasives_Native.Some (q, n1)) -> begin
(

let uu____2883 = (FStar_Ident.text_of_lid q)
in ((uu____2883), (n1)))
end)
in (match (uu____2821) with
| (qname, index1) -> begin
(

let uu____2899 = uu____2821
in (

let rlimit = (

let uu____2908 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____2910 = (

let uu____2912 = (FStar_Options.z3_rlimit ())
in (uu____2912 * (Prims.parse_int "544656")))
in (uu____2908 * uu____2910)))
in (

let next_hint = (get_hint_for qname index1)
in (

let default_settings = (

let uu____2919 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2920 = (FStar_Options.initial_fuel ())
in (

let uu____2922 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____2919; query_fuel = uu____2920; query_ifuel = uu____2922; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2931; FStar_Util.hint_index = uu____2932; FStar_Util.fuel = uu____2933; FStar_Util.ifuel = uu____2934; FStar_Util.unsat_core = uu____2935; FStar_Util.query_elapsed_time = uu____2936; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint))))))
end))
in (match (uu____2814) with
| (default_settings, next_hint) -> begin
(

let uu____2959 = uu____2814
in (

let use_hints_setting = (match (next_hint) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2971; FStar_Util.hint_index = uu____2972; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____2976; FStar_Util.hash = h}) -> begin
((

let uu___379_2993 = default_settings
in {query_env = uu___379_2993.query_env; query_decl = uu___379_2993.query_decl; query_name = uu___379_2993.query_name; query_index = uu___379_2993.query_index; query_range = uu___379_2993.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___379_2993.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___379_2993.query_errors; query_all_labels = uu___379_2993.query_all_labels; query_suffix = uu___379_2993.query_suffix; query_hash = uu___379_2993.query_hash}))::[]
end
| uu____2997 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____3003 = (

let uu____3005 = (FStar_Options.max_ifuel ())
in (

let uu____3007 = (FStar_Options.initial_ifuel ())
in (uu____3005 > uu____3007)))
in (match (uu____3003) with
| true -> begin
(

let uu____3012 = (

let uu___380_3013 = default_settings
in (

let uu____3014 = (FStar_Options.max_ifuel ())
in {query_env = uu___380_3013.query_env; query_decl = uu___380_3013.query_decl; query_name = uu___380_3013.query_name; query_index = uu___380_3013.query_index; query_range = uu___380_3013.query_range; query_fuel = uu___380_3013.query_fuel; query_ifuel = uu____3014; query_rlimit = uu___380_3013.query_rlimit; query_hint = uu___380_3013.query_hint; query_errors = uu___380_3013.query_errors; query_all_labels = uu___380_3013.query_all_labels; query_suffix = uu___380_3013.query_suffix; query_hash = uu___380_3013.query_hash}))
in (uu____3012)::[])
end
| uu____3016 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____3021 = (

let uu____3023 = (

let uu____3025 = (FStar_Options.max_fuel ())
in (uu____3025 / (Prims.parse_int "2")))
in (

let uu____3028 = (FStar_Options.initial_fuel ())
in (uu____3023 > uu____3028)))
in (match (uu____3021) with
| true -> begin
(

let uu____3033 = (

let uu___381_3034 = default_settings
in (

let uu____3035 = (

let uu____3037 = (FStar_Options.max_fuel ())
in (uu____3037 / (Prims.parse_int "2")))
in (

let uu____3040 = (FStar_Options.max_ifuel ())
in {query_env = uu___381_3034.query_env; query_decl = uu___381_3034.query_decl; query_name = uu___381_3034.query_name; query_index = uu___381_3034.query_index; query_range = uu___381_3034.query_range; query_fuel = uu____3035; query_ifuel = uu____3040; query_rlimit = uu___381_3034.query_rlimit; query_hint = uu___381_3034.query_hint; query_errors = uu___381_3034.query_errors; query_all_labels = uu___381_3034.query_all_labels; query_suffix = uu___381_3034.query_suffix; query_hash = uu___381_3034.query_hash})))
in (uu____3033)::[])
end
| uu____3042 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____3047 = ((

let uu____3053 = (FStar_Options.max_fuel ())
in (

let uu____3055 = (FStar_Options.initial_fuel ())
in (uu____3053 > uu____3055))) && (

let uu____3059 = (FStar_Options.max_ifuel ())
in (

let uu____3061 = (FStar_Options.initial_ifuel ())
in (uu____3059 >= uu____3061))))
in (match (uu____3047) with
| true -> begin
(

let uu____3066 = (

let uu___382_3067 = default_settings
in (

let uu____3068 = (FStar_Options.max_fuel ())
in (

let uu____3070 = (FStar_Options.max_ifuel ())
in {query_env = uu___382_3067.query_env; query_decl = uu___382_3067.query_decl; query_name = uu___382_3067.query_name; query_index = uu___382_3067.query_index; query_range = uu___382_3067.query_range; query_fuel = uu____3068; query_ifuel = uu____3070; query_rlimit = uu___382_3067.query_rlimit; query_hint = uu___382_3067.query_hint; query_errors = uu___382_3067.query_errors; query_all_labels = uu___382_3067.query_all_labels; query_suffix = uu___382_3067.query_suffix; query_hash = uu___382_3067.query_hash})))
in (uu____3066)::[])
end
| uu____3072 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____3077 = (

let uu____3079 = (FStar_Options.min_fuel ())
in (

let uu____3081 = (FStar_Options.initial_fuel ())
in (uu____3079 < uu____3081)))
in (match (uu____3077) with
| true -> begin
(

let uu____3086 = (

let uu___383_3087 = default_settings
in (

let uu____3088 = (FStar_Options.min_fuel ())
in {query_env = uu___383_3087.query_env; query_decl = uu___383_3087.query_decl; query_name = uu___383_3087.query_name; query_index = uu___383_3087.query_index; query_range = uu___383_3087.query_range; query_fuel = uu____3088; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___383_3087.query_rlimit; query_hint = uu___383_3087.query_hint; query_errors = uu___383_3087.query_errors; query_all_labels = uu___383_3087.query_all_labels; query_suffix = uu___383_3087.query_suffix; query_hash = uu___383_3087.query_hash}))
in (uu____3086)::[])
end
| uu____3091 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config1 cb -> ((

let uu____3113 = ((used_hint config1) || (FStar_Options.z3_refresh ()))
in (match (uu____3113) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____3116 -> begin
()
end));
(

let uu____3118 = (settings_to_info config1)
in (

let uu____3119 = (with_fuel_and_diagnostics config1 [])
in (

let uu____3122 = (

let uu____3125 = (FStar_SMTEncoding_Z3.get_scope ())
in FStar_Pervasives_Native.Some (uu____3125))
in (FStar_SMTEncoding_Z3.ask uu____3118 (filter_assertions config1.query_env config1.query_hint) config1.query_hash config1.query_all_labels uu____3119 uu____3122 cb))));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___384_3148 = default_settings
in {query_env = uu___384_3148.query_env; query_decl = uu___384_3148.query_decl; query_name = uu___384_3148.query_name; query_index = uu___384_3148.query_index; query_range = uu___384_3148.query_range; query_fuel = uu___384_3148.query_fuel; query_ifuel = uu___384_3148.query_ifuel; query_rlimit = uu___384_3148.query_rlimit; query_hint = uu___384_3148.query_hint; query_errors = errs; query_all_labels = uu___384_3148.query_all_labels; query_suffix = uu___384_3148.query_suffix; query_hash = uu___384_3148.query_hash})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____3149 = (

let uu____3158 = (FStar_Options.admit_smt_queries ())
in (

let uu____3160 = (FStar_Options.admit_except ())
in ((uu____3158), (uu____3160))))
in (match (uu____3149) with
| (true, uu____3168) -> begin
()
end
| (false, FStar_Pervasives_Native.None) -> begin
(check_all_configs all_configs)
end
| (false, FStar_Pervasives_Native.Some (id1)) -> begin
(

let skip = (match ((FStar_Util.starts_with id1 "(")) with
| true -> begin
(

let full_query_id = (

let uu____3198 = (

let uu____3200 = (

let uu____3202 = (

let uu____3204 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.strcat uu____3204 ")"))
in (Prims.strcat ", " uu____3202))
in (Prims.strcat default_settings.query_name uu____3200))
in (Prims.strcat "(" uu____3198))
in (Prims.op_disEquality full_query_id id1))
end
| uu____3210 -> begin
(Prims.op_disEquality default_settings.query_name id1)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____3214 -> begin
()
end))
end)))))))))))
end));
))


let solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> ((

let uu____3244 = (

let uu____3246 = (

let uu____3248 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3248))
in (FStar_Util.format1 "Starting query at %s" uu____3246))
in (FStar_SMTEncoding_Encode.push uu____3244));
(

let uu____3251 = (FStar_Options.no_smt ())
in (match (uu____3251) with
| true -> begin
(

let uu____3254 = (

let uu____3264 = (

let uu____3272 = (

let uu____3274 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" uu____3274))
in ((FStar_Errors.Error_NoSMTButNeeded), (uu____3272), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____3264)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____3254))
end
| uu____3292 -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____3295 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____3295) with
| (prefix1, labels, qry, suffix) -> begin
(

let uu____3308 = uu____3295
in (

let pop1 = (fun uu____3322 -> (

let uu____3323 = (

let uu____3325 = (

let uu____3327 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3327))
in (FStar_Util.format1 "Ending query at %s" uu____3325))
in (FStar_SMTEncoding_Encode.pop uu____3323)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____3330); FStar_SMTEncoding_Term.freevars = uu____3331; FStar_SMTEncoding_Term.rng = uu____3332}; FStar_SMTEncoding_Term.assumption_caption = uu____3333; FStar_SMTEncoding_Term.assumption_name = uu____3334; FStar_SMTEncoding_Term.assumption_fact_ids = uu____3335}) -> begin
(pop1 ())
end
| uu____3352 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____3353) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____3355 -> begin
(failwith "Impossible")
end)))
end)))
end));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot; FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3363 = (

let uu____3370 = (FStar_Options.peek ())
in ((e), (g), (uu____3370)))
in (uu____3363)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____3386 -> ()); FStar_TypeChecker_Env.push = (fun uu____3388 -> ()); FStar_TypeChecker_Env.pop = (fun uu____3391 -> ()); FStar_TypeChecker_Env.snapshot = (fun uu____3394 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); FStar_TypeChecker_Env.rollback = (fun uu____3413 uu____3414 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____3429 uu____3430 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____3433 uu____3434 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3440 = (

let uu____3447 = (FStar_Options.peek ())
in ((e), (g), (uu____3447)))
in (uu____3440)::[])); FStar_TypeChecker_Env.solve = (fun uu____3463 uu____3464 uu____3465 -> ()); FStar_TypeChecker_Env.finish = (fun uu____3472 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____3474 -> ())}




