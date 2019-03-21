
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____13 'Auu____14 'Auu____15 . ('Auu____13, ('Auu____14 * 'Auu____15)) FStar_Util.either  ->  ('Auu____13, 'Auu____14) FStar_Util.either = (fun uu___376_32 -> (match (uu___376_32) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____47) -> begin
FStar_Util.Inr (r)
end))


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db : 'Auu____105 . Prims.string  ->  'Auu____105  ->  unit = (fun src_filename format_filename -> ((

let uu____119 = (FStar_Options.record_hints ())
in (match (uu____119) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____147 -> begin
()
end));
(

let uu____149 = (FStar_Options.use_hints ())
in (match (uu____149) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____156 = (FStar_Options.hint_file ())
in (match (uu____156) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____165 = (FStar_Util.read_hints val_filename)
in (match (uu____165) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____172 = (FStar_Options.hint_info ())
in (match (uu____172) with
| true -> begin
(

let uu____175 = (

let uu____177 = (FStar_Options.hint_file ())
in (match (uu____177) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____187 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____197 -> begin
"invalid; using potentially stale hints"
end) uu____175))
end
| uu____200 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____225 = (FStar_Options.hint_info ())
in (match (uu____225) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____229 -> begin
()
end))
end))))
end
| uu____231 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____242 = (FStar_Options.record_hints ())
in (match (uu____242) with
| true -> begin
(

let hints = (

let uu____246 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____246))
in (

let hints_db = (

let uu____273 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____273; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____279 = (FStar_Options.hint_file ())
in (match (uu____279) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____288 -> begin
()
end));
(FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None);
(FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None);
))


let with_hints_db : 'a . Prims.string  ->  (unit  ->  'a)  ->  'a = (fun fname f -> ((initialize_hints_db fname false);
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
| uu____398 -> begin
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun uu___377_406 -> (match (uu___377_406) with
| FStar_SMTEncoding_Term.Name (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____409 -> begin
false
end)))) || (

let uu____412 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____412)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (

let keep_decl = (fun uu___378_432 -> (match (uu___378_432) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(matches_fact_ids include_assumption_names a)
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
true;
)
end
| FStar_SMTEncoding_Term.Module (uu____447) -> begin
(failwith "Solver.fs::keep_decl should never have been called with a Module decl")
end
| uu____457 -> begin
true
end))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____474 = (FStar_All.pipe_right decls (FStar_List.filter keep_decl))
in (FStar_All.pipe_right uu____474 (fun decls1 -> (FStar_SMTEncoding_Term.Module (((name), (decls1))))::out)))
end
| uu____492 -> begin
(

let uu____493 = (keep_decl d)
in (match (uu____493) with
| true -> begin
(d)::out
end
| uu____496 -> begin
out
end))
end)) [] theory_rev)))
in pruned_theory))))


let rec filter_assertions_with_stats : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool * Prims.int * Prims.int) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____539 = (filter_using_facts_from e theory)
in ((uu____539), (false), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let theory_rev = (FStar_List.rev theory)
in (

let uu____554 = (

let uu____563 = (

let uu____574 = (

let uu____577 = (

let uu____578 = (

let uu____580 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____580))
in FStar_SMTEncoding_Term.Caption (uu____578))
in (uu____577)::[])
in ((uu____574), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (FStar_List.fold_left (fun uu____610 d -> (match (uu____610) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____671 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____689 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____704 = (FStar_All.pipe_right decls (filter_assertions_with_stats e (FStar_Pervasives_Native.Some (core1))))
in (FStar_All.pipe_right uu____704 (fun uu____762 -> (match (uu____762) with
| (decls1, uu____787, r, p) -> begin
(((FStar_SMTEncoding_Term.Module (((name), (decls1))))::theory1), ((n_retained + r)), ((n_pruned + p)))
end))))
end
| uu____807 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) uu____563 theory_rev))
in (match (uu____554) with
| (theory', n_retained, n_pruned) -> begin
(

let uu____830 = uu____554
in ((theory'), (true), (n_retained), (n_pruned)))
end)))
end))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun e core theory -> (

let uu____869 = (filter_assertions_with_stats e core theory)
in (match (uu____869) with
| (theory1, b, uu____888, uu____889) -> begin
((theory1), (b))
end)))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun e x -> (

let uu____918 = (filter_using_facts_from e x)
in ((uu____918), (false))))

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

let uu____1145 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____1147 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason uu____1145 uu____1147 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"with hint"
end
| uu____1156 -> begin
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


let settings_to_info : query_settings  ->  FStar_SMTEncoding_QIReport.query_info = (fun s -> {FStar_SMTEncoding_QIReport.query_info_name = s.query_name; FStar_SMTEncoding_QIReport.query_info_index = s.query_index; FStar_SMTEncoding_QIReport.query_info_range = s.query_range})


let with_fuel_and_diagnostics : query_settings  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decls_t = (fun settings label_assumptions -> (

let n1 = settings.query_fuel
in (

let i = settings.query_ifuel
in (

let rlimit = settings.query_rlimit
in (

let uu____1686 = (

let uu____1689 = (

let uu____1690 = (

let uu____1692 = (FStar_Util.string_of_int n1)
in (

let uu____1694 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1692 uu____1694)))
in FStar_SMTEncoding_Term.Caption (uu____1690))
in (

let uu____1697 = (

let uu____1700 = (

let uu____1701 = (

let uu____1709 = (

let uu____1710 = (

let uu____1715 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1720 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1715), (uu____1720))))
in (FStar_SMTEncoding_Util.mkEq uu____1710))
in ((uu____1709), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1701))
in (

let uu____1724 = (

let uu____1727 = (

let uu____1728 = (

let uu____1736 = (

let uu____1737 = (

let uu____1742 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1747 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1742), (uu____1747))))
in (FStar_SMTEncoding_Util.mkEq uu____1737))
in ((uu____1736), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1728))
in (uu____1727)::(settings.query_decl)::[])
in (uu____1700)::uu____1724))
in (uu____1689)::uu____1697))
in (

let uu____1751 = (

let uu____1754 = (

let uu____1757 = (

let uu____1760 = (

let uu____1761 = (

let uu____1768 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1768)))
in FStar_SMTEncoding_Term.SetOption (uu____1761))
in (uu____1760)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[])
in (

let uu____1773 = (

let uu____1776 = (

let uu____1779 = (FStar_Options.record_hints ())
in (match (uu____1779) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____1784 -> begin
[]
end))
in (

let uu____1786 = (

let uu____1789 = (

let uu____1792 = (FStar_Options.print_z3_statistics ())
in (match (uu____1792) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1797 -> begin
[]
end))
in (FStar_List.append uu____1789 settings.query_suffix))
in (FStar_List.append uu____1776 uu____1786)))
in (FStar_List.append uu____1757 uu____1773)))
in (FStar_List.append label_assumptions uu____1754))
in (FStar_List.append uu____1686 uu____1751)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let get_hint_for : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1829 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1829) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___379_1862 -> (match (uu___379_1862) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1870 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1873 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1891) -> begin
FStar_Pervasives_Native.None
end
| uu____1892 -> begin
(

let uu____1893 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1893) with
| (msg, error_labels) -> begin
(

let err = (

let uu____1906 = (FStar_List.map (fun uu____1934 -> (match (uu____1934) with
| (uu____1949, x, y) -> begin
((FStar_Errors.Error_Z3SolverError), (x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1906})
in FStar_Pervasives_Native.Some (err))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3r -> (

let uu____1966 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____1966) with
| true -> begin
(match (z3r.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1969) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1985 = (settings_to_info settings)
in (

let uu____1986 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask uu____1985 (filter_assertions settings.query_env settings.query_hint) settings.query_hash settings.query_all_labels uu____1986 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))))));
(

let uu____2036 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____2036));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____2085 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err -> (match (err.error_messages) with
| [] -> begin
false
end
| uu____2116 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____2139 = (find_localized_errors errs)
in (FStar_Option.isSome uu____2139)))


let report_errors : query_settings  ->  unit = (fun settings -> ((

let uu____2149 = (find_localized_errors settings.query_errors)
in (match (uu____2149) with
| FStar_Pervasives_Native.Some (err) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____2159 = (

let uu____2161 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2161))
in (FStar_Errors.diag settings.query_range uu____2159)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____2166 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____2179 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2179)))))
in (FStar_All.pipe_right uu____2166 (FStar_String.concat "; ")))
in (

let uu____2187 = (

let uu____2197 = (

let uu____2205 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((FStar_Errors.Error_UnknownFatal_AssertionFailure), (uu____2205), (settings.query_range)))
in (uu____2197)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____2187)))
end));
(

let uu____2223 = ((FStar_Options.detail_errors ()) && (

let uu____2226 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____2226 (Prims.parse_int "1"))))
in (match (uu____2223) with
| true -> begin
(

let initial_fuel1 = (

let uu___380_2232 = settings
in (

let uu____2233 = (FStar_Options.initial_fuel ())
in (

let uu____2235 = (FStar_Options.initial_ifuel ())
in {query_env = uu___380_2232.query_env; query_decl = uu___380_2232.query_decl; query_name = uu___380_2232.query_name; query_index = uu___380_2232.query_index; query_range = uu___380_2232.query_range; query_fuel = uu____2233; query_ifuel = uu____2235; query_rlimit = uu___380_2232.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___380_2232.query_errors; query_all_labels = uu___380_2232.query_all_labels; query_suffix = uu___380_2232.query_suffix; query_hash = uu___380_2232.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____2254 = (settings_to_info settings)
in (

let uu____2255 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask uu____2254 (filter_facts_without_core settings.query_env) settings.query_hash settings.query_all_labels uu____2255 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))))));
(

let uu____2305 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____2305));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____2354 -> begin
()
end));
))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2367 = ((FStar_Options.hint_info ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____2367) with
| true -> begin
(

let uu____2370 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____2370) with
| (status_string, errs) -> begin
(

let uu____2386 = uu____2370
in (

let tag = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2397) -> begin
"succeeded"
end
| uu____2399 -> begin
(Prims.strcat "failed {reason-unknown=" (Prims.strcat status_string "}"))
end)
in (

let range = (

let uu____2404 = (

let uu____2406 = (FStar_Range.string_of_range settings.query_range)
in (

let uu____2408 = (

let uu____2410 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____2410 ")"))
in (Prims.strcat uu____2406 uu____2408)))
in (Prims.strcat "(" uu____2404))
in (

let used_hint_tag = (

let uu____2416 = (used_hint settings)
in (match (uu____2416) with
| true -> begin
" (with hint)"
end
| uu____2421 -> begin
""
end))
in (

let stats = (

let uu____2426 = (FStar_Options.print_z3_statistics ())
in (match (uu____2426) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____2460 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____2460 "}"))))
end
| uu____2465 -> begin
""
end))
in ((

let uu____2469 = (

let uu____2473 = (

let uu____2477 = (

let uu____2481 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____2483 = (

let uu____2487 = (

let uu____2491 = (

let uu____2495 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____2497 = (

let uu____2501 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____2503 = (

let uu____2507 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____2509 = (

let uu____2513 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____2513)::(stats)::[])
in (uu____2507)::uu____2509))
in (uu____2501)::uu____2503))
in (uu____2495)::uu____2497))
in (used_hint_tag)::uu____2491)
in (tag)::uu____2487)
in (uu____2481)::uu____2483))
in (settings.query_name)::uu____2477)
in (range)::uu____2473)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____2469));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____2548 -> (match (uu____2548) with
| (uu____2556, msg, range1) -> begin
(

let tag1 = (

let uu____2563 = (used_hint settings)
in (match (uu____2563) with
| true -> begin
"(Hint-replay failed): "
end
| uu____2568 -> begin
""
end))
in (FStar_Errors.log_issue range1 ((FStar_Errors.Warning_HitReplayFailed), ((Prims.strcat tag1 msg)))))
end))));
))))))
end))
end
| uu____2572 -> begin
()
end)))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2585 = (

let uu____2587 = (FStar_Options.record_hints ())
in (not (uu____2587)))
in (match (uu____2585) with
| true -> begin
()
end
| uu____2590 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2613) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____2614 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____2622 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____2622) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____2678 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) -> begin
(

let uu____2685 = (

let uu____2686 = (get_hint_for settings.query_name settings.query_index)
in (FStar_Option.get uu____2686))
in (store_hint uu____2685))
end
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(

let uu____2690 = (used_hint settings)
in (match (uu____2690) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____2693 -> begin
(store_hint (mk_hint unsat_core))
end))
end
| uu____2695 -> begin
()
end)))
end)))


let process_result : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings result -> ((

let uu____2712 = ((used_hint settings) && (

let uu____2715 = (FStar_Options.z3_refresh ())
in (not (uu____2715))))
in (match (uu____2712) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2718 -> begin
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

let uu____2815 = (f q res)
in (match (uu____2815) with
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

let uu____2846 = (

let uu____2853 = (match (env.FStar_TypeChecker_Env.qtbl_name_and_index) with
| (uu____2866, FStar_Pervasives_Native.None) -> begin
(failwith "No query name set!")
end
| (uu____2892, FStar_Pervasives_Native.Some (q, n1)) -> begin
(

let uu____2915 = (FStar_Ident.text_of_lid q)
in ((uu____2915), (n1)))
end)
in (match (uu____2853) with
| (qname, index1) -> begin
(

let uu____2931 = uu____2853
in (

let rlimit = (

let uu____2940 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____2942 = (

let uu____2944 = (FStar_Options.z3_rlimit ())
in (uu____2944 * (Prims.parse_int "544656")))
in (uu____2940 * uu____2942)))
in (

let next_hint = (get_hint_for qname index1)
in (

let default_settings = (

let uu____2951 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2952 = (FStar_Options.initial_fuel ())
in (

let uu____2954 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____2951; query_fuel = uu____2952; query_ifuel = uu____2954; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2963; FStar_Util.hint_index = uu____2964; FStar_Util.fuel = uu____2965; FStar_Util.ifuel = uu____2966; FStar_Util.unsat_core = uu____2967; FStar_Util.query_elapsed_time = uu____2968; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint))))))
end))
in (match (uu____2846) with
| (default_settings, next_hint) -> begin
(

let uu____2991 = uu____2846
in (

let use_hints_setting = (match (next_hint) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____3003; FStar_Util.hint_index = uu____3004; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____3008; FStar_Util.hash = h}) -> begin
((

let uu___381_3025 = default_settings
in {query_env = uu___381_3025.query_env; query_decl = uu___381_3025.query_decl; query_name = uu___381_3025.query_name; query_index = uu___381_3025.query_index; query_range = uu___381_3025.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___381_3025.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___381_3025.query_errors; query_all_labels = uu___381_3025.query_all_labels; query_suffix = uu___381_3025.query_suffix; query_hash = uu___381_3025.query_hash}))::[]
end
| uu____3029 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____3035 = (

let uu____3037 = (FStar_Options.max_ifuel ())
in (

let uu____3039 = (FStar_Options.initial_ifuel ())
in (uu____3037 > uu____3039)))
in (match (uu____3035) with
| true -> begin
(

let uu____3044 = (

let uu___382_3045 = default_settings
in (

let uu____3046 = (FStar_Options.max_ifuel ())
in {query_env = uu___382_3045.query_env; query_decl = uu___382_3045.query_decl; query_name = uu___382_3045.query_name; query_index = uu___382_3045.query_index; query_range = uu___382_3045.query_range; query_fuel = uu___382_3045.query_fuel; query_ifuel = uu____3046; query_rlimit = uu___382_3045.query_rlimit; query_hint = uu___382_3045.query_hint; query_errors = uu___382_3045.query_errors; query_all_labels = uu___382_3045.query_all_labels; query_suffix = uu___382_3045.query_suffix; query_hash = uu___382_3045.query_hash}))
in (uu____3044)::[])
end
| uu____3048 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____3053 = (

let uu____3055 = (

let uu____3057 = (FStar_Options.max_fuel ())
in (uu____3057 / (Prims.parse_int "2")))
in (

let uu____3060 = (FStar_Options.initial_fuel ())
in (uu____3055 > uu____3060)))
in (match (uu____3053) with
| true -> begin
(

let uu____3065 = (

let uu___383_3066 = default_settings
in (

let uu____3067 = (

let uu____3069 = (FStar_Options.max_fuel ())
in (uu____3069 / (Prims.parse_int "2")))
in (

let uu____3072 = (FStar_Options.max_ifuel ())
in {query_env = uu___383_3066.query_env; query_decl = uu___383_3066.query_decl; query_name = uu___383_3066.query_name; query_index = uu___383_3066.query_index; query_range = uu___383_3066.query_range; query_fuel = uu____3067; query_ifuel = uu____3072; query_rlimit = uu___383_3066.query_rlimit; query_hint = uu___383_3066.query_hint; query_errors = uu___383_3066.query_errors; query_all_labels = uu___383_3066.query_all_labels; query_suffix = uu___383_3066.query_suffix; query_hash = uu___383_3066.query_hash})))
in (uu____3065)::[])
end
| uu____3074 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____3079 = ((

let uu____3085 = (FStar_Options.max_fuel ())
in (

let uu____3087 = (FStar_Options.initial_fuel ())
in (uu____3085 > uu____3087))) && (

let uu____3091 = (FStar_Options.max_ifuel ())
in (

let uu____3093 = (FStar_Options.initial_ifuel ())
in (uu____3091 >= uu____3093))))
in (match (uu____3079) with
| true -> begin
(

let uu____3098 = (

let uu___384_3099 = default_settings
in (

let uu____3100 = (FStar_Options.max_fuel ())
in (

let uu____3102 = (FStar_Options.max_ifuel ())
in {query_env = uu___384_3099.query_env; query_decl = uu___384_3099.query_decl; query_name = uu___384_3099.query_name; query_index = uu___384_3099.query_index; query_range = uu___384_3099.query_range; query_fuel = uu____3100; query_ifuel = uu____3102; query_rlimit = uu___384_3099.query_rlimit; query_hint = uu___384_3099.query_hint; query_errors = uu___384_3099.query_errors; query_all_labels = uu___384_3099.query_all_labels; query_suffix = uu___384_3099.query_suffix; query_hash = uu___384_3099.query_hash})))
in (uu____3098)::[])
end
| uu____3104 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____3109 = (

let uu____3111 = (FStar_Options.min_fuel ())
in (

let uu____3113 = (FStar_Options.initial_fuel ())
in (uu____3111 < uu____3113)))
in (match (uu____3109) with
| true -> begin
(

let uu____3118 = (

let uu___385_3119 = default_settings
in (

let uu____3120 = (FStar_Options.min_fuel ())
in {query_env = uu___385_3119.query_env; query_decl = uu___385_3119.query_decl; query_name = uu___385_3119.query_name; query_index = uu___385_3119.query_index; query_range = uu___385_3119.query_range; query_fuel = uu____3120; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___385_3119.query_rlimit; query_hint = uu___385_3119.query_hint; query_errors = uu___385_3119.query_errors; query_all_labels = uu___385_3119.query_all_labels; query_suffix = uu___385_3119.query_suffix; query_hash = uu___385_3119.query_hash}))
in (uu____3118)::[])
end
| uu____3123 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config1 cb -> ((

let uu____3145 = ((used_hint config1) || (FStar_Options.z3_refresh ()))
in (match (uu____3145) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____3148 -> begin
()
end));
(

let uu____3150 = (settings_to_info config1)
in (

let uu____3151 = (with_fuel_and_diagnostics config1 [])
in (

let uu____3154 = (

let uu____3157 = (FStar_SMTEncoding_Z3.get_scope ())
in FStar_Pervasives_Native.Some (uu____3157))
in (FStar_SMTEncoding_Z3.ask uu____3150 (filter_assertions config1.query_env config1.query_hint) config1.query_hash config1.query_all_labels uu____3151 uu____3154 cb))));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___386_3180 = default_settings
in {query_env = uu___386_3180.query_env; query_decl = uu___386_3180.query_decl; query_name = uu___386_3180.query_name; query_index = uu___386_3180.query_index; query_range = uu___386_3180.query_range; query_fuel = uu___386_3180.query_fuel; query_ifuel = uu___386_3180.query_ifuel; query_rlimit = uu___386_3180.query_rlimit; query_hint = uu___386_3180.query_hint; query_errors = errs; query_all_labels = uu___386_3180.query_all_labels; query_suffix = uu___386_3180.query_suffix; query_hash = uu___386_3180.query_hash})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____3181 = (

let uu____3190 = (FStar_Options.admit_smt_queries ())
in (

let uu____3192 = (FStar_Options.admit_except ())
in ((uu____3190), (uu____3192))))
in (match (uu____3181) with
| (true, uu____3200) -> begin
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

let uu____3230 = (

let uu____3232 = (

let uu____3234 = (

let uu____3236 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.strcat uu____3236 ")"))
in (Prims.strcat ", " uu____3234))
in (Prims.strcat default_settings.query_name uu____3232))
in (Prims.strcat "(" uu____3230))
in (Prims.op_disEquality full_query_id id1))
end
| uu____3242 -> begin
(Prims.op_disEquality default_settings.query_name id1)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____3246 -> begin
()
end))
end)))))))))))
end));
))


let solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> ((

let uu____3276 = (

let uu____3278 = (

let uu____3280 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3280))
in (FStar_Util.format1 "Starting query at %s" uu____3278))
in (FStar_SMTEncoding_Encode.push uu____3276));
(

let uu____3283 = (FStar_Options.no_smt ())
in (match (uu____3283) with
| true -> begin
(

let uu____3286 = (

let uu____3296 = (

let uu____3304 = (

let uu____3306 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" uu____3306))
in ((FStar_Errors.Error_NoSMTButNeeded), (uu____3304), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____3296)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____3286))
end
| uu____3324 -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____3327 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____3327) with
| (prefix1, labels, qry, suffix) -> begin
(

let uu____3340 = uu____3327
in (

let pop1 = (fun uu____3354 -> (

let uu____3355 = (

let uu____3357 = (

let uu____3359 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3359))
in (FStar_Util.format1 "Ending query at %s" uu____3357))
in (FStar_SMTEncoding_Encode.pop uu____3355)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____3362); FStar_SMTEncoding_Term.freevars = uu____3363; FStar_SMTEncoding_Term.rng = uu____3364}; FStar_SMTEncoding_Term.assumption_caption = uu____3365; FStar_SMTEncoding_Term.assumption_name = uu____3366; FStar_SMTEncoding_Term.assumption_fact_ids = uu____3367}) -> begin
(pop1 ())
end
| uu____3384 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____3385) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____3387 -> begin
(failwith "Impossible")
end)))
end)))
end));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot; FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3395 = (

let uu____3402 = (FStar_Options.peek ())
in ((e), (g), (uu____3402)))
in (uu____3395)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____3418 -> ()); FStar_TypeChecker_Env.push = (fun uu____3420 -> ()); FStar_TypeChecker_Env.pop = (fun uu____3423 -> ()); FStar_TypeChecker_Env.snapshot = (fun uu____3426 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); FStar_TypeChecker_Env.rollback = (fun uu____3445 uu____3446 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____3461 uu____3462 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____3465 uu____3466 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3472 = (

let uu____3479 = (FStar_Options.peek ())
in ((e), (g), (uu____3479)))
in (uu____3472)::[])); FStar_TypeChecker_Env.solve = (fun uu____3495 uu____3496 uu____3497 -> ()); FStar_TypeChecker_Env.finish = (fun uu____3504 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____3506 -> ())}




