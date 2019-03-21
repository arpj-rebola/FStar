
open Prims
open FStar_Pervasives

let test_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("Test")::[]) FStar_Range.dummyRange)


let tcenv_ref : FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let test_mod_ref : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = test_lid; FStar_Syntax_Syntax.declarations = []; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = false})))


let parse_mod : Prims.string  ->  FStar_Syntax_DsEnv.env  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.modul) = (fun mod_name1 dsenv1 -> (

let uu____58 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (mod_name1)))
in (match (uu____58) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (m), uu____64) -> begin
(

let uu____81 = (

let uu____86 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul m)
in (uu____86 dsenv1))
in (match (uu____81) with
| (m1, env') -> begin
(

let uu____99 = (

let uu____105 = (FStar_Ident.lid_of_path (("Test")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_DsEnv.prepare_module_or_interface false false env' uu____105 FStar_Syntax_DsEnv.default_mii))
in (match (uu____99) with
| (env'1, uu____116) -> begin
((env'1), (m1))
end))
end))
end
| FStar_Parser_ParseIt.ParseError (err, msg, r) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (r)))))
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (uu____129), uu____130) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" mod_name1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleExpected), (msg)) FStar_Range.dummyRange))
end
| FStar_Parser_ParseIt.Term (uu____157) -> begin
(failwith "Impossible: parsing a Filename always results in an ASTFragment")
end)))


let add_mods : Prims.string Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env) = (fun mod_names dsenv1 env -> (FStar_List.fold_left (fun uu____204 mod_name1 -> (match (uu____204) with
| (dsenv2, env1) -> begin
(

let uu____217 = (parse_mod mod_name1 dsenv2)
in (match (uu____217) with
| (dsenv3, string_mod) -> begin
(

let uu____228 = (FStar_TypeChecker_Tc.check_module env1 string_mod false)
in (match (uu____228) with
| (_mod, env2) -> begin
((dsenv3), (env2))
end))
end))
end)) ((dsenv1), (env)) mod_names))


let init_once : unit  ->  unit = (fun uu____245 -> (

let solver1 = FStar_SMTEncoding_Solver.dummy
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid FStar_TypeChecker_NBE.normalize_for_unit_test)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let uu____249 = (

let uu____254 = (FStar_Options.prims ())
in (

let uu____256 = (FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps)
in (parse_mod uu____254 uu____256)))
in (match (uu____249) with
| (dsenv1, prims_mod) -> begin
(

let env1 = (

let uu___459_260 = env
in {FStar_TypeChecker_Env.solver = uu___459_260.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___459_260.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___459_260.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___459_260.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___459_260.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___459_260.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___459_260.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___459_260.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___459_260.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___459_260.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___459_260.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___459_260.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___459_260.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___459_260.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___459_260.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___459_260.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___459_260.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___459_260.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___459_260.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___459_260.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___459_260.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___459_260.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___459_260.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___459_260.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___459_260.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___459_260.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___459_260.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___459_260.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___459_260.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___459_260.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___459_260.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___459_260.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___459_260.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___459_260.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___459_260.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___459_260.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___459_260.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___459_260.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___459_260.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___459_260.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___459_260.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___459_260.FStar_TypeChecker_Env.nbe})
in (

let uu____261 = (FStar_TypeChecker_Tc.check_module env1 prims_mod false)
in (match (uu____261) with
| (_prims_mod, env2) -> begin
(

let env3 = (

let uu___460_270 = env2
in {FStar_TypeChecker_Env.solver = uu___460_270.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___460_270.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___460_270.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___460_270.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___460_270.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___460_270.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___460_270.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___460_270.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___460_270.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___460_270.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___460_270.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___460_270.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___460_270.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___460_270.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___460_270.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___460_270.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___460_270.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___460_270.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___460_270.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___460_270.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___460_270.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___460_270.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___460_270.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___460_270.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___460_270.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___460_270.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___460_270.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___460_270.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___460_270.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___460_270.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___460_270.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___460_270.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___460_270.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___460_270.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___460_270.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___460_270.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___460_270.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___460_270.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___460_270.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___460_270.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___460_270.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___460_270.FStar_TypeChecker_Env.nbe})
in (

let env4 = (FStar_TypeChecker_Env.set_current_module env3 test_lid)
in (FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (env4)))))
end)))
end));
))))


let rec init : unit  ->  FStar_TypeChecker_Env.env = (fun uu____300 -> (

let uu____301 = (FStar_ST.op_Bang tcenv_ref)
in (match (uu____301) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| uu____328 -> begin
((init_once ());
(init ());
)
end)))


let frag_of_text : Prims.string  ->  FStar_Parser_ParseIt.input_frag = (fun s -> {FStar_Parser_ParseIt.frag_text = s; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})


let pars : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_All.try_with (fun uu___462_354 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let uu____356 = (

let uu____357 = (FStar_All.pipe_left (fun _0_1 -> FStar_Parser_ParseIt.Fragment (_0_1)) (frag_of_text s))
in (FStar_Parser_ParseIt.parse uu____357))
in (match (uu____356) with
| FStar_Parser_ParseIt.Term (t) -> begin
(FStar_ToSyntax_ToSyntax.desugar_term tcenv.FStar_TypeChecker_Env.dsenv t)
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.ASTFragment (uu____365) -> begin
(failwith "Impossible: parsing a Fragment always results in a Term")
end)))
end)) (fun uu___461_379 -> if (

let uu____380 = (FStar_Options.trace_error ())
in (not (uu____380))) then begin
(Obj.magic ((Obj.repr (FStar_Exn.raise uu___461_379))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end)))


let tc' : Prims.string  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_TypeChecker_Env.env) = (fun s -> (

let tm = (pars s)
in (

let tcenv = (init ())
in (

let tcenv1 = (

let uu___463_399 = tcenv
in {FStar_TypeChecker_Env.solver = uu___463_399.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___463_399.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___463_399.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___463_399.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___463_399.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___463_399.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___463_399.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___463_399.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___463_399.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___463_399.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___463_399.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___463_399.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___463_399.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___463_399.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___463_399.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___463_399.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___463_399.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___463_399.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___463_399.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___463_399.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___463_399.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___463_399.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___463_399.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___463_399.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___463_399.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___463_399.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___463_399.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___463_399.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___463_399.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___463_399.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___463_399.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___463_399.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___463_399.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___463_399.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___463_399.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___463_399.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___463_399.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___463_399.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___463_399.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___463_399.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___463_399.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___463_399.FStar_TypeChecker_Env.nbe})
in (

let uu____401 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm)
in (match (uu____401) with
| (tm1, uu____415, g) -> begin
((tm1), (g), (tcenv1))
end))))))


let tc : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____425 = (tc' s)
in (match (uu____425) with
| (tm, uu____433, uu____434) -> begin
tm
end)))


let tc_nbe : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____443 = (tc' s)
in (match (uu____443) with
| (tm, g, tcenv) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard tcenv g);
tm;
)
end)))


let tc_nbe_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun tm -> (

let tcenv = (init ())
in (

let tcenv1 = (

let uu___464_462 = tcenv
in {FStar_TypeChecker_Env.solver = uu___464_462.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___464_462.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___464_462.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___464_462.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___464_462.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___464_462.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___464_462.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___464_462.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___464_462.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___464_462.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___464_462.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___464_462.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___464_462.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___464_462.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___464_462.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___464_462.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___464_462.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___464_462.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___464_462.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___464_462.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___464_462.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___464_462.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___464_462.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___464_462.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___464_462.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___464_462.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___464_462.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___464_462.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___464_462.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___464_462.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___464_462.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___464_462.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___464_462.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___464_462.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___464_462.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___464_462.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___464_462.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___464_462.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___464_462.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___464_462.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___464_462.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___464_462.FStar_TypeChecker_Env.nbe})
in (

let uu____464 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm)
in (match (uu____464) with
| (tm1, uu____472, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g);
tm1;
)
end)))))


let pars_and_tc_fragment : Prims.string  ->  unit = (fun s -> ((FStar_Options.set_option "trace_error" (FStar_Options.Bool (true)));
(

let report = (fun uu____491 -> (

let uu____492 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____492 (fun a1 -> ()))))
in (FStar_All.try_with (fun uu___466_500 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let frag = (frag_of_text s)
in (FStar_All.try_with (fun uu___468_512 -> (match (()) with
| () -> begin
(

let uu____513 = (

let uu____520 = (FStar_ST.op_Bang test_mod_ref)
in (FStar_Universal.tc_one_fragment uu____520 tcenv frag))
in (match (uu____513) with
| (test_mod', tcenv') -> begin
((FStar_ST.op_Colon_Equals test_mod_ref test_mod');
(FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (tcenv')));
(

let n1 = (FStar_Errors.get_err_count ())
in (match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
((report ());
(

let uu____606 = (

let uu____612 = (

let uu____614 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s errors were reported" uu____614))
in ((FStar_Errors.Fatal_ErrorsReported), (uu____612)))
in (FStar_Errors.raise_err uu____606));
)
end
| uu____618 -> begin
()
end));
)
end))
end)) (fun uu___467_622 -> ((report ());
(FStar_Errors.raise_err ((FStar_Errors.Fatal_TcOneFragmentFailed), ((Prims.strcat "tc_one_fragment failed: " s))));
)))))
end)) (fun uu___465_627 -> if (

let uu____628 = (FStar_Options.trace_error ())
in (not (uu____628))) then begin
(Obj.magic ((Obj.repr (FStar_Exn.raise uu___465_627))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end)));
))




