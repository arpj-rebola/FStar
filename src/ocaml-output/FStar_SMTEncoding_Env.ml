
open Prims
open FStar_Pervasives
exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____9 -> begin
false
end))


let add_fuel : 'Auu____18 . 'Auu____18  ->  'Auu____18 Prims.list  ->  'Auu____18 Prims.list = (fun x tl1 -> (

let uu____35 = (FStar_Options.unthrottle_inductives ())
in (match (uu____35) with
| true -> begin
tl1
end
| uu____40 -> begin
(x)::tl1
end)))


let withenv : 'Auu____53 'Auu____54 'Auu____55 . 'Auu____53  ->  ('Auu____54 * 'Auu____55)  ->  ('Auu____54 * 'Auu____55 * 'Auu____53) = (fun c uu____75 -> (match (uu____75) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____91 'Auu____92 'Auu____93 . (('Auu____91, 'Auu____92) FStar_Util.either * 'Auu____93) Prims.list  ->  (('Auu____91, 'Auu____92) FStar_Util.either * 'Auu____93) Prims.list = (fun args -> (FStar_List.filter (fun uu___267_140 -> (match (uu___267_140) with
| (FStar_Util.Inl (uu____150), uu____151) -> begin
false
end
| uu____157 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let uu____190 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____190)))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____220 -> (

let uu____221 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____221)))
in (

let uu____225 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____225) with
| (uu____231, t) -> begin
(

let uu____233 = (

let uu____234 = (FStar_Syntax_Subst.compress t)
in uu____234.FStar_Syntax_Syntax.n)
in (match (uu____233) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____260 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____260) with
| (binders, uu____267) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____277 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____294 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____309 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____309)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____325 = (

let uu____331 = (mk_term_projector_name lid a)
in ((uu____331), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____325)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____347 = (

let uu____353 = (mk_term_projector_name_by_pos lid i)
in ((uu____353), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____347)))


let mk_data_tester : 'Auu____365 . 'Auu____365  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; snapshot : unit  ->  (Prims.int * unit); rollback : Prims.int FStar_Pervasives_Native.option  ->  unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
push1
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
pop1
end))


let __proj__Mkvarops_t__item__snapshot : varops_t  ->  unit  ->  (Prims.int * unit) = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
snapshot1
end))


let __proj__Mkvarops_t__item__rollback : varops_t  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
rollback1
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
fresh1
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
next_id1
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____1297 -> (

let uu____1298 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____1304 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____1298), (uu____1304)))))
in (

let scopes = (

let uu____1327 = (

let uu____1339 = (new_scope ())
in (uu____1339)::[])
in (FStar_Util.mk_ref uu____1327))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____1391 = (

let uu____1395 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1395 (fun uu____1483 -> (match (uu____1483) with
| (names1, uu____1497) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1391) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1511) -> begin
((FStar_Util.incr ctr);
(

let uu____1548 = (

let uu____1550 = (

let uu____1552 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1552))
in (Prims.strcat "__" uu____1550))
in (Prims.strcat y1 uu____1548));
)
end))
in (

let top_scope = (

let uu____1602 = (

let uu____1612 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1612))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1602))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1746 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1833 = (

let uu____1835 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1835))
in (FStar_Util.format2 "%s_%s" pfx uu____1833)))
in (

let string_const = (fun s -> (

let uu____1848 = (

let uu____1851 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1851 (fun uu____1938 -> (match (uu____1938) with
| (uu____1950, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1848) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____1966 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1966))
in (

let top_scope = (

let uu____1970 = (

let uu____1980 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1980))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1970))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____2086 -> (

let uu____2087 = (

let uu____2099 = (new_scope ())
in (

let uu____2109 = (FStar_ST.op_Bang scopes)
in (uu____2099)::uu____2109))
in (FStar_ST.op_Colon_Equals scopes uu____2087)))
in (

let pop1 = (fun uu____2261 -> (

let uu____2262 = (

let uu____2274 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____2274))
in (FStar_ST.op_Colon_Equals scopes uu____2262)))
in (

let snapshot1 = (fun uu____2431 -> (FStar_Common.snapshot push1 scopes ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 scopes depth))
in {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))))

type fvar_binding =
{fvar_lid : FStar_Ident.lident; smt_arity : Prims.int; smt_id : Prims.string; smt_token : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; smt_fuel_partial_app : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option}


let __proj__Mkfvar_binding__item__fvar_lid : fvar_binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app} -> begin
fvar_lid
end))


let __proj__Mkfvar_binding__item__smt_arity : fvar_binding  ->  Prims.int = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app} -> begin
smt_arity
end))


let __proj__Mkfvar_binding__item__smt_id : fvar_binding  ->  Prims.string = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app} -> begin
smt_id
end))


let __proj__Mkfvar_binding__item__smt_token : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app} -> begin
smt_token
end))


let __proj__Mkfvar_binding__item__smt_fuel_partial_app : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app} -> begin
smt_fuel_partial_app
end))


let binder_of_eithervar : 'Auu____2641 'Auu____2642 . 'Auu____2641  ->  ('Auu____2641 * 'Auu____2642 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

type cache_entry =
{cache_symbol_name : Prims.string; cache_symbol_arg_sorts : FStar_SMTEncoding_Term.sort Prims.list; cache_symbol_decls : FStar_SMTEncoding_Term.decl Prims.list; cache_symbol_assumption_names : Prims.string Prims.list}


let __proj__Mkcache_entry__item__cache_symbol_name : cache_entry  ->  Prims.string = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_name
end))


let __proj__Mkcache_entry__item__cache_symbol_arg_sorts : cache_entry  ->  FStar_SMTEncoding_Term.sort Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_arg_sorts
end))


let __proj__Mkcache_entry__item__cache_symbol_decls : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_decls
end))


let __proj__Mkcache_entry__item__cache_symbol_assumption_names : cache_entry  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = cache_symbol_name; cache_symbol_arg_sorts = cache_symbol_arg_sorts; cache_symbol_decls = cache_symbol_decls; cache_symbol_assumption_names = cache_symbol_assumption_names} -> begin
cache_symbol_assumption_names
end))

type env_t =
{bvar_bindings : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap; fvar_bindings : fvar_binding FStar_Util.psmap; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : cache_entry FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string; encoding_quantifier : Prims.bool}


let __proj__Mkenv_t__item__bvar_bindings : env_t  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
bvar_bindings
end))


let __proj__Mkenv_t__item__fvar_bindings : env_t  ->  fvar_binding FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
fvar_bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
warn
end))


let __proj__Mkenv_t__item__cache : env_t  ->  cache_entry FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
cache
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
current_module_name
end))


let __proj__Mkenv_t__item__encoding_quantifier : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; cache = cache; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier} -> begin
encoding_quantifier
end))


let mk_cache_entry : 'Auu____3291 . 'Auu____3291  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls1 -> (

let names1 = (FStar_All.pipe_right t_decls1 (FStar_List.collect (fun uu___268_3334 -> (match (uu___268_3334) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____3341 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls1; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let bvars = (FStar_Util.psmap_fold e.bvar_bindings (fun _k pi acc -> (FStar_Util.pimap_fold pi (fun _i uu____3401 acc1 -> (match (uu____3401) with
| (x, _term) -> begin
(

let uu____3416 = (FStar_Syntax_Print.bv_to_string x)
in (uu____3416)::acc1)
end)) acc)) [])
in (

let allvars = (FStar_Util.psmap_fold e.fvar_bindings (fun _k fvb acc -> (fvb.fvar_lid)::acc) [])
in (

let last_fvar = (match ((FStar_List.rev allvars)) with
| [] -> begin
""
end
| (l)::uu____3439 -> begin
(

let uu____3442 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "...," uu____3442))
end)
in (FStar_String.concat ", " ((last_fvar)::bvars))))))


let lookup_bvar_binding : env_t  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.option = (fun env bv -> (

let uu____3464 = (FStar_Util.psmap_try_find env.bvar_bindings bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____3464) with
| FStar_Pervasives_Native.Some (bvs) -> begin
(FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let lookup_fvar_binding : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str))


let add_bvar_binding : 'Auu____3532 . (FStar_Syntax_Syntax.bv * 'Auu____3532)  ->  (FStar_Syntax_Syntax.bv * 'Auu____3532) FStar_Util.pimap FStar_Util.psmap  ->  (FStar_Syntax_Syntax.bv * 'Auu____3532) FStar_Util.pimap FStar_Util.psmap = (fun bvb bvbs -> (FStar_Util.psmap_modify bvbs (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname.FStar_Ident.idText (fun pimap_opt -> (

let uu____3592 = (

let uu____3599 = (FStar_Util.pimap_empty ())
in (FStar_Util.dflt uu____3599 pimap_opt))
in (FStar_Util.pimap_add uu____3592 (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)))))


let add_fvar_binding : fvar_binding  ->  fvar_binding FStar_Util.psmap  ->  fvar_binding FStar_Util.psmap = (fun fvb fvbs -> (FStar_Util.psmap_add fvbs fvb.fvar_lid.FStar_Ident.str fvb))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____3657 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____3657)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____3683 = (

let uu___269_3684 = env
in (

let uu____3685 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3685; fvar_bindings = uu___269_3684.fvar_bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___269_3684.tcenv; warn = uu___269_3684.warn; cache = uu___269_3684.cache; nolabels = uu___269_3684.nolabels; use_zfuel_name = uu___269_3684.use_zfuel_name; encode_non_total_function_typ = uu___269_3684.encode_non_total_function_typ; current_module_name = uu___269_3684.current_module_name; encoding_quantifier = uu___269_3684.encoding_quantifier}))
in ((ysym), (y), (uu____3683))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3720 = (

let uu___270_3721 = env
in (

let uu____3722 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3722; fvar_bindings = uu___270_3721.fvar_bindings; depth = uu___270_3721.depth; tcenv = uu___270_3721.tcenv; warn = uu___270_3721.warn; cache = uu___270_3721.cache; nolabels = uu___270_3721.nolabels; use_zfuel_name = uu___270_3721.use_zfuel_name; encode_non_total_function_typ = uu___270_3721.encode_non_total_function_typ; current_module_name = uu___270_3721.current_module_name; encoding_quantifier = uu___270_3721.encoding_quantifier}))
in ((ysym), (y), (uu____3720))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3763 = (

let uu___271_3764 = env
in (

let uu____3765 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3765; fvar_bindings = uu___271_3764.fvar_bindings; depth = uu___271_3764.depth; tcenv = uu___271_3764.tcenv; warn = uu___271_3764.warn; cache = uu___271_3764.cache; nolabels = uu___271_3764.nolabels; use_zfuel_name = uu___271_3764.use_zfuel_name; encode_non_total_function_typ = uu___271_3764.encode_non_total_function_typ; current_module_name = uu___271_3764.current_module_name; encoding_quantifier = uu___271_3764.encoding_quantifier}))
in ((ysym), (y), (uu____3763))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___272_3791 = env
in (

let uu____3792 = (add_bvar_binding ((x), (t)) env.bvar_bindings)
in {bvar_bindings = uu____3792; fvar_bindings = uu___272_3791.fvar_bindings; depth = uu___272_3791.depth; tcenv = uu___272_3791.tcenv; warn = uu___272_3791.warn; cache = uu___272_3791.cache; nolabels = uu___272_3791.nolabels; use_zfuel_name = uu___272_3791.use_zfuel_name; encode_non_total_function_typ = uu___272_3791.encode_non_total_function_typ; current_module_name = uu___272_3791.current_module_name; encoding_quantifier = uu___272_3791.encoding_quantifier})))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3812 = (lookup_bvar_binding env a)
in (match (uu____3812) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3823 = (lookup_bvar_binding env a)
in (match (uu____3823) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3834 = (

let uu____3836 = (FStar_Syntax_Print.bv_to_string a)
in (

let uu____3838 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found  %s in environment: %s" uu____3836 uu____3838)))
in (failwith uu____3834))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app -> {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app})


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let fname = (varops.new_fvar x)
in (

let ftok_name = (Prims.strcat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in (

let fvb = (mk_fvb x fname arity (FStar_Pervasives_Native.Some (ftok)) FStar_Pervasives_Native.None)
in (

let uu____3927 = (

let uu___273_3928 = env
in (

let uu____3929 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___273_3928.bvar_bindings; fvar_bindings = uu____3929; depth = uu___273_3928.depth; tcenv = uu___273_3928.tcenv; warn = uu___273_3928.warn; cache = uu___273_3928.cache; nolabels = uu___273_3928.nolabels; use_zfuel_name = uu___273_3928.use_zfuel_name; encode_non_total_function_typ = uu___273_3928.encode_non_total_function_typ; current_module_name = uu___273_3928.current_module_name; encoding_quantifier = uu___273_3928.encoding_quantifier}))
in ((fname), (ftok_name), (uu____3927))))))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

let uu____3945 = (lookup_fvar_binding env a)
in (match (uu____3945) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3948 = (

let uu____3950 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____3950))
in (failwith uu____3948))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None)
in (

let uu___274_3989 = env
in (

let uu____3990 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___274_3989.bvar_bindings; fvar_bindings = uu____3990; depth = uu___274_3989.depth; tcenv = uu___274_3989.tcenv; warn = uu___274_3989.warn; cache = uu___274_3989.cache; nolabels = uu___274_3989.nolabels; use_zfuel_name = uu___274_3989.use_zfuel_name; encode_non_total_function_typ = uu___274_3989.encode_non_total_function_typ; current_module_name = uu___274_3989.current_module_name; encoding_quantifier = uu___274_3989.encoding_quantifier}))))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____4013 = (

let uu____4021 = (

let uu____4024 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____4024)::[])
in ((f), (uu____4021)))
in (FStar_SMTEncoding_Util.mkApp uu____4013))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)))
in (

let uu___275_4033 = env
in (

let uu____4034 = (add_fvar_binding fvb1 env.fvar_bindings)
in {bvar_bindings = uu___275_4033.bvar_bindings; fvar_bindings = uu____4034; depth = uu___275_4033.depth; tcenv = uu___275_4033.tcenv; warn = uu___275_4033.warn; cache = uu___275_4033.cache; nolabels = uu___275_4033.nolabels; use_zfuel_name = uu___275_4033.use_zfuel_name; encode_non_total_function_typ = uu___275_4033.encode_non_total_function_typ; current_module_name = uu___275_4033.current_module_name; encoding_quantifier = uu___275_4033.encoding_quantifier}))))))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____4050 = (lookup_fvar_binding env l)
in (match (uu____4050) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____4059 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____4067, (fuel)::[]) -> begin
(

let uu____4071 = (

let uu____4073 = (

let uu____4075 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____4075 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____4073 "fuel"))
in (match (uu____4071) with
| true -> begin
(

let uu____4092 = (

let uu____4093 = (FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____4093 fuel))
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____4092))
end
| uu____4097 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____4099 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____4100 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____4118 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____4118) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4122 = (

let uu____4124 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____4124))
in (failwith uu____4122))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (Prims.string * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in ((fvb.smt_id), (fvb.smt_arity))))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____4187; FStar_SMTEncoding_Term.rng = uu____4188}) when env.use_zfuel_name -> begin
((g), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4206 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4239 -> begin
((FStar_SMTEncoding_Term.Var (fvb.smt_id)), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.psmap_find_map env.fvar_bindings (fun uu____4260 fvb -> (match ((Prims.op_Equality fvb.smt_id nm)) with
| true -> begin
fvb.smt_token
end
| uu____4267 -> begin
FStar_Pervasives_Native.None
end))))




