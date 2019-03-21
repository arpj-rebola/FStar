
open Prims
open FStar_Pervasives
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = mk1; is = is} -> begin
mk1
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = mk1; is = is} -> begin
is
end))


let prims : prims_t = (

let uu____136 = (FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____136) with
| (asym, a) -> begin
(

let uu____147 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____147) with
| (xsym, x) -> begin
(

let uu____158 = (FStar_SMTEncoding_Env.fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____158) with
| (ysym, y) -> begin
(

let quant = (fun vars body rng x1 -> (

let xname_decl = (

let uu____230 = (

let uu____242 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____242), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____230))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____273 = (

let uu____281 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____281)))
in (FStar_SMTEncoding_Util.mkApp uu____273))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars)
in (

let uu____297 = (

let uu____300 = (

let uu____303 = (

let uu____306 = (

let uu____307 = (

let uu____315 = (

let uu____316 = (

let uu____327 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____327)))
in (FStar_SMTEncoding_Term.mkForall rng uu____316))
in ((uu____315), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____307))
in (

let uu____339 = (

let uu____342 = (

let uu____343 = (

let uu____351 = (

let uu____352 = (

let uu____363 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____363)))
in (FStar_SMTEncoding_Term.mkForall rng uu____352))
in ((uu____351), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____343))
in (uu____342)::[])
in (uu____306)::uu____339))
in (xtok_decl)::uu____303)
in (xname_decl)::uu____300)
in ((xtok1), ((FStar_List.length vars)), (uu____297))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____482 = (

let uu____503 = (

let uu____522 = (

let uu____523 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____523))
in (quant axy uu____522))
in ((FStar_Parser_Const.op_Eq), (uu____503)))
in (

let uu____540 = (

let uu____563 = (

let uu____584 = (

let uu____603 = (

let uu____604 = (

let uu____605 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____605))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____604))
in (quant axy uu____603))
in ((FStar_Parser_Const.op_notEq), (uu____584)))
in (

let uu____622 = (

let uu____645 = (

let uu____666 = (

let uu____685 = (

let uu____686 = (

let uu____687 = (

let uu____692 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____693 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____692), (uu____693))))
in (FStar_SMTEncoding_Util.mkLT uu____687))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____686))
in (quant xy uu____685))
in ((FStar_Parser_Const.op_LT), (uu____666)))
in (

let uu____710 = (

let uu____733 = (

let uu____754 = (

let uu____773 = (

let uu____774 = (

let uu____775 = (

let uu____780 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____781 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____780), (uu____781))))
in (FStar_SMTEncoding_Util.mkLTE uu____775))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____774))
in (quant xy uu____773))
in ((FStar_Parser_Const.op_LTE), (uu____754)))
in (

let uu____798 = (

let uu____821 = (

let uu____842 = (

let uu____861 = (

let uu____862 = (

let uu____863 = (

let uu____868 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____869 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____868), (uu____869))))
in (FStar_SMTEncoding_Util.mkGT uu____863))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____862))
in (quant xy uu____861))
in ((FStar_Parser_Const.op_GT), (uu____842)))
in (

let uu____886 = (

let uu____909 = (

let uu____930 = (

let uu____949 = (

let uu____950 = (

let uu____951 = (

let uu____956 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____957 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____956), (uu____957))))
in (FStar_SMTEncoding_Util.mkGTE uu____951))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____950))
in (quant xy uu____949))
in ((FStar_Parser_Const.op_GTE), (uu____930)))
in (

let uu____974 = (

let uu____997 = (

let uu____1018 = (

let uu____1037 = (

let uu____1038 = (

let uu____1039 = (

let uu____1044 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1045 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1044), (uu____1045))))
in (FStar_SMTEncoding_Util.mkSub uu____1039))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1038))
in (quant xy uu____1037))
in ((FStar_Parser_Const.op_Subtraction), (uu____1018)))
in (

let uu____1062 = (

let uu____1085 = (

let uu____1106 = (

let uu____1125 = (

let uu____1126 = (

let uu____1127 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____1127))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1126))
in (quant qx uu____1125))
in ((FStar_Parser_Const.op_Minus), (uu____1106)))
in (

let uu____1144 = (

let uu____1167 = (

let uu____1188 = (

let uu____1207 = (

let uu____1208 = (

let uu____1209 = (

let uu____1214 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1215 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1214), (uu____1215))))
in (FStar_SMTEncoding_Util.mkAdd uu____1209))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1208))
in (quant xy uu____1207))
in ((FStar_Parser_Const.op_Addition), (uu____1188)))
in (

let uu____1232 = (

let uu____1255 = (

let uu____1276 = (

let uu____1295 = (

let uu____1296 = (

let uu____1297 = (

let uu____1302 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1303 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1302), (uu____1303))))
in (FStar_SMTEncoding_Util.mkMul uu____1297))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1296))
in (quant xy uu____1295))
in ((FStar_Parser_Const.op_Multiply), (uu____1276)))
in (

let uu____1320 = (

let uu____1343 = (

let uu____1364 = (

let uu____1383 = (

let uu____1384 = (

let uu____1385 = (

let uu____1390 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1391 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1390), (uu____1391))))
in (FStar_SMTEncoding_Util.mkDiv uu____1385))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1384))
in (quant xy uu____1383))
in ((FStar_Parser_Const.op_Division), (uu____1364)))
in (

let uu____1408 = (

let uu____1431 = (

let uu____1452 = (

let uu____1471 = (

let uu____1472 = (

let uu____1473 = (

let uu____1478 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1479 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1478), (uu____1479))))
in (FStar_SMTEncoding_Util.mkMod uu____1473))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1472))
in (quant xy uu____1471))
in ((FStar_Parser_Const.op_Modulus), (uu____1452)))
in (

let uu____1496 = (

let uu____1519 = (

let uu____1540 = (

let uu____1559 = (

let uu____1560 = (

let uu____1561 = (

let uu____1566 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1567 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1566), (uu____1567))))
in (FStar_SMTEncoding_Util.mkAnd uu____1561))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1560))
in (quant xy uu____1559))
in ((FStar_Parser_Const.op_And), (uu____1540)))
in (

let uu____1584 = (

let uu____1607 = (

let uu____1628 = (

let uu____1647 = (

let uu____1648 = (

let uu____1649 = (

let uu____1654 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1655 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1654), (uu____1655))))
in (FStar_SMTEncoding_Util.mkOr uu____1649))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1648))
in (quant xy uu____1647))
in ((FStar_Parser_Const.op_Or), (uu____1628)))
in (

let uu____1672 = (

let uu____1695 = (

let uu____1716 = (

let uu____1735 = (

let uu____1736 = (

let uu____1737 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____1737))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1736))
in (quant qx uu____1735))
in ((FStar_Parser_Const.op_Negation), (uu____1716)))
in (uu____1695)::[])
in (uu____1607)::uu____1672))
in (uu____1519)::uu____1584))
in (uu____1431)::uu____1496))
in (uu____1343)::uu____1408))
in (uu____1255)::uu____1320))
in (uu____1167)::uu____1232))
in (uu____1085)::uu____1144))
in (uu____997)::uu____1062))
in (uu____909)::uu____974))
in (uu____821)::uu____886))
in (uu____733)::uu____798))
in (uu____645)::uu____710))
in (uu____563)::uu____622))
in (uu____482)::uu____540))
in (

let mk1 = (fun l v1 -> (

let uu____2096 = (

let uu____2108 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____2198 -> (match (uu____2198) with
| (l', uu____2219) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____2108 (FStar_Option.map (fun uu____2318 -> (match (uu____2318) with
| (uu____2346, b) -> begin
(

let uu____2380 = (FStar_Ident.range_of_lid l)
in (b uu____2380 v1))
end)))))
in (FStar_All.pipe_right uu____2096 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____2463 -> (match (uu____2463) with
| (l', uu____2484) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_Range.range  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun rng env tapp vars -> (

let uu____2552 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____2552) with
| (xxsym, xx) -> begin
(

let uu____2563 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2563) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let uu____2579 = (

let uu____2587 = (

let uu____2588 = (

let uu____2599 = (

let uu____2600 = (

let uu____2605 = (

let uu____2606 = (

let uu____2611 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____2611)))
in (FStar_SMTEncoding_Util.mkEq uu____2606))
in ((xx_has_type), (uu____2605)))
in (FStar_SMTEncoding_Util.mkImp uu____2600))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____2599)))
in (FStar_SMTEncoding_Term.mkForall rng uu____2588))
in (

let uu____2636 = (

let uu____2638 = (

let uu____2640 = (

let uu____2642 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____2642))
in (Prims.strcat module_name uu____2640))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____2638))
in ((uu____2587), (FStar_Pervasives_Native.Some ("pretyping")), (uu____2636))))
in (FStar_SMTEncoding_Util.mkAssume uu____2579)))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let uu____2705 = (

let uu____2706 = (

let uu____2714 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____2714), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2706))
in (

let uu____2719 = (

let uu____2722 = (

let uu____2723 = (

let uu____2731 = (

let uu____2732 = (

let uu____2743 = (

let uu____2744 = (

let uu____2749 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____2749)))
in (FStar_SMTEncoding_Util.mkImp uu____2744))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2743)))
in (

let uu____2768 = (

let uu____2783 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2783))
in (uu____2768 uu____2732)))
in ((uu____2731), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2723))
in (uu____2722)::[])
in (uu____2705)::uu____2719))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____2816 = (

let uu____2817 = (

let uu____2825 = (

let uu____2826 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2827 = (

let uu____2838 = (

let uu____2843 = (

let uu____2846 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____2846)::[])
in (uu____2843)::[])
in (

let uu____2851 = (

let uu____2852 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____2852 tt))
in ((uu____2838), ((bb)::[]), (uu____2851))))
in (FStar_SMTEncoding_Term.mkForall uu____2826 uu____2827)))
in ((uu____2825), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2817))
in (

let uu____2871 = (

let uu____2874 = (

let uu____2875 = (

let uu____2883 = (

let uu____2884 = (

let uu____2895 = (

let uu____2896 = (

let uu____2901 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____2901)))
in (FStar_SMTEncoding_Util.mkImp uu____2896))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2895)))
in (

let uu____2922 = (

let uu____2937 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2937))
in (uu____2922 uu____2884)))
in ((uu____2883), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2875))
in (uu____2874)::[])
in (uu____2816)::uu____2871))))))
in (

let mk_int = (fun env nm tt -> (

let lex_t1 = (

let uu____2961 = (

let uu____2967 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____2967), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mkFreeV uu____2961))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes_y_x = (

let uu____2991 = (FStar_SMTEncoding_Util.mkApp (("Prims.precedes"), ((lex_t1)::(lex_t1)::(y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2991))
in (

let uu____2996 = (

let uu____2997 = (

let uu____3005 = (

let uu____3006 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3007 = (

let uu____3018 = (

let uu____3023 = (

let uu____3026 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____3026)::[])
in (uu____3023)::[])
in (

let uu____3031 = (

let uu____3032 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____3032 tt))
in ((uu____3018), ((bb)::[]), (uu____3031))))
in (FStar_SMTEncoding_Term.mkForall uu____3006 uu____3007)))
in ((uu____3005), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2997))
in (

let uu____3051 = (

let uu____3054 = (

let uu____3055 = (

let uu____3063 = (

let uu____3064 = (

let uu____3075 = (

let uu____3076 = (

let uu____3081 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____3081)))
in (FStar_SMTEncoding_Util.mkImp uu____3076))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____3075)))
in (

let uu____3102 = (

let uu____3117 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3117))
in (uu____3102 uu____3064)))
in ((uu____3063), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____3055))
in (

let uu____3122 = (

let uu____3125 = (

let uu____3126 = (

let uu____3134 = (

let uu____3135 = (

let uu____3146 = (

let uu____3147 = (

let uu____3152 = (

let uu____3153 = (

let uu____3156 = (

let uu____3159 = (

let uu____3162 = (

let uu____3163 = (

let uu____3168 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____3169 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____3168), (uu____3169))))
in (FStar_SMTEncoding_Util.mkGT uu____3163))
in (

let uu____3171 = (

let uu____3174 = (

let uu____3175 = (

let uu____3180 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____3181 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____3180), (uu____3181))))
in (FStar_SMTEncoding_Util.mkGTE uu____3175))
in (

let uu____3183 = (

let uu____3186 = (

let uu____3187 = (

let uu____3192 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____3193 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____3192), (uu____3193))))
in (FStar_SMTEncoding_Util.mkLT uu____3187))
in (uu____3186)::[])
in (uu____3174)::uu____3183))
in (uu____3162)::uu____3171))
in (typing_pred_y)::uu____3159)
in (typing_pred)::uu____3156)
in (FStar_SMTEncoding_Util.mk_and_l uu____3153))
in ((uu____3152), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____3147))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____3146)))
in (

let uu____3217 = (

let uu____3232 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3232))
in (uu____3217 uu____3135)))
in ((uu____3134), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____3126))
in (uu____3125)::[])
in (uu____3054)::uu____3122))
in (uu____2996)::uu____3051)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____3265 = (

let uu____3266 = (

let uu____3274 = (

let uu____3275 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3276 = (

let uu____3287 = (

let uu____3292 = (

let uu____3295 = (FStar_SMTEncoding_Term.boxString b)
in (uu____3295)::[])
in (uu____3292)::[])
in (

let uu____3300 = (

let uu____3301 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____3301 tt))
in ((uu____3287), ((bb)::[]), (uu____3300))))
in (FStar_SMTEncoding_Term.mkForall uu____3275 uu____3276)))
in ((uu____3274), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____3266))
in (

let uu____3320 = (

let uu____3323 = (

let uu____3324 = (

let uu____3332 = (

let uu____3333 = (

let uu____3344 = (

let uu____3345 = (

let uu____3350 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____3350)))
in (FStar_SMTEncoding_Util.mkImp uu____3345))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____3344)))
in (

let uu____3371 = (

let uu____3386 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3386))
in (uu____3371 uu____3333)))
in ((uu____3332), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____3324))
in (uu____3323)::[])
in (uu____3265)::uu____3320))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (

let uu____3414 = (FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp")))
in (uu____3414)::[])))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____3442 = (

let uu____3443 = (

let uu____3451 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____3451), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3443))
in (uu____3442)::[])))
in (

let mk_and_interp = (fun env conj uu____3472 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_and_a_b = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_and_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____3511 = (

let uu____3512 = (

let uu____3520 = (

let uu____3521 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3522 = (

let uu____3533 = (

let uu____3534 = (

let uu____3539 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____3539), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3534))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____3533)))
in (FStar_SMTEncoding_Term.mkForall uu____3521 uu____3522)))
in ((uu____3520), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3512))
in (uu____3511)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____3583 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_or_a_b = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_or_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____3622 = (

let uu____3623 = (

let uu____3631 = (

let uu____3632 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3633 = (

let uu____3644 = (

let uu____3645 = (

let uu____3650 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____3650), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3645))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____3644)))
in (FStar_SMTEncoding_Term.mkForall uu____3632 uu____3633)))
in ((uu____3631), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3623))
in (uu____3622)::[]))))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq2_x_y = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq2_x_y)::[])))
in (

let uu____3732 = (

let uu____3733 = (

let uu____3741 = (

let uu____3742 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3743 = (

let uu____3754 = (

let uu____3755 = (

let uu____3760 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____3760), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3755))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____3754)))
in (FStar_SMTEncoding_Term.mkForall uu____3742 uu____3743)))
in ((uu____3741), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3733))
in (uu____3732)::[]))))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq3_x_y = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq3_x_y)::[])))
in (

let uu____3856 = (

let uu____3857 = (

let uu____3865 = (

let uu____3866 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3867 = (

let uu____3878 = (

let uu____3879 = (

let uu____3884 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____3884), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3879))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____3878)))
in (FStar_SMTEncoding_Term.mkForall uu____3866 uu____3867)))
in ((uu____3865), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3857))
in (uu____3856)::[]))))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_imp_a_b = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_imp_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____3977 = (

let uu____3978 = (

let uu____3986 = (

let uu____3987 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3988 = (

let uu____3999 = (

let uu____4000 = (

let uu____4005 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____4005), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____4000))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____3999)))
in (FStar_SMTEncoding_Term.mkForall uu____3987 uu____3988)))
in ((uu____3986), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3978))
in (uu____3977)::[]))))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_iff_a_b = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_iff_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____4088 = (

let uu____4089 = (

let uu____4097 = (

let uu____4098 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4099 = (

let uu____4110 = (

let uu____4111 = (

let uu____4116 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____4116), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____4111))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____4110)))
in (FStar_SMTEncoding_Term.mkForall uu____4098 uu____4099)))
in ((uu____4097), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4089))
in (uu____4088)::[]))))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let l_not_a = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_not_a)::[])))
in (

let not_valid_a = (

let uu____4181 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4181))
in (

let uu____4186 = (

let uu____4187 = (

let uu____4195 = (

let uu____4196 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4197 = (

let uu____4208 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____4208)))
in (FStar_SMTEncoding_Term.mkForall uu____4196 uu____4197)))
in ((uu____4195), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4187))
in (uu____4186)::[])))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____4253 = (

let uu____4254 = (

let uu____4262 = (

let uu____4263 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____4263 range_ty))
in (

let uu____4264 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "typing_range_const")
in ((uu____4262), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____4264))))
in (FStar_SMTEncoding_Util.mkAssume uu____4254))
in (uu____4253)::[])))
in (

let mk_inversion_axiom = (fun env inversion tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let inversion_t = (FStar_SMTEncoding_Util.mkApp ((inversion), ((t)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((inversion_t)::[])))
in (

let body = (

let hastypeZ = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 t)
in (

let hastypeS = (

let uu____4318 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4318 x1 t))
in (

let uu____4320 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4321 = (

let uu____4332 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____4332)))
in (FStar_SMTEncoding_Term.mkForall uu____4320 uu____4321)))))
in (

let uu____4351 = (

let uu____4352 = (

let uu____4360 = (

let uu____4361 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4362 = (

let uu____4373 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____4373)))
in (FStar_SMTEncoding_Term.mkForall uu____4361 uu____4362)))
in ((uu____4360), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4352))
in (uu____4351)::[])))))))))
in (

let mk_with_type_axiom = (fun env with_type1 tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let ee = (("e"), (FStar_SMTEncoding_Term.Term_sort))
in (

let e = (FStar_SMTEncoding_Util.mkFreeV ee)
in (

let with_type_t_e = (FStar_SMTEncoding_Util.mkApp ((with_type1), ((t)::(e)::[])))
in (

let uu____4436 = (

let uu____4437 = (

let uu____4445 = (

let uu____4446 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4447 = (

let uu____4463 = (

let uu____4464 = (

let uu____4469 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____4470 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____4469), (uu____4470))))
in (FStar_SMTEncoding_Util.mkAnd uu____4464))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____4463)))
in (FStar_SMTEncoding_Term.mkForall' uu____4446 uu____4447)))
in ((uu____4445), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____4437))
in (uu____4436)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____4991 = (FStar_Util.find_opt (fun uu____5029 -> (match (uu____5029) with
| (l, uu____5045) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____4991) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____5088, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5149 = (FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env)
in (match (uu____5149) with
| (form, decls) -> begin
(

let uu____5158 = (

let uu____5161 = (FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str))))
in (uu____5161)::[])
in (FStar_List.append decls uu____5158))
end))))


let encode_free_var : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5218 = (((

let uu____5222 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.FStar_SMTEncoding_Env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____5222)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____5218) with
| true -> begin
(

let arg_sorts = (

let uu____5236 = (

let uu____5237 = (FStar_Syntax_Subst.compress t_norm)
in uu____5237.FStar_Syntax_Syntax.n)
in (match (uu____5236) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____5243) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____5281 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____5288 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____5290 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____5290) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____5330 -> begin
(

let uu____5332 = (prims.is lid)
in (match (uu____5332) with
| true -> begin
(

let vname = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar lid)
in (

let uu____5343 = (prims.mk lid vname)
in (match (uu____5343) with
| (tok, arity, definition) -> begin
(

let env1 = (FStar_SMTEncoding_Env.push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____5371 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____5377 = (

let uu____5396 = (FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp t_norm)
in (match (uu____5396) with
| (args, comp) -> begin
(

let comp1 = (

let uu____5424 = (FStar_TypeChecker_Env.is_reifiable_comp env.FStar_SMTEncoding_Env.tcenv comp)
in (match (uu____5424) with
| true -> begin
(

let uu____5429 = (FStar_TypeChecker_Env.reify_comp (

let uu___382_5432 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___382_5432.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___382_5432.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___382_5432.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___382_5432.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___382_5432.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___382_5432.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___382_5432.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___382_5432.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___382_5432.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___382_5432.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___382_5432.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___382_5432.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___382_5432.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___382_5432.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___382_5432.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___382_5432.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___382_5432.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___382_5432.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___382_5432.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___382_5432.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___382_5432.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___382_5432.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___382_5432.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___382_5432.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___382_5432.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___382_5432.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___382_5432.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___382_5432.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___382_5432.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___382_5432.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___382_5432.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___382_5432.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___382_5432.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___382_5432.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___382_5432.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___382_5432.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___382_5432.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___382_5432.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___382_5432.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___382_5432.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___382_5432.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___382_5432.FStar_TypeChecker_Env.nbe}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____5429))
end
| uu____5434 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____5455 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.FStar_SMTEncoding_Env.tcenv comp1)
in ((args), (uu____5455)))
end
| uu____5476 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____5377) with
| (formals, (pre_opt, res_t)) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____5536 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____5536) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____5570 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___372_5631 -> (match (uu___372_5631) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____5635 = (FStar_Util.prefix vars)
in (match (uu____5635) with
| (uu____5659, (xxsym, uu____5661)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____5685 = (

let uu____5686 = (

let uu____5694 = (

let uu____5695 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____5696 = (

let uu____5707 = (

let uu____5708 = (

let uu____5713 = (

let uu____5714 = (FStar_SMTEncoding_Term.mk_tester (FStar_SMTEncoding_Env.escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____5714))
in ((vapp), (uu____5713)))
in (FStar_SMTEncoding_Util.mkEq uu____5708))
in ((((vapp)::[])::[]), (vars), (uu____5707)))
in (FStar_SMTEncoding_Term.mkForall uu____5695 uu____5696)))
in ((uu____5694), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (FStar_SMTEncoding_Env.escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____5686))
in (uu____5685)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____5729 = (FStar_Util.prefix vars)
in (match (uu____5729) with
| (uu____5753, (xxsym, uu____5755)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (FStar_SMTEncoding_Env.mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____5787 = (

let uu____5788 = (

let uu____5796 = (

let uu____5797 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____5798 = (

let uu____5809 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____5809)))
in (FStar_SMTEncoding_Term.mkForall uu____5797 uu____5798)))
in ((uu____5796), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____5788))
in (uu____5787)::[])))))
end))
end
| uu____5822 -> begin
[]
end)))))
in (

let uu____5823 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____5823) with
| (vars, guards, env', decls1, uu____5850) -> begin
(

let uu____5863 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5876 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____5876), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____5880 = (FStar_SMTEncoding_EncodeTerm.encode_formula p env')
in (match (uu____5880) with
| (g, ds) -> begin
(

let uu____5893 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____5893), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____5863) with
| (guard, decls11) -> begin
(

let vtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____5910 = (

let uu____5918 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____5918)))
in (FStar_SMTEncoding_Util.mkApp uu____5910))
in (

let uu____5924 = (

let vname_decl = (

let uu____5932 = (

let uu____5944 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____5964 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____5944), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____5932))
in (

let uu____5975 = (

let env2 = (

let uu___383_5981 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___383_5981.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___383_5981.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___383_5981.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___383_5981.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___383_5981.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___383_5981.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___383_5981.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___383_5981.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___383_5981.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___383_5981.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let uu____5982 = (

let uu____5984 = (FStar_SMTEncoding_EncodeTerm.head_normal env2 tt)
in (not (uu____5984)))
in (match (uu____5982) with
| true -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____5991 -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____5975) with
| (tok_typing, decls2) -> begin
(

let uu____6001 = (match (formals) with
| [] -> begin
(

let tok_typing1 = (FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
in (

let uu____6025 = (

let uu____6026 = (

let uu____6029 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____6029))
in (FStar_SMTEncoding_Env.push_free_var env1 lid arity vname uu____6026))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____6025))))
end
| uu____6039 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_app_0 = (

let uu____6054 = (

let uu____6062 = (FStar_List.hd vars)
in (uu____6062)::[])
in (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm uu____6054))
in (

let name_tok_corr_formula = (fun pat -> (

let uu____6084 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6085 = (

let uu____6096 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((pat)::[])::[]), (vars), (uu____6096)))
in (FStar_SMTEncoding_Term.mkForall uu____6084 uu____6085))))
in (

let name_tok_corr = (

let uu____6106 = (

let uu____6114 = (name_tok_corr_formula vtok_app)
in ((uu____6114), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____6106))
in (

let tok_typing1 = (

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm ((ff)::[]))
in (

let vtok_app_r = (FStar_SMTEncoding_EncodeTerm.mk_Apply f ((((vtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let guarded_tok_typing = (

let uu____6153 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6154 = (

let uu____6165 = (

let uu____6166 = (

let uu____6171 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in (

let uu____6172 = (name_tok_corr_formula vapp)
in ((uu____6171), (uu____6172))))
in (FStar_SMTEncoding_Util.mkAnd uu____6166))
in ((((vtok_app_r)::[])::[]), ((ff)::[]), (uu____6165)))
in (FStar_SMTEncoding_Term.mkForall uu____6153 uu____6154)))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))))
end)
in (match (uu____6001) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end))
end)))
in (match (uu____5924) with
| (decls2, env2) -> begin
(

let uu____6223 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____6233 = (FStar_SMTEncoding_EncodeTerm.encode_term res_t1 env')
in (match (uu____6233) with
| (encoded_res_t, decls) -> begin
(

let uu____6248 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____6248), (decls)))
end)))
in (match (uu____6223) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____6265 = (

let uu____6273 = (

let uu____6274 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6275 = (

let uu____6286 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____6286)))
in (FStar_SMTEncoding_Term.mkForall uu____6274 uu____6275)))
in ((uu____6273), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____6265))
in (

let freshness = (

let uu____6302 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____6302) with
| true -> begin
(

let uu____6310 = (

let uu____6311 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6312 = (

let uu____6325 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____6343 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((vname), (uu____6325), (FStar_SMTEncoding_Term.Term_sort), (uu____6343))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____6311 uu____6312)))
in (

let uu____6349 = (

let uu____6352 = (

let uu____6353 = (FStar_Syntax_Syntax.range_of_fv fv)
in (pretype_axiom uu____6353 env2 vapp vars))
in (uu____6352)::[])
in (uu____6310)::uu____6349))
end
| uu____6354 -> begin
[]
end))
in (

let g = (

let uu____6359 = (

let uu____6362 = (

let uu____6365 = (

let uu____6368 = (

let uu____6371 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____6371)
in (FStar_List.append freshness uu____6368))
in (FStar_List.append decls3 uu____6365))
in (FStar_List.append decls2 uu____6362))
in (FStar_List.append decls11 uu____6359))
in ((g), (env2)))))
end))
end))))
end))
end))))
end)))
end)))
end))
end))))


let declare_top_level_let : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env x t t_norm -> (

let uu____6413 = (FStar_SMTEncoding_Env.lookup_fvar_binding env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6413) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6424 = (encode_free_var false env x t t_norm [])
in (match (uu____6424) with
| (decls, env1) -> begin
(

let fvb = (FStar_SMTEncoding_Env.lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env lid t quals -> (

let tt = (FStar_SMTEncoding_EncodeTerm.norm env t)
in (

let uu____6495 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____6495) with
| (decls, env1) -> begin
(

let uu____6514 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____6514) with
| true -> begin
(

let uu____6523 = (

let uu____6526 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____6526))
in ((uu____6523), (env1)))
end
| uu____6531 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____6586 lb -> (match (uu____6586) with
| (decls, env1) -> begin
(

let uu____6606 = (

let uu____6613 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____6613 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____6606) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____6646 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6646) with
| (hd1, args) -> begin
(

let uu____6690 = (

let uu____6691 = (FStar_Syntax_Util.un_uinst hd1)
in uu____6691.FStar_Syntax_Syntax.n)
in (match (uu____6690) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6697, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____6721 -> begin
false
end))
end))))

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____6732 -> begin
false
end))


let copy_env : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Env.env_t = (fun en -> (

let uu___384_6740 = en
in (

let uu____6741 = (FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___384_6740.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___384_6740.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___384_6740.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___384_6740.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___384_6740.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu____6741; FStar_SMTEncoding_Env.nolabels = uu___384_6740.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___384_6740.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___384_6740.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___384_6740.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___384_6740.FStar_SMTEncoding_Env.encoding_quantifier})))


let encode_top_level_let : FStar_SMTEncoding_Env.env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env uu____6773 quals -> (match (uu____6773) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____6880 = (FStar_Util.first_N nbinders formals)
in (match (uu____6880) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____6981 uu____6982 -> (match (((uu____6981), (uu____6982))) with
| ((formal, uu____7008), (binder, uu____7010)) -> begin
(

let uu____7031 = (

let uu____7038 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____7038)))
in FStar_Syntax_Syntax.NT (uu____7031))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____7052 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____7093 -> (match (uu____7093) with
| (x, i) -> begin
(

let uu____7112 = (

let uu___385_7113 = x
in (

let uu____7114 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___385_7113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___385_7113.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7114}))
in ((uu____7112), (i)))
end))))
in (FStar_All.pipe_right uu____7052 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____7138 = (

let uu____7143 = (FStar_Syntax_Subst.compress body)
in (

let uu____7144 = (

let uu____7145 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____7145))
in (FStar_Syntax_Syntax.extend_app_n uu____7143 uu____7144)))
in (uu____7138 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t e -> (

let tcenv = (

let uu___386_7201 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___386_7201.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___386_7201.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___386_7201.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___386_7201.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___386_7201.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___386_7201.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___386_7201.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___386_7201.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___386_7201.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___386_7201.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___386_7201.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___386_7201.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___386_7201.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___386_7201.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___386_7201.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___386_7201.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___386_7201.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___386_7201.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___386_7201.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___386_7201.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___386_7201.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___386_7201.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___386_7201.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___386_7201.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___386_7201.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___386_7201.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___386_7201.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___386_7201.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___386_7201.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___386_7201.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___386_7201.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___386_7201.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___386_7201.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___386_7201.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___386_7201.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___386_7201.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___386_7201.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___386_7201.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___386_7201.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___386_7201.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___386_7201.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___386_7201.FStar_TypeChecker_Env.nbe})
in (

let subst_comp1 = (fun formals actuals comp -> (

let subst1 = (FStar_List.map2 (fun uu____7273 uu____7274 -> (match (((uu____7273), (uu____7274))) with
| ((x, uu____7300), (b, uu____7302)) -> begin
(

let uu____7323 = (

let uu____7330 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____7330)))
in FStar_Syntax_Syntax.NT (uu____7323))
end)) formals actuals)
in (FStar_Syntax_Subst.subst_comp subst1 comp)))
in (

let rec arrow_formals_comp_norm = (fun norm1 t1 -> (

let t2 = (

let uu____7355 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7355))
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (formals, comp) -> begin
(FStar_Syntax_Subst.open_comp formals comp)
end
| FStar_Syntax_Syntax.Tm_refine (uu____7384) -> begin
(

let uu____7391 = (FStar_Syntax_Util.unrefine t2)
in (arrow_formals_comp_norm norm1 uu____7391))
end
| uu____7392 when (not (norm1)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::[]) tcenv t2)
in (arrow_formals_comp_norm true t_norm))
end
| uu____7395 -> begin
(

let uu____7396 = (FStar_Syntax_Syntax.mk_Total t2)
in (([]), (uu____7396)))
end)))
in (

let aux = (fun t1 e1 -> (

let uu____7438 = (FStar_Syntax_Util.abs_formals e1)
in (match (uu____7438) with
| (binders, body, lopt) -> begin
(

let uu____7470 = (match (binders) with
| [] -> begin
(arrow_formals_comp_norm true t1)
end
| uu____7486 -> begin
(arrow_formals_comp_norm false t1)
end)
in (match (uu____7470) with
| (formals, comp) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let uu____7520 = (match ((nformals < nbinders)) with
| true -> begin
(

let uu____7564 = (FStar_Util.first_N nformals binders)
in (match (uu____7564) with
| (bs0, rest) -> begin
(

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____7648 = (subst_comp1 formals bs0 comp)
in ((bs0), (body1), (uu____7648))))
end))
end
| uu____7659 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____7688 = (eta_expand1 binders formals body (FStar_Syntax_Util.comp_result comp))
in (match (uu____7688) with
| (binders1, body1) -> begin
(

let uu____7741 = (subst_comp1 formals binders1 comp)
in ((binders1), (body1), (uu____7741)))
end))
end
| uu____7752 -> begin
(

let uu____7754 = (subst_comp1 formals binders comp)
in ((binders), (body), (uu____7754)))
end)
end)
in (match (uu____7520) with
| (binders1, body1, comp1) -> begin
((binders1), (body1), (comp1))
end))))
end))
end)))
in (

let uu____7814 = (aux t e)
in (match (uu____7814) with
| (binders, body, comp) -> begin
(

let uu____7860 = (

let uu____7871 = (FStar_TypeChecker_Env.is_reifiable_comp tcenv comp)
in (match (uu____7871) with
| true -> begin
(

let comp1 = (FStar_TypeChecker_Env.reify_comp tcenv comp FStar_Syntax_Syntax.U_unknown)
in (

let body1 = (FStar_TypeChecker_Util.reify_body tcenv body)
in (

let uu____7886 = (aux comp1 body1)
in (match (uu____7886) with
| (more_binders, body2, comp2) -> begin
(((FStar_List.append binders more_binders)), (body2), (comp2))
end))))
end
| uu____7946 -> begin
((binders), (body), (comp))
end))
in (match (uu____7860) with
| (binders1, body1, comp1) -> begin
(

let uu____7969 = (FStar_Syntax_Util.ascribe body1 ((FStar_Util.Inl ((FStar_Syntax_Util.comp_result comp1))), (FStar_Pervasives_Native.None)))
in ((binders1), (uu____7969), (comp1)))
end))
end)))))))
in (FStar_All.try_with (fun uu___388_7996 -> (match (()) with
| () -> begin
(

let uu____8003 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____8003) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____8017 -> begin
(

let uu____8019 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____8082 lb -> (match (uu____8082) with
| (toks, typs, decls, env1) -> begin
((

let uu____8137 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____8137) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____8140 -> begin
()
end));
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____8143 = (

let uu____8152 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____8152 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____8143) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____8019) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let env_decls = (copy_env env1)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun rng curry fvb vars -> (

let mk_fv = (fun uu____8282 -> (match ((Prims.op_Equality fvb.FStar_SMTEncoding_Env.smt_arity (Prims.parse_int "0"))) with
| true -> begin
(FStar_SMTEncoding_Util.mkFreeV ((fvb.FStar_SMTEncoding_Env.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____8287 -> begin
(FStar_SMTEncoding_EncodeTerm.raise_arity_mismatch fvb.FStar_SMTEncoding_Env.smt_id fvb.FStar_SMTEncoding_Env.smt_arity (Prims.parse_int "0") rng)
end))
in (match (vars) with
| [] -> begin
(mk_fv ())
end
| uu____8295 -> begin
(match (curry) with
| true -> begin
(match (fvb.FStar_SMTEncoding_Env.smt_token) with
| FStar_Pervasives_Native.Some (ftok) -> begin
(FStar_SMTEncoding_EncodeTerm.mk_Apply ftok vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8305 = (mk_fv ())
in (FStar_SMTEncoding_EncodeTerm.mk_Apply uu____8305 vars))
end)
end
| uu____8306 -> begin
(

let uu____8308 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_app rng (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)) fvb.FStar_SMTEncoding_Env.smt_arity uu____8308))
end)
end)))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____8369; FStar_Syntax_Syntax.lbeff = uu____8370; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____8372; FStar_Syntax_Syntax.lbpos = uu____8373})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let uu____8397 = (

let uu____8404 = (FStar_TypeChecker_Env.open_universes_in env2.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____8404) with
| (tcenv', uu____8420, e_t) -> begin
(

let uu____8426 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____8437 -> begin
(failwith "Impossible")
end)
in (match (uu____8426) with
| (e1, t_norm1) -> begin
(((

let uu___389_8454 = env2
in {FStar_SMTEncoding_Env.bvar_bindings = uu___389_8454.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___389_8454.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___389_8454.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___389_8454.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___389_8454.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___389_8454.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___389_8454.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___389_8454.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___389_8454.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___389_8454.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____8397) with
| (env', e1, t_norm1) -> begin
(

let uu____8464 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____8464) with
| (binders, body, t_body_comp) -> begin
(

let curry = (Prims.op_disEquality fvb.FStar_SMTEncoding_Env.smt_arity (FStar_List.length binders))
in (

let t_body = (FStar_Syntax_Util.comp_result t_body_comp)
in ((

let uu____8493 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____8493) with
| true -> begin
(

let uu____8498 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____8501 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____8498 uu____8501)))
end
| uu____8504 -> begin
()
end));
(

let uu____8506 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____8506) with
| (vars, _guards, env'1, binder_decls, uu____8533) -> begin
(

let app = (

let uu____8547 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____8548 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb uu____8547 fvb uu____8548)))
in (

let uu____8551 = (

let is_logical = (

let uu____8564 = (

let uu____8565 = (FStar_Syntax_Subst.compress t_body)
in uu____8565.FStar_Syntax_Syntax.n)
in (match (uu____8564) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.logical_lid) -> begin
true
end
| uu____8571 -> begin
false
end))
in (

let is_prims = (

let uu____8575 = (

let uu____8576 = (FStar_All.pipe_right lbn FStar_Util.right)
in (FStar_All.pipe_right uu____8576 FStar_Syntax_Syntax.lid_of_fv))
in (FStar_All.pipe_right uu____8575 (fun lid -> (

let uu____8585 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____8585 FStar_Parser_Const.prims_lid)))))
in (

let uu____8586 = ((not (is_prims)) && ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) || is_logical))
in (match (uu____8586) with
| true -> begin
(

let uu____8602 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____8603 = (FStar_SMTEncoding_EncodeTerm.encode_formula body env'1)
in ((app), (uu____8602), (uu____8603))))
end
| uu____8612 -> begin
(

let uu____8614 = (FStar_SMTEncoding_EncodeTerm.encode_term body env'1)
in ((app), (app), (uu____8614)))
end))))
in (match (uu____8551) with
| (pat, app1, (body1, decls2)) -> begin
(

let eqn = (

let uu____8638 = (

let uu____8646 = (

let uu____8647 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____8648 = (

let uu____8659 = (FStar_SMTEncoding_Util.mkEq ((app1), (body1)))
in ((((pat)::[])::[]), (vars), (uu____8659)))
in (FStar_SMTEncoding_Term.mkForall uu____8647 uu____8648)))
in (

let uu____8668 = (

let uu____8669 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____8669))
in ((uu____8646), (uu____8668), ((Prims.strcat "equation_" fvb.FStar_SMTEncoding_Env.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____8638))
in (

let uu____8675 = (

let uu____8678 = (

let uu____8681 = (

let uu____8684 = (

let uu____8687 = (primitive_type_axioms env2.FStar_SMTEncoding_Env.tcenv flid fvb.FStar_SMTEncoding_Env.smt_id app1)
in (FStar_List.append ((eqn)::[]) uu____8687))
in (FStar_List.append decls2 uu____8684))
in (FStar_List.append binder_decls uu____8681))
in (FStar_List.append decls1 uu____8678))
in ((uu____8675), (env2))))
end)))
end));
)))
end))
end)))
end
| uu____8692 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____8757 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "fuel")
in ((uu____8757), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____8763 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____8816 fvb -> (match (uu____8816) with
| (gtoks, env3) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let g = (

let uu____8871 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____8871))
in (

let gtok = (

let uu____8875 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____8875))
in (

let env4 = (

let uu____8878 = (

let uu____8881 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) uu____8881))
in (FStar_SMTEncoding_Env.push_free_var env3 flid fvb.FStar_SMTEncoding_Env.smt_arity gtok uu____8878))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____8763) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____9008 t_norm uu____9010 -> (match (((uu____9008), (uu____9010))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____9042; FStar_Syntax_Syntax.lbeff = uu____9043; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____9045; FStar_Syntax_Syntax.lbpos = uu____9046}) -> begin
(

let uu____9073 = (

let uu____9080 = (FStar_TypeChecker_Env.open_universes_in env3.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____9080) with
| (tcenv', uu____9096, e_t) -> begin
(

let uu____9102 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____9113 -> begin
(failwith "Impossible")
end)
in (match (uu____9102) with
| (e1, t_norm1) -> begin
(((

let uu___390_9130 = env3
in {FStar_SMTEncoding_Env.bvar_bindings = uu___390_9130.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___390_9130.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___390_9130.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___390_9130.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___390_9130.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___390_9130.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___390_9130.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___390_9130.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___390_9130.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___390_9130.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____9073) with
| (env', e1, t_norm1) -> begin
((

let uu____9145 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____9145) with
| true -> begin
(

let uu____9150 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____9152 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____9154 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____9150 uu____9152 uu____9154))))
end
| uu____9157 -> begin
()
end));
(

let uu____9159 = (destruct_bound_function fvb.FStar_SMTEncoding_Env.fvar_lid t_norm1 e1)
in (match (uu____9159) with
| (binders, body, tres_comp) -> begin
(

let curry = (Prims.op_disEquality fvb.FStar_SMTEncoding_Env.smt_arity (FStar_List.length binders))
in (

let uu____9188 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env3.FStar_SMTEncoding_Env.tcenv tres_comp)
in (match (uu____9188) with
| (pre_opt, tres) -> begin
((

let uu____9212 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____9212) with
| true -> begin
(

let uu____9217 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____9219 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____9222 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____9224 = (FStar_Syntax_Print.comp_to_string tres_comp)
in (FStar_Util.print4 "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n" uu____9217 uu____9219 uu____9222 uu____9224)))))
end
| uu____9227 -> begin
()
end));
(

let uu____9229 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____9229) with
| (vars, guards, env'1, binder_decls, uu____9260) -> begin
(

let uu____9273 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9286 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____9286), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____9290 = (FStar_SMTEncoding_EncodeTerm.encode_formula pre env'1)
in (match (uu____9290) with
| (guard, decls0) -> begin
(

let uu____9303 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append guards ((guard)::[])))
in ((uu____9303), (decls0)))
end))
end)
in (match (uu____9273) with
| (guard, guard_decls) -> begin
(

let binder_decls1 = (FStar_List.append binder_decls guard_decls)
in (

let decl_g = (

let uu____9326 = (

let uu____9338 = (

let uu____9341 = (

let uu____9344 = (

let uu____9347 = (FStar_Util.first_N fvb.FStar_SMTEncoding_Env.smt_arity vars)
in (FStar_Pervasives_Native.fst uu____9347))
in (FStar_List.map FStar_Pervasives_Native.snd uu____9344))
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____9341)
in ((g), (uu____9338), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____9326))
in (

let env02 = (FStar_SMTEncoding_Env.push_zfuel_name env01 fvb.FStar_SMTEncoding_Env.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let rng = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let app = (

let uu____9378 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb rng fvb uu____9378))
in (

let mk_g_app = (fun args -> (FStar_SMTEncoding_EncodeTerm.maybe_curry_app rng (FStar_SMTEncoding_Term.Var (g)) (fvb.FStar_SMTEncoding_Env.smt_arity + (Prims.parse_int "1")) args))
in (

let gsapp = (

let uu____9393 = (

let uu____9396 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____9396)::vars_tm)
in (mk_g_app uu____9393))
in (

let gmax = (

let uu____9402 = (

let uu____9405 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____9405)::vars_tm)
in (mk_g_app uu____9402))
in (

let uu____9410 = (FStar_SMTEncoding_EncodeTerm.encode_term body env'1)
in (match (uu____9410) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____9428 = (

let uu____9436 = (

let uu____9437 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9438 = (

let uu____9454 = (

let uu____9455 = (

let uu____9460 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((guard), (uu____9460)))
in (FStar_SMTEncoding_Util.mkImp uu____9455))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____9454)))
in (FStar_SMTEncoding_Term.mkForall' uu____9437 uu____9438)))
in (

let uu____9474 = (

let uu____9475 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.FStar_SMTEncoding_Env.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____9475))
in ((uu____9436), (uu____9474), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____9428))
in (

let eqn_f = (

let uu____9482 = (

let uu____9490 = (

let uu____9491 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9492 = (

let uu____9503 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____9503)))
in (FStar_SMTEncoding_Term.mkForall uu____9491 uu____9492)))
in ((uu____9490), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____9482))
in (

let eqn_g' = (

let uu____9517 = (

let uu____9525 = (

let uu____9526 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9527 = (

let uu____9538 = (

let uu____9539 = (

let uu____9544 = (

let uu____9545 = (

let uu____9548 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____9548)::vars_tm)
in (mk_g_app uu____9545))
in ((gsapp), (uu____9544)))
in (FStar_SMTEncoding_Util.mkEq uu____9539))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____9538)))
in (FStar_SMTEncoding_Term.mkForall uu____9526 uu____9527)))
in ((uu____9525), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____9517))
in (

let uu____9562 = (

let gapp = (mk_g_app ((fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (

let uu____9574 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_EncodeTerm.mk_Apply uu____9574 ((fuel)::vars)))
in (

let uu____9576 = (

let uu____9584 = (

let uu____9585 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9586 = (

let uu____9597 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____9597)))
in (FStar_SMTEncoding_Term.mkForall uu____9585 uu____9586)))
in ((uu____9584), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____9576)))
in (

let uu____9610 = (

let uu____9619 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tres env'1 gapp)
in (match (uu____9619) with
| (g_typing, d3) -> begin
(

let uu____9634 = (

let uu____9637 = (

let uu____9638 = (

let uu____9646 = (

let uu____9647 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9648 = (

let uu____9659 = (FStar_SMTEncoding_Util.mkImp ((guard), (g_typing)))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____9659)))
in (FStar_SMTEncoding_Term.mkForall uu____9647 uu____9648)))
in ((uu____9646), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____9638))
in (uu____9637)::[])
in ((d3), (uu____9634)))
end))
in (match (uu____9610) with
| (aux_decls, typing_corr) -> begin
((aux_decls), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end))))
in (match (uu____9562) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls1 (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))))
end))
end));
)
end)))
end));
)
end))
end))
in (

let uu____9722 = (

let uu____9735 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____9798 uu____9799 -> (match (((uu____9798), (uu____9799))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____9924 = (encode_one_binding env01 gtok ty lb)
in (match (uu____9924) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____9735))
in (match (uu____9722) with
| (decls2, eqns, env01) -> begin
(

let uu____9997 = (

let isDeclFun = (fun uu___373_10012 -> (match (uu___373_10012) with
| FStar_SMTEncoding_Term.DeclFun (uu____10014) -> begin
true
end
| uu____10027 -> begin
false
end))
in (

let uu____10029 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____10029 (FStar_List.partition isDeclFun))))
in (match (uu____9997) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____10069 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___374_10075 -> (match (uu___374_10075) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____10078 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____10086 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.FStar_SMTEncoding_Env.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____10086))))))
in (match (uu____10069) with
| true -> begin
((decls1), (env_decls))
end
| uu____10099 -> begin
(FStar_All.try_with (fun uu___392_10108 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____10122 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___391_10125 -> (match (uu___391_10125) with
| FStar_SMTEncoding_Env.Inner_let_rec -> begin
((decls1), (env_decls))
end)))
end)))))))))
end))
end))
end)) (fun uu___387_10137 -> (match (uu___387_10137) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____10146 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____10146 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let nm = (

let uu____10216 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____10216) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____10222 = (encode_sigelt' env se)
in (match (uu____10222) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____10234 = (

let uu____10235 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10235))
in (uu____10234)::[])
end
| uu____10238 -> begin
(

let uu____10239 = (

let uu____10242 = (

let uu____10243 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10243))
in (uu____10242)::g)
in (

let uu____10246 = (

let uu____10249 = (

let uu____10250 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10250))
in (uu____10249)::[])
in (FStar_List.append uu____10239 uu____10246)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____10266 = (

let uu____10267 = (FStar_Syntax_Subst.compress t)
in uu____10267.FStar_Syntax_Syntax.n)
in (match (uu____10266) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____10272)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____10277 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____10286 = (

let uu____10287 = (FStar_Syntax_Subst.compress t)
in uu____10287.FStar_Syntax_Syntax.n)
in (match (uu____10286) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____10292)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____10297 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10303) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____10309) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____10321) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____10322) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____10323) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____10336) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____10338 = (

let uu____10340 = (FStar_TypeChecker_Env.is_reifiable_effect env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname)
in (not (uu____10340)))
in (match (uu____10338) with
| true -> begin
(([]), (env))
end
| uu____10347 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____10369 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____10401 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____10401) with
| (formals, uu____10421) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____10445 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____10445) with
| (aname, atok, env2) -> begin
(

let uu____10471 = (

let uu____10476 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (FStar_SMTEncoding_EncodeTerm.encode_term uu____10476 env2))
in (match (uu____10471) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____10488 = (

let uu____10489 = (

let uu____10501 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10521 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____10501), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____10489))
in (uu____10488)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____10538 = (

let aux = (fun uu____10599 uu____10600 -> (match (((uu____10599), (uu____10600))) with
| ((bv, uu____10659), (env3, acc_sorts, acc)) -> begin
(

let uu____10706 = (FStar_SMTEncoding_Env.gen_term_var env3 bv)
in (match (uu____10706) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____10538) with
| (uu____10790, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____10816 = (

let uu____10824 = (

let uu____10825 = (FStar_Ident.range_of_lid a.FStar_Syntax_Syntax.action_name)
in (

let uu____10826 = (

let uu____10837 = (

let uu____10838 = (

let uu____10843 = (FStar_SMTEncoding_EncodeTerm.mk_Apply tm xs_sorts)
in ((app), (uu____10843)))
in (FStar_SMTEncoding_Util.mkEq uu____10838))
in ((((app)::[])::[]), (xs_sorts), (uu____10837)))
in (FStar_SMTEncoding_Term.mkForall uu____10825 uu____10826)))
in ((uu____10824), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____10816))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply tok_term xs_sorts)
in (

let uu____10860 = (

let uu____10868 = (

let uu____10869 = (FStar_Ident.range_of_lid a.FStar_Syntax_Syntax.action_name)
in (

let uu____10870 = (

let uu____10881 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____10881)))
in (FStar_SMTEncoding_Term.mkForall uu____10869 uu____10870)))
in ((uu____10868), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____10860))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____10896 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____10896) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10922, uu____10923) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____10924 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____10924) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____10946, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____10953 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___375_10959 -> (match (uu___375_10959) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____10962) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____10968) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____10971 -> begin
false
end))))
in (not (uu____10953)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____10978 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____10981 = (

let uu____10988 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____10988 env fv t quals))
in (match (uu____10981) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____11007 = (

let uu____11008 = (primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv lid tname tsym)
in (FStar_List.append decls uu____11008))
in ((uu____11007), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____11014 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____11014) with
| (uvs, f1) -> begin
(

let env1 = (

let uu___393_11026 = env
in (

let uu____11027 = (FStar_TypeChecker_Env.push_univ_vars env.FStar_SMTEncoding_Env.tcenv uvs)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___393_11026.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___393_11026.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___393_11026.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu____11027; FStar_SMTEncoding_Env.warn = uu___393_11026.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___393_11026.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___393_11026.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___393_11026.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___393_11026.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___393_11026.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___393_11026.FStar_SMTEncoding_Env.encoding_quantifier}))
in (

let f2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::[]) env1.FStar_SMTEncoding_Env.tcenv f1)
in (

let uu____11029 = (FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1)
in (match (uu____11029) with
| (f3, decls) -> begin
(

let g = (

let uu____11043 = (

let uu____11044 = (

let uu____11052 = (

let uu____11053 = (

let uu____11055 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____11055))
in FStar_Pervasives_Native.Some (uu____11053))
in (

let uu____11059 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f3), (uu____11052), (uu____11059))))
in (FStar_SMTEncoding_Util.mkAssume uu____11044))
in (uu____11043)::[])
in (((FStar_List.append decls g)), (env1)))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____11064) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____11078 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____11100 = (

let uu____11103 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11103.FStar_Syntax_Syntax.fv_name)
in uu____11100.FStar_Syntax_Syntax.v)
in (

let uu____11104 = (

let uu____11106 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.FStar_SMTEncoding_Env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____11106))
in (match (uu____11104) with
| true -> begin
(

let val_decl = (

let uu___394_11138 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___394_11138.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___394_11138.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___394_11138.FStar_Syntax_Syntax.sigattrs})
in (

let uu____11139 = (encode_sigelt' env1 val_decl)
in (match (uu____11139) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____11154 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____11078) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____11175, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____11177; FStar_Syntax_Syntax.lbtyp = uu____11178; FStar_Syntax_Syntax.lbeff = uu____11179; FStar_Syntax_Syntax.lbdef = uu____11180; FStar_Syntax_Syntax.lbattrs = uu____11181; FStar_Syntax_Syntax.lbpos = uu____11182})::[]), uu____11183) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____11202 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____11202) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2t_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2t_x)::[])))
in (

let decls = (

let uu____11245 = (

let uu____11248 = (

let uu____11249 = (

let uu____11257 = (

let uu____11258 = (FStar_Syntax_Syntax.range_of_fv b2t1)
in (

let uu____11259 = (

let uu____11270 = (

let uu____11271 = (

let uu____11276 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____11276)))
in (FStar_SMTEncoding_Util.mkEq uu____11271))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____11270)))
in (FStar_SMTEncoding_Term.mkForall uu____11258 uu____11259)))
in ((uu____11257), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____11249))
in (uu____11248)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____11245)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____11308, uu____11309) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___376_11319 -> (match (uu___376_11319) with
| FStar_Syntax_Syntax.Discriminator (uu____11321) -> begin
true
end
| uu____11323 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____11325, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____11337 = (

let uu____11339 = (FStar_List.hd l.FStar_Ident.ns)
in uu____11339.FStar_Ident.idText)
in (Prims.op_Equality uu____11337 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___377_11346 -> (match (uu___377_11346) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____11349 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____11352) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___378_11366 -> (match (uu___378_11366) with
| FStar_Syntax_Syntax.Projector (uu____11368) -> begin
true
end
| uu____11374 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11378 = (FStar_SMTEncoding_Env.try_lookup_free_var env l)
in (match (uu____11378) with
| FStar_Pervasives_Native.Some (uu____11385) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___395_11387 = se
in (

let uu____11388 = (FStar_Ident.range_of_lid l)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____11388; FStar_Syntax_Syntax.sigquals = uu___395_11387.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___395_11387.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___395_11387.FStar_Syntax_Syntax.sigattrs}))
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____11391) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11406) -> begin
(

let uu____11415 = (encode_sigelts env ses)
in (match (uu____11415) with
| (g, env1) -> begin
(

let uu____11432 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___379_11455 -> (match (uu___379_11455) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____11457; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____11458; FStar_SMTEncoding_Term.assumption_fact_ids = uu____11459}) -> begin
false
end
| uu____11466 -> begin
true
end))))
in (match (uu____11432) with
| (g', inversions) -> begin
(

let uu____11482 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___380_11503 -> (match (uu___380_11503) with
| FStar_SMTEncoding_Term.DeclFun (uu____11505) -> begin
true
end
| uu____11518 -> begin
false
end))))
in (match (uu____11482) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____11535, tps, k, uu____11538, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___381_11557 -> (match (uu___381_11557) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____11561 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____11574 = c
in (match (uu____11574) with
| (name, args, uu____11579, uu____11580, uu____11581) -> begin
(

let uu____11592 = (

let uu____11593 = (

let uu____11605 = (FStar_All.pipe_right args (FStar_List.map (fun uu____11632 -> (match (uu____11632) with
| (uu____11641, sort, uu____11643) -> begin
sort
end))))
in ((name), (uu____11605), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____11593))
in (uu____11592)::[])
end))
end
| uu____11652 -> begin
(

let uu____11654 = (FStar_Ident.range_of_lid t)
in (FStar_SMTEncoding_Term.constructor_to_decl uu____11654 c))
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____11682 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____11690 = (FStar_TypeChecker_Env.try_lookup_lid env.FStar_SMTEncoding_Env.tcenv l)
in (FStar_All.pipe_right uu____11690 FStar_Option.isNone)))))
in (match (uu____11682) with
| true -> begin
[]
end
| uu____11723 -> begin
(

let uu____11725 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____11725) with
| (xxsym, xx) -> begin
(

let uu____11738 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____11777 l -> (match (uu____11777) with
| (out, decls) -> begin
(

let uu____11797 = (FStar_TypeChecker_Env.lookup_datacon env.FStar_SMTEncoding_Env.tcenv l)
in (match (uu____11797) with
| (uu____11808, data_t) -> begin
(

let uu____11810 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____11810) with
| (args, res) -> begin
(

let indices = (

let uu____11854 = (

let uu____11855 = (FStar_Syntax_Subst.compress res)
in uu____11855.FStar_Syntax_Syntax.n)
in (match (uu____11854) with
| FStar_Syntax_Syntax.Tm_app (uu____11858, indices) -> begin
indices
end
| uu____11884 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____11914 -> (match (uu____11914) with
| (x, uu____11922) -> begin
(

let uu____11927 = (

let uu____11928 = (

let uu____11936 = (FStar_SMTEncoding_Env.mk_term_projector_name l x)
in ((uu____11936), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____11928))
in (FStar_SMTEncoding_Env.push_term_var env1 x uu____11927))
end)) env))
in (

let uu____11941 = (FStar_SMTEncoding_EncodeTerm.encode_args indices env1)
in (match (uu____11941) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____11968 -> begin
()
end);
(

let eqs = (

let uu____11971 = (FStar_List.map2 (fun v1 a -> (

let uu____11989 = (

let uu____11994 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____11994), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____11989))) vars indices1)
in (FStar_All.pipe_right uu____11971 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____11997 = (

let uu____11998 = (

let uu____12003 = (

let uu____12004 = (

let uu____12009 = (FStar_SMTEncoding_Env.mk_data_tester env1 l xx)
in ((uu____12009), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____12004))
in ((out), (uu____12003)))
in (FStar_SMTEncoding_Util.mkOr uu____11998))
in ((uu____11997), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____11738) with
| (data_ax, decls) -> begin
(

let uu____12022 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____12022) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____12039 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____12039 xx tapp))
end
| uu____12044 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____12046 = (

let uu____12054 = (

let uu____12055 = (FStar_Ident.range_of_lid t)
in (

let uu____12056 = (

let uu____12067 = (FStar_SMTEncoding_Env.add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____12080 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____12067), (uu____12080))))
in (FStar_SMTEncoding_Term.mkForall uu____12055 uu____12056)))
in (

let uu____12089 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____12054), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____12089))))
in (FStar_SMTEncoding_Util.mkAssume uu____12046)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____12095 = (

let uu____12100 = (

let uu____12101 = (FStar_Syntax_Subst.compress k)
in uu____12101.FStar_Syntax_Syntax.n)
in (match (uu____12100) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____12136 -> begin
((tps), (k))
end))
in (match (uu____12095) with
| (formals, res) -> begin
(

let uu____12143 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____12143) with
| (formals1, res1) -> begin
(

let uu____12154 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____12154) with
| (vars, guards, env', binder_decls, uu____12179) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____12193 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env t arity)
in (match (uu____12193) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____12223 = (

let uu____12231 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____12231)))
in (FStar_SMTEncoding_Util.mkApp uu____12223))
in (

let uu____12237 = (

let tname_decl = (

let uu____12247 = (

let uu____12248 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____12276 -> (match (uu____12276) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____12297 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((tname), (uu____12248), (FStar_SMTEncoding_Term.Term_sort), (uu____12297), (false))))
in (constructor_or_logic_type_decl uu____12247))
in (

let uu____12305 = (match (vars) with
| [] -> begin
(

let uu____12318 = (

let uu____12319 = (

let uu____12322 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____12322))
in (FStar_SMTEncoding_Env.push_free_var env1 t arity tname uu____12319))
in (([]), (uu____12318)))
end
| uu____12334 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____12344 = (FStar_Ident.range_of_lid t)
in (

let uu____12345 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token uu____12344 ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____12345)))
in (

let ttok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____12361 = (

let uu____12369 = (

let uu____12370 = (FStar_Ident.range_of_lid t)
in (

let uu____12371 = (

let uu____12387 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____12387)))
in (FStar_SMTEncoding_Term.mkForall' uu____12370 uu____12371)))
in ((uu____12369), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12361))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____12305) with
| (tok_decls, env2) -> begin
(

let uu____12414 = (FStar_Ident.lid_equals t FStar_Parser_Const.lex_t_lid)
in (match (uu____12414) with
| true -> begin
((tok_decls), (env2))
end
| uu____12425 -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end))
end)))
in (match (uu____12237) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____12442 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____12442) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____12464 = (

let uu____12465 = (

let uu____12473 = (

let uu____12474 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____12474))
in ((uu____12473), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12465))
in (uu____12464)::[])
end
| uu____12480 -> begin
[]
end)
in (

let uu____12482 = (

let uu____12485 = (

let uu____12488 = (

let uu____12489 = (

let uu____12497 = (

let uu____12498 = (FStar_Ident.range_of_lid t)
in (

let uu____12499 = (

let uu____12510 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____12510)))
in (FStar_SMTEncoding_Term.mkForall uu____12498 uu____12499)))
in ((uu____12497), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12489))
in (uu____12488)::[])
in (FStar_List.append karr uu____12485))
in (FStar_List.append decls1 uu____12482)))
end))
in (

let aux = (

let uu____12525 = (

let uu____12528 = (inversion_axioms tapp vars)
in (

let uu____12531 = (

let uu____12534 = (

let uu____12535 = (FStar_Ident.range_of_lid t)
in (pretype_axiom uu____12535 env2 tapp vars))
in (uu____12534)::[])
in (FStar_List.append uu____12528 uu____12531)))
in (FStar_List.append kindingAx uu____12525))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____12540, uu____12541, uu____12542, uu____12543, uu____12544) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____12552, t, uu____12554, n_tps, uu____12556) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____12566 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____12566) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____12614 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env d arity)
in (match (uu____12614) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____12642 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____12642) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____12662 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____12662) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____12741 = (FStar_SMTEncoding_Env.mk_term_projector_name d x)
in ((uu____12741), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____12748 = (

let uu____12749 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____12749), (true)))
in (

let uu____12757 = (

let uu____12764 = (FStar_Ident.range_of_lid d)
in (FStar_SMTEncoding_Term.constructor_to_decl uu____12764))
in (FStar_All.pipe_right uu____12748 uu____12757)))
in (

let app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____12776 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____12776) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____12788)::uu____12789 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (FStar_SMTEncoding_EncodeTerm.mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____12848 = (FStar_Ident.range_of_lid d)
in (

let uu____12849 = (

let uu____12860 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____12860)))
in (FStar_SMTEncoding_Term.mkForall uu____12848 uu____12849)))))))
end
| uu____12881 -> begin
tok_typing
end)
in (

let uu____12892 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____12892) with
| (vars', guards', env'', decls_formals, uu____12917) -> begin
(

let uu____12930 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (FStar_SMTEncoding_EncodeTerm.encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____12930) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____12960 -> begin
(

let uu____12969 = (

let uu____12970 = (FStar_Ident.range_of_lid d)
in (

let uu____12971 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token uu____12970 ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____12971)))
in (uu____12969)::[])
end)
in (

let encode_elim = (fun uu____12987 -> (

let uu____12988 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____12988) with
| (head1, args) -> begin
(

let uu____13039 = (

let uu____13040 = (FStar_Syntax_Subst.compress head1)
in uu____13040.FStar_Syntax_Syntax.n)
in (match (uu____13039) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____13052; FStar_Syntax_Syntax.vars = uu____13053}, uu____13054) -> begin
(

let uu____13059 = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____13059) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____13080 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____13080) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____13134 -> begin
(

let uu____13135 = (

let uu____13141 = (

let uu____13143 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____13143))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____13141)))
in (FStar_Errors.raise_error uu____13135 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____13163 = (

let uu____13165 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____13165))
in (match (uu____13163) with
| true -> begin
(

let uu____13181 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____13181)::[])
end
| uu____13182 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____13184 = (

let uu____13198 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____13255 uu____13256 -> (match (((uu____13255), (uu____13256))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____13367 = (

let uu____13375 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____13375))
in (match (uu____13367) with
| (uu____13389, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____13400 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____13400)::eqns_or_guards)
end
| uu____13403 -> begin
(

let uu____13405 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____13405)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____13198))
in (match (uu____13184) with
| (uu____13426, arg_vars, elim_eqns_or_guards, uu____13429) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____13456 = (

let uu____13464 = (

let uu____13465 = (FStar_Ident.range_of_lid d)
in (

let uu____13466 = (

let uu____13477 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____13479 = (

let uu____13480 = (

let uu____13485 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____13485)))
in (FStar_SMTEncoding_Util.mkImp uu____13480))
in ((((ty_pred)::[])::[]), (uu____13477), (uu____13479))))
in (FStar_SMTEncoding_Term.mkForall uu____13465 uu____13466)))
in ((uu____13464), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____13456))
in (

let subterm_ordering = (

let lex_t1 = (

let uu____13500 = (

let uu____13506 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____13506), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mkFreeV uu____13500))
in (

let uu____13509 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____13509) with
| true -> begin
(

let x = (

let uu____13518 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____13518), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____13523 = (

let uu____13531 = (

let uu____13532 = (FStar_Ident.range_of_lid d)
in (

let uu____13533 = (

let uu____13544 = (

let uu____13549 = (

let uu____13552 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in (uu____13552)::[])
in (uu____13549)::[])
in (

let uu____13557 = (

let uu____13558 = (

let uu____13563 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____13565 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in ((uu____13563), (uu____13565))))
in (FStar_SMTEncoding_Util.mkImp uu____13558))
in ((uu____13544), ((x)::[]), (uu____13557))))
in (FStar_SMTEncoding_Term.mkForall uu____13532 uu____13533)))
in (

let uu____13580 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____13531), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____13580))))
in (FStar_SMTEncoding_Util.mkAssume uu____13523))))
end
| uu____13586 -> begin
(

let prec = (

let uu____13591 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____13627 -> begin
(

let uu____13629 = (

let uu____13630 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 uu____13630 dapp1))
in (uu____13629)::[])
end))))
in (FStar_All.pipe_right uu____13591 FStar_List.flatten))
in (

let uu____13637 = (

let uu____13645 = (

let uu____13646 = (FStar_Ident.range_of_lid d)
in (

let uu____13647 = (

let uu____13658 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____13660 = (

let uu____13661 = (

let uu____13666 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____13666)))
in (FStar_SMTEncoding_Util.mkImp uu____13661))
in ((((ty_pred)::[])::[]), (uu____13658), (uu____13660))))
in (FStar_SMTEncoding_Term.mkForall uu____13646 uu____13647)))
in ((uu____13645), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____13637)))
end)))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____13684 = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____13684) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____13705 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____13705) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____13759 -> begin
(

let uu____13760 = (

let uu____13766 = (

let uu____13768 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____13768))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____13766)))
in (FStar_Errors.raise_error uu____13760 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____13788 = (

let uu____13790 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____13790))
in (match (uu____13788) with
| true -> begin
(

let uu____13806 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____13806)::[])
end
| uu____13807 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____13809 = (

let uu____13823 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____13880 uu____13881 -> (match (((uu____13880), (uu____13881))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____13992 = (

let uu____14000 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____14000))
in (match (uu____13992) with
| (uu____14014, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____14025 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____14025)::eqns_or_guards)
end
| uu____14028 -> begin
(

let uu____14030 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14030)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____13823))
in (match (uu____13809) with
| (uu____14051, arg_vars, elim_eqns_or_guards, uu____14054) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____14081 = (

let uu____14089 = (

let uu____14090 = (FStar_Ident.range_of_lid d)
in (

let uu____14091 = (

let uu____14102 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14104 = (

let uu____14105 = (

let uu____14110 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____14110)))
in (FStar_SMTEncoding_Util.mkImp uu____14105))
in ((((ty_pred)::[])::[]), (uu____14102), (uu____14104))))
in (FStar_SMTEncoding_Term.mkForall uu____14090 uu____14091)))
in ((uu____14089), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____14081))
in (

let subterm_ordering = (

let lex_t1 = (

let uu____14125 = (

let uu____14131 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____14131), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mkFreeV uu____14125))
in (

let uu____14134 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____14134) with
| true -> begin
(

let x = (

let uu____14143 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____14143), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14148 = (

let uu____14156 = (

let uu____14157 = (FStar_Ident.range_of_lid d)
in (

let uu____14158 = (

let uu____14169 = (

let uu____14174 = (

let uu____14177 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in (uu____14177)::[])
in (uu____14174)::[])
in (

let uu____14182 = (

let uu____14183 = (

let uu____14188 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14190 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in ((uu____14188), (uu____14190))))
in (FStar_SMTEncoding_Util.mkImp uu____14183))
in ((uu____14169), ((x)::[]), (uu____14182))))
in (FStar_SMTEncoding_Term.mkForall uu____14157 uu____14158)))
in (

let uu____14205 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____14156), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____14205))))
in (FStar_SMTEncoding_Util.mkAssume uu____14148))))
end
| uu____14211 -> begin
(

let prec = (

let uu____14216 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____14252 -> begin
(

let uu____14254 = (

let uu____14255 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 uu____14255 dapp1))
in (uu____14254)::[])
end))))
in (FStar_All.pipe_right uu____14216 FStar_List.flatten))
in (

let uu____14262 = (

let uu____14270 = (

let uu____14271 = (FStar_Ident.range_of_lid d)
in (

let uu____14272 = (

let uu____14283 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14285 = (

let uu____14286 = (

let uu____14291 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14291)))
in (FStar_SMTEncoding_Util.mkImp uu____14286))
in ((((ty_pred)::[])::[]), (uu____14283), (uu____14285))))
in (FStar_SMTEncoding_Term.mkForall uu____14271 uu____14272)))
in ((uu____14270), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____14262)))
end)))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| uu____14308 -> begin
((

let uu____14310 = (

let uu____14316 = (

let uu____14318 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14320 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14318 uu____14320)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____14316)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____14310));
(([]), ([]));
)
end))
end)))
in (

let uu____14328 = (encode_elim ())
in (match (uu____14328) with
| (decls2, elim) -> begin
(

let g = (

let uu____14354 = (

let uu____14357 = (

let uu____14360 = (

let uu____14363 = (

let uu____14366 = (

let uu____14367 = (

let uu____14379 = (

let uu____14380 = (

let uu____14382 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14382))
in FStar_Pervasives_Native.Some (uu____14380))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14379)))
in FStar_SMTEncoding_Term.DeclFun (uu____14367))
in (uu____14366)::[])
in (

let uu____14389 = (

let uu____14392 = (

let uu____14395 = (

let uu____14398 = (

let uu____14401 = (

let uu____14404 = (FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok))))
in (

let uu____14409 = (

let uu____14412 = (

let uu____14413 = (

let uu____14421 = (

let uu____14422 = (FStar_Ident.range_of_lid d)
in (

let uu____14423 = (

let uu____14434 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14434)))
in (FStar_SMTEncoding_Term.mkForall uu____14422 uu____14423)))
in ((uu____14421), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____14413))
in (

let uu____14447 = (

let uu____14450 = (

let uu____14451 = (

let uu____14459 = (

let uu____14460 = (FStar_Ident.range_of_lid d)
in (

let uu____14461 = (

let uu____14472 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14474 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14472), (uu____14474))))
in (FStar_SMTEncoding_Term.mkForall uu____14460 uu____14461)))
in ((uu____14459), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____14451))
in (uu____14450)::[])
in (uu____14412)::uu____14447))
in (uu____14404)::uu____14409))
in (FStar_List.append uu____14401 elim))
in (FStar_List.append decls_pred uu____14398))
in (FStar_List.append decls_formals uu____14395))
in (FStar_List.append proxy_fresh uu____14392))
in (FStar_List.append uu____14363 uu____14389)))
in (FStar_List.append decls3 uu____14360))
in (FStar_List.append decls2 uu____14357))
in (FStar_List.append binder_decls uu____14354))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end)))
end)))
end)))
end))))
and encode_sigelts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14512 se -> (match (uu____14512) with
| (g, env1) -> begin
(

let uu____14532 = (encode_sigelt env1 se)
in (match (uu____14532) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14600 -> (match (uu____14600) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_Syntax_Syntax.Binding_univ (uu____14637) -> begin
(((i + (Prims.parse_int "1"))), (decls), (env1))
end
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env1.FStar_SMTEncoding_Env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14645 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14645) with
| true -> begin
(

let uu____14650 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14652 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14654 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14650 uu____14652 uu____14654))))
end
| uu____14657 -> begin
()
end));
(

let uu____14659 = (FStar_SMTEncoding_EncodeTerm.encode_term t1 env1)
in (match (uu____14659) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14677 = (

let uu____14685 = (

let uu____14687 = (

let uu____14689 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____14689 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____14687))
in (FStar_SMTEncoding_Env.new_term_constant_from_string env1 x uu____14685))
in (match (uu____14677) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____14709 = (FStar_Options.log_queries ())
in (match (uu____14709) with
| true -> begin
(

let uu____14712 = (

let uu____14714 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14716 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14718 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14714 uu____14716 uu____14718))))
in FStar_Pervasives_Native.Some (uu____14712))
end
| uu____14722 -> begin
FStar_Pervasives_Native.None
end))
in (

let ax = (

let a_name = (Prims.strcat "binder_" xxsym)
in (FStar_SMTEncoding_Util.mkAssume ((t2), (FStar_Pervasives_Native.Some (a_name)), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_Syntax_Syntax.Binding_lid (x, (uu____14742, t)) -> begin
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____14762 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____14762) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end)
end))
in (

let uu____14789 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14789) with
| (uu____14816, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____14832 'Auu____14833 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____14832 * 'Auu____14833) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____14906 -> (match (uu____14906) with
| (l, uu____14919, uu____14920) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____14971 -> (match (uu____14971) with
| (l, uu____14986, uu____14987) -> begin
(

let uu____14998 = (FStar_All.pipe_left (fun _0_4 -> FStar_SMTEncoding_Term.Echo (_0_4)) (FStar_Pervasives_Native.fst l))
in (

let uu____15001 = (

let uu____15004 = (

let uu____15005 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15005))
in (uu____15004)::[])
in (uu____14998)::uu____15001))
end))))
in ((prefix1), (suffix)))))


let last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> (

let uu____15034 = (

let uu____15037 = (

let uu____15038 = (FStar_Util.psmap_empty ())
in (

let uu____15053 = (FStar_Util.psmap_empty ())
in (

let uu____15056 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____15060 = (

let uu____15062 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____15062 FStar_Ident.string_of_lid))
in {FStar_SMTEncoding_Env.bvar_bindings = uu____15038; FStar_SMTEncoding_Env.fvar_bindings = uu____15053; FStar_SMTEncoding_Env.depth = (Prims.parse_int "0"); FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu____15056; FStar_SMTEncoding_Env.nolabels = false; FStar_SMTEncoding_Env.use_zfuel_name = false; FStar_SMTEncoding_Env.encode_non_total_function_typ = true; FStar_SMTEncoding_Env.current_module_name = uu____15060; FStar_SMTEncoding_Env.encoding_quantifier = false}))))
in (uu____15037)::[])
in (FStar_ST.op_Colon_Equals last_env uu____15034)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Env.env_t = (fun cmn tcenv -> (

let uu____15104 = (FStar_ST.op_Bang last_env)
in (match (uu____15104) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15132 -> begin
(

let uu___396_15135 = e
in (

let uu____15136 = (FStar_Ident.string_of_lid cmn)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___396_15135.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___396_15135.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___396_15135.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = uu___396_15135.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___396_15135.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___396_15135.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___396_15135.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___396_15135.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu____15136; FStar_SMTEncoding_Env.encoding_quantifier = uu___396_15135.FStar_SMTEncoding_Env.encoding_quantifier}))
end)))


let set_env : FStar_SMTEncoding_Env.env_t  ->  unit = (fun env -> (

let uu____15144 = (FStar_ST.op_Bang last_env)
in (match (uu____15144) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15171)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : unit  ->  unit = (fun uu____15203 -> (

let uu____15204 = (FStar_ST.op_Bang last_env)
in (match (uu____15204) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let top = (copy_env hd1)
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1)))
end)))


let pop_env : unit  ->  unit = (fun uu____15264 -> (

let uu____15265 = (FStar_ST.op_Bang last_env)
in (match (uu____15265) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15292)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let snapshot_env : unit  ->  (Prims.int * unit) = (fun uu____15329 -> (FStar_Common.snapshot push_env last_env ()))


let rollback_env : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop_env last_env depth))


let init : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 FStar_SMTEncoding_Term.preludeDecls);
))


let snapshot : Prims.string  ->  (FStar_TypeChecker_Env.solver_depth_t * unit) = (fun msg -> (FStar_Util.atomically (fun uu____15382 -> (

let uu____15383 = (snapshot_env ())
in (match (uu____15383) with
| (env_depth, ()) -> begin
(

let uu____15405 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ())
in (match (uu____15405) with
| (varops_depth, ()) -> begin
(

let uu____15427 = (FStar_SMTEncoding_Z3.snapshot msg)
in (match (uu____15427) with
| (z3_depth, ()) -> begin
((((env_depth), (varops_depth), (z3_depth))), (()))
end))
end))
end)))))


let rollback : Prims.string  ->  FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Util.atomically (fun uu____15485 -> (

let uu____15486 = (match (depth) with
| FStar_Pervasives_Native.Some (s1, s2, s3) -> begin
((FStar_Pervasives_Native.Some (s1)), (FStar_Pervasives_Native.Some (s2)), (FStar_Pervasives_Native.Some (s3)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____15486) with
| (env_depth, varops_depth, z3_depth) -> begin
((rollback_env env_depth);
(FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback varops_depth);
(FStar_SMTEncoding_Z3.rollback msg z3_depth);
)
end)))))


let push : Prims.string  ->  unit = (fun msg -> (

let uu____15581 = (snapshot msg)
in ()))


let pop : Prims.string  ->  unit = (fun msg -> (rollback msg FStar_Pervasives_Native.None))


let open_fact_db_tags : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____15627)::uu____15628, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___397_15636 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___397_15636.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___397_15636.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___397_15636.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____15637 -> begin
d
end))


let fact_dbs_for_lid : FStar_SMTEncoding_Env.env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____15657 = (

let uu____15660 = (

let uu____15661 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____15661))
in (

let uu____15662 = (open_fact_db_tags env)
in (uu____15660)::uu____15662))
in (FStar_SMTEncoding_Term.Name (lid))::uu____15657))


let encode_top_level_facts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____15689 = (encode_sigelt env se)
in (match (uu____15689) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____15734 = (FStar_Options.log_queries ())
in (match (uu____15734) with
| true -> begin
(

let uu____15739 = (

let uu____15740 = (

let uu____15742 = (

let uu____15744 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15744 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15742))
in FStar_SMTEncoding_Term.Caption (uu____15740))
in (uu____15739)::decls)
end
| uu____15760 -> begin
decls
end)))
in ((

let uu____15763 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____15763) with
| true -> begin
(

let uu____15766 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____15766))
end
| uu____15769 -> begin
()
end));
(

let env = (

let uu____15772 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15772 tcenv))
in (

let uu____15773 = (encode_top_level_facts env se)
in (match (uu____15773) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____15787 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15787));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun tcenv modul -> (

let uu____15801 = ((FStar_Options.lax ()) && (FStar_Options.ml_ish ()))
in (match (uu____15801) with
| true -> begin
()
end
| uu____15804 -> begin
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15812 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15816 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____15816) with
| true -> begin
(

let uu____15819 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15819))
end
| uu____15824 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____15865 se -> (match (uu____15865) with
| (g, env2) -> begin
(

let uu____15885 = (encode_top_level_facts env2 se)
in (match (uu____15885) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____15908 = (encode_signature (

let uu___398_15917 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___398_15917.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___398_15917.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___398_15917.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___398_15917.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = false; FStar_SMTEncoding_Env.cache = uu___398_15917.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___398_15917.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___398_15917.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___398_15917.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___398_15917.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___398_15917.FStar_SMTEncoding_Env.encoding_quantifier}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15908) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____15937 = (FStar_Options.log_queries ())
in (match (uu____15937) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_SMTEncoding_Term.Module (((name), ((FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[]))))))::[])
end
| uu____15949 -> begin
decls1
end)))
in ((set_env (

let uu___399_15954 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___399_15954.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___399_15954.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___399_15954.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___399_15954.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu___399_15954.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___399_15954.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___399_15954.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___399_15954.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___399_15954.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___399_15954.FStar_SMTEncoding_Env.encoding_quantifier}));
(

let uu____15957 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____15957) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15961 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
))
end)))


let encode_query : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____16022 = (

let uu____16024 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____16024.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____16022));
(

let env = (

let uu____16026 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____16026 tcenv))
in (

let uu____16027 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
(

let uu____16066 = (aux rest)
in (match (uu____16066) with
| (out, rest1) -> begin
(

let t = (

let uu____16094 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____16094) with
| FStar_Pervasives_Native.Some (uu____16097) -> begin
(

let uu____16098 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____16098 x.FStar_Syntax_Syntax.sort))
end
| uu____16099 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t)
in (

let uu____16103 = (

let uu____16106 = (FStar_Syntax_Syntax.mk_binder (

let uu___400_16109 = x
in {FStar_Syntax_Syntax.ppname = uu___400_16109.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___400_16109.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____16106)::out)
in ((uu____16103), (rest1)))))
end))
end
| uu____16114 -> begin
(([]), (bindings))
end))
in (

let uu____16121 = (aux tcenv.FStar_TypeChecker_Env.gamma)
in (match (uu____16121) with
| (closing, bindings) -> begin
(

let uu____16148 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____16148), (bindings)))
end)))
in (match (uu____16027) with
| (q1, bindings) -> begin
(

let uu____16179 = (encode_env_bindings env bindings)
in (match (uu____16179) with
| (env_decls, env1) -> begin
((

let uu____16201 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____16201) with
| true -> begin
(

let uu____16208 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____16208))
end
| uu____16211 -> begin
()
end));
(

let uu____16213 = (FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1)
in (match (uu____16213) with
| (phi, qdecls) -> begin
(

let uu____16234 = (

let uu____16239 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____16239 phi))
in (match (uu____16234) with
| (labels, phi1) -> begin
(

let uu____16256 = (encode_labels labels)
in (match (uu____16256) with
| (label_prefix, label_suffix) -> begin
(

let caption = (

let uu____16293 = (FStar_Options.log_queries ())
in (match (uu____16293) with
| true -> begin
(

let uu____16298 = (

let uu____16299 = (

let uu____16301 = (FStar_Syntax_Print.term_to_string q1)
in (Prims.strcat "Encoding query formula: " uu____16301))
in FStar_SMTEncoding_Term.Caption (uu____16299))
in (uu____16298)::[])
end
| uu____16304 -> begin
[]
end))
in (

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix (FStar_List.append qdecls caption)))
in (

let qry = (

let uu____16310 = (

let uu____16318 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____16319 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "@query")
in ((uu____16318), (FStar_Pervasives_Native.Some ("query")), (uu____16319))))
in (FStar_SMTEncoding_Util.mkAssume uu____16310))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix))))))
end))
end))
end));
)
end))
end)));
))




