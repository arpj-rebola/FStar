
open Prims
open FStar_Pervasives
type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut


let uu___is_VerifyAll : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyAll -> begin
true
end
| uu____9 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____31 -> begin
false
end))


type files_for_module_name =
(Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap

type color =
| White
| Gray
| Black


let uu___is_White : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| White -> begin
true
end
| uu____54 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____65 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____76 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____87 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____98 -> begin
false
end))


let check_and_strip_suffix : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let try_strip = (fun ext -> (

let lext = (FStar_String.length ext)
in (

let l = (FStar_String.length f)
in (

let uu____145 = ((l > lext) && (

let uu____148 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____148 ext)))
in (match (uu____145) with
| true -> begin
(

let uu____155 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____155))
end
| uu____159 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let matches = (FStar_List.map try_strip suffixes)
in (

let uu____172 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____172) with
| (FStar_Pervasives_Native.Some (m))::uu____186 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____198 -> begin
FStar_Pervasives_Native.None
end))))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____215 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____215 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____229 = (is_interface f)
in (not (uu____229))))


let list_of_option : 'Auu____236 . 'Auu____236 FStar_Pervasives_Native.option  ->  'Auu____236 Prims.list = (fun uu___116_245 -> (match (uu___116_245) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____254 . ('Auu____254 FStar_Pervasives_Native.option * 'Auu____254 FStar_Pervasives_Native.option)  ->  'Auu____254 Prims.list = (fun uu____269 -> (match (uu____269) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let module_name_of_file : Prims.string  ->  Prims.string = (fun f -> (

let uu____298 = (

let uu____302 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____302))
in (match (uu____298) with
| FStar_Pervasives_Native.Some (longname) -> begin
longname
end
| FStar_Pervasives_Native.None -> begin
(

let uu____309 = (

let uu____315 = (FStar_Util.format1 "not a valid FStar file: %s" f)
in ((FStar_Errors.Fatal_NotValidFStarFile), (uu____315)))
in (FStar_Errors.raise_err uu____309))
end)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____329 = (module_name_of_file f)
in (FStar_String.lowercase uu____329)))


let namespace_of_module : Prims.string  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun f -> (

let lid = (

let uu____342 = (FStar_Ident.path_of_text f)
in (FStar_Ident.lid_of_path uu____342 FStar_Range.dummyRange))
in (match (lid.FStar_Ident.ns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____345 -> begin
(

let uu____348 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_Pervasives_Native.Some (uu____348))
end)))


type file_name =
Prims.string


type module_name =
Prims.string

type dependence =
| UseInterface of module_name
| PreferInterface of module_name
| UseImplementation of module_name
| FriendImplementation of module_name


let uu___is_UseInterface : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UseInterface (_0) -> begin
true
end
| uu____390 -> begin
false
end))


let __proj__UseInterface__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseInterface (_0) -> begin
_0
end))


let uu___is_PreferInterface : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PreferInterface (_0) -> begin
true
end
| uu____414 -> begin
false
end))


let __proj__PreferInterface__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| PreferInterface (_0) -> begin
_0
end))


let uu___is_UseImplementation : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
true
end
| uu____438 -> begin
false
end))


let __proj__UseImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
_0
end))


let uu___is_FriendImplementation : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FriendImplementation (_0) -> begin
true
end
| uu____462 -> begin
false
end))


let __proj__FriendImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| FriendImplementation (_0) -> begin
_0
end))


let dep_to_string : dependence  ->  Prims.string = (fun uu___117_481 -> (match (uu___117_481) with
| UseInterface (f) -> begin
(Prims.strcat "UseInterface " f)
end
| PreferInterface (f) -> begin
(Prims.strcat "PreferInterface " f)
end
| UseImplementation (f) -> begin
(Prims.strcat "UseImplementation " f)
end
| FriendImplementation (f) -> begin
(Prims.strcat "FriendImplementation " f)
end))


type dependences =
dependence Prims.list


let empty_dependences : 'Auu____500 . unit  ->  'Auu____500 Prims.list = (fun uu____503 -> [])

type dep_node =
{edges : dependences; color : color}


let __proj__Mkdep_node__item__edges : dep_node  ->  dependences = (fun projectee -> (match (projectee) with
| {edges = edges; color = color} -> begin
edges
end))


let __proj__Mkdep_node__item__color : dep_node  ->  color = (fun projectee -> (match (projectee) with
| {edges = edges; color = color} -> begin
color
end))

type dependence_graph =
| Deps of dep_node FStar_Util.smap


let uu___is_Deps : dependence_graph  ->  Prims.bool = (fun projectee -> true)


let __proj__Deps__item___0 : dependence_graph  ->  dep_node FStar_Util.smap = (fun projectee -> (match (projectee) with
| Deps (_0) -> begin
_0
end))

type deps =
{dep_graph : dependence_graph; file_system_map : files_for_module_name; cmd_line_files : file_name Prims.list; all_files : file_name Prims.list; interfaces_with_inlining : module_name Prims.list}


let __proj__Mkdeps__item__dep_graph : deps  ->  dependence_graph = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
dep_graph
end))


let __proj__Mkdeps__item__file_system_map : deps  ->  files_for_module_name = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
file_system_map
end))


let __proj__Mkdeps__item__cmd_line_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
cmd_line_files
end))


let __proj__Mkdeps__item__all_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
all_files
end))


let __proj__Mkdeps__item__interfaces_with_inlining : deps  ->  module_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
interfaces_with_inlining
end))


let deps_try_find : dependence_graph  ->  Prims.string  ->  dep_node FStar_Pervasives_Native.option = (fun uu____722 k -> (match (uu____722) with
| Deps (m) -> begin
(FStar_Util.smap_try_find m k)
end))


let deps_add_dep : dependence_graph  ->  Prims.string  ->  dep_node  ->  unit = (fun uu____744 k v1 -> (match (uu____744) with
| Deps (m) -> begin
(FStar_Util.smap_add m k v1)
end))


let deps_keys : dependence_graph  ->  Prims.string Prims.list = (fun uu____759 -> (match (uu____759) with
| Deps (m) -> begin
(FStar_Util.smap_keys m)
end))


let deps_empty : unit  ->  dependence_graph = (fun uu____771 -> (

let uu____772 = (FStar_Util.smap_create (Prims.parse_int "41"))
in Deps (uu____772)))


let mk_deps : dependence_graph  ->  files_for_module_name  ->  file_name Prims.list  ->  file_name Prims.list  ->  module_name Prims.list  ->  deps = (fun dg fs c a i -> {dep_graph = dg; file_system_map = fs; cmd_line_files = c; all_files = a; interfaces_with_inlining = i})


let empty_deps : deps = (

let uu____821 = (deps_empty ())
in (

let uu____822 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (mk_deps uu____821 uu____822 [] [] [])))


let module_name_of_dep : dependence  ->  module_name = (fun uu___118_843 -> (match (uu___118_843) with
| UseInterface (m) -> begin
m
end
| PreferInterface (m) -> begin
m
end
| UseImplementation (m) -> begin
m
end
| FriendImplementation (m) -> begin
m
end))


let resolve_module_name : files_for_module_name  ->  module_name  ->  module_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____872 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____872) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____899) -> begin
(

let uu____921 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____921))
end
| FStar_Pervasives_Native.Some (uu____924, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____947 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____947))
end
| uu____950 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____983 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____983) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____1010) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____1033 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____1066 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1066) with
| FStar_Pervasives_Native.Some (uu____1092, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____1116 -> begin
FStar_Pervasives_Native.None
end)))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1145 = (interface_of file_system_map key)
in (FStar_Option.isSome uu____1145)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1165 = (implementation_of file_system_map key)
in (FStar_Option.isSome uu____1165)))


let cache_file_name_internal : Prims.string  ->  (Prims.string * Prims.bool) = (fun fn -> (

let cache_fn = (

let uu____1192 = (

let uu____1194 = (FStar_Options.lax ())
in (match (uu____1194) with
| true -> begin
".checked.lax"
end
| uu____1199 -> begin
".checked"
end))
in (Prims.strcat fn uu____1192))
in (

let uu____1202 = (

let uu____1206 = (FStar_All.pipe_right cache_fn FStar_Util.basename)
in (FStar_Options.find_file uu____1206))
in (match (uu____1202) with
| FStar_Pervasives_Native.Some (path) -> begin
((path), (true))
end
| FStar_Pervasives_Native.None -> begin
(

let mname = (FStar_All.pipe_right fn module_name_of_file)
in (

let uu____1227 = (FStar_All.pipe_right mname FStar_Options.should_be_already_cached)
in (match (uu____1227) with
| true -> begin
(

let uu____1238 = (

let uu____1244 = (FStar_Util.format1 "Expected %s to be already checked but could not find it" mname)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1244)))
in (FStar_Errors.raise_err uu____1238))
end
| uu____1254 -> begin
(

let uu____1256 = (FStar_Options.prepend_cache_dir cache_fn)
in ((uu____1256), (false)))
end)))
end))))


let cache_file_name : Prims.string  ->  Prims.string = (fun fn -> (

let uu____1270 = (FStar_All.pipe_right fn cache_file_name_internal)
in (FStar_All.pipe_right uu____1270 FStar_Pervasives_Native.fst)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____1342 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____1342)))))))
in (

let maybe_use_cache_of = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____1356 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____1361 = (interface_of file_system_map key)
in (match (uu____1361) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1368 = (

let uu____1374 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____1374)))
in (FStar_Errors.raise_err uu____1368))
end
| FStar_Pervasives_Native.Some (f) -> begin
f
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____1384 = ((cmd_line_has_impl key) && (

let uu____1387 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____1387)))
in (match (uu____1384) with
| true -> begin
(

let uu____1394 = (FStar_Options.expose_interfaces ())
in (match (uu____1394) with
| true -> begin
(

let uu____1398 = (

let uu____1400 = (implementation_of file_system_map key)
in (FStar_Option.get uu____1400))
in (maybe_use_cache_of uu____1398))
end
| uu____1405 -> begin
(

let uu____1407 = (

let uu____1413 = (

let uu____1415 = (

let uu____1417 = (implementation_of file_system_map key)
in (FStar_Option.get uu____1417))
in (

let uu____1422 = (

let uu____1424 = (interface_of file_system_map key)
in (FStar_Option.get uu____1424))
in (FStar_Util.format3 "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" key uu____1415 uu____1422)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____1413)))
in (FStar_Errors.raise_err uu____1407))
end))
end
| uu____1432 -> begin
(

let uu____1434 = (

let uu____1436 = (interface_of file_system_map key)
in (FStar_Option.get uu____1436))
in (maybe_use_cache_of uu____1434))
end))
end
| PreferInterface (key) -> begin
(

let uu____1443 = (implementation_of file_system_map key)
in (match (uu____1443) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1449 = (

let uu____1455 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1455)))
in (FStar_Errors.raise_err uu____1449))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| UseImplementation (key) -> begin
(

let uu____1465 = (implementation_of file_system_map key)
in (match (uu____1465) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1471 = (

let uu____1477 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1477)))
in (FStar_Errors.raise_err uu____1471))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| FriendImplementation (key) -> begin
(

let uu____1487 = (implementation_of file_system_map key)
in (match (uu____1487) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1493 = (

let uu____1499 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1499)))
in (FStar_Errors.raise_err uu____1493))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____1560 = (deps_try_find deps fn)
in (match (uu____1560) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some ({edges = deps1; color = uu____1568}) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let print_graph : dependence_graph  ->  unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1582 = (

let uu____1584 = (

let uu____1586 = (

let uu____1588 = (

let uu____1592 = (

let uu____1596 = (deps_keys graph)
in (FStar_List.unique uu____1596))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1610 = (

let uu____1611 = (deps_try_find graph k)
in (FStar_Util.must uu____1611))
in uu____1610.edges)
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (

let uu____1632 = (

let uu____1634 = (lowercase_module_name k)
in (r uu____1634))
in (FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1632 (r (module_name_of_dep dep1)))))
in (FStar_List.map print7 deps))))) uu____1592))
in (FStar_String.concat "\n" uu____1588))
in (Prims.strcat uu____1586 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1584))
in (FStar_Util.write_file "dep.graph" uu____1582));
))


let build_inclusion_candidates_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1655 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____1681 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____1681))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.is_directory d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____1721 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____1721 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____1752 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____1756 -> begin
(

let uu____1758 = (

let uu____1764 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____1764)))
in (FStar_Errors.raise_err uu____1758))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____1827 = (FStar_Util.smap_try_find map1 key)
in (match (uu____1827) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____1874 = (is_interface full_path)
in (match (uu____1874) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____1894 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1923 = (is_interface full_path)
in (match (uu____1923) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____1944 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____1965 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____1983 -> (match (uu____1983) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____1965));
(FStar_List.iter (fun f -> (

let uu____2002 = (lowercase_module_name f)
in (add_entry uu____2002 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____2034 = (

let uu____2038 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____2038))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____2074 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____2074))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____2162 -> begin
()
end)) uu____2034));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____2231 -> begin
[]
end)
in (

let names = (

let uu____2238 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____2238 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____2261 = (string_of_lid l last1)
in (FStar_String.lowercase uu____2261)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____2270 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____2270)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____2292 = (

let uu____2294 = (

let uu____2296 = (

let uu____2298 = (

let uu____2302 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____2302))
in (FStar_Util.must uu____2298))
in (FStar_String.lowercase uu____2296))
in (Prims.op_disEquality uu____2294 k'))
in (match (uu____2292) with
| true -> begin
(

let uu____2307 = (FStar_Ident.range_of_lid lid)
in (

let uu____2308 = (

let uu____2314 = (

let uu____2316 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____2316 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____2314)))
in (FStar_Errors.log_issue uu____2307 uu____2308)))
end
| uu____2321 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____2332 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____2354 = (FStar_Options.prims_basename ())
in (

let uu____2356 = (

let uu____2360 = (FStar_Options.pervasives_basename ())
in (

let uu____2362 = (

let uu____2366 = (FStar_Options.pervasives_native_basename ())
in (uu____2366)::[])
in (uu____2360)::uu____2362))
in (uu____2354)::uu____2356))
in (match ((FStar_List.mem filename corelibs)) with
| true -> begin
[]
end
| uu____2384 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____2409 = (

let uu____2412 = (lowercase_module_name full_filename)
in (namespace_of_module uu____2412))
in (match (uu____2409) with
| FStar_Pervasives_Native.None -> begin
implicit_deps
end
| FStar_Pervasives_Native.Some (ns) -> begin
(FStar_List.append implicit_deps ((((ns), (Open_namespace)))::[]))
end)))
end))))


let dep_subsumed_by : dependence  ->  dependence  ->  Prims.bool = (fun d d' -> (match (((d), (d'))) with
| (PreferInterface (l'), FriendImplementation (l)) -> begin
(Prims.op_Equality l l')
end
| uu____2451 -> begin
(Prims.op_Equality d d')
end))


let collect_one : files_for_module_name  ->  Prims.string  ->  (dependence Prims.list * dependence Prims.list * Prims.bool) = (fun original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let mo_roots = (FStar_Util.mk_ref [])
in (

let has_inline_for_extraction = (FStar_Util.mk_ref false)
in (

let set_interface_inlining = (fun uu____2516 -> (

let uu____2517 = (is_interface filename)
in (match (uu____2517) with
| true -> begin
(FStar_ST.op_Colon_Equals has_inline_for_extraction true)
end
| uu____2564 -> begin
()
end)))
in (

let add_dep = (fun deps1 d -> (

let uu____2724 = (

let uu____2726 = (

let uu____2728 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (dep_subsumed_by d) uu____2728))
in (not (uu____2726)))
in (match (uu____2724) with
| true -> begin
(

let uu____2797 = (

let uu____2800 = (FStar_ST.op_Bang deps1)
in (d)::uu____2800)
in (FStar_ST.op_Colon_Equals deps1 uu____2797))
end
| uu____2933 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let dep_edge = (fun module_name -> PreferInterface (module_name))
in (

let add_dependence_edge = (fun original_or_working_map lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____2981 = (resolve_module_name original_or_working_map key)
in (match (uu____2981) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (dep_edge module_name));
(

let uu____3024 = ((has_interface original_or_working_map module_name) && (has_implementation original_or_working_map module_name))
in (match (uu____3024) with
| true -> begin
(add_dep mo_roots (UseImplementation (module_name)))
end
| uu____3060 -> begin
()
end));
true;
)
end
| uu____3063 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____3082 = ((let_open && (add_dependence_edge working_map lid)) || ((not (let_open)) && (add_dependence_edge original_map lid)))
in (match (uu____3082) with
| true -> begin
true
end
| uu____3087 -> begin
((match (let_open) with
| true -> begin
(

let uu____3091 = (FStar_Ident.range_of_lid lid)
in (

let uu____3092 = (

let uu____3098 = (

let uu____3100 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____3100))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3098)))
in (FStar_Errors.log_issue uu____3091 uu____3092)))
end
| uu____3105 -> begin
()
end);
false;
)
end)))
in (

let record_open_namespace = (fun lid -> (

let key = (lowercase_join_longident lid true)
in (

let r = (enter_namespace original_map working_map key)
in (match ((not (r))) with
| true -> begin
(

let uu____3120 = (FStar_Ident.range_of_lid lid)
in (

let uu____3121 = (

let uu____3127 = (

let uu____3129 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____3129))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3127)))
in (FStar_Errors.log_issue uu____3120 uu____3121)))
end
| uu____3134 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____3149 = (record_open_module let_open lid)
in (match (uu____3149) with
| true -> begin
()
end
| uu____3152 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____3155 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____3166 -> (match (uu____3166) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____3173 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (

let uu____3190 = (FStar_Ident.text_of_id ident)
in (FStar_String.lowercase uu____3190))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____3195 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____3195) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____3263 = (FStar_Ident.range_of_lid lid)
in (

let uu____3264 = (

let uu____3270 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3270)))
in (FStar_Errors.log_issue uu____3263 uu____3264)));
false;
)
end)))))
in (

let add_dep_on_module = (fun module_name -> (

let uu____3281 = (add_dependence_edge working_map module_name)
in (match (uu____3281) with
| true -> begin
()
end
| uu____3284 -> begin
(

let uu____3286 = (FStar_Options.debug_any ())
in (match (uu____3286) with
| true -> begin
(

let uu____3289 = (FStar_Ident.range_of_lid module_name)
in (

let uu____3290 = (

let uu____3296 = (

let uu____3298 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____3298))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____3296)))
in (FStar_Errors.log_issue uu____3289 uu____3290)))
end
| uu____3302 -> begin
()
end))
end)))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3310 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (add_dep_on_module module_name))
end))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_module = (fun uu___119_3438 -> (match (uu___119_3438) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3449 = (

let uu____3451 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____3451))
in ())
end
| uu____3453 -> begin
()
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____3457) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3468 = (

let uu____3470 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____3470))
in ())
end
| uu____3472 -> begin
()
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
(match ((FStar_List.contains FStar_Parser_AST.Inline_for_extraction x.FStar_Parser_AST.quals)) with
| true -> begin
(set_interface_inlining ())
end
| uu____3484 -> begin
()
end);
)) decls))
and collect_decl = (fun d -> (match (d) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Friend (lid) -> begin
(

let uu____3492 = (

let uu____3493 = (lowercase_join_longident lid true)
in FriendImplementation (uu____3493))
in (add_dep deps uu____3492))
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let uu____3531 = (record_module_alias ident lid)
in (match (uu____3531) with
| true -> begin
(

let uu____3534 = (

let uu____3535 = (lowercase_join_longident lid true)
in (dep_edge uu____3535))
in (add_dep deps uu____3534))
end
| uu____3571 -> begin
()
end))
end
| FStar_Parser_AST.TopLevelLet (uu____3573, patterms) -> begin
(FStar_List.iter (fun uu____3595 -> (match (uu____3595) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (uu____3604, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____3610, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3612; FStar_Parser_AST.mdest = uu____3613; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3615; FStar_Parser_AST.mdest = uu____3616; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____3618, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3620; FStar_Parser_AST.mdest = uu____3621; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____3625, tc, ts) -> begin
((match (tc) with
| true -> begin
(record_lid FStar_Parser_Const.mk_class_lid)
end
| uu____3650 -> begin
()
end);
(

let ts1 = (FStar_List.map (fun uu____3664 -> (match (uu____3664) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1));
)
end
| FStar_Parser_AST.Exception (uu____3677, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____3684) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____3685) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____3721 = (

let uu____3723 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____3723 > (Prims.parse_int "1")))
in (match (uu____3721) with
| true -> begin
(

let uu____3770 = (

let uu____3776 = (

let uu____3778 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____3778))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____3776)))
in (

let uu____3783 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____3770 uu____3783)))
end
| uu____3784 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___120_3786 -> (match (uu___120_3786) with
| FStar_Parser_AST.TyconAbstract (uu____3787, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____3799, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____3813, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3859 -> (match (uu____3859) with
| (uu____3868, t, uu____3870) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____3875, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3937 -> (match (uu____3937) with
| (uu____3951, t, uu____3953, uu____3954) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___121_3965 -> (match (uu___121_3965) with
| FStar_Parser_AST.DefineEffect (uu____3966, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____3980, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun b -> ((collect_aqual b.FStar_Parser_AST.aqual);
(match (b) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3993, t); FStar_Parser_AST.brange = uu____3995; FStar_Parser_AST.blevel = uu____3996; FStar_Parser_AST.aqual = uu____3997} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____4000, t); FStar_Parser_AST.brange = uu____4002; FStar_Parser_AST.blevel = uu____4003; FStar_Parser_AST.aqual = uu____4004} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____4008; FStar_Parser_AST.blevel = uu____4009; FStar_Parser_AST.aqual = uu____4010} -> begin
(collect_term t)
end
| uu____4013 -> begin
()
end);
))
and collect_aqual = (fun uu___122_4014 -> (match (uu___122_4014) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (t)) -> begin
(collect_term t)
end
| uu____4018 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___123_4022 -> (match (uu___123_4022) with
| FStar_Const.Const_int (uu____4023, FStar_Pervasives_Native.Some (signedness, width)) -> begin
(

let u = (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)
in (

let w = (match (width) with
| FStar_Const.Int8 -> begin
"8"
end
| FStar_Const.Int16 -> begin
"16"
end
| FStar_Const.Int32 -> begin
"32"
end
| FStar_Const.Int64 -> begin
"64"
end)
in (

let uu____4050 = (

let uu____4051 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (dep_edge uu____4051))
in (add_dep deps uu____4050))))
end
| FStar_Const.Const_char (uu____4087) -> begin
(add_dep deps (dep_edge "fstar.char"))
end
| FStar_Const.Const_float (uu____4123) -> begin
(add_dep deps (dep_edge "fstar.float"))
end
| uu____4158 -> begin
()
end))
and collect_term' = (fun uu___126_4159 -> (match (uu___126_4159) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((

let uu____4168 = (

let uu____4170 = (FStar_Ident.text_of_id s)
in (Prims.op_Equality uu____4170 "@"))
in (match (uu____4168) with
| true -> begin
(

let uu____4175 = (

let uu____4176 = (

let uu____4177 = (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
in (FStar_Ident.lid_of_path uu____4177 FStar_Range.dummyRange))
in FStar_Parser_AST.Name (uu____4176))
in (collect_term' uu____4175))
end
| uu____4179 -> begin
()
end));
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____4181) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____4182) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____4185) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Name (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((match ((Prims.op_Equality (FStar_List.length termimps) (Prims.parse_int "1"))) with
| true -> begin
(record_lid lid)
end
| uu____4210 -> begin
()
end);
(FStar_List.iter (fun uu____4219 -> (match (uu____4219) with
| (t, uu____4225) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____4235) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____4237, patterms, t) -> begin
((FStar_List.iter (fun uu____4287 -> (match (uu____4287) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____4316 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
in ());
(collect_pattern pat);
(collect_term t1);
)
end)) patterms);
(collect_term t);
)
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
((record_open true lid);
(collect_term t);
)
end
| FStar_Parser_AST.Bind (uu____4326, t1, t2) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
((collect_term t1);
(collect_term t2);
(collect_term t3);
)
end
| FStar_Parser_AST.Match (t, bs) -> begin
((collect_term t);
(collect_branches bs);
)
end
| FStar_Parser_AST.TryWith (t, bs) -> begin
((collect_term t);
(collect_branches bs);
)
end
| FStar_Parser_AST.Ascribed (t1, t2, FStar_Pervasives_Native.None) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Ascribed (t1, t2, FStar_Pervasives_Native.Some (tac)) -> begin
((collect_term t1);
(collect_term t2);
(collect_term tac);
)
end
| FStar_Parser_AST.Record (t, idterms) -> begin
((FStar_Util.iter_opt t collect_term);
(FStar_List.iter (fun uu____4422 -> (match (uu____4422) with
| (uu____4427, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____4430) -> begin
(collect_term t)
end
| FStar_Parser_AST.Product (binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
((FStar_List.iter (fun uu___124_4459 -> (match (uu___124_4459) with
| FStar_Util.Inl (b) -> begin
(collect_binder b)
end
| FStar_Util.Inr (t1) -> begin
(collect_term t1)
end)) binders);
(collect_term t);
)
end
| FStar_Parser_AST.QForall (binders, ts, t) -> begin
((collect_binders binders);
(FStar_List.iter (FStar_List.iter collect_term) ts);
(collect_term t);
)
end
| FStar_Parser_AST.QExists (binders, ts, t) -> begin
((collect_binders binders);
(FStar_List.iter (FStar_List.iter collect_term) ts);
(collect_term t);
)
end
| FStar_Parser_AST.Refine (binder, t) -> begin
((collect_binder binder);
(collect_term t);
)
end
| FStar_Parser_AST.NamedTyp (uu____4507, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____4511) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____4519) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____4527, uu____4528) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (t, uu____4534) -> begin
(collect_term t)
end
| FStar_Parser_AST.Antiquote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.VQuote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end
| FStar_Parser_AST.CalcProof (rel, init1, steps) -> begin
((

let uu____4548 = (FStar_Ident.lid_of_str "FStar.Calc")
in (add_dep_on_module uu____4548));
(collect_term rel);
(collect_term init1);
(FStar_List.iter (fun uu___125_4558 -> (match (uu___125_4558) with
| FStar_Parser_AST.CalcStep (rel1, just, next) -> begin
((collect_term rel1);
(collect_term just);
(collect_term next);
)
end)) steps);
)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___127_4568 -> (match (uu___127_4568) with
| FStar_Parser_AST.PatVar (uu____4569, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatTvar (uu____4575, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatWild (aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatOp (uu____4584) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____4585) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatName (uu____4593) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____4601) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____4622 -> (match (uu____4622) with
| (uu____4627, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, (t, FStar_Pervasives_Native.None)) -> begin
((collect_pattern p);
(collect_term t);
)
end
| FStar_Parser_AST.PatAscribed (p, (t, FStar_Pervasives_Native.Some (tac))) -> begin
((collect_pattern p);
(collect_term t);
(collect_term tac);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____4672 -> (match (uu____4672) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____4690 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____4690) with
| (ast, uu____4714) -> begin
(

let mname = (lowercase_module_name filename)
in ((

let uu____4732 = ((is_interface filename) && (has_implementation original_map mname))
in (match (uu____4732) with
| true -> begin
(add_dep mo_roots (UseImplementation (mname)))
end
| uu____4768 -> begin
()
end));
(collect_module ast);
(

let uu____4771 = (FStar_ST.op_Bang deps)
in (

let uu____4819 = (FStar_ST.op_Bang mo_roots)
in (

let uu____4867 = (FStar_ST.op_Bang has_inline_for_extraction)
in ((uu____4771), (uu____4819), (uu____4867)))));
))
end))));
))))))))))))))))))


let collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap FStar_ST.ref = (

let uu____4944 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (FStar_Util.mk_ref uu____4944))


let set_collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap  ->  unit = (fun cache -> (FStar_ST.op_Colon_Equals collect_one_cache cache))


let dep_graph_copy : dependence_graph  ->  dependence_graph = (fun dep_graph -> (

let uu____5066 = dep_graph
in (match (uu____5066) with
| Deps (g) -> begin
(

let uu____5070 = (FStar_Util.smap_copy g)
in Deps (uu____5070))
end)))


let topological_dependences_of : files_for_module_name  ->  dependence_graph  ->  Prims.string Prims.list  ->  file_name Prims.list  ->  Prims.bool  ->  (file_name Prims.list * Prims.bool) = (fun file_system_map dep_graph interfaces_needing_inlining root_files for_extraction -> (

let rec all_friend_deps_1 = (fun dep_graph1 cycle uu____5215 filename -> (match (uu____5215) with
| (all_friends, all_files) -> begin
(

let dep_node = (

let uu____5256 = (deps_try_find dep_graph1 filename)
in (FStar_Util.must uu____5256))
in (match (dep_node.color) with
| Gray -> begin
(failwith "Impossible: cycle detected after cycle detection has passed")
end
| Black -> begin
((all_friends), (all_files))
end
| White -> begin
((

let uu____5287 = (FStar_Options.debug_any ())
in (match (uu____5287) with
| true -> begin
(

let uu____5290 = (

let uu____5292 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_String.concat ", " uu____5292))
in (FStar_Util.print2 "Visiting %s: direct deps are %s\n" filename uu____5290))
end
| uu____5299 -> begin
()
end));
(deps_add_dep dep_graph1 filename (

let uu___131_5303 = dep_node
in {edges = uu___131_5303.edges; color = Gray}));
(

let uu____5304 = (

let uu____5315 = (dependences_of file_system_map dep_graph1 root_files filename)
in (all_friend_deps dep_graph1 cycle ((all_friends), (all_files)) uu____5315))
in (match (uu____5304) with
| (all_friends1, all_files1) -> begin
((deps_add_dep dep_graph1 filename (

let uu___132_5351 = dep_node
in {edges = uu___132_5351.edges; color = Black}));
(

let uu____5353 = (FStar_Options.debug_any ())
in (match (uu____5353) with
| true -> begin
(FStar_Util.print1 "Adding %s\n" filename)
end
| uu____5357 -> begin
()
end));
(

let uu____5359 = (

let uu____5363 = (FStar_List.collect (fun uu___128_5370 -> (match (uu___128_5370) with
| FriendImplementation (m) -> begin
(m)::[]
end
| d -> begin
[]
end)) dep_node.edges)
in (FStar_List.append uu____5363 all_friends1))
in ((uu____5359), ((filename)::all_files1)));
)
end));
)
end))
end))
and all_friend_deps = (fun dep_graph1 cycle all_friends filenames -> (FStar_List.fold_left (fun all_friends1 k -> (all_friend_deps_1 dep_graph1 ((k)::cycle) all_friends1 k)) all_friends filenames))
in ((

let uu____5436 = (FStar_Options.debug_any ())
in (match (uu____5436) with
| true -> begin
(FStar_Util.print_string "==============Phase1==================\n")
end
| uu____5440 -> begin
()
end));
(

let widened = (FStar_Util.mk_ref false)
in (

let widen_deps = (fun friends deps -> (

let uu____5465 = deps
in (match (uu____5465) with
| Deps (dg) -> begin
(

let uu____5469 = (deps_empty ())
in (match (uu____5469) with
| Deps (dg') -> begin
(

let widen_one = (fun deps1 -> (FStar_All.pipe_right deps1 (FStar_List.map (fun d -> (match (d) with
| PreferInterface (m) when ((FStar_List.contains m friends) && (has_implementation file_system_map m)) -> begin
((FStar_ST.op_Colon_Equals widened true);
FriendImplementation (m);
)
end
| uu____5541 -> begin
d
end)))))
in ((FStar_Util.smap_fold dg (fun filename dep_node uu____5549 -> (

let uu____5551 = (

let uu___133_5552 = dep_node
in (

let uu____5553 = (widen_one dep_node.edges)
in {edges = uu____5553; color = White}))
in (FStar_Util.smap_add dg' filename uu____5551))) ());
Deps (dg');
))
end))
end)))
in (

let dep_graph1 = (

let uu____5555 = ((FStar_Options.cmi ()) && for_extraction)
in (match (uu____5555) with
| true -> begin
(widen_deps interfaces_needing_inlining dep_graph)
end
| uu____5558 -> begin
dep_graph
end))
in (

let uu____5560 = (all_friend_deps dep_graph1 [] (([]), ([])) root_files)
in (match (uu____5560) with
| (friends, all_files_0) -> begin
((

let uu____5603 = (FStar_Options.debug_any ())
in (match (uu____5603) with
| true -> begin
(

let uu____5606 = (

let uu____5608 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) friends)
in (FStar_String.concat ", " uu____5608))
in (FStar_Util.print3 "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n" (FStar_String.concat ", " all_files_0) uu____5606 (FStar_String.concat ", " interfaces_needing_inlining)))
end
| uu____5624 -> begin
()
end));
(

let dep_graph2 = (widen_deps friends dep_graph1)
in (

let uu____5627 = ((

let uu____5639 = (FStar_Options.debug_any ())
in (match (uu____5639) with
| true -> begin
(FStar_Util.print_string "==============Phase2==================\n")
end
| uu____5643 -> begin
()
end));
(all_friend_deps dep_graph2 [] (([]), ([])) root_files);
)
in (match (uu____5627) with
| (uu____5662, all_files) -> begin
((

let uu____5677 = (FStar_Options.debug_any ())
in (match (uu____5677) with
| true -> begin
(FStar_Util.print1 "Phase2 complete: all_files = %s\n" (FStar_String.concat ", " all_files))
end
| uu____5682 -> begin
()
end));
(

let uu____5684 = (FStar_ST.op_Bang widened)
in ((all_files), (uu____5684)));
)
end)));
)
end)))));
)))


let collect : Prims.string Prims.list  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____5776 = (FStar_Options.find_file fn)
in (match (uu____5776) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5782 = (

let uu____5788 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____5788)))
in (FStar_Errors.raise_err uu____5782))
end
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end)))))
in (

let dep_graph = (deps_empty ())
in (

let file_system_map = (build_map all_cmd_line_files1)
in (

let interfaces_needing_inlining = (FStar_Util.mk_ref [])
in (

let add_interface_for_inlining = (fun l -> (

let l1 = (lowercase_module_name l)
in (

let uu____5818 = (

let uu____5822 = (FStar_ST.op_Bang interfaces_needing_inlining)
in (l1)::uu____5822)
in (FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____5818))))
in (

let rec discover_one = (fun file_name -> (

let uu____5929 = (

let uu____5931 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____5931 FStar_Pervasives_Native.None))
in (match (uu____5929) with
| true -> begin
(

let uu____5937 = (

let uu____5949 = (

let uu____5963 = (FStar_ST.op_Bang collect_one_cache)
in (FStar_Util.smap_try_find uu____5963 file_name))
in (match (uu____5949) with
| FStar_Pervasives_Native.Some (cached) -> begin
cached
end
| FStar_Pervasives_Native.None -> begin
(collect_one file_system_map file_name)
end))
in (match (uu____5937) with
| (deps, mo_roots, needs_interface_inlining) -> begin
((match (needs_interface_inlining) with
| true -> begin
(add_interface_for_inlining file_name)
end
| uu____6093 -> begin
()
end);
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____6100 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____6100) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____6105 -> begin
deps
end)))
in (

let dep_node = (

let uu____6108 = (FStar_List.unique deps1)
in {edges = uu____6108; color = White})
in ((deps_add_dep dep_graph file_name dep_node);
(

let uu____6110 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____6110));
)));
)
end))
end
| uu____6116 -> begin
()
end)))
in ((FStar_List.iter discover_one all_cmd_line_files1);
(

let cycle_detected = (fun dep_graph1 cycle filename -> ((FStar_Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (FStar_String.concat "\n`used by` " cycle));
(print_graph dep_graph1);
(FStar_Util.print_string "\n");
(

let uu____6150 = (

let uu____6156 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Fatal_CyclicDependence), (uu____6156)))
in (FStar_Errors.raise_err uu____6150));
))
in (

let full_cycle_detection = (fun all_command_line_files -> (

let dep_graph1 = (dep_graph_copy dep_graph)
in (

let rec aux = (fun cycle filename -> (

let node = (

let uu____6193 = (deps_try_find dep_graph1 filename)
in (match (uu____6193) with
| FStar_Pervasives_Native.Some (node) -> begin
node
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6197 = (FStar_Util.format1 "Failed to find dependences of %s" filename)
in (failwith uu____6197))
end))
in (

let direct_deps = (FStar_All.pipe_right node.edges (FStar_List.collect (fun x -> (match (x) with
| UseInterface (f) -> begin
(

let uu____6211 = (implementation_of file_system_map f)
in (match (uu____6211) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6222 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| PreferInterface (f) -> begin
(

let uu____6228 = (implementation_of file_system_map f)
in (match (uu____6228) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6239 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| uu____6243 -> begin
(x)::[]
end))))
in (match (node.color) with
| Gray -> begin
(cycle_detected dep_graph1 cycle filename)
end
| Black -> begin
()
end
| White -> begin
((deps_add_dep dep_graph1 filename (

let uu___134_6246 = node
in {edges = direct_deps; color = Gray}));
(

let uu____6248 = (dependences_of file_system_map dep_graph1 all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____6248));
(deps_add_dep dep_graph1 filename (

let uu___135_6258 = node
in {edges = direct_deps; color = Black}));
)
end))))
in (FStar_List.iter (aux []) all_command_line_files))))
in ((full_cycle_detection all_cmd_line_files1);
(FStar_All.pipe_right all_cmd_line_files1 (FStar_List.iter (fun f -> (

let m = (lowercase_module_name f)
in (FStar_Options.add_verify_module m)))));
(

let inlining_ifaces = (FStar_ST.op_Bang interfaces_needing_inlining)
in (

let uu____6324 = (

let uu____6333 = (

let uu____6335 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____6335 FStar_Pervasives_Native.None))
in (topological_dependences_of file_system_map dep_graph inlining_ifaces all_cmd_line_files1 uu____6333))
in (match (uu____6324) with
| (all_files, uu____6348) -> begin
((

let uu____6358 = (FStar_Options.debug_any ())
in (match (uu____6358) with
| true -> begin
(FStar_Util.print1 "Interfaces needing inlining: %s\n" (FStar_String.concat ", " inlining_ifaces))
end
| uu____6363 -> begin
()
end));
((all_files), ((mk_deps dep_graph file_system_map all_cmd_line_files1 all_files inlining_ifaces)));
)
end)));
)));
))))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun deps f -> (dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f))


let hash_dependences : deps  ->  Prims.string  ->  Prims.string  ->  (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option = (fun deps fn cache_file -> (

let file_system_map = deps.file_system_map
in (

let all_cmd_line_files = deps.cmd_line_files
in (

let deps1 = deps.dep_graph
in (

let fn1 = (

let uu____6425 = (FStar_Options.find_file fn)
in (match (uu____6425) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____6433 -> begin
fn
end))
in (

let digest_of_file1 = (fun fn2 -> ((

let uu____6447 = (FStar_Options.debug_any ())
in (match (uu____6447) with
| true -> begin
(FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2)
end
| uu____6451 -> begin
()
end));
(FStar_Util.digest_of_file fn2);
))
in (

let module_name = (lowercase_module_name fn1)
in (

let source_hash = (digest_of_file1 fn1)
in (

let interface_hash = (

let uu____6466 = ((is_implementation fn1) && (has_interface file_system_map module_name))
in (match (uu____6466) with
| true -> begin
(

let uu____6477 = (

let uu____6484 = (

let uu____6486 = (

let uu____6488 = (interface_of file_system_map module_name)
in (FStar_Option.get uu____6488))
in (digest_of_file1 uu____6486))
in (("interface"), (uu____6484)))
in (uu____6477)::[])
end
| uu____6508 -> begin
[]
end))
in (

let binary_deps = (

let uu____6520 = (dependences_of file_system_map deps1 all_cmd_line_files fn1)
in (FStar_All.pipe_right uu____6520 (FStar_List.filter (fun fn2 -> (

let uu____6535 = ((is_interface fn2) && (

let uu____6538 = (lowercase_module_name fn2)
in (Prims.op_Equality uu____6538 module_name)))
in (not (uu____6535)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____6554 = (lowercase_module_name fn11)
in (

let uu____6556 = (lowercase_module_name fn2)
in (FStar_String.compare uu____6554 uu____6556)))) binary_deps)
in (

let rec hash_deps = (fun out uu___129_6589 -> (match (uu___129_6589) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps2 -> begin
(

let cache_fn = (cache_file_name fn2)
in (

let digest = (match ((FStar_Util.file_exists cache_fn)) with
| true -> begin
(

let uu____6652 = (digest_of_file1 fn2)
in FStar_Pervasives_Native.Some (uu____6652))
end
| uu____6655 -> begin
FStar_Pervasives_Native.None
end)
in (match (digest) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6670 = (FStar_Options.debug_any ())
in (match (uu____6670) with
| true -> begin
(

let uu____6673 = (FStar_Util.basename cache_fn)
in (FStar_Util.print2 "%s: missed digest of file %s\n" cache_file uu____6673))
end
| uu____6676 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (dig) -> begin
(

let uu____6689 = (

let uu____6698 = (

let uu____6705 = (lowercase_module_name fn2)
in ((uu____6705), (dig)))
in (uu____6698)::out)
in (hash_deps uu____6689 deps2))
end)))
end))
in (hash_deps [] binary_deps1)))))))))))))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____6745 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____6771 -> (match (uu____6771) with
| (m, d) -> begin
(

let uu____6785 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____6785))
end))))
in (FStar_All.pipe_right uu____6745 (FStar_String.concat "\n"))))


let print_make : deps  ->  unit = (fun deps -> (

let file_system_map = deps.file_system_map
in (

let all_cmd_line_files = deps.cmd_line_files
in (

let deps1 = deps.dep_graph
in (

let keys = (deps_keys deps1)
in (FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let dep_node = (

let uu____6820 = (deps_try_find deps1 f)
in (FStar_All.pipe_right uu____6820 FStar_Option.get))
in (

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) dep_node.edges)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))))))))))))


let print_raw : deps  ->  unit = (fun deps -> (

let uu____6849 = deps.dep_graph
in (match (uu____6849) with
| Deps (deps1) -> begin
(

let uu____6853 = (

let uu____6855 = (FStar_Util.smap_fold deps1 (fun k dep_node out -> (

let uu____6873 = (

let uu____6875 = (

let uu____6877 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_All.pipe_right uu____6877 (FStar_String.concat ";\n\t")))
in (FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____6875))
in (uu____6873)::out)) [])
in (FStar_All.pipe_right uu____6855 (FStar_String.concat ";;\n")))
in (FStar_All.pipe_right uu____6853 FStar_Util.print_endline))
end)))


let print_full : deps  ->  unit = (fun deps -> (

let sort_output_files = (fun orig_output_file_map -> (

let order = (FStar_Util.mk_ref [])
in (

let remaining_output_files = (FStar_Util.smap_copy orig_output_file_map)
in (

let visited_other_modules = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let should_visit = (fun lc_module_name -> ((

let uu____6949 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____6949)) || (

let uu____6956 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____6956))))
in (

let mark_visiting = (fun lc_module_name -> (

let ml_file_opt = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in ((FStar_Util.smap_remove remaining_output_files lc_module_name);
(FStar_Util.smap_add visited_other_modules lc_module_name true);
ml_file_opt;
)))
in (

let emit_output_file_opt = (fun ml_file_opt -> (match (ml_file_opt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (ml_file) -> begin
(

let uu____6999 = (

let uu____7003 = (FStar_ST.op_Bang order)
in (ml_file)::uu____7003)
in (FStar_ST.op_Colon_Equals order uu____6999))
end))
in (

let rec aux = (fun uu___130_7110 -> (match (uu___130_7110) with
| [] -> begin
()
end
| (lc_module_name)::modules_to_extract -> begin
(

let visit_file = (fun file_opt -> (match (file_opt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (file_name) -> begin
(

let uu____7138 = (deps_try_find deps.dep_graph file_name)
in (match (uu____7138) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7141 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____7141))
end
| FStar_Pervasives_Native.Some ({edges = immediate_deps; color = uu____7145}) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____7154 = (should_visit lc_module_name)
in (match (uu____7154) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____7162 = (implementation_of deps.file_system_map lc_module_name)
in (visit_file uu____7162));
(

let uu____7167 = (interface_of deps.file_system_map lc_module_name)
in (visit_file uu____7167));
(emit_output_file_opt ml_file_opt);
))
end
| uu____7171 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____7179 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____7179));
))))))))))
in (

let keys = (deps_keys deps.dep_graph)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____7253 = (

let uu____7255 = (

let uu____7259 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____7259))
in (FStar_Option.get uu____7255))
in (FStar_Util.replace_chars uu____7253 46 (*.*) "_"))
in (FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____7284 = (output_file ".ml" f)
in (norm_path uu____7284)))
in (

let output_krml_file = (fun f -> (

let uu____7296 = (output_file ".krml" f)
in (norm_path uu____7296)))
in (

let output_cmx_file = (fun f -> (

let uu____7308 = (output_file ".cmx" f)
in (norm_path uu____7308)))
in (

let cache_file = (fun f -> (

let uu____7325 = (FStar_All.pipe_right f cache_file_name_internal)
in (FStar_All.pipe_right uu____7325 (fun uu____7354 -> (match (uu____7354) with
| (f1, b) -> begin
(((norm_path f1)), (b))
end)))))
in (

let transitive_krml = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let set_of_unchecked_files = (

let uu____7405 = (

let uu____7416 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_List.fold_left (fun set_of_unchecked_files file_name -> (

let dep_node = (

let uu____7455 = (deps_try_find deps.dep_graph file_name)
in (FStar_All.pipe_right uu____7455 FStar_Option.get))
in (

let iface_deps = (

let uu____7465 = (is_interface file_name)
in (match (uu____7465) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7474 -> begin
(

let uu____7476 = (

let uu____7480 = (lowercase_module_name file_name)
in (interface_of deps.file_system_map uu____7480))
in (match (uu____7476) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (iface) -> begin
(

let uu____7492 = (

let uu____7495 = (

let uu____7496 = (deps_try_find deps.dep_graph iface)
in (FStar_Option.get uu____7496))
in uu____7495.edges)
in FStar_Pervasives_Native.Some (uu____7492))
end))
end))
in (

let iface_deps1 = (FStar_Util.map_opt iface_deps (FStar_List.filter (fun iface_dep -> (

let uu____7513 = (FStar_Util.for_some (dep_subsumed_by iface_dep) dep_node.edges)
in (not (uu____7513))))))
in (

let norm_f = (norm_path file_name)
in (

let files = (FStar_List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) dep_node.edges)
in (

let files1 = (match (iface_deps1) with
| FStar_Pervasives_Native.None -> begin
files
end
| FStar_Pervasives_Native.Some (iface_deps2) -> begin
(

let iface_files = (FStar_List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) iface_deps2)
in (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) (FStar_List.append files iface_files)))
end)
in (

let files2 = (FStar_List.map norm_path files1)
in (

let files3 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files2)
in (

let files4 = (FStar_String.concat "\\\n\t" files3)
in (

let uu____7572 = (cache_file file_name)
in (match (uu____7572) with
| (cache_file_name1, b) -> begin
(

let set_of_unchecked_files1 = (match (b) with
| true -> begin
set_of_unchecked_files
end
| uu____7596 -> begin
(FStar_Util.set_add file_name set_of_unchecked_files)
end)
in ((FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1 norm_f files4);
(

let already_there = (

let uu____7605 = (

let uu____7619 = (

let uu____7621 = (output_file ".krml" file_name)
in (norm_path uu____7621))
in (FStar_Util.smap_try_find transitive_krml uu____7619))
in (match (uu____7605) with
| FStar_Pervasives_Native.Some (uu____7638, already_there, uu____7640) -> begin
already_there
end
| FStar_Pervasives_Native.None -> begin
[]
end))
in ((

let uu____7675 = (

let uu____7677 = (output_file ".krml" file_name)
in (norm_path uu____7677))
in (

let uu____7680 = (

let uu____7692 = (

let uu____7694 = (output_file ".exe" file_name)
in (norm_path uu____7694))
in (

let uu____7697 = (

let uu____7701 = (

let uu____7705 = (

let uu____7709 = (deps_of deps file_name)
in (FStar_List.map (fun x -> (

let uu____7719 = (output_file ".krml" x)
in (norm_path uu____7719))) uu____7709))
in (FStar_List.append already_there uu____7705))
in (FStar_List.unique uu____7701))
in ((uu____7692), (uu____7697), (false))))
in (FStar_Util.smap_add transitive_krml uu____7675 uu____7680)));
(

let uu____7741 = (

let uu____7750 = (FStar_Options.cmi ())
in (match (uu____7750) with
| true -> begin
(topological_dependences_of deps.file_system_map deps.dep_graph deps.interfaces_with_inlining ((file_name)::[]) true)
end
| uu____7764 -> begin
(

let maybe_widen_deps = (fun f_deps -> (FStar_List.map (fun dep1 -> (file_of_dep_aux false deps.file_system_map deps.cmd_line_files dep1)) f_deps))
in (

let fst_files = (maybe_widen_deps dep_node.edges)
in (

let fst_files_from_iface = (match (iface_deps1) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (iface_deps2) -> begin
(maybe_widen_deps iface_deps2)
end)
in (

let uu____7798 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) (FStar_List.append fst_files fst_files_from_iface))
in ((uu____7798), (false))))))
end))
in (match (uu____7741) with
| (all_fst_files_dep, widened) -> begin
(

let all_checked_fst_dep_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.map (fun f -> (

let uu____7845 = (FStar_All.pipe_right f cache_file)
in (FStar_All.pipe_right uu____7845 FStar_Pervasives_Native.fst)))))
in ((

let uu____7869 = (is_implementation file_name)
in (match (uu____7869) with
| true -> begin
((

let uu____7873 = ((FStar_Options.cmi ()) && widened)
in (match (uu____7873) with
| true -> begin
((

let uu____7877 = (output_ml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7877 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)));
(

let uu____7881 = (output_krml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7881 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)));
)
end
| uu____7885 -> begin
((

let uu____7888 = (output_ml_file file_name)
in (FStar_Util.print2 "%s: %s \n\n" uu____7888 cache_file_name1));
(

let uu____7891 = (output_krml_file file_name)
in (FStar_Util.print2 "%s: %s\n\n" uu____7891 cache_file_name1));
)
end));
(

let cmx_files = (

let extracted_fst_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.filter (fun df -> ((

let uu____7916 = (lowercase_module_name df)
in (

let uu____7918 = (lowercase_module_name file_name)
in (Prims.op_disEquality uu____7916 uu____7918))) && (

let uu____7922 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____7922))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file)))
in (

let uu____7932 = (

let uu____7934 = (lowercase_module_name file_name)
in (FStar_Options.should_extract uu____7934))
in (match (uu____7932) with
| true -> begin
(

let uu____7937 = (output_cmx_file file_name)
in (

let uu____7939 = (output_ml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7937 uu____7939 (FStar_String.concat "\\\n\t" cmx_files))))
end
| uu____7943 -> begin
()
end)));
)
end
| uu____7945 -> begin
(

let uu____7947 = ((

let uu____7951 = (

let uu____7953 = (lowercase_module_name file_name)
in (has_implementation deps.file_system_map uu____7953))
in (not (uu____7951))) && (is_interface file_name))
in (match (uu____7947) with
| true -> begin
(

let uu____7956 = ((FStar_Options.cmi ()) && widened)
in (match (uu____7956) with
| true -> begin
(

let uu____7959 = (output_krml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7959 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)))
end
| uu____7963 -> begin
(

let uu____7965 = (output_krml_file file_name)
in (FStar_Util.print2 "%s: %s \n\n" uu____7965 cache_file_name1))
end))
end
| uu____7968 -> begin
()
end))
end));
set_of_unchecked_files1;
))
end));
));
))
end)))))))))))) uu____7416))
in (FStar_All.pipe_right keys uu____7405))
in (

let uu____7976 = (

let uu____7987 = (

let uu____7991 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____7991 (FStar_Util.sort_with FStar_String.compare)))
in (FStar_All.pipe_right uu____7987 (fun l -> (

let uu____8028 = (FStar_All.pipe_right l (FStar_List.filter (fun f -> (FStar_Util.set_mem f set_of_unchecked_files))))
in ((l), (uu____8028))))))
in (match (uu____7976) with
| (all_fst_files, all_unchecked_fst_files) -> begin
(

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____8086 = (FStar_Options.should_extract mname)
in (match (uu____8086) with
| true -> begin
(

let uu____8089 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____8089))
end
| uu____8092 -> begin
()
end))))));
(sort_output_files ml_file_map);
))
in (

let all_krml_files = (

let krml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right keys (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____8116 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____8116))))));
(sort_output_files krml_file_map);
))
in (

let rec make_transitive = (fun f -> (

let uu____8135 = (

let uu____8147 = (FStar_Util.smap_try_find transitive_krml f)
in (FStar_Util.must uu____8147))
in (match (uu____8135) with
| (exe, deps1, seen) -> begin
(match (seen) with
| true -> begin
((exe), (deps1))
end
| uu____8217 -> begin
((FStar_Util.smap_add transitive_krml f ((exe), (deps1), (true)));
(

let deps2 = (

let uu____8241 = (

let uu____8245 = (FStar_List.map (fun dep1 -> (

let uu____8261 = (make_transitive dep1)
in (match (uu____8261) with
| (uu____8273, deps2) -> begin
(dep1)::deps2
end))) deps1)
in (FStar_List.flatten uu____8245))
in (FStar_List.unique uu____8241))
in ((FStar_Util.smap_add transitive_krml f ((exe), (deps2), (true)));
((exe), (deps2));
));
)
end)
end)))
in ((

let uu____8309 = (FStar_Util.smap_keys transitive_krml)
in (FStar_List.iter (fun f -> (

let uu____8334 = (make_transitive f)
in (match (uu____8334) with
| (exe, deps1) -> begin
(

let deps2 = (

let uu____8355 = (FStar_List.unique ((f)::deps1))
in (FStar_String.concat " " uu____8355))
in (

let wasm = (

let uu____8364 = (FStar_Util.substring exe (Prims.parse_int "0") ((FStar_String.length exe) - (Prims.parse_int "4")))
in (Prims.strcat uu____8364 ".wasm"))
in ((FStar_Util.print2 "%s: %s\n\n" exe deps2);
(FStar_Util.print2 "%s: %s\n\n" wasm deps2);
)))
end))) uu____8309));
(

let uu____8373 = (

let uu____8375 = (FStar_All.pipe_right all_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8375 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8373));
(

let uu____8394 = (

let uu____8396 = (FStar_All.pipe_right all_unchecked_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8396 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n" uu____8394));
(

let uu____8415 = (

let uu____8417 = (FStar_All.pipe_right all_ml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8417 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8415));
(

let uu____8435 = (

let uu____8437 = (FStar_All.pipe_right all_krml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8437 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8435));
))))
end)))))))))))))


let print : deps  ->  unit = (fun deps -> (

let uu____8461 = (FStar_Options.dep ())
in (match (uu____8461) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(print_full deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph deps.dep_graph)
end
| FStar_Pervasives_Native.Some ("raw") -> begin
(print_raw deps)
end
| FStar_Pervasives_Native.Some (uu____8473) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))


let print_fsmap : (Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap  ->  Prims.string = (fun fsmap -> (FStar_Util.smap_fold fsmap (fun k uu____8528 s -> (match (uu____8528) with
| (v0, v1) -> begin
(

let uu____8557 = (

let uu____8559 = (FStar_Util.format3 "%s -> (%s, %s)" k (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1))
in (Prims.strcat "; " uu____8559))
in (Prims.strcat s uu____8557))
end)) ""))


let module_has_interface : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let uu____8580 = (

let uu____8582 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8582))
in (has_interface deps.file_system_map uu____8580)))


let deps_has_implementation : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let m = (

let uu____8598 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8598))
in (FStar_All.pipe_right deps.all_files (FStar_Util.for_some (fun f -> ((is_implementation f) && (

let uu____8609 = (

let uu____8611 = (module_name_of_file f)
in (FStar_String.lowercase uu____8611))
in (Prims.op_Equality uu____8609 m))))))))




