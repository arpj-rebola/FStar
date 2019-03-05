#light "off"
module FStar.Ident
open Prims
open FStar.ST
open FStar.All
open FStar.Range

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type ident = {idText:string;
              idRange:Range.range}

type path = list<string>

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type lident = {ns:list<ident>; //["FStar"; "Basic"]
               ident:ident;    //"lident"
               nsstr:string; // Cached version of the namespace
               str:string} // Cached version of string_of_lid

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type lid = lident

let mk_ident ((text,range) : string * Range.range) : ident = {idText=text; idRange=range}
let reserved_prefix : string = "uu___"
let _gen : Range.range -> ident =
    let x = Util.mk_ref 0 in
    fun r -> x := !x + 1; mk_ident (reserved_prefix ^ string_of_int !x, r)
let gen (r : Range.range) : ident = _gen r // need this indirection for F#, ugh

let range_of_id (id:ident) : Range.range = id.idRange
let id_of_text (str : string) : ident = mk_ident(str, dummyRange)
let text_of_id (id:ident) : string = id.idText
let text_of_path (path : list<string>) : string = Util.concat_l "." path
let path_of_text (text : string) : list<string> = String.split ['.'] text
let path_of_ns (ns : list<ident>) : list<string> = List.map text_of_id ns
let path_of_lid (lid : lident) : list<string> = List.map text_of_id (lid.ns@[lid.ident])
let ids_of_lid (lid : lident) : list<ident> = lid.ns@[lid.ident]
let lid_of_ns_and_id (ns : list<ident>) (id : ident) : lident =
    let nsstr : string = List.map text_of_id ns |> text_of_path in
    {ns=ns;
     ident=id;
     nsstr=nsstr;
     str=(if nsstr="" then id.idText else nsstr ^ "." ^ id.idText)}
let lid_of_ids (ids : list<ident>) : lident =
    let (ns, id) : (list<ident> * ident) = Util.prefix ids in
    lid_of_ns_and_id ns id
let lid_of_str (str : string) : lident =
    lid_of_ids (List.map id_of_text (Util.split str "."))
let lid_of_path (path : list<string>) (pos : Range.range) : lident =
    let ids : list<ident> = List.map (fun s -> mk_ident(s, pos)) path in
    lid_of_ids ids
let text_of_lid (lid : lident) = lid.str
let lid_equals (l1 : lident) (l2 : lident) : bool = l1.str = l2.str
let ident_equals (id1 : ident) (id2 : ident) : bool = id1.idText = id2.idText
let range_of_lid (lid:lid) : Range.range = range_of_id lid.ident
let set_lid_range (l : lident) (r : Range.range) = {l with ident={l.ident with idRange=r}}
let lid_add_suffix (l : lident) (s : string) : lident =
    let path = path_of_lid l in
    lid_of_path (path@[s]) (range_of_lid l)
let ml_path_of_lid (lid : lident) : string = String.concat "_" <| (path_of_ns lid.ns)@[text_of_id lid.ident]

let string_of_ident (id : ident) : string = id.idText

(* JP: I don't understand why a lid has both a str and a semantic list of
 * namespaces followed by a lowercase identifiers... *)
let string_of_lid (lid : lident) : string = text_of_path (path_of_lid lid)
