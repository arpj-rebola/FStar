#light "off"

module FStar.SMTEncoding.Analysis
open FStar.Range
open FStar.SMTEncoding.Term

type query_info = {
    query_info_name    : string ;
    query_info_index   : int ;
    query_info_range   : range ;
}

val qiprofile_analysis : list<(query_info * decls_t)> -> string -> unit

