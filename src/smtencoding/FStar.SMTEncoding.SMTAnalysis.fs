#light "off"

module FStar.SMTEncoding.SMTAnalysis
open FStar
open FStar.All
open FStar.Range
open FStar.Util
module ST = FStar.SMTEncoding.Term
module SP = FStar.SMTEncoding.SMTProof

type fundecl_dict = psmap<smt_function>

let smt_sort_to_raw_sort (s : ST.sort) : SP.sort =
    match s with
      | ST.Bool_sort -> SP.Boolean
      | ST.Int_sort -> SP.Integer
      | ST.String_sort -> SP.String
      | ST.Term_sort -> SP.Term
      | ST.Fuel_sort -> SP.Fuel
      | _ -> failwith "Unsupported SMT sort"

let make_signature (l : decs_t)