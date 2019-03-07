#light "off"

module FStar.SMTEncoding.Analysis
open FStar
open FStar.All
open FStar.Common
open FStar.List
open FStar.Range
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util
open FStar.SMTEncoding.Term
open FStar.BaseTypes
module DEP = FStar.Parser.Dep

let max (i : int) (j : int) : int = if i < j then j else i

type pretty_alignment =
    | PrettyLeft
    | PrettyRight
    | PrettyMark of string

let prettyprint_table (fmt : list<pretty_alignment>) (tab : list<(list<string>)>) : string * int =
    let max (i : int) (j : int) : int = if i < j then j else i in
    let mark_split (align : pretty_alignment) (s : string) : (string * string) = match align with
        | PrettyLeft -> ("" , s)
        | PrettyRight -> (s , "")
        | PrettyMark sep -> 
            let spl : list<string> = split s sep in
            ((List.hd spl) ^ sep , List.tl spl |> String.concat sep)
    in
    let measure (align : pretty_alignment) ((l , r) : (int * int)) (s : string) : (int * int) =
        let (ls , rs) : (string * string) = mark_split align s in
        let (lx , rx) : (int * int) = (String.length ls , String.length rs) in
        ((max l lx) , (max r rx))
    in
    let rec maxlength (fmt : list<pretty_alignment>) (ln : list<(int * int)>) (row : list<string>) : list<(int * int)> = match (fmt , ln , row) with
        | (fmt_hd :: fmt_tl , ln_hd :: ln_tl , row_hd :: row_tl) ->
            (measure fmt_hd ln_hd row_hd) :: (maxlength fmt_tl ln_tl row_tl)
        | _ -> []
    in
    let maxlength_init : list<(int * int)> = tabulate (List.length fmt) (fun _ -> (0 , 0)) in
    let maxlength_list : list<(int * int)> = List.fold_left (maxlength fmt) maxlength_init tab in
    let totallength : int = List.fold_left (fun (x : int) ((l , r) : int * int) -> x + l + r) 0 maxlength_list in
    let enlarge ((sl , sr) : (string * string)) ((l , r) : (int * int)) : string =
        (repeat (l - String.length sl) " ") ^ sl ^ sr ^ (repeat (r - String.length sr) " ")
    in
    let rec enlarge_row (fmt : list<pretty_alignment>) (ln : list<(int * int)>) (row : list<string>) : list<string> = match (fmt , ln , row) with
        | (fmt_hd :: fmt_tl , (ln_l , ln_r) :: ln_tl , row_hd :: row_tl) ->
            let (sl , sr) : (string * string) = mark_split fmt_hd row_hd in
            (enlarge (sl , sr) (ln_l , ln_r)) :: (enlarge_row fmt_tl ln_tl row_tl)
        | _ -> []
    in
    let lines : list<string> = List.map (enlarge_row fmt maxlength_list) tab |> List.map (fun l -> String.concat "  " l) in
    let totallength : int = List.fold_left (fun (x : int) (s : string) -> max x (String.length s)) 0 lines in
    (lines |> String.concat "\n" , totallength)

type query_info = {
    query_info_name    : string ;
    query_info_index   : int ;
    query_info_range   : Range.range ;
}

type qiprofile_map = psmap<(int * int * int)>

type quantifier_info = {
    quantifier_info_query : query_info ;
    quantifier_info_quantifier : term ;
    quantifier_info_context : term ;
}

type qiprofile = {
    qiprofile_id : string ;
    qiprofile_quantifiers : list<quantifier_info> ;
    qiprofile_instances : int ;
    qiprofile_generation : int ;
    qiprofile_cost : int ;
}

let query_name (q : query_info) : string =
    let fn : string = file_of_range q.query_info_range in
    let rg : string = if String.length fn = 0 || char_at fn 0 = '<' then "" else
        let s1 : string = q.query_info_range |> end_of_range |> string_of_pos in
        let s2 : string = q.query_info_range |> end_of_range |> string_of_pos in
        format " (%s-%s)" [s1 ; s2]
    in
    "(" ^ q.query_info_name ^ " , " ^ (string_of_int q.query_info_index) ^ ") from " ^ fn ^ rg

let quantifier_file (q : quantifier_info) : string = file_of_range (q.quantifier_info_quantifier.rng)

let quantifier_module (q : quantifier_info) : string =
    let fn : string = quantifier_file q in
    if String.length fn = 0 || char_at fn 0 = '<' then fn else DEP.module_name_of_file fn

let quantifier_range (q : quantifier_info) : string =
    let fn : string = quantifier_file q in
    if String.length fn = 0 || char_at fn 0 = '<' then "" else
        let s1 : string = q.quantifier_info_quantifier.rng |> end_of_range |> string_of_pos in
        let s2 : string = q.quantifier_info_quantifier.rng |> end_of_range |> string_of_pos in
        format "(%s-%s)" [s1 ; s2]

let parse_qiprofile (s : string) : qiprofile_map =
    let parse_line (line : string) : option<(string * int * int * int)> =
        if starts_with line "[quantifier_instances]" then begin
            match split (substring_from line 22) ":" |> List.map trim_string with
                | [id ; inst ; gen ; cost] -> Some (id , int_of_string inst , int_of_string gen , int_of_string cost)
                | _ -> failwith "could not parse quantifier instantiation info"
        end else None
    in
    let comp ((qid1 , inst1 , gen1 , cost1) : string * int * int * int) ((qid2 , inst2 , gen2 , cost2) : string * int * int * int) : int = 
        compare qid1 qid2
    in
    let conflate (l : list<(string * int * int * int)>): list<(string * int * int * int)> =
        let rec aux (qid : string) (inst : int) (gen : int) (cost : int) (l : list<(string * int * int * int)>) (o : list<(string * int * int * int)>) =
            match l with
                | [] -> List.rev ((qid , inst , gen , cost) :: o)
                | (hd_qid , hd_inst , hd_gen , hd_cost) :: tl ->
                    if hd_qid = qid then aux qid (inst + hd_inst) (max gen hd_gen) (max cost hd_cost) tl o
                    else aux hd_qid hd_inst hd_gen hd_cost tl ((qid , inst , gen , cost) :: o)
        in
        match l with
            | [] -> []
            | (qid , inst , gen , cost) :: tl -> aux qid inst gen cost l []
    in
    let add (o : qiprofile_map) ((qid , inst , gen , cost) : (string * int * int * int)) : qiprofile_map =
        psmap_add o qid (inst , gen , cost)
    in
    String.split ['\n'] s |>
        List.map trim_string |>
        List.map parse_line |>
        collect_some |>
        sort_with comp |>
        conflate |>
        List.fold_left add (psmap_empty ())
    

let rec extract_quantifiers_from_decls (query : query_info) (decl : decl) : list<(string * quantifier_info)> =
    let from_term (context : term) (tm0 : term) : list<(string * quantifier_info)> =
        let rec aux (tm : term) : list<(string * quantifier_info)> = match tm.tm with
            | App (_ , tms) -> List.flatten (List.map aux tms)
            | Quant (_ , _ , _ , _ , t , qid) -> begin match !qid with
                | Some id -> (id , {
                        quantifier_info_query = query ;
                        quantifier_info_quantifier = tm ;
                        quantifier_info_context = context }) :: (aux t)
                | None -> failwith "No QID found"
            end
            | Let (tms , t) -> (aux t) @ (List.collect aux tms)
            | Labeled (t , _ , _)
            | LblPos (t , _) -> aux t
            | _ -> []
        in
        aux tm0
    in
    match decl with
        | DefineFun (nm , args , ret , tm , _) -> from_term tm tm
        | Assume a -> from_term a.assumption_term a.assumption_term
        | Module (s , ds) -> extract_quantifiers (query , ds)
        | _ -> []

and extract_quantifiers ((query , decls) : query_info * list<decl>) : list<(string * quantifier_info)> =
    List.fold_left (fun (l : list<(string * quantifier_info)>) (d : decl) -> (extract_quantifiers_from_decls query d) @ l) [] decls
    

let profile_quantifiers (queries : list<(query_info * list<decl>)>) (qiprofile_output : string) : psmap<qiprofile> =
    let comp ((id1 , q1) : (string * quantifier_info)) ((id2 , q2) : (string * quantifier_info)) : int = 
        compare id1 id2
    in
    let conflate (l : list<(string * quantifier_info)>) : list<(string * list<quantifier_info>)> =
        let rec aux (i : list<(string * quantifier_info)>) (id : string) (ls : list<quantifier_info>) (o : list<(string * list<quantifier_info>)>) : list<(string * list<quantifier_info>)> =
            match i with
                | (idx , qinfo) :: tl ->
                    if id = idx then aux tl id (qinfo :: ls) o
                    else aux tl idx [qinfo] ((id , List.rev ls) :: o)
                | [] -> (id , List.rev ls) :: o
        in
        match l with
            | [] -> []
            | (s , q) :: tl -> List.rev (aux tl s [q] [])
    in
    let qip : qiprofile_map = parse_qiprofile qiprofile_output in
    let insert (o : psmap<qiprofile>) ((id , info) : string * list<quantifier_info>) : psmap<qiprofile> =
        let (inst , gen , cost) : (int * int * int) = match psmap_try_find qip id with
            | None -> (0 , 0 , 0)
            | Some x -> x
        in
        let value = {
            qiprofile_id = id ;
            qiprofile_quantifiers = info ;
            qiprofile_instances = inst ;
            qiprofile_generation = gen ;
            qiprofile_cost = cost ; }
        in
        psmap_add o id value
    in
    List.collect extract_quantifiers queries |> 
    sort_with comp |>
    conflate |>
    List.fold_left insert (psmap_empty ())

let tabular_profile (q : psmap<qiprofile>) : list<(list<string>)> =
    let comp ((i1 , q1) : int * string) ((i2 , q2) : int * string) : int = if i1 < i2 then 1 else (if i1 > i2 then -1 else 0) in
    let qid_to_tail_rows (info : quantifier_info) : list<string> =
        [ "" ; "" ; quantifier_module info ; quantifier_file info ; quantifier_range info ]
    in
    let qid_to_rows (o : list<(list<string>)>) (k : string) : list<(list<string>)> =
        let prof : qiprofile = must (psmap_try_find q k) in
        if prof.qiprofile_instances > 0 then
            match prof.qiprofile_quantifiers with
                | [] -> failwith "QID not found"
                | hd :: tl ->
                    o @ ([ prof.qiprofile_id ;
                            string_of_int (prof.qiprofile_instances) ;
                            quantifier_module hd ;
                            quantifier_file hd ;
                            quantifier_range hd ] :: (List.map qid_to_tail_rows tl))
        else o
    in
    psmap_fold q (fun (k : string) (v : qiprofile) (acc : list<(int * string)>) -> (v.qiprofile_instances , k) :: acc) [] |>
    sort_with comp |>
    List.map (fun ((i , q) : int * string) -> q) |>
    List.fold_left qid_to_rows []
    
let qiprofile_analysis (queries : list<(query_info * list<decl>)>) (qiprofile_output : string) : unit =
    match queries with
        | [] -> ()
        | _ -> 
            let q : psmap<qiprofile> = profile_quantifiers queries qiprofile_output in
            let tab : list<(list<string>)> = tabular_profile q in
            let fmt : list<pretty_alignment> = [PrettyRight ; PrettyRight ; PrettyLeft ; PrettyRight ; PrettyLeft] in
            let (content_string , content_length) : string * int = prettyprint_table fmt tab in
            let (header_string , header_length) : string * int =
                let headers : list<string> = queries |> List.map (fun ((q , ds) : query_info * list<decl>) -> query_name q) in
                String.concat "\n" headers , List.fold_left (fun (x : int) (s : string) -> max x (String.length s)) 0 headers
            in
            let line : string = repeat (max content_length header_length) "-" in
            print (line ^ "\n" ^ header_string ^ "\n" ^ line ^ "\n" ^ content_string ^ "\n" ^ line ^ "\n\n" ) []


// type quantifier_info = {
//     qid         : string ;
//     quantifier  : term ;
//     context     : term ;
//     profile     : option<qi_info> ;
// }

// type functor_info = {
//     fid         : string ;
//     sort        : list<sort> * sort ;
//     definition  : option<term> ;
//     // modul       : string ;
// }

// type assumption_info = {
//     aid         : string ;
//     term        : term ;
//     // modul       : string ;
// }

// type list_query_analytics = {
//     list_query_quantifiers : list<quantifier_info> ;
//     list_query_assumptions : list<assumption_info> ;
//     list_query_functors    : list<functor_info> ;
// }

// type query_analytics = {
//     query_analytics_info        : query_info ;
//     query_analytics_quantifiers : psmap<quantifier_info> ;
//     query_analytics_assumptions : psmap<assumption_info> ;
//     query_analytics_functors    : psmap<functor_info> ;
// }

// let query_name (q : query_info) : string =
//     "(" ^ q.query_info_name ^ ", " ^ (string_of_int q.query_info_index) ^ ")"

// let quantifier_instances (q : quantifier_info) : int = match q.profile with
//     | None -> 0
//     | Some qip -> qip.instances

// let list_to_map_info (qr : query_info) (l : list_query_analytics) : query_analytics =
//     let qfun (m : psmap<quantifier_info>) (q : quantifier_info) : psmap<quantifier_info> =
//         psmap_add m (q.qid) q
//     in
//     let afun (m : psmap<assumption_info>) (a : assumption_info) : psmap<assumption_info> =
//         psmap_add m (a.aid) a
//     in
//     let ffun (m : psmap<functor_info>) (f : functor_info) : psmap<functor_info> =
//         psmap_add m (f.fid) f
//     in
//     ({
//         query_analytics_info        = qr ;
//         query_analytics_quantifiers = (List.fold_left qfun (psmap_empty ()) (l.list_query_quantifiers)) ;
//         query_analytics_assumptions = (List.fold_left afun (psmap_empty ()) (l.list_query_assumptions)) ;
//         query_analytics_functors    = (List.fold_left ffun (psmap_empty ()) (l.list_query_functors)) ;
//     })

// let analyze_term (qip : qi_profile) (ctx : term) : list<quantifier_info> =
//     let rec aux (tm : term) : list<quantifier_info> = match tm.tm with
//         | App (_ , tms) -> List.flatten (List.map aux tms)
//         | Quant (_ , _ , _ , _ , t , qid) -> begin match !qid with
//                 | Some id -> {
//                         qid = id ;
//                         quantifier = tm ;
//                         context = ctx ;
//                         profile = psmap_try_find qip id ; } :: (aux t)
//                 | None -> print "No QID found" [] ; (aux t)
//             end
//         | Let (tms , t) ->
//             (aux t) @ (List.flatten (List.map aux tms))
//         | Labeled (t , _ , _)
//         | LblPos (t , _) -> aux t
//         | _ -> []
//     in
//     aux ctx

// let rec analyze_decl (qip : qi_profile) (info : list_query_analytics) (decl : decl) : list_query_analytics =
//     match decl with
//         | DeclFun (nm , args , ret , _) ->
//             let finfo : functor_info = {fid = nm ; sort = args , ret ; definition = None } in
//             {info with list_query_functors = finfo :: info.list_query_functors }
//         | DefineFun (nm , args , ret , tm , _) ->
//             let finfo : functor_info = {fid = nm ; sort = args , ret ; definition = Some tm } in
//             let qinfos : list<quantifier_info> = analyze_term qip tm in
//             {info with list_query_functors = finfo :: info.list_query_functors ; list_query_quantifiers = qinfos @ info.list_query_quantifiers}
//         | Assume a ->
//             let ainfo : assumption_info = {aid = a.assumption_name ; term = a.assumption_term } in
//             let qinfos : list<quantifier_info> = analyze_term qip a.assumption_term in
//             {info with list_query_assumptions = ainfo :: info.list_query_assumptions ; list_query_quantifiers = qinfos @ info.list_query_quantifiers }
//         | Module (s , ds) -> List.fold_left (analyze_decl qip) info ds
//         | _ -> info

// let print_quantifiers (qa : query_analytics) : unit =
//     let q : psmap<quantifier_info> = qa.query_analytics_quantifiers in
//     let comp (qi1 : quantifier_info) (qi2 : quantifier_info) : int = match (qi1.profile , qi2.profile) with
//         | (Some x1 , Some x2) -> let (y1 , y2) = (x1.instances , x2.instances) in if y1 < y2 then 1 else (if y1 = y2 then 0 else -1)
//         | _ -> 0
//     in
//     let ls : list<quantifier_info> = psmap_fold q (fun (k : string) (qi : quantifier_info) (l : list<quantifier_info>) -> qi :: l) []
//             |> List.filter (fun (qi : quantifier_info) -> is_some qi.profile)
//             |> sort_with comp
//     in
//     let qi_to_range (qi :quantifier_info) : string =
//         string_of_range (qi.context.rng)
//     in
//     let qi_to_module (qi : quantifier_info) : string =
//         let fn : string = file_of_range (qi.context.rng) in
//         if String.length fn = 0 || char_at fn 0 = '<' then fn else DEP.module_name_of_file fn
//     in
//     let to_row (qi : quantifier_info) : list<string> =
//         [qi.qid ; string_of_int ((Option.get (qi.profile)).instances) ; qi_to_module qi ; qi_to_range qi]
//     in
//     let row_format : list<pretty_alignment> = [PrettyRight ; PrettyRight ; PrettyLeft ; PrettyMark "("] in
//     let contents : string = (List.map to_row ls) |> prettyprint_table row_format in
//     let header : string = "\n\n< Quantifier instantiantions for query " ^ query_name qa.query_analytics_info ^ " >\n" in
//     print (header ^ contents ^ "\n") []

// let analyze_query (r : z3result) : unit =
//     let empty : list_query_analytics = {
//         list_query_quantifiers = [] ;
//         list_query_assumptions = [] ;
//         list_query_functors = [] ; }
//     in
//     let list_info : list_query_analytics = List.fold_left (analyze_decl r.z3result_qiprofile) empty r.z3result_query_decls in
//     let info : query_analytics = list_to_map_info r.z3result_query_info list_info in
//     print_quantifiers (info)
