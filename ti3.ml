module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Globals
open Cprinter
open Gen

let eq_str s1 s2 = (String.compare s1 s2) = 0

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)
    
let rec partition_eq eq ls = 
  match ls with
  | [] -> []
  | e::es -> 
    let eq_es, neq_es = List.partition (eq e) es in
    (e::eq_es)::(partition_eq eq neq_es)
    
(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: CP.formula;
  termr_fname: ident; (* Collect from RHS *)
  termr_lhs: CP.term_ann list;
  termr_rhs: CP.term_ann;
  termr_rhs_params: CP.spec_var list; (* For simplification on condition *)
}

let print_ret_trel rel = 
  string_of_trrel_assume (rel.ret_ctx, rel.termr_lhs, rel.termr_rhs)
  
(* Temporal Relation at Call *)
type call_trel = {
  trel_id: int;
  call_ctx: CP.formula;
  termu_fname: ident; (* Collect from LHS *)
  termu_lhs: CP.term_ann;
  termu_rhs: CP.term_ann;
  termu_rhs_params: CP.spec_var list; (* For substitution on condition *)
}

let print_call_trel_debug rel = 
  string_of_turel_debug (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)

let print_call_trel rel = 
  string_of_turel_assume (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)
  
let compare_trel r1 r2 = compare r1.trel_id r2.trel_id
  
let eq_trel r1 r2 = r1.trel_id == r2.trel_id

let dummy_trel = {
  trel_id = -1;
  call_ctx = CP.mkTrue no_pos;
  termu_fname = "";
  termu_lhs = CP.MayLoop;
  termu_rhs = CP.MayLoop; 
  termu_rhs_params = []; }
  
let update_call_trel rel ilhs irhs = 
  { rel with
    termu_lhs = ilhs;  
    termu_rhs = irhs; }

type tntrel =
  | Ret of ret_trel
  | Call of call_trel

let string_of_tntrel = function
  | Ret rrel -> "@Return: " ^ (print_ret_trel rrel)
  | Call crel -> "@Call: " ^ (print_call_trel crel)

let subst_cond_with_ann params ann cond =
  match ann with
  | CP.TermU uid
  | CP.TermR uid ->
    let args = uid.CP.tu_args in
    CP.subst_term_avoid_capture (List.combine params args) cond
  | _ -> cond

(* TNT Case Spec *)
type tnt_case_spec = 
  | Sol of (CP.term_ann * CP.exp list)
  | Unknown
  | Cases of (CP.formula * tnt_case_spec) list

let rec pr_tnt_case_spec (spec: tnt_case_spec) = 
  match spec with
  | Cases cl ->
    pr_args (Some("V",1)) (Some "A") "case " "{" "}" "" 
    (
      fun (c, s) -> wrap_box ("B",0) (pr_op_adhoc 
        (fun () -> pr_pure_formula c) " -> " )
        (fun () -> pr_tnt_case_spec s; fmt_string ";")
    ) cl 
  | Unknown -> (* fmt_string "Unk" *) fmt_string "requires MayLoop ensures true"
  | Sol (ann, rnk) ->
    match ann with
    | CP.Loop -> fmt_string "requires Loop ensures false"
    | _ -> 
      fmt_string "requires ";
      pr_var_measures (ann, rnk, []);
      fmt_string " ensures true"

let print_tnt_case_spec = poly_string_of_pr pr_tnt_case_spec

(* Utilities for Path Traces *)
type path_trace = (CP.spec_var * bool) list

type and_or_tree = 
  | TSgl of path_trace
  | TSeq of and_or_tree list
  | TPar of and_or_tree list

let print_path_trace pt =
  pr_list (fun (v, b) -> if b then (!CP.print_sv v) else "!" ^ (!CP.print_sv v)) pt

let rec print_and_or_tree t =
  match t with 
  | TSgl pt -> "TSgl " ^ (print_path_trace pt)
  | TSeq seq -> "TSeq {" ^ (pr_list print_and_or_tree seq) ^ "}"
  | TPar par -> "TPar [" ^ (pr_list print_and_or_tree par) ^ "]"

(* Tracking path of a formula *)
let path_of_formula f =
  let ls = CP.split_conjunctions f in
  let bvs = List.concat (List.map (fun f -> opt_to_list (CP.getBVar f)) ls) in
  let bvs = Gen.BList.remove_dups_eq (fun (v1, _) (v2, _) -> CP.eq_spec_var v1 v2) bvs in
  bvs
  
let eq_path_elem (v1, s1) (v2, s2) =
  (CP.eq_spec_var v1 v2) && (s1 == s2)  

 (* p1 and p2 are in the same sequence *)   
let eq_path p1 p2 =
  Gen.BList.list_setequal_eq eq_path_elem p1 p2
  
(* p1 is sub-path of p2 *)  
let is_sub_path p1 p2 = 
  (Gen.BList.subset_eq eq_path_elem p2 p1) &&
  (List.length p1 > List.length p2)
  
let rec eq_path_formula f1 f2 =
  let p1 = path_of_formula f1 in
  let p2 = path_of_formula f2 in
  eq_path p1 p2

(* This method assumes that the path_traces is sorted by length *)     
let rec and_or_tree_of_path_traces path_traces =
  match path_traces with
  | [] -> TSgl []
  | p::ps ->
    let p_len = List.length p in
    let same_len_p, others = List.partition (fun q -> (List.length q) == p_len) ps in
    let eq_path_grps = partition_eq eq_path (p::same_len_p) in 
    (* Group of same path traces *)
    match eq_path_grps with
    | [] -> and_or_tree_of_path_traces others
    | grp::[] -> and_tree_of_path_traces grp others
    | _ -> TPar (List.map (fun grp -> and_tree_of_path_traces grp others) eq_path_grps)
      
and and_tree_of_path_traces same_path_grp other_traces = 
  match same_path_grp with
  | [] -> and_or_tree_of_path_traces other_traces
  | s::_ -> 
    let sub_path_traces = List.filter (fun p -> is_sub_path p s) other_traces in
    let sgl_path_grp = List.map (fun p -> TSgl p) same_path_grp in
    match sub_path_traces with
    | [] -> begin match sgl_path_grp with
      | [] -> TSgl []
      | s::[] -> s
      | _ -> TSeq sgl_path_grp end
    | _ -> TSeq (sgl_path_grp @ [and_or_tree_of_path_traces sub_path_traces])

let and_or_tree_of_path_traces path_traces =
  let sorted_path_traces = List.sort (fun p1 p2 -> 
    compare (List.length p1) (List.length p2)) path_traces in
  and_or_tree_of_path_traces sorted_path_traces
  