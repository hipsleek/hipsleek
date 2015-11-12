#include "xdebug.cppo"

open Cast
open Globals
open VarGen
open Gen.Basic

module CP = Cpure

let is_prim_proc prog id = 
  try
    let proc = Hashtbl.find prog.new_proc_decls id in
    not proc.proc_is_main
  with _ -> true

let is_prim_proc prog id = 
  Debug.no_1 "is_prim_proc" idf string_of_bool
    (fun _ -> is_prim_proc prog id) id

let is_rec_proc prog mn = 
  try
    let proc = find_proc prog mn in
    proc.proc_is_recursive
  with _ -> false

let rec_calls_of_exp exp = 
  let f exp = 
    match exp with
    | ICall e -> if e.exp_icall_is_rec then Some ([e.exp_icall_method_name]) else None
    | SCall e -> if e.exp_scall_is_rec then Some ([e.exp_scall_method_name]) else None
    | _ -> None
  in fold_exp exp f List.concat []

let callees_of_exp prog exp = 
  let f_call mn =
    try
      let proc = Hashtbl.find prog.new_proc_decls mn in
      if proc.proc_is_main then Some [proc] 
      else None
    with _ -> None  
  in
  let f exp = 
    match exp with
    | ICall e -> f_call e.exp_icall_method_name
    | SCall e -> f_call e.exp_scall_method_name
    | _ -> None
  in fold_exp exp f List.concat []

let has_ref_params prog mn =
  try
    let proc = find_proc prog mn in
    proc.proc_by_name_params != []
  with _ -> false

let has_named_params prog mn =
  try
    let proc = find_proc prog mn in
    List.exists (fun (t, _) -> is_node_typ t) proc.proc_args
  with _ -> false

let set_inf_obj_proc itype proc = 
  (* let n_static_specs = Cformula.set_inf_obj_struc itype proc.proc_static_specs in *)
  let n_static_specs = Cformula.set_inf_obj_struc itype (proc.proc_stk_of_static_specs # top) in
  let n_dynamic_specs = Cformula.set_inf_obj_struc itype proc.proc_dynamic_specs in
  let () = proc.proc_stk_of_static_specs # push_pr x_loc n_static_specs in
  { proc with 
    (* proc_static_specs = n_static_specs; *)
    proc_dynamic_specs = n_dynamic_specs; }

let eq_str s1 s2 = String.compare s1 s2 == 0

let remove_dups_id = Gen.BList.remove_dups_eq eq_str

let diff_id = Gen.BList.difference_eq eq_str

let eq_proc p1 p2 = eq_str p1.proc_name p2.proc_name

let remove_dups_proc = Gen.BList.remove_dups_eq eq_proc

let diff_proc = Gen.BList.difference_eq eq_proc

(*********************************************)
(* Call graph to track the sequence of calls *)
(*********************************************)
let eq_num_ident (s1, i1) (s2, i2) =
  (i1 == i2) && (String.compare s1 s2 == 0)

let remove_dups_nid = Gen.BList.remove_dups_eq eq_num_ident

let diff_nid = Gen.BList.difference_eq eq_num_ident

let print_num_ident (s, i) =
  s ^ (if i >= 0 then (":" ^ (string_of_int i)) else "") 

module NumIdent = struct
  type t = ident * int
  let compare (i1, n1) (i2, n2) = 
    let ic = compare i1 i2 in
    if ic == 0 then compare n1 n2
    else ic  
  let hash = Hashtbl.hash
  let equal = eq_num_ident
end

module CG = Graph.Persistent.Digraph.Concrete(NumIdent)
module CGO = Graph.Oper.P(CG)

let print_call_seq_graph csg = 
  CG.fold_edges (fun s d a -> 
      "\n" ^ (print_num_ident s) ^ " -> " ^ (print_num_ident d) ^ a)  csg ""

let call_seq_graph_of_exp prog mn exp : CG.t = 
  let helper_call cg index roots ce =
    if is_prim_proc prog ce then cg, roots, index
    else
      let dst = (ce, index) in
      let n_cg = List.fold_left (fun g r -> CG.add_edge g r dst) (CG.add_vertex cg dst) roots in
      n_cg, [dst], index + 1 
  in
  let rec helper cg roots index exp : (CG.t * NumIdent.t list * int) = 
    match exp with
    | Label e -> helper cg roots index e.exp_label_exp
    | Assign e -> helper cg roots index e.exp_assign_rhs
    | Bind e -> helper cg roots index e.exp_bind_body
    | Block e -> helper cg roots index e.exp_block_body
    | Cond e -> 
      let n_cg, then_n_roots, n_index = helper cg roots index e.exp_cond_then_arm in
      let n_cg, else_n_roots, n_index = helper cg roots n_index e.exp_cond_else_arm in
      n_cg, then_n_roots @ else_n_roots, n_index
    | Cast e -> helper cg roots index e.exp_cast_body
    | Catch e -> helper cg roots index e.exp_catch_body
    | ICall e -> helper_call cg index roots e.exp_icall_method_name
    | SCall e -> helper_call cg index roots e.exp_scall_method_name
    | Seq e ->
      let n_cg, n_roots, n_index = helper cg roots index e.exp_seq_exp1 in
      helper n_cg n_roots n_index e.exp_seq_exp2
    | While e -> helper cg roots index e.exp_while_body
    | Try e -> helper cg roots index e.exp_try_body
    | _ -> cg, roots, index
  in
  let init_index = 0 in
  let cg, _, _ = helper CG.empty [(mn, init_index)] (init_index + 1) exp in
  cg

let call_seq_graph_of_exp prog mn exp =
  Debug.no_1 "call_seq_graph_of_exp" idf print_call_seq_graph
    (fun _ -> call_seq_graph_of_exp prog mn exp) mn

let call_seq_graph_of_proc prog proc =
  match proc.proc_body with
  | None -> CG.empty
  | Some e -> call_seq_graph_of_exp prog proc.proc_name e

let csg_proc_tbl: (ident, CG.t) Hashtbl.t = Hashtbl.create 20

let build_csg_proc_tbl prog = 
  Hashtbl.iter 
    (fun _ proc ->
      if proc.proc_is_main then
        Hashtbl.add csg_proc_tbl proc.proc_name (call_seq_graph_of_proc prog proc)
      else ()) 
    prog.new_proc_decls
  
(*************************************************)
(* Construct a data dependency graph from an exp *)
(*************************************************)
let print_data_dependency_graph ddg = 
  IG.fold_edges (fun s d a -> "\n" ^ s ^ " -> " ^ d ^ a)  ddg ""

let data_dependency_graph_of_call_exp prog ddg src mn args =
  if is_prim_proc prog mn then
    match src with
    | None -> ddg
    | Some v -> List.fold_left (fun g i -> IG.add_edge g v i) ddg args
  else
    (* Method call depends on its arguments *)
    let ddg = List.fold_left (fun g i -> IG.add_edge g mn i) ddg args in
    (* Pass-by-name (ref) parameters depend on their method call *)
    let mn_decl = look_up_proc_def_raw prog.new_proc_decls mn in
    let by_name_params = mn_decl.proc_by_name_params in
    let ddg = List.fold_left (fun g (arg, par) ->
        if List.exists (fun sv -> eq_str (P.name_of_spec_var sv) (snd arg)) by_name_params 
        then IG.add_edge g par mn
        else g) ddg (List.combine mn_decl.proc_args args) 
    in
    (* Src depends on the method call *) 
    match src with
    | None -> ddg
    | Some v -> IG.add_edge ddg v mn

let data_dependency_graph_of_exp prog mn exp =
  (* src depends on exp *)
  let rec helper ddg src exp = 
    match exp with
    | Label e -> helper ddg src e.exp_label_exp
    | Assign e ->
      (* let ddg = IG.add_edge ddg src e.exp_assign_lhs in *)
      helper ddg (Some e.exp_assign_lhs) e.exp_assign_rhs
    | Bind e ->
      let bvar = snd e.exp_bind_bound_var in
      (* let ddg = IG.add_edge ddg src bvar in *)
      let ddg = List.fold_left (fun g (_, i) ->
          IG.add_edge g bvar i) ddg e.exp_bind_fields in
      helper ddg (Some bvar) e.exp_bind_body
    | Block e -> helper ddg src e.exp_block_body
    | Cond e ->
      let ddg = IG.add_edge ddg mn e.exp_cond_condition in
      let ddg = helper ddg src e.exp_cond_then_arm in
      helper ddg src e.exp_cond_else_arm
    | Cast e -> helper ddg src e.exp_cast_body 
    | Catch e -> helper ddg src e.exp_catch_body 
    | ICall e -> 
      data_dependency_graph_of_call_exp prog ddg src e.exp_icall_method_name e.exp_icall_arguments
    | SCall e -> 
      data_dependency_graph_of_call_exp prog ddg src e.exp_scall_method_name e.exp_scall_arguments
    | Seq e ->
      let ddg = helper ddg src e.exp_seq_exp1 in
      helper ddg src e.exp_seq_exp2
    | Var e ->
        (match src with 
        | Some v -> IG.add_edge ddg v e.exp_var_name
        | None -> ddg)
    | While e -> 
      let ddg = IG.add_edge ddg mn e.exp_while_condition in
      helper ddg src e.exp_while_body
    | Try e ->
      let ddg = helper ddg src e.exp_try_body in
      helper ddg src e.exp_catch_clause
    | _ -> ddg
  in helper (IG.empty) None exp

let data_dependency_graph_of_exp prog mn exp =
  Debug.no_1 "data_dependency_graph_of_exp" idf print_data_dependency_graph
    (fun _ -> data_dependency_graph_of_exp prog mn exp) mn

let data_dependency_graph_of_proc prog proc =
  match proc.proc_body with
  | None -> IG.empty
  | Some e -> data_dependency_graph_of_exp prog proc.proc_name e

let ddg_proc_tbl: (ident, IG.t) Hashtbl.t = Hashtbl.create 20

let build_ddg_proc_tbl prog = 
  Hashtbl.iter 
    (fun _ proc ->
      if proc.proc_is_main then
        Hashtbl.add ddg_proc_tbl proc.proc_name (data_dependency_graph_of_proc prog proc)
      else ()) 
    prog.new_proc_decls

(***********************)
(* Unified ddg and csg *)
(***********************)
let var_index = -1 (* For normal vars *)
let root_index = 0

let seq_data_dependency_graph_of_call_exp prog ddg src index mn args =
  let args = List.map (fun v -> (v, var_index)) args in
  if is_prim_proc prog mn then
    let ddg = 
      if (snd src == root_index) then ddg
      else List.fold_left (fun g i -> CG.add_edge g src i) ddg args
    in ddg, index
  else
    (* Method call depends on its arguments *)
    let ddg = List.fold_left (fun g i -> CG.add_edge g (mn, index) i) ddg args in
    (* Pass-by-name (ref) parameters depend on their method call *)
    let mn_decl = look_up_proc_def_raw prog.new_proc_decls mn in
    let by_name_params = 
      mn_decl.proc_by_name_params @
      List.filter CP.is_node_typ mn_decl.proc_by_value_params 
    in
    let () = y_tinfo_hp (add_str (mn ^ ":by_name_params") !CP.print_svl) by_name_params in
    let ddg = List.fold_left (fun g (arg, par) ->
        if List.exists (fun sv -> eq_str (P.name_of_spec_var sv) (snd arg)) by_name_params 
        then CG.add_edge g par (mn, index)
        else g) ddg (List.combine mn_decl.proc_args args) 
    in
    (* Src depends on the method call *) 
    let ddg =
      if (snd src == root_index) then ddg
      else CG.add_edge ddg src (mn, index)
    in ddg, index + 1

let seq_data_dependency_graph_of_exp prog mn exp : CG.t =
  (* src depends on exp *)
  let rec helper ddg src index exp : (CG.t * int) = 
    match exp with
    | Label e -> helper ddg src index e.exp_label_exp
    | Assign e -> helper ddg (e.exp_assign_lhs, var_index) index e.exp_assign_rhs
    | Bind e ->
      let bvar = snd e.exp_bind_bound_var in
      if e.exp_bind_read_only then (* READ *)
        let ddg = List.fold_left (fun g (_, i) ->
            CG.add_edge g (i, var_index) (bvar, var_index)) ddg e.exp_bind_fields
        in
        helper ddg src index e.exp_bind_body
      else (* WRITE *)
        let ddg = List.fold_left (fun g (_, i) ->
            CG.add_edge g (bvar, var_index) (i, var_index)) ddg e.exp_bind_fields in
        helper ddg (bvar, var_index) index e.exp_bind_body
    | Block e -> helper ddg src index e.exp_block_body
    | Cond e ->
      let ddg = CG.add_edge ddg (mn, root_index) (e.exp_cond_condition, var_index) in
      let ddg, n_index = helper ddg src index e.exp_cond_then_arm in
      helper ddg src n_index e.exp_cond_else_arm
    | Cast e -> helper ddg src index e.exp_cast_body 
    | Catch e -> helper ddg src index e.exp_catch_body 
    | ICall e -> 
      seq_data_dependency_graph_of_call_exp prog ddg src index e.exp_icall_method_name e.exp_icall_arguments
    | SCall e -> 
      seq_data_dependency_graph_of_call_exp prog ddg src index e.exp_scall_method_name e.exp_scall_arguments
    | Seq e ->
      let ddg, n_index = helper ddg src index e.exp_seq_exp1 in
      helper ddg src n_index e.exp_seq_exp2
    | Var e ->
      let ddg = 
        if (snd src == root_index) then ddg
        else CG.add_edge ddg src (e.exp_var_name, var_index)
      in ddg, index
    | While e -> 
      let ddg = CG.add_edge ddg (mn, root_index) (e.exp_while_condition, var_index) in
      helper ddg src index e.exp_while_body
    | Try e ->
      let ddg, n_index = helper ddg src index e.exp_try_body in
      helper ddg src n_index e.exp_catch_clause
    | _ -> ddg, index
  in 
  let cg, _ = helper (CG.empty) (mn, root_index) (root_index + 1) exp in
  cg

let seq_data_dependency_graph_of_exp prog mn exp =
  Debug.no_1 "seq_data_dependency_graph_of_exp" idf print_call_seq_graph
    (fun _ -> seq_data_dependency_graph_of_exp prog mn exp) mn

let seq_data_dependency_graph_of_proc prog proc =
  match proc.proc_body with
  | None -> CG.empty, CG.empty
  | Some e ->
    let sdg = seq_data_dependency_graph_of_exp prog proc.proc_name e in
    let trans_sdg = CGO.transitive_closure ~reflexive:true sdg in
    sdg, trans_sdg

let sdg_proc_tbl: (ident, CG.t * CG.t) Hashtbl.t = Hashtbl.create 20

let build_sdg_proc_tbl prog = 
  Hashtbl.iter 
    (fun _ proc ->
      if proc.proc_is_main then
        Hashtbl.add sdg_proc_tbl proc.proc_name (seq_data_dependency_graph_of_proc prog proc)
      else ()) 
    prog.new_proc_decls

(* dst is data dependent on src 
 * iff there is a path of ddg from dst to src *)
let is_data_dependent trans_ddg src dst = 
  (* let checker = PCG.create ddg in    *)
  (* try PCG.check_path checker dst src *)
  (* with _ -> false                    *)
  IG.mem_edge trans_ddg dst src

let is_data_dependent trans_ddg src dst = 
  Debug.no_2 "is_data_dependent" idf idf string_of_bool
    (fun _ _ -> is_data_dependent trans_ddg src dst) src dst

(* Note: call_seq_graph csg is acyclic *)
(* We must infer post-condition of a method    *)
(* if a successor in the call sequence depends *)
(* on its output.                              *)
let should_infer_post_for_call csg trans_ddg src =
  let rec helper ws analyzed_calls =
    let succ = List.concat (List.map (fun s -> CG.succ csg s) ws) in
    if is_empty succ then false
    else
      let succ = remove_dups_nid succ in
      let not_analyzed_calls = diff_id (List.map fst succ) analyzed_calls in
      let mn = fst src in
      try
        let dependent_call = List.find (fun dst -> is_data_dependent trans_ddg mn dst) not_analyzed_calls in
        let () = x_binfo_pp ("@post is added into " ^ mn ^ " for " ^ dependent_call) no_pos in
        true
      with Not_found -> helper succ (analyzed_calls @ not_analyzed_calls)
  in helper [src] []

let collect_cond_depend_procs root sdg = 
  let rec helper curr ws = 
    let succ = List.concat (List.map (fun v -> CG.succ sdg v) curr) in
    let depend_procs, n_curr = List.partition (fun (_, i) -> i > root_index) succ in
    let n_curr = remove_dups_nid (diff_nid n_curr ws) in
    match n_curr with
    | [] -> depend_procs
    | _ -> depend_procs @ (helper n_curr (ws @ curr))
  in helper (CG.succ sdg root) []

let collect_infer_post_procs_for_tnt_acc acc prog proc =
  match proc.proc_body with
  | None -> acc
  | Some e -> 
    let mn = proc.proc_name in
    let () = x_binfo_pp ("Analyzing data dependence on the body of " ^ mn ^ " ...") no_pos in
    (* let csg = call_seq_graph_of_exp prog mn e in                                                     *)
    (* let ddg = data_dependency_graph_of_exp prog mn e in                                              *)
    (* let trans_ddg = IGO.transitive_closure ~reflexive:true ddg in                                    *)
    (* let root = (mn, 0) in                                                                            *)
    (* CG.fold_vertex (fun src infer_post_procs ->                                                      *)
    (*     (* If a method has already been marked as @post, we do not need to work on it again *)       *)
    (*     if (eq_num_ident src root) || (List.exists (fun mn -> eq_str mn (fst src)) infer_post_procs) *)
    (*     then infer_post_procs                                                                        *)
    (*     else if (should_infer_post_for_call csg trans_ddg src) then infer_post_procs @ [(fst src)]   *)
    (*     else infer_post_procs                                                                        *)
    (* ) csg acc                                                                                        *)
    
    (* let sdg = seq_data_dependency_graph_of_exp prog mn e in       *)
    (* let trans_sdg = CGO.transitive_closure ~reflexive:true sdg in *)
    try
      let sdg, trans_sdg = Hashtbl.find sdg_proc_tbl mn in
      CG.fold_vertex (fun (src, index) infer_post_procs ->
          if (index == root_index) then
            (* (* Find procs which the conditional conditions depend on *)                   *)
            (* let cond_depend_procs = collect_cond_depend_procs (src, index) sdg in         *)
            (* let () = if not (is_empty cond_depend_procs) then x_binfo_pp (                *)
            (*       "@post is added into " ^ (pr_list print_num_ident cond_depend_procs) ^  *)
            (*       " for conditions in " ^ (print_num_ident (src, index))) no_pos          *)
            (* in                                                                            *)
            (* infer_post_procs @ (List.map fst cond_depend_procs)                           *)
            infer_post_procs
          (* If a method has already been marked as @post, we do not need to work on it again *)
          else if (index == var_index) || (List.exists (fun mn -> eq_str mn src) infer_post_procs) 
          then infer_post_procs
          else
            let depend_procs = CG.pred trans_sdg (src, index) in
            try
              (* A succ of src (w.r.t the call sequence) depends on its output *)
              let succ_depend_proc = List.find (fun (_, i) -> i > index) depend_procs in
              let () = x_binfo_pp (
                  "@post is added into " ^ (print_num_ident (src, index)) ^ 
                  " for " ^ (print_num_ident succ_depend_proc)) no_pos in
              infer_post_procs @ [src]
            with _ -> infer_post_procs
        ) sdg acc
    with _ -> acc

let collect_callees_of_proc prog proc =
  match proc.proc_body with
  | None -> []
  | Some e -> callees_of_exp prog e

let rec collect_should_infer_term_procs prog inf_term_procs =
  let rec helper analyzed_procs analyzing_procs =
    match analyzing_procs with
    | [] -> analyzed_procs
    | p::ps -> 
      let callees_of_p = collect_callees_of_proc prog p in
      let n_analyzing_procs = diff_proc (remove_dups_proc callees_of_p) (analyzed_procs @ analyzing_procs) in
      let () = if not (is_empty n_analyzing_procs) then x_binfo_pp (
          "@term is added into " ^ (pr_list (fun p -> p.proc_name) n_analyzing_procs) ^ 
          " for " ^ p.proc_name) no_pos 
      in
      helper (analyzed_procs @ [p]) (ps @ n_analyzing_procs)
  in
  helper [] inf_term_procs

let collect_infer_post_procs_for_output prog mn = 
  try
    let output_vars = get_output_vars_proc prog mn in
    let _, trans_sdg = Hashtbl.find sdg_proc_tbl mn in
    let depend_procs = remove_dups_nid (List.concat (List.map
        (* Only get dependent procs *)
        (fun v -> List.filter (fun (_, i) -> i > root_index) (CG.succ trans_sdg v)) 
        (List.map (fun v -> (v, var_index)) output_vars)))
    in
    List.map fst depend_procs
  with _ -> []

let rec collect_should_infer_post_procs_for_output prog inf_post_procs =
  let rec helper analyzed_procs analyzing_procs =
    match analyzing_procs with
    | [] -> analyzed_procs
    | p::ps -> 
      let depend_procs_p_ret = collect_infer_post_procs_for_output prog p in
      let n_analyzing_procs = diff_id depend_procs_p_ret (analyzed_procs @ analyzing_procs) in
      let () = if not (is_empty n_analyzing_procs) then x_binfo_pp (
          "@post is added into " ^ (pr_list idf n_analyzing_procs) ^ 
          " for " ^ p ^ " output") no_pos 
      in
      helper (analyzed_procs @ [p]) (ps @ n_analyzing_procs)
  in
  helper [] inf_post_procs

let set_inf_obj_for_tnt_prog prog =
  (* Step 1: Incrementally adding @term into callees of @term or @term_wo_post callers *)
  let inf_term_procs = Hashtbl.fold (fun _ proc acc ->
      let spec = proc.proc_stk_of_static_specs # top (* proc.proc_static_specs *) in
      if not (Cformula.is_inf_term_struc spec) then acc
      else acc @ [proc]) prog.new_proc_decls [] 
  in
  let inc_inf_term_procs = diff_proc (collect_should_infer_term_procs prog inf_term_procs) inf_term_procs in
  let inc_inf_term_mn = List.map (fun proc -> proc.proc_name) inc_inf_term_procs in
  let prog = { prog with
    new_proc_decls = proc_decls_map (fun proc ->
        if List.mem proc.proc_name inc_inf_term_mn
        then set_inf_obj_proc INF_TERM proc
        else proc) prog.new_proc_decls; }
  in
  (* let n_tbl = proc_decls_map (fun proc ->        *)
  (*     if List.mem proc.proc_name inc_inf_term_mn *)
  (*     then set_inf_obj_proc INF_TERM proc        *)
  (*     else proc) prog.new_proc_decls             *)
  (* in                                             *)
  if not !Globals.tnt_add_post then prog
  else
    (* Step 2: Incrementally adding @post into dependent procs of @term procs *)
    (* Consider @term only, not @term_wo_post and the others *)
    let inf_term_only_procs = Hashtbl.fold (fun _ proc acc ->
        let spec = proc.proc_stk_of_static_specs # top in
        if not (Cformula.is_inf_term_only_struc spec) then acc
        else acc @ [proc]) prog.new_proc_decls [] 
    in

    let () = build_sdg_proc_tbl prog in
    
    (* Parameters of proc depends on inf_post_procs *)
    let inf_post_procs = List.fold_left (fun acc proc ->
        let dprocs = collect_infer_post_procs_for_tnt_acc acc prog proc in
        acc @ dprocs) [] inf_term_only_procs in
    let inf_post_procs = Gen.BList.remove_dups_eq eq_str inf_post_procs in

    (* Return values or Ref parameters of proc depends on inf_post_procs *)
    let inc_inf_post_procs = 
      if !Globals.inc_add_post then
        collect_should_infer_post_procs_for_output prog inf_post_procs 
      else inf_post_procs
    in
    { prog with
      new_proc_decls = proc_decls_map (fun proc ->
          if List.mem proc.proc_name inc_inf_post_procs
          then set_inf_obj_proc INF_POST proc
          else proc) prog.new_proc_decls; }
    (* let n_tbl = proc_decls_map (fun proc ->         *)
    (*   if List.mem proc.proc_name inc_inf_post_procs *)
    (*   then set_inf_obj_proc INF_POST proc           *)
    (*   else proc) prog.new_proc_decls                *)
    (* in ()                                           *)
