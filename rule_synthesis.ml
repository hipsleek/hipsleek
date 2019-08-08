#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

open Synthesis

module CA = Cast
module IA = Iast
module CF = Cformula
module CP = Cpure
module SB = Songbird

let check_goal_procs_x goal =
  let procs = goal.gl_proc_decls in
  let aux proc_decl =
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let specs = get_pre_post specs in
    let aux_pre_post (pre, post) =
      let () = x_binfo_hp (add_str "pre" pr_formula) pre no_pos in
      let () = x_binfo_hp (add_str "post" pr_formula) post no_pos in
      let post_nodes = post |> get_heap |> get_heap_nodes
                       |> List.map (fun (x,_,_) -> x) in
      let post_views = post |> get_heap |> get_heap_views
                       |> List.map (fun (x,_,_) -> x) in
      let pre_nodes = pre |> get_heap |> get_heap_nodes
                       |> List.map (fun (x,_,_) -> x) in
      let pre_views = pre |> get_heap |> get_heap_views
                     |> List.map (fun (x,_,_) -> x) in
      let post_vars = post_nodes @ post_views in
      let pre_vars = pre_nodes @ pre_views in
      let () = x_binfo_hp (add_str "pre vars" pr_vars) pre_vars no_pos in
      let () = x_binfo_hp (add_str "post vars" pr_vars) post_vars no_pos in
      List.length post_vars > List.length pre_vars in
    List.exists aux_pre_post specs in
  List.exists aux procs

let check_goal_procs goal =
  Debug.no_1 "check_goal_procs" pr_goal string_of_bool
    (fun _ -> check_goal_procs_x goal) goal

let check_entail_sleek_x prog ante (conseq:CF.formula) =
  let ante = CF.set_flow_in_formula (CF.mkTrueFlow ()) ante in
  let conseq = CF.set_flow_in_formula (CF.mkTrueFlow ()) conseq in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let conseq = CF.struc_formula_of_formula conseq no_pos in
  let list_ctx, _ = Solver.heap_entail_struc_init prog false true
      (CF.SuccCtx[ctx]) conseq no_pos None in
  if CF.isFailCtx list_ctx then false, None
  else
    let residue = CF.formula_of_list_context list_ctx in
    true, Some residue

let check_entail_sleek prog ante conseq =
  Debug.no_2 "check_entail_sleek" pr_formula pr_formula
    (fun (x, _) -> string_of_bool x)
    (fun _ _ -> check_entail_sleek_x prog ante conseq) ante conseq

let check_entail_exact_sleek_x prog ante (conseq:CF.formula) =
  let ante = CF.set_flow_in_formula (CF.mkTrueFlow ()) ante in
  let conseq = CF.set_flow_in_formula (CF.mkTrueFlow ()) conseq in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let conseq = CF.struc_formula_of_formula conseq no_pos in
  let list_ctx, _ = Solver.heap_entail_struc_init prog false true
      (CF.SuccCtx[ctx]) conseq no_pos None in
  if CF.isFailCtx list_ctx then false
  else
    let residue = CF.formula_of_list_context list_ctx in
    if CF.isEmpFormula residue then true
    else false

let check_entail_exact_sleek prog ante conseq =
  Debug.no_2 "check_entail_exact_sleek" pr_formula pr_formula string_of_bool
    (fun _ _ -> check_entail_exact_sleek_x prog ante conseq) ante conseq

let check_entail_exact_wrapper_x prog ante conseq =
  let ante = rm_emp_formula ante in
  let conseq = rm_emp_formula conseq in
  (* let ante = simplify_min_max ante in
   * let conseq = simplify_min_max conseq in *)
  if contains_lseg prog then
    let () = x_tinfo_pp "marking" no_pos in
    SB.check_entail_exact prog ante conseq
  else
    try
      check_entail_exact_sleek prog ante conseq
    with _ ->
      SB.check_entail_exact prog ante conseq

let check_entail_exact_wrapper prog ante conseq =
  Debug.no_2 "check_entail_exact_wrapper" pr_formula pr_formula
    string_of_bool
    (fun _ _ -> check_entail_exact_wrapper_x prog ante conseq) ante conseq

let check_entail_wrapper_x prog ante conseq =
  let ante = rm_emp_formula ante in
  let conseq = rm_emp_formula conseq in
  let conseq = rm_unk_type_formula prog conseq in
  if contains_lseg prog then
    let () = x_tinfo_pp "marking" no_pos in
    SB.check_entail_residue prog ante conseq
  else
    try
      check_entail_sleek prog ante conseq
    with _ ->  SB.check_entail_residue prog ante conseq

let check_entail_wrapper prog ante conseq =
  Debug.no_2 "check_entail_wrapper" pr_formula pr_formula
    (fun (x, _) -> string_of_bool x)
    (fun _ _ -> check_entail_wrapper_x prog ante conseq) ante conseq

let choose_rule_post_assign goal : rule list =
  let trace = goal.gl_trace in
  if List.length trace > 2 then []
  else
    let all_vars = goal.gl_vars in
    let post = goal.gl_post_cond in
    let pre = goal.gl_pre_cond in
    let e_vars = CF.get_exists post in
    let () = x_tinfo_hp (add_str "e_vars" pr_vars) e_vars no_pos in
    let post_pf = CF.get_pure post |> remove_exists_vars_pf in
    let post_conjuncts = CP.split_conjunctions post_pf in
    x_tinfo_hp (add_str "conjuncts" (pr_list pr_pf)) post_conjuncts no_pos;
    let eq_pairs = List.map (find_exists_substs e_vars) post_conjuncts
                   |> List.concat in
    let pr_pairs = pr_list (pr_pair pr_var pr_exp) in
    let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
    let filter_fun (x,y) =
      let vars = CP.afv y in
      vars = [] in
    (* not(is_null_type (CP.type_of_sv x)) && *)
    let filter_eq = Gen.BList.remove_dups_eq
        (fun x1 x2 -> CP.eq_sv (fst x1) (fst x2)) in
    let eq_pairs = eq_pairs |> filter_eq |> List.filter filter_fun in
    let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
    let mk_rule (var, exp) =
      RlPostAssign {
        rapost_lhs = var;
        rapost_rhs = exp
      } in
    List.map mk_rule eq_pairs

let choose_rule_assign_x goal : rule list =
  let res_vars = CF.fv goal.gl_post_cond |> List.filter CP.is_res_sv in
  let all_vars = goal.gl_vars @ res_vars in
  let post = goal.gl_post_cond in
  let exists_vars = CF.get_exists post in
  let post_vars = CF.fv post in
  let post_vars = CP.diff_svl post_vars exists_vars in
  let () = x_tinfo_hp (add_str "vars" pr_vars) post_vars no_pos in
  let post_pf = CF.get_pure goal.gl_post_cond |> remove_exists_pf in
  let () = x_tinfo_hp (add_str "pf" pr_pf) post_pf no_pos in
  let post_conjuncts = CP.split_conjunctions post_pf in
  let eq_pairs = List.map (find_exists_substs post_vars) post_conjuncts
                 |> List.concat in
  let pr_pairs = pr_list (pr_pair pr_var pr_exp) in
  let filter_fun (x,y) = (List.mem x all_vars) &&
                         CP.subset (CP.afv y) all_vars in
  let eq_pairs = eq_pairs |> List.filter filter_fun in
  let filter_with_ante ante (var, exp) =
    let ante_pf = CF.get_pure ante in
    let var = CP.mkVar var no_pos in
    let conseq = CP.mkEqExp var exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula conseq ante in
    not(SB.check_pure_entail ante_pf conseq) && (SB.check_sat goal.gl_prog n_pre) in
  let eq_pairs = eq_pairs |> List.filter (filter_with_ante goal.gl_pre_cond) in
  let mk_rule (var, exp) =
    if CP.is_res_sv var then RlReturn {r_exp = exp; r_checked = false;}
    else
      RlAssign {
        ra_lhs = var;
        ra_rhs = exp;
        ra_numeric = false;
      } in
  List.map mk_rule eq_pairs

let choose_rule_assign goal =
  Debug.no_1 "choose_rule_assign" pr_goal pr_rules
    (fun _ -> choose_rule_assign_x goal) goal

let get_node_vars post_cond =
  let post_vars = post_cond |> CF.fv |> List.filter is_node_var in
  let exists_vars = post_cond |> CF.get_exists |> List.filter is_node_var in
  let post_vars = post_vars@exists_vars in
  let n_post = remove_exists post_cond in
  let filter_fun var =
    let var_f = extract_var_f n_post var in
    match var_f with
    | Some f -> CF.is_emp_formula f |> negate
    | None -> false in
  post_vars |> List.filter filter_fun

let choose_rule_heap_assign goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let pre_nodes = get_node_vars pre in
  let post_nodes = get_node_vars post in
  let pre_pf = CF.get_pure pre in
  let post_pf = CF.get_pure post in
  let ante_pf = CP.mkAnd pre_pf post_pf no_pos in
  let mk_rule lhs rhs =
    if has_heap_assign lhs rhs goal.gl_trace then []
    else
      let rule = RlHeapAssign {
          rha_left = lhs;
          rha_right = rhs
        } in
      [rule] in
  let check_eq_var var1 var2 =
    let conseq = CP.mkEqVar var1 var2 no_pos in
    SB.check_pure_entail ante_pf conseq in
  if List.length pre_nodes = 1 && List.length post_nodes = 1 then
    let pre_node = List.hd pre_nodes in
    let post_node = List.hd post_nodes in
    let post = remove_exists post in
    let pre_f = extract_var_f pre pre_node |> Gen.unsome in
    let post_f = extract_var_f post post_node |> Gen.unsome in
    let pre_hf = get_hf pre_f in
    let post_hf = get_hf post_f in
    match pre_hf, post_hf with
    | CF.DataNode dn1, CF.DataNode dn2 ->
      let args1 = dn1.CF.h_formula_data_arguments in
      let args2 = dn2.CF.h_formula_data_arguments in
      let var1 = dn1.CF.h_formula_data_node in
      let var2 = dn2.CF.h_formula_data_node in
      if not(CP.eq_sv var1 var2) && CP.mem var1 all_vars &&
         CP.mem var2 all_vars && List.for_all2 check_eq_var args1 args2 then
        mk_rule var2 var1
      else []
    | CF.ViewNode vn1, CF.ViewNode vn2 ->
      let args1 = vn1.CF.h_formula_view_arguments in
      let args2 = vn2.CF.h_formula_view_arguments in
      let var1 = vn1.CF.h_formula_view_node in
      let var2 = vn2.CF.h_formula_view_node in
      if not(CP.eq_sv var1 var2) && CP.mem var1 all_vars &&
         CP.mem var2 all_vars &&
         List.for_all2 check_eq_var args1 args2 then
        mk_rule var2 var1
      else []
    | _ -> []
  else []

let choose_rule_fwrite goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let prog = goal.gl_prog in
  let pre_nodes = pre |> get_heap |> get_heap_nodes in
  let pr_nodes = pr_list (pr_triple pr_var pr_id pr_vars) in
  x_tinfo_hp (add_str "pre_nodes" pr_nodes) pre_nodes no_pos;
  let post_nodes = post |> get_heap |> get_heap_nodes in
  x_tinfo_hp (add_str "post_nodes" pr_nodes) post_nodes no_pos;
  let aux post_nodes (var, data_name, args) =
    try
      let triple = List.find (fun (y, _, _) -> CP.eq_sv y var) post_nodes in
      let _, _, post_args = triple in
      let data_decls = prog.Cast.prog_data_decls in
      let data = List.find (fun x -> eq_str x.Cast.data_name data_name)
          data_decls in
      let fields = List.map fst data.Cast.data_fields in
      let arg_pairs = List.combine args post_args in
      let arg_triples = List.map2 (fun (x,y) z -> (x,y,z)) arg_pairs fields in
      let filter_fun (x,y, z) = not(CP.eq_sv x y) in
      let dif_fields = List.filter filter_fun arg_triples in
      dif_fields |> List.map (fun (x, y, z) -> (var, y, z))
    with _ -> [] in
  let tuples = pre_nodes |> List.map (aux post_nodes) |> List.concat in
  let filter (_,n_val, _) = CP.mem n_val all_vars in
  let tuples = tuples |> List.filter filter in
  let mk_fwrite_rule (var, n_val, field) =
    RlFWrite {
      rfw_bound_var = var;
      rfw_field = field;
      rfw_value = n_val;
    } in
  tuples |> List.map mk_fwrite_rule

let is_same_shape (f1:CF.formula) (f2:CF.formula) =
  let check_hf (hf1:CF.h_formula) (hf2:CF.h_formula) =
    match hf1, hf2 with
    | CF.HEmp, HEmp -> (true, [])
    | DataNode dn1, DataNode dn2 ->
      let arg1 = dn1.h_formula_data_arguments in
      let arg2 = dn2.h_formula_data_arguments in
      if List.length arg1 = List.length arg2
      then (true, List.combine arg1 arg2)
      else (false, [])
    | ViewNode vn1, ViewNode vn2 ->
      let arg1 = vn1.h_formula_view_arguments in
      let arg2 = vn2.h_formula_view_arguments in
      if List.length arg1 = List.length arg2
      then (true, List.combine arg1 arg2)
      else (false, [])
    | _ -> (false, []) in
  let hf1,hf2 = get_hf f1, get_hf f2 in
  check_hf hf1 hf2

let unify_pair goal proc_decl arg pre_var =
  let pre_cond = goal.gl_pre_cond in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  (* let pre_proc = specs |> get_pre_cond |> rm_emp_formula in *)
  let proc_pre_list = specs |> get_pre_post |> List.map fst
                      |> List.map rm_emp_formula in
  let aux proc_pre =
    let a_pre = arg |> extract_var_f proc_pre in
    let l_pre = pre_var |> extract_var_f pre_cond in
    match a_pre, l_pre with
    | Some apre_f, Some lpre_f ->
      let () = x_tinfo_hp (add_str "pre_f" pr_formula) apre_f no_pos in
      let () = x_tinfo_hp (add_str "cand_f" pr_formula) lpre_f no_pos in
      is_same_shape apre_f lpre_f
    | _ -> false, [] in
  let res = proc_pre_list |> List.map aux
            |> List.filter (fun (x, _) -> x) in
  if res != [] then List.hd res
  else (false, [])

let unify_arg_x goal proc_decl arg =
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "arg" pr_var) arg no_pos in
  let candidate_vars = goal.gl_vars |> List.filter (equal_type arg)
                       |> List.filter (fun x -> CP.mem x goal.gl_vars) in
  let () = x_tinfo_hp (add_str "cand vars" pr_vars) candidate_vars no_pos in
  let ss_vars = List.map (fun candidate_var ->
      let (x,y) = unify_pair goal proc_decl arg candidate_var in
      (candidate_var, x, y)) candidate_vars in
  let ss_vars = List.filter (fun (_,x,_) -> x) ss_vars in
  let ss_vars = List.map (fun (x,_,y) -> (x,y)) ss_vars in
  let candidate_vars = ss_vars |> List.map fst in
  let () = x_tinfo_hp (add_str "cand vars" pr_vars) candidate_vars no_pos in
  ss_vars

let unify_arg goal proc_decl arg =
  Debug.no_2 "unify_arg" pr_goal pr_var
    (fun x -> List.map fst x |> pr_vars)
    (fun _ _ -> unify_arg_x goal proc_decl arg) goal arg

let unify_fcall proc_decl pre_proc post_proc goal =
  let proc_args = proc_decl.Cast.proc_args |>
                  List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let ss_args = proc_args |> List.map (unify_arg goal proc_decl) in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let ss_args = mk_args_input ss_args in
  let contain_res = CF.fv post_proc |> List.map CP.name_of_sv
                    |> List.exists (eq_str res_name) in
  let ss_args = List.filter(fun list_and_subst ->
      let list = List.map fst list_and_subst in
      let n_list = CP.remove_dups_svl list in
      List.length n_list = List.length list
    ) ss_args in
  let check_residue (fname, params, is_res, subst) =
    let () = x_tinfo_hp (add_str "params" pr_vars) params no_pos in
    let proc_decl = goal.gl_proc_decls
                    |> List.find (fun x -> eq_str x.Cast.proc_name fname) in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let spec_pairs = get_pre_post specs in
    (* to check a list of pre/post *)
    let (pre_proc, post_proc) = List.hd spec_pairs in
    (* TODO: fix this one *)
    let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
    let fun_args = proc_decl.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let substs = (List.combine fun_args params) @ subst in
    let params_pre = CF.subst substs pre_proc in
    let exists_vars = CF.fv params_pre |> List.filter (fun x -> CP.not_mem x params) in
    let fresh_evars = List.map CP.mk_fresh_sv exists_vars in
    let params_pre = CF.subst (List.combine exists_vars fresh_evars) params_pre in
    let params_pre = CF.wrap_exists fresh_evars params_pre |> rm_emp_formula in
    let ent_check, residue = check_entail_wrapper goal.gl_prog pre_cond
        params_pre in
    (ent_check, fname, params, is_res, subst, residue) in
  let mk_rule (fname, params, is_res, subst, residue) =
    let residue = Gen.unsome residue in
    if is_res then
      let res = List.find (fun x -> eq_str (CP.name_of_sv x) res_name)
          (CF.fv post_proc) in
      let n_var = CP.mk_typed_sv (CP.type_of_sv res)
          ("rs" ^ (string_of_int !res_num)) in
      let () = res_num := !res_num + 1 in
      RlFuncRes {
        rfr_fname = fname;
        rfr_params = params;
        rfr_substs = subst;
        rfr_residue = residue;
        rfr_return = n_var}
    else RlFuncCall{
        rfc_fname = fname;
        rfc_residue = residue;
        rfc_params = params;
        rfc_substs = subst} in
  let aux args_substs =
    let args = List.map fst args_substs in
    let substs = List.map snd args_substs |> List.concat in
    let is_cur_vars = List.for_all (fun x ->
        List.exists (fun y -> CP.eq_spec_var x y) goal.gl_vars) args in
    let has_res_arg = List.exists is_res_sv_syn args in
    let args_called = is_fcall_called goal.gl_trace args ||
                      is_fres_called goal.gl_trace args in
    let called = is_fcall_ever_called goal.gl_trace in
    let eq_args = List.for_all2 CP.eq_sv args proc_args in
    if is_cur_vars && (not has_res_arg) && (not args_called) && not eq_args
       && not (called) then
      let fname = proc_decl.Cast.proc_name in
      let fc_rule = if contain_res then (fname, args, true, substs)
        else (fname, args, false, substs) in
      [fc_rule]
    else [] in
  let list = ss_args |> List.map aux |> List.concat in
  let rules = list |> List.map check_residue in
  let rules = rules |> List.filter (fun (x,_,_,_,_,_) -> x)
              |> List.map (fun (_,a,b,c,d,e) -> (a,b,c,d,e)) in
  rules |> List.map mk_rule

let check_head_allocate_x goal : CP.spec_var list =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let pre_nodes = pre |> get_heap |> get_heap_nodes
                  |> List.map (fun (x,_,_) -> x) in
  let pre_views = pre |> get_heap |> get_heap_views
                   |> List.map (fun (x,_,_) -> x) in
  let post_nodes = post |> get_heap |> get_heap_nodes
                  |> List.map (fun (x,_,_) -> x) in
  let post_views = post |> get_heap |> get_heap_views
                   |> List.map (fun (x,_,_) -> x) in
  let pre_vars = pre_nodes @ pre_views in
  let post_vars = post_nodes @ post_views in
  let all_vars = goal.gl_vars |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "pre node" pr_vars) pre_vars no_pos in
  let () = x_tinfo_hp (add_str "post node" pr_vars) post_vars no_pos in
  let n_vars = post_vars |> List.filter (fun x -> CP.mem x all_vars)
              |> List.filter (fun x -> not(CP.mem x pre_vars)) in
  let () = x_tinfo_hp (add_str "allocate vars" pr_vars) n_vars no_pos in
  if not (CP.subset pre_vars post_vars) then
    n_vars
  else []

let check_head_allocate goal =
  Debug.no_1 "check_head_allocate" pr_goal pr_vars
    (fun _ -> check_head_allocate_x goal) goal

let choose_rule_func_call goal =
  if check_head_allocate goal != [] &&
     not (check_goal_procs goal) then []
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let procs = goal.gl_proc_decls in
    let aux proc_decl =
      let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
      (* TODO: fix this one *)
      (* let pre_cond = specs |> get_pre_cond |> rm_emp_formula in
       * let post_cond = specs |> get_post_cond |> rm_emp_formula in *)
      let spec_pairs = get_pre_post specs in
      let pre_cond, post_cond = List.hd spec_pairs in
      let rules = unify_fcall proc_decl pre_cond post_cond goal in
      rules in
    procs |> List.map aux |> List.concat

let check_allocate goal pre post =
  let pre_vars = pre |> get_heap |> get_heap_nodes in
  let post_vars = post |> get_heap |> get_heap_nodes in
  let all_vars = goal.gl_vars |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "all vars" pr_vars) all_vars no_pos in
  let pre_node_vars = pre |> CF.fv |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "pre nodes" pr_vars) pre_node_vars no_pos in
  (CP.diff_svl all_vars pre_node_vars != []) ||
  (List.length post_vars = 2 && List.length pre_vars = 1)

let check_mk_null pre post =
  let pre_vars = pre |> get_heap |> get_heap_nodes in
  let post_vars = post |> get_heap |> get_heap_nodes in
  List.length post_vars - List.length pre_vars = 1

let choose_rule_unfold_pre goal =
  if check_head_allocate goal != [] then []
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let vars, prog = goal.gl_vars, goal.gl_prog in
    let vnodes = get_unfold_view goal.gl_vars pre in
    let helper vnode =
      let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
      let nf = do_unfold_view_vnode goal.gl_prog pr_views args pre in
      let () = x_tinfo_hp (add_str "nf" pr_formulas) nf no_pos in
      let pre_list = List.filter (fun x -> SB.check_unsat goal.gl_prog x
                                           |> negate) nf in
      if pre_list = [] then []
      else if List.length pre_list = 1 then
        let n_pre = pre_list |> List.hd |> remove_exists |> rm_emp_formula in
        let rule = RlUnfoldPre {n_pre = n_pre} in
        [rule]
      else [] in
    vnodes |> List.map helper |> List.concat

let choose_rule_unfold_post goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let prog = goal.gl_prog in
  let res_vars = CF.fv goal.gl_post_cond |> List.filter CP.is_res_sv in
  let vars = goal.gl_vars @ res_vars |> CP.remove_dups_svl in
  let e_vars = CF.get_exists post |> List.filter is_node_var in
  let () = x_tinfo_hp (add_str "e_vars" pr_vars) e_vars no_pos in
  let vnodes = get_unfold_view vars post in
  let e_vnodes = get_unfold_view e_vars post in
  let pre_pf = CF.get_pure pre in
  let check_sat_wrapper formula =
    try
      (* let formula = formula |> remove_exists in *)
      let n_formula = CF.add_pure_formula_to_formula pre_pf formula in
      SB.check_sat prog n_formula
    (* let tmp = SB.check_unsat prog n_formula in
     * tmp |> negate *)
    with _ -> true in
  let helper_exists vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args post in
    x_tinfo_hp (add_str "nf" pr_formulas) nf no_pos;
    let nf = nf |> List.filter check_sat_wrapper in
    x_tinfo_hp (add_str "nf" pr_formulas) nf no_pos;
    if List.length nf = 1 then
      let case_f = List.hd nf in
      let rule =  RlUnfoldPost {
          rp_var = vnode.CF.h_formula_view_node;
          rp_case_formula = case_f} in
      [rule]
    else [] in
  let helper vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args post in
    let prog = goal.gl_prog in
    let nf = nf |> List.filter check_sat_wrapper in
    let rules = nf |> List.map (fun f -> RlUnfoldPost {
        rp_var = vnode.CF.h_formula_view_node;
        rp_case_formula = f}) in
    rules |> List.rev in
  if has_unfold_post goal.gl_trace ||
     check_head_allocate goal != [] then []
  else
    let rules1 = vnodes |> List.map helper |> List.concat in
    let rules2 = e_vnodes |> List.map helper |> List.concat in
    rules1@rules2

let choose_rule_numeric_x goal =
  let vars = goal.gl_vars |> List.filter is_int_var in
  x_tinfo_hp (add_str "vars" pr_vars) vars no_pos;
  let post_vars = CF.fv goal.gl_post_cond in
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let pre_vars, post_vars = CF.fv pre, CF.fv post in
  let post_vars = List.filter is_int_var post_vars in
  let vars_lhs = List.filter (fun x -> CP.mem x vars || CP.is_res_sv x) post_vars in
  let () = x_tinfo_hp (add_str "vars_lhs" pr_vars) vars_lhs no_pos in
  let filter_with_ante ante (var, exp) =
    let ante_pf = CF.get_pure ante in
    let var = CP.mkVar var no_pos in
    let conseq = CP.mkEqExp var exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula conseq ante in
    not(SB.check_pure_entail ante_pf conseq)
    && (SB.check_sat goal.gl_prog n_pre) in
  let create_templ all_vars cur_var =
    let other_vars = List.filter (fun x -> not(CP.eq_sv x cur_var)) all_vars in
    let var_formula = extract_var_f post cur_var in
    match var_formula with
    | Some var_f ->
      let pure_pre, var_pf = CF.get_pure pre, CF.get_pure var_f in
      let tmpl_args = List.map (fun x -> CP.mkVar x no_pos) other_vars in
      let templ = CP.Template (CP.mkTemplate tmpl_name tmpl_args no_pos) in
      let n_pf = CP.mkEqExp (CP.mkVar cur_var no_pos) templ no_pos in
      let n_pre = CP.mkAnd pure_pre n_pf no_pos in
      begin
        try
          let defn = SB.infer_templ_defn goal.gl_prog n_pre var_pf tmpl_name other_vars in
          begin
            match defn with
            | Some def ->
              let def = CP.norm_exp def in
              if filter_with_ante pre (cur_var, def) then
                let rule = if CP.is_res_sv cur_var then
                    RlReturn { r_exp = def; r_checked = false}
                  else
                    RlAssign {
                      ra_lhs = cur_var;
                      ra_rhs = def;
                      ra_numeric = true;
                    } in [rule]
              else []
            | _ -> []
          end
        with _ -> []
      end
    | None -> [] in
  let rules = vars_lhs |> List.map (fun x -> create_templ vars x) in
  rules |> List.concat

let choose_rule_numeric_end goal =
  let vars = goal.gl_vars |> List.filter is_int_var in
  x_tinfo_hp (add_str "vars" pr_vars) vars no_pos;
  let post_vars = CF.fv goal.gl_post_cond in
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let pre_vars, post_vars = CF.fv pre, CF.fv post in
  let post_vars = List.filter is_int_var post_vars in
  let vars_lhs = List.filter (fun x -> CP.mem x vars || CP.is_res_sv x)
      post_vars in
  let vars_lhs = List.filter (fun x -> CP.mem x pre_vars |> negate) vars_lhs in
  let () = x_tinfo_hp (add_str "vars_lhs" pr_vars) vars_lhs no_pos in
  let rec vars2exp vars = match vars with
    | [] -> CP.mkIConst 0 no_pos
    | h::tail ->
      let e2 = vars2exp tail in
      CP.Add ((CP.Var (h, no_pos)), e2, no_pos) in
  let create_templ all_vars cur_var =
    let other_vars = List.filter (fun x -> not(CP.eq_sv x cur_var)) all_vars in
    let rhs_e = vars2exp other_vars in
    let rules = [] in
    let rhs_one = CP.Add (rhs_e, CP.mkIConst 1 no_pos, no_pos) in
    let added_pf = CP.mkEqExp (CP.Var (cur_var, no_pos)) rhs_one no_pos in
    let n_pre = CF.add_pure_formula_to_formula added_pf pre in
    let rules = if check_entail_exact_wrapper goal.gl_prog n_pre post then
        let rule = if CP.is_res_sv cur_var then
            RlReturn { r_exp = rhs_one;
                       r_checked = true;
                     }
          else RlAssign {
              ra_lhs = cur_var;
              ra_rhs = rhs_one;
              ra_numeric = true;
            } in
        rule::rules
      else rules in
    rules in
  let rules = vars_lhs |> List.map (fun x -> create_templ vars x) in
  rules |> List.concat

let choose_rule_numeric goal =
  Debug.no_1 "choose_rule_numeric" pr_goal pr_rules
    (fun _ -> choose_rule_numeric_end goal) goal

let find_instantiate_var_x goal var =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let post_vars = CF.fv post in
  let all_vars = CF.fv pre |> List.filter is_node_var in
  let pf1, pf2 = CF.get_pure pre, CF.get_pure post in
  let ante = CP.mkAnd pf1 pf2 no_pos |> remove_exists_vars_pf in
  let () = x_tinfo_hp (add_str "ante" pr_pf) ante no_pos in
  let helper_pure var1 var2 =
    let conseq = CP.mkEqVar var1 var2 no_pos in
    SB.check_pure_entail ante conseq in
  let helper f1 f2 = match f1, f2 with
    | CF.Exists bf1, CF.Base bf2 ->
      let hf1 = bf1.CF.formula_exists_heap in
      let hf2 = bf2.CF.formula_base_heap in
      begin
        match hf1, hf2 with
        | CF.ViewNode vnode1, CF.ViewNode vnode2 ->
          let args1 = vnode1.CF.h_formula_view_arguments in
          let args2 = vnode2.CF.h_formula_view_arguments in
          List.length args1 = List.length args2
        (* List.exists2 (fun x y -> helper_pure x y) args1 args2 *)
        | _ -> false
      end
    | _ -> false in
  let compare_two_vars var1 var2 =
    if CP.mem var2 post_vars then false
    else
      let var1_f = extract_var_f post var1 in
      let var2_f = extract_var_f pre var2 in
      match var1_f, var2_f with
      | Some f1, Some f2 -> helper f1 f2
      | _ -> false in
  let equal_vars = List.filter (fun x -> compare_two_vars var x) all_vars in
  equal_vars

let find_instantiate_var goal var =
  Debug.no_2 "find_instantiate_var" pr_goal pr_var pr_vars
    (fun _ _ -> find_instantiate_var_x goal var) goal var

let choose_rule_return goal =
  let post = goal.gl_post_cond in
  let pre = goal.gl_pre_cond in
  let post_vars = post |> get_node_vars in
  let all_vars = goal.gl_vars in
  let check_return res_var r_var =
    let n_pf = CP.mkEqVar res_var r_var no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pf pre in
    let () = x_tinfo_hp (add_str "post" pr_formula) post no_pos in
    let ent_check, _ = check_entail_wrapper goal.gl_prog n_pre post in
    ent_check in
  if List.length post_vars = 1 then
    let p_var = List.hd post_vars in
    if CP.is_res_sv p_var then
      let pre = goal.gl_pre_cond in
      let pre_vars = pre |> get_node_vars
                     |> List.filter (fun x -> CP.mem x all_vars && not(CP.is_res_sv x)) in
      let pre_vars = List.filter (check_return p_var) pre_vars in
      let aux pre_var =
        let rule = RlReturn {
            r_exp = CP.mkVar pre_var no_pos;
            r_checked = true;
          } in
        [rule] in
      pre_vars |> List.map aux |> List.concat
    else []
  else []

let choose_rule_allocate_return goal : rule list =
  let prog = goal.gl_prog in
  let all_vars = goal.gl_vars in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "pre" pr_formula) goal.gl_pre_cond no_pos in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let data_decls = prog.C.prog_data_decls in
  let others = ["__Exc"; "thrd"; "Object"; "int_ptr"; "barrier"] in
  let filter_fun x = not(List.mem x.C.data_name others) in
  let data_decls = data_decls |> List.filter filter_fun in
  let rec check_eq_params args = match args with
    | [] -> false
    | h::tail -> if CP.mem h tail then true
      else check_eq_params tail in
  let check_params_end args =
    if check_eq_params args then false
    else
      let args = List.filter is_node_var args in
      let pre_vars = pre |> get_heap |> get_heap_nodes in
      let pre_nodes = pre_vars |> List.map (fun (x,_,y) -> (x,y)) in
      let pre_nodes = pre_nodes |> List.filter (fun (x,_) -> CP.mem x args) in
      let pre_vars = pre_nodes |> List.map fst in
      let other_args = List.filter (fun x -> not(CP.mem x pre_vars)) args in
      let all_vars = pre_nodes |> List.map (fun (x,y) -> x::y) |> List.concat in
      let all_vars = other_args@all_vars in
      let rm_duplicate_vars = CP.remove_dups_svl all_vars in
      if List.length all_vars != List.length rm_duplicate_vars then false
      else true in
  let eq_tuple tuple1 tuple2 =
    let commutative_int tuple1 tuple2 =
      let int_args1 = tuple1 |> List.filter is_int_var in
      let int_args2 = tuple2 |> List.filter is_int_var in
      CP.subset int_args1 int_args2 && CP.subset int_args2 int_args1 in
    let commutative_node tuple1 tuple2 =
      let node_args1 = tuple1 |> List.filter is_node_var in
      let node_args2 = tuple2 |> List.filter is_node_var in
      CP.subset node_args1 node_args2 && CP.subset node_args2 node_args1 in
    commutative_int tuple1 tuple2 && commutative_node tuple1 tuple2 in
  let mk_rule_end data_decl allocate_var args =
    if check_params_end args then
      let data = data_decl.C.data_name in
      let hf = CF.mkDataNode allocate_var data args no_pos in
      let n_pre = add_h_formula_to_formula hf goal.gl_pre_cond in
      if check_entail_exact_wrapper prog n_pre post then
        let rule = {
          ra_var = allocate_var;
          ra_data = data;
          ra_params = args;
          ra_pre = n_pre;
          ra_end = true;
          ra_lookahead = None;
        } in
        [rule]
      else []
    else [] in
  let aux_end allocate_var data_decl =
    let n_eq_var al_var x = CP.eq_sv al_var x |> negate in
    let all_vars = List.filter (n_eq_var allocate_var) all_vars in
    let pre_nodes = pre |> get_heap |> get_heap_nodes
                   |> List.map (fun (x,_,_) -> x) in
    let pre_views = pre |> get_heap |> get_heap_views
                    |> List.map (fun (x,_,_) -> x) in
    let pre_vars = pre_nodes @ pre_views in
    let all_vars = all_vars |> List.filter (fun x ->
        if is_node_var x then CP.mem x pre_vars else true) in
    let () = x_tinfo_hp (add_str "pre vars" pr_vars) pre_vars no_pos in
    let () = x_tinfo_hp (add_str "all vars" pr_vars) all_vars no_pos in
    let args = data_decl.C.data_fields |> List.map fst
               |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let () = x_tinfo_hp (add_str "args" pr_vars) args no_pos in
    let arg_types = List.map CP.type_of_sv args in
    let helper_typ typ =
      all_vars |> List.filter (fun x -> CP.type_of_sv x = typ) in
    let args_list = arg_types |> List.map helper_typ in
    let args_groups = args_list |> mk_args_input in
    let filter_fun list = has_allocate goal.gl_trace list |> negate in
    let args_groups = args_groups |> List.filter filter_fun in
    let args_groups = args_groups |> Gen.BList.remove_dups_eq eq_tuple in
    let rules = args_groups |> List.map (mk_rule_end data_decl allocate_var)
                |> List.concat in
    rules in
  let allocate_vars = check_head_allocate goal in
  if allocate_vars != [] then
    let allocate_var = List.hd allocate_vars in
    let () = x_tinfo_hp (add_str "var" pr_var) allocate_var no_pos in
    let rules = data_decls |> List.map (aux_end allocate_var) |> List.concat in
    let rules = rules |> List.map (fun x -> RlAllocate x) in
    rules
  else []

