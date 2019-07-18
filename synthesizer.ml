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

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)
(*********************************************************************
 * Choosing rules
 *********************************************************************)

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

let check_entail_exact_wrapper prog ante conseq =
  try
    check_entail_exact_sleek prog ante conseq
  with _ -> SB.check_entail_exact prog ante conseq

let check_entail_wrapper prog ante conseq =
  try
    check_entail_sleek prog ante conseq
  with _ -> SB.check_entail_residue prog ante conseq

let rec find_sub_var sv cur_vars pre_pf =
  match pre_pf with
  | CP.BForm (b, _) ->
    let bvars = CP.bfv b in
    if List.exists (fun x -> CP.eq_spec_var x sv) bvars then
      let (pf, _) = b in
      (match pf with
       | Eq (e1, e2, _) ->
         begin
           match e1, e2 with
           | Var (sv1, _), Var (sv2, _) ->
             if CP.eq_spec_var sv1 sv
             && List.exists (fun x -> CP.eq_spec_var x sv2) cur_vars
             then Some sv2
             else if CP.eq_spec_var sv2 sv
                  && List.exists (fun x -> CP.eq_spec_var x sv1) cur_vars
             then Some sv1
             else None
           | _ -> None
         end
       | _ -> None
      )
    else None
  | CP.And (f1, f2, _) ->
    let res1 = find_sub_var sv cur_vars f1 in
    if res1 = None then find_sub_var sv cur_vars f2
        else res1
  | _ -> None

(* let choose_rule_pre_assign goal : rule list =
 *   let all_vars = goal.gl_vars in
 *   let post = goal.gl_post_cond in
 *   let pre = goal.gl_pre_cond in
 *   let pre_vars = CF.fv pre in
 *   let pre_pf = CF.get_pure pre in
 *   let pre_conjuncts = CP.split_conjunctions pre_pf in
 *   let eq_pairs = List.map (find_exists_substs pre_vars) pre_conjuncts
 *                  |> List.concat in
 *   let pr_pairs = pr_list (pr_pair pr_var pr_exp) in
 *   let filter_fun (x,y) =
 *     let vars = CP.afv y in
 *     not(CP.mem x all_vars) && vars != [] && CP.subset vars all_vars in
 *   let filter_eq = Gen.BList.remove_dups_eq
 *       (fun x1 x2 -> CP.eq_sv (fst x1) (fst x2)) in
 *   let eq_pairs = eq_pairs |> filter_eq |> List.filter filter_fun in
 *   let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
 *   let mk_rule (var, exp) =
 *     RlPreAssign {
 *       rpa_lhs = var;
 *       rpa_rhs = exp
 *     } in
 *   List.map mk_rule eq_pairs *)

let choose_rule_post_assign goal : rule list =
  let all_vars = goal.gl_vars in
  let post = goal.gl_post_cond in
  let pre = goal.gl_pre_cond in
  let e_vars = CF.get_exists post |> List.filter is_node_var in
  let post_pf = CF.get_pure post |> remove_exists_vars_pf in
  let post_conjuncts = CP.split_conjunctions post_pf in
  let eq_pairs = List.map (find_exists_substs e_vars) post_conjuncts
                 |> List.concat in
  let filter_fun (x,y) =
    let vars = CP.afv y in
    vars = [] in
    (* not(CP.mem x all_vars) && CP.subset vars all_vars in *)
  let filter_eq = Gen.BList.remove_dups_eq
      (fun x1 x2 -> CP.eq_sv (fst x1) (fst x2)) in
  let eq_pairs = eq_pairs |> filter_eq |> List.filter filter_fun in
  let mk_rule (var, exp) =
    RlPostAssign {
      rapost_lhs = var;
      rapost_rhs = exp
    } in
  List.map mk_rule eq_pairs

let check_allocate pre post =
  let pre_vars = pre |> get_heap |> get_heap_nodes in
  let post_vars = post |> get_heap |> get_heap_nodes in
  List.length post_vars - List.length pre_vars = 1

let choose_rule_allocate goal : rule list =
  let prog = goal.gl_prog in
  let all_vars = goal.gl_vars in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "all vars" pr_vars) all_vars no_pos in
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
  let mk_rule data_decl args =
    let data = data_decl.C.data_name in
    let var_name = fresh_name () in
    let var = CP.mk_typed_sv (Named data) var_name in
    RlAllocate {
      ra_var = var;
      ra_data = data;
      ra_params = args;
    } in
  let aux data_decl =
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
    let rules = args_groups |> List.map (mk_rule data_decl) in
    rules in
  if check_allocate pre post then
    data_decls |> List.map aux |> List.concat
  else []

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
        ra_rhs = exp
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
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let a_pre = arg |> extract_var_f pre_proc in
  let l_pre = pre_var |> extract_var_f pre_cond in
  match a_pre, l_pre with
  | Some apre_f, Some lpre_f ->
    let () = x_tinfo_hp (add_str "pre_f" pr_formula) apre_f no_pos in
    let () = x_tinfo_hp (add_str "cand_f" pr_formula) lpre_f no_pos in
    is_same_shape apre_f lpre_f
  | _ -> false, []

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
    let proc_decl = goal.gl_proc_decls
                    |> List.find (fun x -> eq_str x.Cast.proc_name fname) in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
    let post_proc = specs |> get_post_cond |> rm_emp_formula in
    let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
    let fun_args = proc_decl.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let substs = (List.combine fun_args params) @ subst in
    let params_pre = CF.subst substs pre_proc in
    let exists_vars = CF.fv params_pre |> List.filter (fun x -> CP.not_mem x params) in
    let fresh_evars = List.map CP.mk_fresh_sv exists_vars in
    let params_pre = CF.subst (List.combine exists_vars fresh_evars) params_pre in
    let params_pre = CF.wrap_exists fresh_evars params_pre in
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

let choose_rule_func_call goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let procs = goal.gl_proc_decls in
  (* let proc_names = List.map (fun x -> x.C.proc_name) procs in
   * let () = x_tinfo_hp (add_str "procs" (pr_list pr_id)) proc_names no_pos in *)
  let aux proc_decl =
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let pre_cond = specs |> get_pre_cond |> rm_emp_formula in
    let post_cond = specs |> get_post_cond |> rm_emp_formula in
    let rules = unify_fcall proc_decl pre_cond post_cond goal in
    rules in
  procs |> List.map aux |> List.concat

let choose_rule_unfold_pre goal =
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
      let n_pre = pre_list |> List.hd |> remove_exists in
      let rule = RlUnfoldPre {n_pre = n_pre} in
      [rule]
    else [] in
  vnodes |> List.map helper |> List.concat

 (* let get_cond_exp prog formula base recursive puref vars =
  *  let conjuncs = CP.split_conjunctions puref in
  *  let aux pf =
  *    let n_bf = CF.add_pure_formula_to_formula pf formula in
  *    let n_pf = CP.mkNot_s pf in
  *    let n_rc = CF.add_pure_formula_to_formula n_pf formula in
  *    let fst = SB.check_entail_exact prog n_bf base in
  *    let snd = SB.check_entail_exact prog n_rc recursive in
  *    fst && snd in
  *  conjuncs |> List.filter (fun x -> CP.subset (CP.fv x) vars)
  *  |> List.filter aux *)

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
  if has_unfold_post goal.gl_trace then []
  else
    let rules1 = vnodes |> List.map helper |> List.concat in
    let rules2 = e_vnodes |> List.map helper_exists |> List.concat in
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
                    } in [rule]
              else []
            | _ -> []
          end
        with _ -> []
      end
    | None -> [] in
  let rules = vars_lhs |> List.map (fun x -> create_templ vars x) in
  rules |> List.concat

let choose_rule_numeric goal =
  Debug.no_1 "choose_rule_numeric" pr_goal pr_rules
    (fun _ -> choose_rule_numeric_x goal) goal

let find_instantiate_var_x goal var =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
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
          List.exists2 (fun x y -> helper_pure x y) args1 args2
        | _ -> false
      end
    | _ -> false in
  let compare_two_vars var1 var2 =
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

let choose_rule_frame_pred goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let exists_vars = CF.get_exists post |> List.filter is_node_var in
  let filter (lhs, rhs) =
    let n_pre, pre_vars = frame_var_formula pre rhs in
    let n_post, post_vars = frame_var_formula post lhs in
    (* let check_field f field =
     *   match extract_var_f f field with
     *   | Some var_f -> if CF.is_emp_formula var_f then true
     *     else false
     *   | _ -> true in
     * let check_pre = List.for_all (check_field pre) pre_vars in
     * let check_post = List.for_all (check_field post) post_vars in *)
    if (List.length pre_vars = List.length post_vars) (* &&
        * check_pre && check_post *) then
      let pre_vars = rhs::pre_vars in
      let post_vars = lhs::post_vars in
      let rule = RlFramePred {
          rfp_lhs = lhs;
          rfp_rhs = rhs;
          rfp_pairs = List.combine pre_vars post_vars;
          rfp_pre = n_pre;
          rfp_post = n_post;
        } in [rule]
    else [] in
  let helper var =
    let eq_vars = find_instantiate_var goal var in
    eq_vars |> List.map (fun x -> (var, x)) in
  exists_vars |> List.map helper |> List.concat |> List.map filter
  |> List.concat

let find_frame_node_var goal all_vars post_var =
  let all_vars = List.filter (fun x -> not(CP.eq_sv x post_var)) all_vars in
  let () = x_tinfo_hp (add_str "post var" pr_var) post_var no_pos in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let pre_vars = get_node_vars pre in
  let pre_vars = List.filter (fun x -> not(CP.mem x all_vars)) pre_vars in
  let () = x_tinfo_hp (add_str "pre vars" pr_vars) pre_vars no_pos in
  let pre_pf = CF.get_pure pre in
  let post_pf = CF.get_pure post in
  let pf = CP.mkAnd pre_pf post_pf no_pos in
  let helper_arg arg1 arg2 =
    let conseq = CP.mkEqVar arg1 arg2 no_pos in
    SB.check_pure_entail pf conseq in
  let helper_hf hf1 hf2 = match hf1, hf2 with
    | CF.DataNode dn1, CF.DataNode dn2 ->
      let args1 = dn1.CF.h_formula_data_arguments in
      let args2 = dn2.CF.h_formula_data_arguments in
      let () = x_tinfo_hp (add_str "args1" pr_vars) args1 no_pos in
      let () = x_tinfo_hp (add_str "args2" pr_vars) args2 no_pos in
      List.exists2 helper_arg args1 args2
    | _ -> false in
  let helper pre_var =
    let pre_f = extract_var_f pre pre_var in
    let post_f = extract_var_f post post_var in
    match pre_f, post_f with
    | Some f1, Some f2 ->
      begin
        match f1, f2 with
        | CF.Base bf1, CF.Base bf2 ->
          let hf1, hf2 = bf1.CF.formula_base_heap, bf2.CF.formula_base_heap in
          helper_hf hf1 hf2
        | CF.Base bf1, CF.Exists bf2 ->
          let hf1 = bf1.CF.formula_base_heap in
          let hf2 = bf2.CF.formula_exists_heap in
          helper_hf hf1 hf2
        | _ -> false
      end
    | _ -> false in
  let frame_vars = pre_vars |> List.filter helper in
  frame_vars |> List.map (fun x -> (post_var, x))

let choose_rule_frame_data goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let post_vars = post |> get_node_vars in
  let () = x_tinfo_hp (add_str "post vars" pr_vars) post_vars no_pos in
  let pairs = post_vars |> List.map (find_frame_node_var goal post_vars)
              |> List.concat in
  let pr_pairs = pr_list (pr_pair pr_var pr_var) in
  let () = x_tinfo_hp (add_str "pairs" pr_pairs) pairs no_pos in
  let filter (lhs, rhs) =
    let n_pre, pre_vars = frame_var_formula pre rhs in
    let n_post, post_vars = frame_var_formula post lhs in
    let () = x_tinfo_hp (add_str "pre_vars" pr_vars) pre_vars no_pos in
    let () = x_tinfo_hp (add_str "post_vars" pr_vars) post_vars no_pos in
    if (List.length pre_vars = List.length post_vars) then
      let pre_vars = rhs::pre_vars in
      let post_vars = lhs::post_vars in
      let rule = RlFrameData {
          rfd_lhs = lhs;
          rfd_rhs = rhs;
          rfd_pairs = List.combine pre_vars post_vars;
          rfd_pre = n_pre;
          rfd_post = n_post;
        } in [rule]
    else [] in
  pairs |> List.map filter |> List.concat

(* let choose_rule_exists_right goal =
 *   let post = goal.gl_post_cond in
 *   let exists_vars = CF.get_exists post in
 *   if exists_vars = [] then []
 *   else
 *     let post_pf = CF.get_pure goal.gl_post_cond in
 *     let post_conjuncts = CP.split_conjunctions post_pf in
 *     let eq_pairs = List.map (find_exists_substs exists_vars) post_conjuncts
 *                    |> List.concat in
 *     let collected_exists_vars = eq_pairs |> List.map fst |> CP.remove_dups_svl in
 *     if collected_exists_vars = [] then []
 *     else
 *       let n_post = remove_exists_vars post collected_exists_vars in
 *       let n_post = subst_term_formula eq_pairs n_post in
 *       let rule = RlExistsRight {n_post = n_post} in
 *       [rule] *)

let rec choose_rule_interact goal rules =
  if rules = [] then
    let () = x_binfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
    rules
  else
    let str = pr_list_ln pr_rule rules in
    let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
    let () = x_binfo_hp (add_str "Rules" pr_rules) rules no_pos in
    let choose_str = "Please choose a/q or from 1 to "
                     ^ (string_of_int (List.length rules)) ^ ": " in
    let () = x_binfo_pp choose_str no_pos in
    let choice = String.uppercase_ascii (String.trim (read_line ())) in
    if eq_str choice "A" then
      let () = enable_i := false in
      rules
    else if eq_str choice "Q" then
      []
    else
      let rule_id = int_of_string (choice) in
      let rules_w_ids = List.mapi (fun i x -> (i, x)) rules in
      let chosen_rules, other_rules =
        List.partition (fun (x, _) -> x + 1 = rule_id) rules_w_ids in
      if chosen_rules = [] then
        let err_str = "Wrong choose, please choose again" in
        let () = x_binfo_hp (add_str "Error" pr_id) err_str no_pos in
        choose_rule_interact goal rules
      else
        let chosen_rules = List.map snd chosen_rules in
        let other_rules = List.map snd other_rules in
        let () = x_binfo_hp (add_str "You chose" (pr_list_ln pr_rule))
            chosen_rules no_pos in
        chosen_rules @ other_rules

let choose_rule_mk_null goal : rule list=
  if has_mk_null goal.gl_trace then []
  else
    let pre = goal.gl_pre_cond in
    let post = goal.gl_post_cond in
    let prog = goal.gl_prog in
    let data_decls = prog.C.prog_data_decls in
    let others = ["__Exc"; "thrd"; "Object"; "__Error"; "__MayError"; "__Fail";
                  "char_star"; "int_ptr_ptr"; "int_ptr"; "lock"; "barrier";
                  "__RET"; "__ArrBoundErr"; "__DivByZeroErr"; "String"] in
    let filter_fun x = not(List.mem x.C.data_name others) in
    let data_decls = data_decls |> List.filter filter_fun in
    let procs = goal.gl_proc_decls in
    let aux_proc_args proc =
      let args = proc.C.proc_args in
      args |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let all_args = procs |> List.map aux_proc_args |> List.concat
                   |> CP.remove_dups_svl in
    let int_vars = goal.gl_vars |> List.filter is_int_var
                 |> List.filter (fun x -> CP.mem x all_args) in
    let aux_int var =
      let n_var = CP.fresh_spec_var var in
      let one = CP.mkIConst 1 no_pos in
      let n_var_e = CP.mkVar var no_pos in
      let minus_one = CP.mkSubtract n_var_e one no_pos in
      RlMkNull {
        rmn_var = n_var;
        rmn_null = minus_one;
      } in
    let aux data_decl =
      let data_name = data_decl.C.data_name in
      let typ = Globals.Named data_name in
      let name = Globals.fresh_name () in
      let var = CP.mk_typed_sv typ name in
      RlMkNull {rmn_null = CP.Null no_pos;
                rmn_var = var} in
    if check_allocate pre post then
      let list1 = data_decls |> List.map aux in
      let list2 = int_vars |> List.map aux_int in
      list1 @ list2
      (* list1 *)
    else []

let choose_rule_fread_x goal =
  let vars, pre_cond = goal.gl_vars, goal.gl_pre_cond in
  let rec helper_hf (hf:CF.h_formula) = match hf with
    | DataNode dnode -> let dn_var = dnode.CF.h_formula_data_node in
      if List.exists (fun x -> CP.eq_spec_var x dn_var) vars then
        let dn_name = dnode.CF.h_formula_data_name in
        let dn_args = dnode.CF.h_formula_data_arguments in
        [(dn_var, dn_name, dn_args)]
      else []
    | Star sf -> let hf1, hf2 = sf.h_formula_star_h1, sf.h_formula_star_h2 in
      (helper_hf hf1) @ (helper_hf hf2)
    | _ -> [] in
  let rec helper_f (f:CF.formula) = match f with
    | Base bf -> helper_hf bf.CF.formula_base_heap
    | Or bf -> let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
      (helper_f f1) @ (helper_f f2)
    | Exists bf -> helper_hf bf.formula_exists_heap in
  let triples = helper_f pre_cond in
  let pr_triples = pr_list (pr_triple pr_var pr_id pr_vars) in
  let () = x_tinfo_hp (add_str "triples" pr_triples) triples no_pos in
  let filter_rule rule =
    let var = rule.rfr_value in
    let () = x_tinfo_hp (add_str "var" pr_var) var no_pos in
    let n_goal = {goal with gl_vars = [var]} in
    let n_goal2 = {goal with gl_vars = var::goal.gl_vars} in
    let unfold_rules = choose_rule_unfold_pre n_goal in
    let fcall_rules = choose_rule_func_call n_goal2 in
    let fwrite_rules = choose_rule_fwrite n_goal2 in
    List.exists (rule_use_var var) fwrite_rules ||
    unfold_rules != [] || (List.exists (rule_use_var var) fcall_rules) in
  let helper_triple (var, data, args) =
    let prog = goal.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let filter_fun (x, _) = CP.mem x vars |> negate in
    let d_arg_pairs = List.filter filter_fun d_arg_pairs in
    let helper_arg (arg, field) =
      let rbind = {
          rfr_bound_var = var;
          rfr_field = field;
          rfr_value = arg;
        } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  List.map helper_triple triples |> List.concat
  |> List.filter (fun x -> is_fread_called goal.gl_trace x |> negate)
  |> List.filter filter_rule
  |> List.map (fun x -> RlFRead x) |> List.rev

let choose_rule_fread goal =
  Debug.no_1 "choose_rule_fread" pr_goal pr_rules
    (fun _ -> choose_rule_fread_x goal) goal

let choose_main_rules goal =
  let cur_time = get_time () in
  let duration = cur_time -. goal.gl_start_time in
  if duration > !synthesis_timeout && not(!enable_i) then
    []
  else
    let rs = [] in
    let rs = rs @ (choose_rule_unfold_pre goal) in
    let rs = rs @ (choose_rule_frame_pred goal) in
    let rs = rs @ (choose_rule_assign goal) in
    let rs = rs @ (choose_rule_fread goal) in
    let rs = rs @ (choose_rule_fwrite goal) in
    let rs = rs @ (choose_rule_numeric goal) in
    let rs = rs @ (choose_rule_func_call goal) in
    let rs = rs @ (choose_rule_frame_data goal) in
    (* let rs = rs @ (choose_rule_pre_assign goal) in *)
    let rs = rs @ (choose_rule_post_assign goal) in
    let rs = rs @ (choose_rule_allocate goal) in
    let rs = rs @ (choose_rule_mk_null goal) in
    let rs = rs @ (choose_rule_return goal) in
    let rs = rs @ (choose_rule_heap_assign goal) in
    let rs = eliminate_useless_rules goal rs in
    let rs = if rs = [] then
        choose_rule_unfold_post goal
    else rs in
    let rs = reorder_rules goal rs in
    rs

let mk_rule_free goal residue =
  let post = goal.gl_post_cond in
  let pre_nodes = goal.gl_pre_cond |> get_heap |> get_heap_nodes in
  let post_nodes = goal.gl_post_cond |> get_heap |> get_heap_nodes in
  let pre_node_vars = pre_nodes |> List.map (fun (x, _,_) -> x) in
  let post_node_vars = post_nodes |> List.map (fun (x, _,_) -> x) in
  let free_vars = CP.diff_svl pre_node_vars post_node_vars in
  if List.length free_vars > 0 then
    let rule = RlFree {
        rd_vars = free_vars;
      } in
    [rule]
  else []

let choose_rule_skip goal =
  if is_code_rule goal.gl_trace then
    let prog, pre, post = goal.gl_prog, goal.gl_pre_cond, goal.gl_post_cond in
    try
      (* to check_residue for the delete case *)
      let sk, residue = check_entail_wrapper prog pre post in
      if sk then
        let residue = Gen.unsome residue in
        if CF.is_emp_formula residue then
          let rule = RlSkip in [rule]
        else mk_rule_free goal residue
      else []
    with _ -> []
  else []

let choose_synthesis_rules_x goal : rule list =
  let rules =
    try
      (* let _ = choose_rule_exists_right goal |> raise_rules in *)
      let _ = choose_rule_skip goal |> raise_rules in
      let _ = choose_main_rules goal |> raise_rules in
      []
    with ERules rs -> rs in
  rules

let choose_synthesis_rules goal =
  Debug.no_1 "choose_synthesis_rules" pr_goal pr_rules
    (fun _ -> choose_synthesis_rules_x goal) goal

(*********************************************************************
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rcore =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let lhs, rhs = rcore.ra_lhs, rcore.ra_rhs in
  let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf pre in
  let post_vars = CF.fv post in
  let sub_goal = {goal with gl_pre_cond = n_pre;
                            gl_trace = (RlAssign rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlAssign rcore) [sub_goal]

(* let process_rule_pre_assign goal rcore =
 *   let lhs = rcore.rpa_lhs in
 *   let n_vars = lhs::goal.gl_vars in
 *   let sub_goal = {goal with gl_vars = n_vars;
 *                             gl_trace = (RlPreAssign rcore)::goal.gl_trace} in
 *   mk_derivation_subgoals goal (RlPreAssign rcore) [sub_goal] *)

let process_rule_post_assign goal rcore =
  let lhs = rcore.rapost_lhs in
  let rhs = rcore.rapost_rhs in
  let n_vars = lhs::goal.gl_vars in
  let n_post = remove_exists_vars goal.gl_post_cond [lhs] in
  let e_var = CP.mkVar lhs no_pos in
  let n_pf = CP.mkEqExp e_var rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf goal.gl_pre_cond in
  let sub_goal = {goal with gl_vars = n_vars;
                            gl_post_cond = n_post;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlPostAssign rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlPostAssign rcore) [sub_goal]

let process_rule_return goal rcore =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let lhs = goal.gl_post_cond |> CF.fv |> List.find CP.is_res_sv in
  let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rcore.r_exp no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf pre in
  let ent_check = check_entail_exact_wrapper goal.gl_prog n_pre post in
  match ent_check with
  | true -> mk_derivation_success goal (RlReturn rcore)
  | false -> mk_derivation_fail goal (RlReturn rcore)

let subs_fwrite formula var field new_val data_decls =
  match (formula:CF.formula) with
  | Base bf -> let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper (hf:CF.h_formula) = match hf with
      | DataNode dnode ->
        let data_var = dnode.h_formula_data_node in
        if CP.eq_spec_var data_var var then
          let n_dnode = set_field dnode field new_val data_decls in
          (CF.DataNode n_dnode)
        else hf
      | Star sf -> let n_h1 = helper sf.CF.h_formula_star_h1 in
        let n_h2 = helper sf.CF.h_formula_star_h2 in
        Star {sf with h_formula_star_h1 = n_h1;
                      h_formula_star_h2 = n_h2}
      | _ -> hf in
    CF.Base {bf with formula_base_heap = helper hf}
  | _ -> formula

let process_rule_fwrite goal rcore =
  let pre, var = goal.gl_pre_cond, rcore.rfw_bound_var in
  let field, prog = rcore.rfw_field, goal.gl_prog in
  let rhs, data_decls = rcore.rfw_value, prog.prog_data_decls in
  let n_pre = subs_fwrite pre var field rhs data_decls in
  let n_goal = {goal with gl_pre_cond = n_pre;
                          gl_trace = (RlFWrite rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlFWrite rcore) [n_goal]

let process_rule_fread goal rcore =
    let vars = [rcore.rfr_value] @ goal.gl_vars |> CP.remove_dups_svl in
    let n_goal = {goal with gl_vars = vars;
                            gl_trace = (RlFRead rcore)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlFRead rcore) [n_goal]

let aux_func_call goal rule fname params subst res_var residue =
  let proc_decl = goal.gl_proc_decls
                  |> List.find (fun x -> eq_str x.Cast.proc_name fname) in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let post_proc = specs |> get_post_cond |> rm_emp_formula in
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let fun_args = proc_decl.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let substs = (List.combine fun_args params) @ subst in
  (* let params_pre = CF.subst substs pre_proc in
   * let exists_vars = CF.fv params_pre |> List.filter (fun x -> CP.not_mem x params) in
   * let fresh_evars = List.map CP.mk_fresh_sv exists_vars in
   * let params_pre = CF.subst (List.combine exists_vars fresh_evars) params_pre in *)
  (* let params_pre = CF.wrap_exists fresh_evars params_pre in *)
  (* let ent_check, residue =
   *   SB.check_entail_residue goal.gl_prog pre_cond params_pre in
   * match ent_check, residue with
   * | true, Some red -> *)
  let red = residue in
  let params_post = CF.subst substs post_proc in
  let () = x_tinfo_hp (add_str "param_post" pr_formula) params_post no_pos in
  let evars = CF.get_exists params_post in
  let post_state = add_formula_to_formula red params_post in
  let np_vars = CF.fv post_state in
  let contain_res = np_vars |> List.map (fun x -> CP.name_of_sv x)
                    |> List.exists (fun x -> x = res_name) in
  let post_state, n_vars = if res_var != None then
      let res = List.find (fun x -> eq_str (CP.name_of_sv x) res_name)
          (CF.fv post_proc) in
      let n_var = Gen.unsome res_var in
      let n_f = CF.subst [(res, n_var)] post_state in
      (n_f, goal.gl_vars @ [n_var])
    else post_state, goal.gl_vars in
  let () = x_tinfo_hp (add_str "post" pr_formula) post_state no_pos in
  let sub_goal = {goal with gl_vars = n_vars;
                            gl_trace = rule::goal.gl_trace;
                            gl_pre_cond = post_state} in
  mk_derivation_subgoals goal rule [sub_goal]
(* | _ -> mk_derivation_fail goal rule *)

let process_rule_func_call goal rc : derivation =
  let fname, params = rc.rfc_fname, rc.rfc_params in
  let residue = rc.rfc_residue in
  aux_func_call goal (RlFuncCall rc) fname params rc.rfc_substs None residue

let process_rule_func_res goal rcore : derivation =
  let fname, params = rcore.rfr_fname, rcore.rfr_params in
  let res_var = Some rcore.rfr_return in
  let residue = rcore.rfr_residue in
  aux_func_call goal (RlFuncRes rcore) fname params rcore.rfr_substs res_var residue

let process_rule_unfold_pre goal rcore =
  let n_pres = rcore.n_pre in
  let n_goal = {goal with gl_pre_cond = rcore.n_pre;
                          gl_trace = (RlUnfoldPre rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPre rcore) [n_goal]

let process_rule_frame_pred goal rcore =
  let eq_pairs = rcore.rfp_pairs in
  let eq_pairs = List.map (fun (x,y) -> (y,x)) eq_pairs in
  let () = x_tinfo_hp (add_str "substs" pr_substs) eq_pairs no_pos in
  let post = rcore.rfp_post in
  let e_vars = eq_pairs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = remove_exists_vars post exists_vars in
  let n_post = CF.subst eq_pairs n_post in
  let n_exists_vars = CP.diff_svl exists_vars e_vars in
  let n_post = add_exists_vars n_post n_exists_vars in
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  let subgoal = {goal with gl_post_cond = n_post;
                           gl_trace = (RlFramePred rcore)::goal.gl_trace;
                           gl_pre_cond = rcore.rfp_pre} in
  mk_derivation_subgoals goal (RlFramePred rcore) [subgoal]

let process_rule_frame_data goal rcore =
  let substs = rcore.rfd_pairs in
  let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) substs in
  let eq_pf = mkAndList eq_pairs in
  let post = rcore.rfd_post in
  let substs = substs |> List.map (fun (x,y) -> (y,x)) in
  let () = x_tinfo_hp (add_str "substs" pr_substs) substs no_pos in
  let e_vars = substs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = remove_exists_vars post exists_vars in
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  let n_post = CF.subst substs n_post in
  let e_vars = CP.diff_svl exists_vars e_vars in
  let n_post = add_exists_vars n_post e_vars in
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  (* let n_post = CF.add_pure_formula_to_formula eq_pf n_post in
   * let () = x_binfo_hp (add_str "n_post" pr_formula) n_post no_pos in *)
  let subgoal = {goal with gl_post_cond = n_post;
                           gl_trace = (RlFrameData rcore)::goal.gl_trace;
                           gl_pre_cond = rcore.rfd_pre} in
  mk_derivation_subgoals goal (RlFrameData rcore) [subgoal]

let process_rule_unfold_post goal rcore =
  let n_goal = {goal with gl_post_cond = rcore.rp_case_formula;
                          gl_trace = (RlUnfoldPost rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPost rcore) [n_goal]

let process_rule_skip goal =
  if is_code_rule goal.gl_trace then
    mk_derivation_success goal RlSkip
  else mk_derivation_fail goal RlSkip

let process_rule_free goal rc =
  mk_derivation_success goal (RlFree rc)

let process_rule_mk_null goal rcore =
  let n_exp = rcore.rmn_null in
  let var = rcore.rmn_var in
  let all_vars = var::goal.gl_vars in
  let var_e = CP.mkVar var no_pos in
  let pf = CP.mkEqExp var_e n_exp no_pos in
  let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
  let n_goal = {goal with gl_vars = all_vars;
                          gl_pre_cond = n_pre;
                          gl_trace = (RlMkNull rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlMkNull rcore) [n_goal]

let process_rule_allocate goal rcore =
  let data = rcore.ra_data in
  let params = rcore.ra_params in
  let var = rcore.ra_var in
  let hf = CF.mkDataNode var data params no_pos in
  let n_pre = add_h_formula_to_formula hf goal.gl_pre_cond in
  let n_goal = {goal with gl_vars = var::goal.gl_vars;
                          gl_pre_cond = n_pre;
                          gl_trace = (RlAllocate rcore)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlAllocate rcore) [n_goal]

let process_rule_heap_assign goal rcore =
  let lhs = rcore.rha_left in
  let rhs = rcore.rha_right in
  let n_pf = CP.mkEqVar lhs rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf goal.gl_pre_cond in
  let n_goal = {goal with gl_trace = (RlHeapAssign rcore)::goal.gl_trace;
                          gl_pre_cond = n_pre} in
  mk_derivation_subgoals goal (RlHeapAssign rcore) [n_goal]

(*********************************************************************
 * The search procedure
 *********************************************************************)
let rec synthesize_one_goal goal : synthesis_tree =
  let goal = simplify_goal goal in
  let trace = goal.gl_trace in
  if num_of_code_rules trace > 2 || length_of_trace trace > 3
     || List.length trace > 6
     (*current wrong with 5*)
  then
    let () = x_binfo_pp "MORE THAN NUMBER OF RULES ALLOWED" no_pos in
    mk_synthesis_tree_fail goal [] "more than number of rules allowed"
  else
    let cur_time = get_time () in
    let duration = cur_time -. goal.gl_start_time in
    if duration > !synthesis_timeout && not(!enable_i) then
      mk_synthesis_tree_fail goal [] "TIMEOUT"
    else
      let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
      let rules = choose_synthesis_rules goal in
      process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  let rec process atrees rules =
    let rules = if !enable_i then choose_rule_interact goal rules
      else rules in
    match rules with
    | rule::other_rules ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      let atrees = atrees @ [stree] in
      if is_synthesis_tree_success stree then
        let pts = get_synthesis_tree_status stree in
        mk_synthesis_tree_search goal atrees pts
      else process atrees other_rules
    | [] ->
      let () = fail_branch_num := !fail_branch_num + 1 in
      let () = x_tinfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
      mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_one_rule goal rule : derivation =
  let () = x_tinfo_hp (add_str "processing rule" pr_rule) rule no_pos in
  let cur_time = get_time () in
  let duration = cur_time -. goal.gl_start_time in
  if duration > !synthesis_timeout && not(!enable_i) then
    mk_derivation_fail goal rule
  else
    match rule with
    | RlFuncCall rcore -> process_rule_func_call goal rcore
    | RlAllocate rcore -> process_rule_allocate goal rcore
    | RlFuncRes rcore -> process_rule_func_res goal rcore
    (* | RlPreAssign rcore -> process_rule_pre_assign goal rcore *)
    | RlPostAssign rcore -> process_rule_post_assign goal rcore
    | RlAssign rcore -> process_rule_assign goal rcore
    | RlReturn rcore -> process_rule_return goal rcore
    | RlFWrite rcore -> process_rule_fwrite goal rcore
    | RlUnfoldPre rcore -> process_rule_unfold_pre goal rcore
    | RlUnfoldPost rcore -> process_rule_unfold_post goal rcore
    | RlFRead rcore -> process_rule_fread goal rcore
    | RlFramePred rcore -> process_rule_frame_pred goal rcore
    | RlFrameData rcore -> process_rule_frame_data goal rcore
    (* | RlExistsRight rcore -> process_rule_exists_right goal rcore *)
    | RlSkip -> process_rule_skip goal
    | RlMkNull rcore -> process_rule_mk_null goal rcore
    | RlHeapAssign rcore -> process_rule_heap_assign goal rcore
    | RlFree rc -> process_rule_free goal rc

and process_conjunctive_subgoals goal rule (sub_goals: goal list) : synthesis_tree =
  let rec helper goals subtrees st_cores =
    match goals with
    | sub_goal::other_goals ->
      let syn_tree = synthesize_one_goal sub_goal in
      let status = get_synthesis_tree_status syn_tree in
      begin
        match status with
        | StUnkn _ -> mk_synthesis_tree_fail goal [] "one of subgoals failed"
        | StValid st_core ->
          helper other_goals (subtrees@[syn_tree]) (st_cores@[st_core])
      end
    | [] -> let st_core = mk_synthesis_tree_core goal rule st_cores in
      mk_synthesis_tree_derive goal rule subtrees (StValid st_core)
  in helper sub_goals [] []

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal [] "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs

(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)
let synthesize_program goal =
  let goal = simplify_goal goal in
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = get_synthesis_tree_status st in
  let () = x_tinfo_hp (add_str "synthesis tree " pr_st) st no_pos in
  match st_status with
  | StValid st_core ->
    (* let st_core = rm_useless_stc st_core in *)
    let () = x_binfo_hp (add_str "tree_core " pr_st_core) st_core no_pos in
    let i_exp = synthesize_st_core st_core in
    let () = x_tinfo_hp (add_str "iast exp" pr_i_exp_opt) i_exp no_pos in
    i_exp
  | StUnkn _ -> let () = x_binfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
    let () = x_binfo_hp (add_str "fail branches" pr_int) (!fail_branch_num) no_pos in
    None

let synthesize_cast_stmts goal =
  let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = get_synthesis_tree_status st in
  match st_status with
  | StValid st_core ->
    let () = x_binfo_hp (add_str "tree_core " pr_st_core) st_core no_pos in
    let c_exp = st_core2cast st_core in
    let () = x_tinfo_hp (add_str "c_exp" pr_c_exp_opt) c_exp no_pos in
    c_exp
  | StUnkn _ -> let () = x_binfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
    None

let synthesize_wrapper iprog prog proc pre_cond post_cond vars called_procs num =
  let goal = mk_goal_w_procs prog called_procs pre_cond post_cond vars in
  let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
  let start_time = get_time () in
  let iast_exp = synthesize_program goal in
  let duration = get_time () -. start_time in
  let () = synthesis_time := (!synthesis_time) +. duration in
  let pname, i_procs = proc.Cast.proc_name, iprog.Iast.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.Iast.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, false)
    | Some exp0 -> (replace_exp_proc exp0 i_proc num, true) in
  let n_iprocs = List.map (fun x -> if contains pname x.Iast.proc_name
                            then n_proc else x) i_procs in
  ({iprog with I.prog_proc_decls = n_iprocs}, res)

let synthesize_block_wrapper prog orig_proc proc pre_cond post_cond vars =
  (* let all_vars = (CF.fv pre_cond) @ (CF.fv post_cond) in *)
  let goal = mk_goal_w_procs prog [orig_proc] pre_cond post_cond vars in
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let c_exp = synthesize_cast_stmts goal in
  match c_exp with
  | None -> None
  | Some exp ->
    let body = proc.C.proc_body |> Gen.unsome in
    let () = x_tinfo_hp (add_str "body" pr_c_exp) body no_pos in
    let n_body = replace_cexp_aux exp body in
    let () = x_tinfo_hp (add_str "n_body" pr_c_exp) n_body no_pos in
    Some n_body

let synthesize_entailments_one (iprog:IA.prog_decl) prog proc proc_names =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  match hps with
  | None -> ()
  | Some hps_list ->
    let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
        iprog.IA.prog_proc_decls in
    let decl_vars = match iproc.IA.proc_body with
      | None -> []
      | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
    let syn_vars = proc.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let stop = ref false in
    let helper hps =
      if !stop then ()
      else
        let post_hp = List.find (fun x -> x.Cast.hp_name = "N_Q1") hps in
        let pre_hp = List.find (fun x -> x.Cast.hp_name = "N_P1") hps in
        let post = post_hp.Cast.hp_formula in
        let pre = pre_hp.Cast.hp_formula |> remove_exists in
        if isHFalse post then
          let () = x_binfo_hp (add_str "post" pr_formula) post no_pos in
          ()
        else
          let all_procs = CA.list_of_procs prog in
          let filter_fun proc =
            let proc_name = proc.CA.proc_name |> CA.unmingle_name in
            List.mem proc_name proc_names in
          let called_procs = List.filter filter_fun all_procs in
          let (n_iprog, res) = synthesize_wrapper iprog prog proc
              pre post syn_vars called_procs 1 in
          if res then
            try
              let cprog, _ = Astsimp.trans_prog n_iprog in
              let () = Typechecker.check_prog_wrapper n_iprog cprog in
              let () = stop := true in
              repair_res := Some n_iprog
            with _ -> ()
          else () in
    List.iter helper hps_list

let synthesize_entailments_two (iprog:IA.prog_decl) prog proc proc_names =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_two prog entailments in
  let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
      iprog.IA.prog_proc_decls in
  let decl_vars = match iproc.IA.proc_body with
    | None -> []
    | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
  let syn_vars = proc.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
  let helper iprog hps num =
    let post_hp = if num = 1 then
        List.find (fun x -> x.Cast.hp_name = "N_Q1") hps
      else List.find (fun x -> x.Cast.hp_name = "N_Q2") hps in
    let pre_hp = if num = 1 then
        List.find (fun x -> x.Cast.hp_name = "N_P1") hps
      else List.find (fun x -> x.Cast.hp_name = "N_P2") hps in
    let post = post_hp.Cast.hp_formula in
    let pre = pre_hp.Cast.hp_formula |> remove_exists in
    let all_procs = CA.list_of_procs prog in
    let filter_fun proc =
      let proc_name = proc.CA.proc_name |> CA.unmingle_name in
      List.mem proc_name proc_names in
    let called_procs = List.filter filter_fun all_procs in
    let (n_iprog, res) = synthesize_wrapper iprog prog proc
        pre post syn_vars called_procs num in
    (n_iprog, res) in
  match hps with
  | None -> None
  | Some (hps1, hps2) ->
    let hp1 = List.hd hps1 in
    let (n_iprog, res) = helper iprog hp1 1 in
    if res then
      let hp2 = List.hd hps2 in
      let (n_iprog, res) = helper n_iprog hp2 2 in
      if res then Some n_iprog
      else None
    else None


let statement_search (iprog: IA.prog_decl) prog proc (suspicious: I.exp)
    candidates =
  (* let ents = !Synthesis.entailments |> List.rev in *)
  (* let triples = !Synthesis.triples |> List.rev in *)
  (* let hps = prog.CA.prog_hp_decls @ !unk_hps in
   * let hps = Gen.BList.remove_dups_eq eq_hp_decl hps in
   * let s_goal = Searcher.mk_search_goal iprog prog proc triples in
   * let _ = Searcher.solve_unknown_hp s_goal candidates in *)
  None

let synthesize_block_statements iprog prog orig_proc proc decl_vars =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  let syn_vars = proc.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
  let helper cur_res hps =
    if cur_res != None then cur_res
    else
      let post_hp = List.find (fun x -> x.Cast.hp_name = "QQ") hps in
      let pre_hp = List.find (fun x -> x.Cast.hp_name = "PP") hps in
      let post = post_hp.Cast.hp_formula in
      let pre = pre_hp.Cast.hp_formula |> remove_exists in
      let n_block = synthesize_block_wrapper prog orig_proc proc
          pre post syn_vars in
      match n_block with
      | None -> None
      | Some block ->
        let orig_body = orig_proc.C.proc_body |> Gen.unsome in
        x_tinfo_hp (add_str "o_body" pr_c_exp) orig_body no_pos;
        let n_body = replace_cexp_aux block orig_body in
        let n_proc = {orig_proc with C.proc_body = Some n_body} in
        let () = verified_procs := [] in
        try
          (* need to check later*)
          let _ = Typechecker.check_proc_wrapper iprog prog n_proc None [] in
          let () = x_binfo_hp (add_str "n_body" pr_c_exp) n_body no_pos in
          Some n_proc
        with _ -> None in
  match hps with
  | None -> None
  | Some hps_list ->
    let hp = hps_list |> List.hd in
    helper None hp
(* List.fold_left helper None hps_list *)

let infer_block_specs (iprog:IA.prog_decl) prog proc =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  match hps with
  | None -> None
  | Some hps_list ->
    let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
        iprog.IA.prog_proc_decls in
    let decl_vars = match iproc.IA.proc_body with
      | None -> []
      | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
    let syn_vars = proc.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let helper hps =
      let post_hp = List.find (fun x -> x.Cast.hp_name = "QQ") hps in
      let pre_hp = List.find (fun x -> x.Cast.hp_name = "PP") hps in
      let post = post_hp.Cast.hp_formula in
      let pre = pre_hp.Cast.hp_formula |> remove_exists in
      (pre, post) in
    let specs = hps_list |> List.map helper in
    Some specs

