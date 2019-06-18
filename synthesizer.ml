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
  (* let conseq = CF.trans_flow_formula conseq in *)
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let conseq = CF.struc_formula_of_formula conseq no_pos in
  (* let list_ctx, _ = Solver.heap_entail_after_sat_struc 1 prog false false ctx conseq None None
   *     None no_pos None [] in *)
  let list_ctx, _ = Solver.heap_entail_struc_init prog false true
      (CF.SuccCtx[ctx]) conseq no_pos None in
  (* let conseq = CF.struc_formula_of_formula conseq no_pos in
   * let _,list_ctx,_ = sleekcore.sleek_entail_check 1 [] [] prog [] ante conseq in *)
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
  (* let conseq = CF.trans_flow_formula conseq in *)
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

let choose_rule_assign_x goal : rule list =
  let res_vars = CF.fv goal.gl_post_cond |> List.filter CP.is_res_sv in
  let all_vars = goal.gl_vars @ res_vars in
  let post = goal.gl_post_cond in
  let exists_vars = CF.get_exists post in
  let post_vars = CF.fv post in
  let post_vars = CP.diff_svl post_vars exists_vars in
  let post_pf = CF.get_pure goal.gl_post_cond in
  let post_conjuncts = CP.split_conjunctions post_pf in
  let eq_pairs = List.map (find_exists_substs post_vars) post_conjuncts
                 |> List.concat in
  let filter_fun (x,y) = (List.mem x all_vars) &&
                         CP.subset (CP.afv y) all_vars in
  let eq_pairs = eq_pairs |> List.filter filter_fun in
  let ante_pf = CF.get_pure goal.gl_pre_cond in
  let filter_with_ante ante (var, exp) =
    let var = CP.mkVar var no_pos in
    let conseq = CP.mkEqExp var exp no_pos in
    not(SB.check_pure_entail ante conseq) in
  let eq_pairs = eq_pairs |> List.filter (filter_with_ante ante_pf) in
  if eq_pairs = [] then []
  else
    let mk_rule (var, exp) =
      if CP.is_res_sv var then RlReturn {r_exp = exp}
      else
        (* let exp = CP.simp_mult exp; *)
        RlAssign {
          ra_lhs = var;
          ra_rhs = exp
        } in
    List.map mk_rule eq_pairs

let choose_rule_assign goal =
  Debug.no_1 "choose_rule_assign" pr_goal pr_rules
    (fun _ -> choose_rule_assign_x goal) goal

let choose_rule_fwrite goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let prog = goal.gl_prog in
  let pre_nodes = pre |> get_heap |> get_heap_nodes in
  let pr_nodes = pr_list (pr_triple pr_var pr_id pr_vars) in
  let () = x_tinfo_hp (add_str "pre_nodes" pr_nodes) pre_nodes no_pos in
  let post_nodes = post |> get_heap |> get_heap_nodes in
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
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  let pre_proc = specs |> get_pre_cond |> rm_emp_formula in
  let post_proc = specs |> get_post_cond |> rm_emp_formula in
  let a_pre = arg |> extract_var_f pre_proc in
  let l_pre = pre_var |> extract_var_f pre_cond in
  match a_pre, l_pre with
  | Some apre_f, Some lpre_f ->
    is_same_shape apre_f lpre_f
  | _ -> false, []

let unify_arg_x goal proc_decl arg =
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "all vars" pr_vars) (CF.fv pre_cond) no_pos in
  let pre_vars = CF.fv pre_cond |> List.filter (equal_type arg)
               |> List.filter (fun x -> CP.mem x goal.gl_vars) in
  let ss_vars = List.map (fun pre_var ->
      let (x,y) = unify_pair goal proc_decl arg pre_var in
      (pre_var, x, y)) pre_vars in
  let ss_vars = List.filter (fun (_,x,_) -> x) ss_vars in
  let ss_vars = List.map (fun (x,_,y) -> (x,y)) ss_vars in
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
  let aux args_substs =
    let args = List.map fst args_substs in
    let substs = List.map snd args_substs |> List.concat in
    let is_cur_vars = List.for_all (fun x ->
        List.exists (fun y -> CP.eq_spec_var x y) goal.gl_vars) args in
    let has_res_arg = List.exists is_res_sv_syn args in
    let called = is_fcall_called goal.gl_trace args ||
                 is_fres_called goal.gl_trace args in
    let eq_args = List.for_all2 CP.eq_sv args proc_args in
    if is_cur_vars && (not has_res_arg) && (not called) && not eq_args then
      let fc_rule = if contain_res then
          let res = List.find (fun x -> eq_str (CP.name_of_sv x) res_name)
              (CF.fv post_proc) in
          let n_var = CP.mk_typed_sv (CP.type_of_sv res)
              ("rs" ^ (string_of_int !res_num)) in
          let () = res_num := !res_num + 1 in
          RlFuncRes {
            rfr_fname = proc_decl.Cast.proc_name;
            rfr_params = args;
            rfr_return = n_var;
            rfr_substs = substs}
        else RlFuncCall {
            rfc_fname = proc_decl.Cast.proc_name;
            rfc_params = args;
            rfc_substs = substs} in
      [fc_rule]
    else [] in
  ss_args |> List.map aux |> List.concat


let choose_rule_func_call goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let procs = goal.gl_proc_decls in
  if procs = [] then []
  else
    let proc_decl = List.hd procs in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let pre_cond = specs |> get_pre_cond |> rm_emp_formula in
    let post_cond = specs |> get_post_cond |> rm_emp_formula in
    let rules = unify_fcall proc_decl pre_cond post_cond goal in
    rules

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
  let helper_triple (var, data, args) =
    let prog = goal.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let d_arg_pairs = List.filter (fun (x,_) -> not(CP.mem x vars)) d_arg_pairs in
    let helper_arg (arg, field) =
      let rbind = {
          rfr_bound_var = var;
          rfr_field = field;
          rfr_value = arg;
        } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  List.map helper_triple triples |> List.concat
  |> List.filter (fun x -> is_fread_called goal.gl_trace x |> negate)
  |> List.map (fun x -> RlFRead x)

let choose_rule_fread goal =
  Debug.no_1 "choose_rule_fread" pr_goal pr_rules
    (fun _ -> choose_rule_fread_x goal) goal

let get_cond_exp prog formula base recursive puref vars =
  let conjuncs = CP.split_conjunctions puref in
  let aux pf =
    let n_bf = CF.add_pure_formula_to_formula pf formula in
    let n_pf = CP.mkNot_s pf in
    let n_rc = CF.add_pure_formula_to_formula n_pf formula in
    let fst = check_entail_exact_sleek prog n_bf base in
    let snd = check_entail_exact_sleek prog n_rc recursive in
    fst && snd in
  conjuncs |> List.filter (fun x -> CP.subset (CP.fv x) vars)
  |> List.filter aux

let choose_rule_unfold_pre goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let vars, prog = goal.gl_vars, goal.gl_prog in
  let vnodes = get_unfold_view goal.gl_vars pre in
  let helper vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args pre in
    let pre_list = List.filter (fun x -> SB.check_unsat goal.gl_prog x
                                         |> negate) nf in
    if pre_list = [] then []
    (* else if List.length pre_list = 2 then
     *   let vn_var = vnode.CF.h_formula_view_node in
     *   let base_pf = pre_list |> List.hd |> CF.get_pure in
     *   let cond = extract_var_pf base_pf [vn_var] in
     *   let base, recur = List.hd pre_list, pre_list |> List.tl |> List.hd in
     *   let cond_exp = get_cond_exp prog pre base recur cond vars in
     *   if cond_exp = [] then []
     *   else
     *     let cond_exp = CP.join_conjunctions cond_exp in
     *     let rule = RlBranch { rb_if_pre = base |> remove_exists;
     *                           rb_cond = cond_exp;
     *                           rb_else_pre = recur |> remove_exists} in
     *     [rule] *)
    else if List.length pre_list = 1 then
      let n_pre = pre_list |> List.hd |> remove_exists in
      let n_pre = CF.simplify_formula n_pre vars in
      let rule = RlUnfoldPre {n_pre = n_pre} in
      [rule]
    else [] in
  (* if has_unfold_pre goal.gl_trace then []
   * else *)
  vnodes |> List.map helper |> List.concat

let choose_rule_unfold_post goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let res_vars = CF.fv goal.gl_post_cond |> List.filter CP.is_res_sv in
  let vars = goal.gl_vars @ res_vars |> CP.remove_dups_svl in
  let vnodes = get_unfold_view vars post in
  let helper vnode =
    let pr_views, args = need_unfold_rhs goal.gl_prog vnode in
    let nf = do_unfold_view_vnode goal.gl_prog pr_views args post in
    let rules = nf |> List.map (fun f -> RlUnfoldPost {
        rp_var = vnode.CF.h_formula_view_node;
        rp_case_formula = f}) in
    rules in
  if has_unfold_post goal.gl_trace then []
  else vnodes |> List.map helper |> List.concat

let choose_rule_numeric_x goal =
  let vars = goal.gl_vars |> List.filter is_int_var in
  let post_vars = CF.fv goal.gl_post_cond in
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let pre_vars, post_vars = CF.fv pre, CF.fv post in
  let vars_lhs = List.filter (fun x -> (CP.is_res_spec_var x && is_int_var x)
                                     || CP.mem x vars) post_vars in
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
      let defn = SB.infer_templ_defn goal.gl_prog n_pre var_pf tmpl_name other_vars in
      begin
        match defn with
        | Some def ->
          let def = CP.norm_exp def in
          let rule = if CP.is_res_sv cur_var then
              RlReturn { r_exp = def}
            else
              RlAssign {
                ra_lhs = cur_var;
                ra_rhs = def;
              } in [rule]
        | _ -> []
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

let find_frame_node_var goal post_var =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let pre_vars = pre |> CF.fv |> List.filter is_node_var
                 |> List.filter (CP.eq_sv post_var) in
  let pre_pf = CF.get_pure pre in
  let helper_arg pf arg1 arg2 =
    let conseq = CP.mkEqVar arg1 arg2 no_pos in
    SB.check_pure_entail pf conseq in
  let helper_hf hf1 hf2 = match hf1, hf2 with
    | CF.DataNode dn1, CF.DataNode dn2 ->
      let args1 = dn1.CF.h_formula_data_arguments in
      let args2 = dn2.CF.h_formula_data_arguments in
      List.for_all2 (helper_arg pre_pf) args1 args2
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
          let hf1, hf2 = bf1.CF.formula_base_heap, bf2.CF.formula_exists_heap in
          helper_hf hf1 hf2
        | _ -> false
      end
    | _ -> false in
  let frame_vars = pre_vars |> List.filter helper in
  frame_vars |> List.map (fun x -> (post_var, x))

let choose_rule_frame_data goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let post_vars = post |> CF.fv |> List.filter is_node_var in
  let pairs = post_vars |> List.map (find_frame_node_var goal) |> List.concat in
  let filter (lhs, rhs) =
    let n_pre, pre_vars = frame_var_formula pre rhs in
    let n_post, post_vars = frame_var_formula post lhs in
    let check_field f field =
      match extract_var_f f field with
      | Some var_f -> if CF.is_emp_formula var_f then true
        else false
      | _ -> true in
    let check_pre = List.for_all (check_field pre) pre_vars in
    let check_post = List.for_all (check_field post) post_vars in
    if (List.length pre_vars = List.length post_vars) &&
       check_pre && check_post then
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

let choose_rule_exists_right goal =
  let post = goal.gl_post_cond in
  let exists_vars = CF.get_exists post in
  if exists_vars = [] then []
  else
    let post_pf = CF.get_pure goal.gl_post_cond in
    let post_conjuncts = CP.split_conjunctions post_pf in
    let eq_pairs = List.map (find_exists_substs exists_vars) post_conjuncts
                   |> List.concat in
    let collected_exists_vars = eq_pairs |> List.map fst |> CP.remove_dups_svl in
    if collected_exists_vars = [] then []
    else
      let n_post = remove_exists_vars post collected_exists_vars in
      let n_post = subst_term_formula eq_pairs n_post in
      let rule = RlExistsRight {n_post = n_post} in
      [rule]

let rec choose_rule_interact goal rules =
  if rules = [] then
    let () = x_binfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
    rules
  else
    let str = pr_list_ln pr_rule rules in
    let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
    let () = x_binfo_hp (add_str "Rules\n" pr_rules) rules no_pos in
    let choose_str = "Please choose from 1 to "
                     ^ (string_of_int (List.length rules)) ^ ": " in
    let () = x_binfo_pp choose_str no_pos in
    let choice = String.uppercase_ascii (String.trim (read_line ())) in
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

let choose_main_rules goal =
  let rs = [] in
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ choose_rule_frame_pred goal in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_fwrite goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  let rs = rs @ (choose_rule_func_call goal) in
  let rs = rs @ choose_rule_frame_data goal in
  let rs = eliminate_useless_rules goal rs in
  let rs = reorder_rules goal rs in
  rs

let choose_rule_skip goal =
  if is_code_rule goal.gl_trace then
    let prog, pre, post = goal.gl_prog, goal.gl_pre_cond, goal.gl_post_cond in
    let sk = check_entail_exact_sleek prog pre post in
    if sk then let rule = RlSkip in [rule]
    else []
  else []

let choose_synthesis_rules_x goal : rule list =
  let rules =
    try
      let goal = simplify_goal goal in
      let _ = choose_rule_exists_right goal |> raise_rules in
      let _ = choose_rule_skip goal |> raise_rules in
      let _ = choose_main_rules goal |> raise_rules in
      []
    with ERules rs -> rs in
  if !enable_i then choose_rule_interact goal rules
  else rules

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

let process_rule_return goal rcore =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let lhs = goal.gl_post_cond |> CF.fv |> List.find CP.is_res_sv in
  let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rcore.r_exp no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf pre in
  let ent_check = check_entail_exact_sleek goal.gl_prog n_pre post in
  match ent_check with
  | true -> mk_derivation_success goal (RlReturn rcore)
  | false -> mk_derivation_fail goal (RlReturn rcore)

let subs_fwrite formula var field new_val data_decls =
  match (formula:CF.formula) with
  | Base bf -> let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper (hf:CF.h_formula) = match hf with
      | DataNode dnode -> let data_var = dnode.h_formula_data_node in
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

let aux_func_call goal rule fname params subst res_var =
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
  let ent_check, residue =
    check_entail_sleek goal.gl_prog pre_cond params_pre in
  match ent_check, residue with
  | true, Some red ->
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
  | _ ->
    let () = x_tinfo_pp "marking" no_pos in
    mk_derivation_fail goal rule

let process_rule_func_call goal rcore : derivation =
  let fname, params = rcore.rfc_fname, rcore.rfc_params in
  aux_func_call goal (RlFuncCall rcore) fname params rcore.rfc_substs None

let process_rule_fold_left goal rcore : derivation =
  let n_goal = {goal with gl_trace = (RlFoldLeft rcore)::goal.gl_trace;
                          gl_pre_cond = rcore.rfl_pre} in
  mk_derivation_subgoals goal (RlFoldLeft rcore) [n_goal]

let process_rule_func_res goal rcore : derivation =
  let fname, params = rcore.rfr_fname, rcore.rfr_params in
  let res_var = Some rcore.rfr_return in
  aux_func_call goal (RlFuncRes rcore) fname params rcore.rfr_substs res_var

let process_rule_unfold_pre goal rcore =
  let n_pres = rcore.n_pre in
  let n_goal = {goal with gl_trace = (RlUnfoldPre rcore)::goal.gl_trace;
                          gl_pre_cond = rcore.n_pre} in
  mk_derivation_subgoals goal (RlUnfoldPre rcore) [n_goal]

let process_rule_frame_pred goal rcore =
  let eq_pairs = rcore.rfp_pairs in
  (* let eq_pairs = (rcore.rfp_lhs, rcore.rfp_rhs)::eq_pairs in *)
  let eq_pairs = List.map (fun (x,y) -> (y,x)) eq_pairs in
  let () = x_tinfo_hp (add_str "substs" pr_substs) eq_pairs no_pos in
  (* let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) substs in
   * let eq_pf = mkAndList eq_pairs in *)
  let post = rcore.rfp_post in
  let e_var = rcore.rfp_lhs in
  (* let n_post = post in *)
  let n_post = remove_exists_vars post [e_var] in
  let n_post = CF.subst eq_pairs n_post in
  (* let n_post = CF.add_pure_formula_to_formula eq_pf n_post in *)
  let subgoal = {goal with gl_post_cond = n_post;
                           gl_trace = (RlFramePred rcore)::goal.gl_trace;
                           gl_pre_cond = rcore.rfp_pre} in
  mk_derivation_subgoals goal (RlFramePred rcore) [subgoal]

let process_rule_frame_data goal rcore =
  let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) rcore.rfd_pairs in
  let eq_pf = mkAndList eq_pairs in
  let n_post = CF.add_pure_formula_to_formula eq_pf rcore.rfd_post in
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

(*********************************************************************
 * The search procedure
 *********************************************************************)
let rec synthesize_one_goal goal : synthesis_tree =
  if List.length goal.gl_trace > 6 then
    let () = x_tinfo_pp "MORE THAN NUMBER OF RULES ALLOWED" no_pos in
    mk_synthesis_tree_fail goal [] "more than number of rules allowed"
  else
    let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
    let rules = choose_synthesis_rules goal in
    process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  let rec process atrees rules =
    match rules with
    | rule::other_rules ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      let atrees = atrees @ [stree] in
      if is_synthesis_tree_success stree then
        let pts = get_synthesis_tree_status stree in
        mk_synthesis_tree_search goal atrees pts
      else process atrees other_rules
    | [] -> let () = fail_branch_num := !fail_branch_num + 1 in
      let () = x_tinfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
      mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_one_rule goal rule : derivation =
  let () = x_tinfo_hp (add_str "processing rule" pr_rule) rule no_pos in
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore
  | RlFoldLeft rcore -> process_rule_fold_left goal rcore
  | RlFuncRes rcore -> process_rule_func_res goal rcore
  | RlAssign rcore -> process_rule_assign goal rcore
  | RlReturn rcore -> process_rule_return goal rcore
  | RlFWrite rcore -> process_rule_fwrite goal rcore
  | RlUnfoldPre rcore -> process_rule_unfold_pre goal rcore
  | RlUnfoldPost rcore -> process_rule_unfold_post goal rcore
  | RlFRead rcore -> process_rule_fread goal rcore
  | RlFramePred rcore -> process_rule_frame_pred goal rcore
  | RlFrameData rcore -> process_rule_frame_data goal rcore
  | RlExistsLeft rcore -> process_rule_exists_left goal rcore
  | RlExistsRight rcore -> process_rule_exists_right goal rcore
  | RlBranch rcore -> process_rule_branch goal rcore
  | RlSkip -> process_rule_skip goal

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
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = get_synthesis_tree_status st in
  match st_status with
  | StValid st_core ->
    (* let st_core = rm_useless_stc st_core in *)
    let () = x_binfo_hp (add_str "tree_core " pr_st_core) st_core no_pos in
    let i_exp = synthesize_st_core st_core in
    let () = x_tinfo_hp (add_str "iast exp" pr_iast_exp_opt) i_exp no_pos in
    i_exp
  | StUnkn _ -> let () = x_binfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
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

let synthesize_wrapper iprog prog proc pre_cond post_cond vars =
  let all_vars = (CF.fv pre_cond) @ (CF.fv post_cond) in
  let goal = mk_goal_w_procs prog [proc] pre_cond post_cond vars in
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let iast_exp = synthesize_program goal in
  let pname, i_procs = proc.Cast.proc_name, iprog.Iast.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.Iast.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, false)
    | Some exp0 -> (replace_exp_proc exp0 i_proc, true) in
  let n_iprocs = List.map (fun x -> if contains pname x.Iast.proc_name
                            then n_proc else x) i_procs in
  ({iprog with I.prog_proc_decls = n_iprocs}, res)

let synthesize_block_wrapper prog orig_proc proc pre_cond post_cond vars =
  let all_vars = (CF.fv pre_cond) @ (CF.fv post_cond) in
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

let synthesize_entailments (iprog:IA.prog_decl) prog proc =
  let entailments = !Synthesis.entailments |> List.rev in
  let start_time = get_time () in
  let hps = SB.solve_entailments prog entailments in
  let solve_time = get_time() -. start_time in
  match hps with
  | None -> ()
  | Some hps_list ->
    let () = x_binfo_pp "marking" no_pos in
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
        let () = x_binfo_pp "marking" no_pos in
        let post_hp = List.find (fun x -> x.Cast.hp_name = "QQ") hps in
        let pre_hp = List.find (fun x -> x.Cast.hp_name = "PP") hps in
        let post = post_hp.Cast.hp_formula in
        let pre = pre_hp.Cast.hp_formula |> remove_exists in
        let (n_iprog, res) = synthesize_wrapper iprog prog proc
            pre post syn_vars in
        if res then
          try
            let cprog, _ = Astsimp.trans_prog n_iprog in
            let () = Typechecker.check_prog_wrapper n_iprog cprog in
            let () = stop := true in
            repair_res := Some n_iprog
          with _ -> ()
        else () in
    List.iter helper hps_list

let synthesize_block_statements iprog prog orig_proc proc decl_vars =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments prog entailments in
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
        let () = x_tinfo_hp (add_str "o_body" pr_c_exp) orig_body no_pos in
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
    let hp = hps_list |> List.rev |> List.hd in
    helper None hp
(* List.fold_left helper None hps_list *)

let infer_block_specs (iprog:IA.prog_decl) prog proc =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments prog entailments in
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
