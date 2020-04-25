#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

(* open Synthesis *)

module CA = Cast
module IA = Iast
module CF = Cformula
module CP = Cpure
module SB = Songbird
module Syn = Synthesis

let rec process_list applied_fun list = match list with
  | [] -> []
  | head::tail ->
    let rules = applied_fun head in
    if rules = [] then process_list applied_fun tail
    else rules

(* START CHECKING FOR MAKING RULES *)
let check_head_allocate (goal: Syn.goal) : CP.spec_var list =
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let pre_vars = pre |> Syn.get_heap_variables in
  let post_vars = post |> Syn.get_heap_variables in
  let all_vars = goal.Syn.gl_vars |> List.filter Syn.is_node_var in
  let () = x_tinfo_hp (add_str "pre node" Syn.pr_vars) pre_vars no_pos in
  let () = x_tinfo_hp (add_str "post node" Syn.pr_vars) post_vars no_pos in
  let filter_fun x = CP.mem x all_vars || CP.is_res_sv x in
  let n_vars = post_vars |> List.filter filter_fun
               |> List.filter (fun x -> CP.mem x pre_vars |> Syn.negate) in
  let () = x_tinfo_hp (add_str "allocate vars" Syn.pr_vars) n_vars no_pos in
  if not (CP.subset pre_vars post_vars) then n_vars
  else []

let check_head_allocate goal =
  Debug.no_1 "check_head_allocate" Syn.pr_goal Syn.pr_vars
    (fun _ -> check_head_allocate goal) goal

let check_allocate goal pre post =
  let pre_vars = pre |> Syn.get_heap |> Syn.get_heap_nodes in
  let post_vars = post |> Syn.get_heap |> Syn.get_heap_nodes in
  let all_vars = goal.Syn.gl_vars |> List.filter Syn.is_node_var in
  let () = x_binfo_hp (add_str "all vars" Syn.pr_vars) all_vars no_pos in
  let pre_node_vars = pre |> CF.fv |> List.filter Syn.is_node_var in
  let () = x_binfo_hp (add_str "pre nodes" Syn.pr_vars) pre_node_vars no_pos in
  (CP.diff_svl all_vars pre_node_vars != []) ||
  (List.length post_vars = 2 && List.length pre_vars = 1)

let check_mk_null pre post =
  let pre_vars = pre |> Syn.get_heap |> Syn.get_heap_nodes in
  let post_vars = post |> Syn.get_heap |> Syn.get_heap_nodes in
  List.length post_vars - List.length pre_vars = 1

(* let find_equal_var formula var =
 *   let pf = formula |> CF.get_pure |> remove_exists_pf in
 *   let eq_pairs = get_equality_pairs pf in
 *   let find_fun (x,y) = CP.eq_sv x var || CP.eq_sv y var in
 *   let pair = List.find find_fun eq_pairs in
 *   let (fst, snd) = pair in
 *   if CP.eq_sv fst var then snd else fst
 * 
 * let find_equal_var formula var =
 *   Debug.no_2 "find_equal_var" pr_f pr_var pr_var
 *     (fun _ _ -> find_equal_var formula var) formula var *)

let check_goal_procs goal =
  let procs = goal.Syn.gl_proc_decls in
  let aux proc_decl =
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let specs = Syn.get_pre_post specs in
    let aux_pre_post (pre, post) =
      let post_vars = post |> Syn.get_heap_variables in
      let pre_vars = pre |> Syn.get_heap_variables in
      let () = x_tinfo_hp (add_str "pre vars" Syn.pr_vars) pre_vars no_pos in
      let () = x_tinfo_hp (add_str "post vars" Syn.pr_vars) post_vars no_pos in
      List.length post_vars > List.length pre_vars in
    List.exists aux_pre_post specs in
  List.exists aux procs

let check_goal_procs goal =
  Debug.no_1 "check_goal_procs" Syn.pr_goal string_of_bool
    (fun _ -> check_goal_procs goal) goal

let check_head_allocate_wrapper goal =
  let vars = check_head_allocate goal in
  vars != [] && not (check_goal_procs goal)

let check_head_allocate_wrapper goal =
  Debug.no_1 "check_head_allocate_wrapper" Syn.pr_goal string_of_bool
    (fun _ -> check_head_allocate_wrapper goal) goal

(* END CHECKING FOR MAKING RULES *)

let get_subst_from_list_context (l_ctx: CF.list_context) =
  let aux_ent_state ent_s =
    let fst, snd = ent_s.CF.es_subst in
    List.combine fst snd in
  let rec aux_ctx ctx = match ctx with
    | CF.Ctx ent_state -> aux_ent_state ent_state
    | CF.OCtx (ctx1, ctx2) -> (aux_ctx ctx1) @ (aux_ctx ctx2) in
  match l_ctx with
  | CF.FailCtx _ -> []
  | CF.SuccCtx ctx_list -> ctx_list |> List.map aux_ctx |> List.concat

let get_subst_from_list_context l_ctx =
  Debug.no_1 "get_subst_from_list_context" Cprinter.string_of_list_context
    Syn.pr_substs (fun _ -> get_subst_from_list_context l_ctx) l_ctx

let get_evars_from_list_context (l_ctx: CF.list_context) =
  let rec aux_ctx ctx = match ctx with
    | CF.Ctx ent_state -> ent_state.CF.es_evars
    | CF.OCtx (ctx1, ctx2) -> (aux_ctx ctx1) @ (aux_ctx ctx2) in
  match l_ctx with
  | CF.FailCtx _ -> []
  | CF.SuccCtx ctx_list -> ctx_list |> List.map aux_ctx |> List.concat

let get_es_pf_from_list_context (l_ctx: CF.list_context) =
  let rec aux_ctx ctx = match ctx with
    | CF.Ctx ent_state -> ent_state.CF.es_aux_conseq
    | CF.OCtx (ctx1, ctx2) ->
      let pf1 = aux_ctx ctx1 in
      let pf2 = aux_ctx ctx2 in
      CP.mkAnd pf1 pf2 no_pos in
  match l_ctx with
  | CF.FailCtx _ -> report_error no_pos "cannot applied"
  | CF.SuccCtx ctx_list -> ctx_list |> List.map aux_ctx |> CP.join_conjunctions

let rename_conseq (conseq: CF.formula) =
  let e_vars = CF.get_exists conseq in
  let h_args = Syn.get_heap_args conseq
               |> List.filter (fun x -> CP.mem x e_vars |> Syn.negate) in
  let n_args = h_args |> List.map CP.fresh_spec_var in
  let substs = List.combine h_args n_args in
  let n_conseq = conseq |> CF.subst substs in
  let n_pf = Syn.mk_pure_form_from_eq_pairs substs in
  let n_conseq = CF.add_pure_formula_to_formula n_pf n_conseq in
  Syn.add_exists_vars n_conseq n_args

let rename_conseq conseq =
  Debug.no_1 "rename_conseq" Syn.pr_f Syn.pr_f
    (fun _ -> rename_conseq conseq) conseq

let get_prefix (s:string) : string =
  let slen = (String.length s) in
  let ri =
    try
      let n = (String.rindex s '_') in
      let l = (slen-(n+1)) in
      if (l==0) then slen-1
      else n
    with  _ -> slen in
  String.sub s 0 ri

let check_entail_sleek prog ante (conseq:CF.formula) =
  let conseq = rename_conseq conseq in
  let ante = CF.set_flow_in_formula (CF.mkTrueFlow ()) ante in
  let exists_vars = CF.get_exists conseq in
  let conseq = CF.set_flow_in_formula (CF.mkTrueFlow ()) conseq in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let conseq = CF.struc_formula_of_formula conseq no_pos in
  let list_ctx, _ = Solver.heap_entail_struc_init prog false true
      (CF.SuccCtx[ctx]) conseq no_pos None in
  let common_prefix fst snd =
    let fst_prefix = fst |> CP.name_of_sv |> get_prefix in
    let snd_prefix = snd |> CP.name_of_sv |> get_prefix in
    eq_str fst_prefix snd_prefix in
  let get_exists_pair old_vars n_evar =
    let old_evar = List.find (common_prefix n_evar) old_vars in
    (old_evar, n_evar) in
  let get_exists_pair old_vars n_var =
    Debug.no_2 "get_exists_pair" Syn.pr_vars Syn.pr_var (pr_pair Syn.pr_var Syn.pr_var)
      (fun _ _ -> get_exists_pair old_vars n_var) old_vars n_var in
  let is_fail_ctx list_ctx =
    if CF.isFailCtx list_ctx then true
    else
      let residue = CF.formula_of_list_context list_ctx in
      Syn.isHFalse residue in
  if is_fail_ctx list_ctx then false, None
  else
    let () = x_tinfo_hp (add_str "list ctx" Syn.pr_ctxs) list_ctx no_pos in
    let residue = CF.formula_of_list_context list_ctx in
    let evars_residue = get_evars_from_list_context list_ctx in
    let evar_substs = exists_vars |> List.map (get_exists_pair evars_residue) in
    let () = x_tinfo_hp (add_str "evar subst" Syn.pr_substs) evar_substs no_pos in
    let n_pf =
      let residue_pairs = get_subst_from_list_context list_ctx in
      let fst_vars = List.map fst evar_substs in
      let residue_pairs = residue_pairs |> List.filter
                            (fun (x,_) -> CP.mem x fst_vars) in
      let pf1 = Syn.mk_pure_form_from_eq_pairs residue_pairs in
      let pf2 = get_es_pf_from_list_context list_ctx in
      CP.mkAnd pf1 pf2 no_pos in
    let n_pf = CP.subst evar_substs n_pf in
    let residue = CF.add_pure_formula_to_formula n_pf residue in
    true, Some residue

let check_entail_sleek prog ante conseq =
  Debug.no_2 "check_entail_sleek" Syn.pr_f Syn.pr_f
    (pr_pair string_of_bool Syn.pr_f_opt)
    (fun _ _ -> check_entail_sleek prog ante conseq) ante conseq

let check_entail_exact_sleek prog ante (conseq:CF.formula) =
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
  Debug.no_2 "check_entail_exact_sleek" Syn.pr_f Syn.pr_f string_of_bool
    (fun _ _ -> check_entail_exact_sleek prog ante conseq) ante conseq

let check_entail_exact_wrapper prog ante conseq =
  let ante = Syn.rm_emp_formula ante in
  let conseq = Syn.rm_emp_formula conseq in
  if Syn.contains_lseg prog then
    SB.check_entail_exact prog ante conseq
  else
    let start = get_time () in
    let res = check_entail_exact_sleek prog ante conseq in
    let duration = get_time () -. start in
    let () = if duration > 1.0 then
        let () = x_tinfo_hp (add_str "ent" Syn.pr_ent) (ante, conseq) no_pos in
        x_tinfo_hp (add_str "duration" string_of_float) duration no_pos in
    res

let check_entail_exact_wrapper prog ante conseq =
  Debug.no_2 "check_entail_exact_wrapper" Syn.pr_f Syn.pr_f
    string_of_bool
    (fun _ _ -> check_entail_exact_wrapper prog ante conseq) ante conseq

let check_entail_wrapper prog ante conseq =
  let ante = Syn.rm_emp_formula ante in
  let conseq = Syn.rm_emp_formula conseq in
  if Syn.contains_lseg prog then
    SB.check_entail_residue prog ante conseq
  else
    let start = get_time () in
    let res = check_entail_sleek prog ante conseq in
    let duration = get_time () -. start in
    let () = if duration > 1.0 then
        let () = x_tinfo_hp (add_str "ent" Syn.pr_ent) (ante, conseq) no_pos in
        x_tinfo_hp (add_str "duration" string_of_float) duration no_pos in
    res

let check_entail_wrapper prog ante conseq =
  let ante = Syn.remove_exists ante in
  Debug.no_2 "check_entail_wrapper" Syn.pr_f Syn.pr_f
    (pr_pair string_of_bool Syn.pr_f_opt)
    (fun _ _ -> check_entail_wrapper prog ante conseq) ante conseq

let check_sat_wrapper prog formula =
  if Syn.contains_lseg prog then
    SB.check_sat prog formula
  else Solver.unsat_base_nth 7 prog (ref 0) formula |> Syn.negate

let check_unsat_wrapper prog formula =
  if Syn.contains_lseg prog then
    SB.check_unsat prog formula
  else Solver.unsat_base_nth 7 prog (ref 0) formula

let check_unsat_wrapper prog formula =
  Debug.no_1 "check_unsat_wrapper" Syn.pr_f string_of_bool
    (fun _ -> check_unsat_wrapper prog formula) formula

let choose_rule_assign_end_node (goal: Syn.goal) : Syn.rule list =
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let pre_vars = pre_cond |> CF.fv in
  let post_vars = post_cond |> Syn.get_heap_variables in
  let filter_fun x = CP.mem x all_vars in
  let lhs_vars = post_vars |> List.filter filter_fun in
  let () = x_tinfo_hp (add_str "lhs_vars" Syn.pr_vars) lhs_vars no_pos in
  let lhs_vars = lhs_vars |> List.filter (fun x -> not(CP.mem x pre_vars)) in
  let () = x_tinfo_hp (add_str "lhs_vars" Syn.pr_vars) lhs_vars no_pos in
  if List.length lhs_vars = 1 then
    let rhs_vars = pre_vars |> List.filter Syn.is_node_var
                   |> List.filter (fun x -> CP.mem x all_vars)
                   |> List.filter (fun x -> not(CP.mem x post_vars)) in
    let () = x_tinfo_hp (add_str "rhs_vars" Syn.pr_vars) rhs_vars no_pos in
    let lhs_var = List.hd lhs_vars in
    let aux_var rhs_var =
      let n_pf = CP.mkEqVar lhs_var rhs_var no_pos in
      let n_pre = CF.add_pure_formula_to_formula n_pf pre_cond in
      let prog = goal.Syn.gl_prog in
      if check_entail_exact_wrapper prog n_pre post_cond then
        let rule = if CP.is_res_sv lhs_var then
            Syn.RlReturn {
              Syn.r_exp = CP.Var (rhs_var, no_pos);
              Syn.r_checked = true}
          else Syn.RlAssign {
              Syn.ra_lhs = lhs_var;
              Syn.ra_rhs = CP.Var (rhs_var, no_pos);
              Syn.ra_numeric = true;
            } in
        [rule]
      else [] in
    rhs_vars |> process_list aux_var
  else []

let choose_rule_assign_end_node goal =
  Debug.no_1 "choose_rule_assign_end_node" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_assign_end_node goal) goal

let choose_rule_assign_end_numeric (goal: Syn.goal) : Syn.rule list=
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let all_vars = goal.Syn.gl_vars |> List.filter Syn.is_int_var in
  let pre_vars = pre |> CF.fv in
  let post_vars = CF.fv post in
  let post_vars = List.filter Syn.is_int_var post_vars in
  let filter_fun x = CP.mem x all_vars || CP.is_res_sv x in
  let lhs_vars = post_vars |> List.filter filter_fun in
  let () = x_tinfo_hp (add_str "lhs_vars" Syn.pr_vars) lhs_vars no_pos in
  let lhs_vars = lhs_vars |> List.filter (fun x -> not(CP.mem x pre_vars)) in
  let () = x_tinfo_hp (add_str "lhs_vars" Syn.pr_vars) lhs_vars no_pos in
  let rhs_vars = goal.gl_trace |> Syn.get_trace_vars in
  if List.length lhs_vars = 1 then
    let lhs_var = List.hd lhs_vars in
    let aux rhs_var =
      let n_pf = CP.mkEqVar lhs_var rhs_var no_pos in
      let n_pre = CF.add_pure_formula_to_formula n_pf goal.gl_pre_cond in
      let prog = goal.Syn.gl_prog in
      if check_entail_exact_wrapper prog n_pre goal.gl_post_cond then
        let rule = if CP.is_res_sv lhs_var then
            Syn.RlReturn {
              r_exp = CP.Var (rhs_var, no_pos);
              r_checked = true}
          else
            Syn.RlAssign {
              ra_lhs = lhs_var;
              ra_rhs = CP.Var (rhs_var, no_pos);
              ra_numeric = true;
            } in
        [rule]
      else [] in
    rhs_vars |> process_list aux
  else []

let choose_rule_assign_end goal =
  let rules = choose_rule_assign_end_node goal in
  if rules = [] then
    choose_rule_assign_end_numeric goal
  else rules

let choose_rule_assign_end goal =
  Debug.no_1 "choose_rule_assign_end" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_assign_end goal) goal

let choose_rule_assign goal : Syn.rule list =
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let post = goal.Syn.gl_post_cond in
  let res_vars = post |> CF.fv |> List.filter CP.is_res_sv in
  let all_vars = goal.gl_vars @ res_vars in
  let post_vars = CF.fv post in
  let () = x_tinfo_hp (add_str "vars" Syn.pr_vars) post_vars no_pos in
  let post_pf = CF.get_pure goal.Syn.gl_post_cond |> Syn.remove_exists_pf in
  let () = x_tinfo_hp (add_str "pf" Syn.pr_pf) post_pf no_pos in
  let post_conjuncts = CP.split_conjunctions post_pf in
  let eq_pairs = List.map (Syn.find_exists_substs post_vars) post_conjuncts
                 |> List.concat in
  let filter_fun (x,y) = (List.mem x all_vars) &&
                         CP.subset (CP.afv y) all_vars in
  let eq_pairs = eq_pairs |> List.filter filter_fun in
  let ante_filter ante (var, exp) =
    let ante_pf = CF.get_pure ante in
    let var = CP.mkVar var no_pos in
    let conseq = CP.mkEqExp var exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula conseq ante in
    not(SB.check_pure_entail ante_pf conseq) &&
    (check_sat_wrapper goal.Syn.gl_prog n_pre) in
  let eq_pairs = eq_pairs |> List.filter (ante_filter goal.Syn.gl_pre_cond) in
  let mk_rule (var, exp) =
    if CP.is_res_sv var then Syn.RlReturn {r_exp = exp; r_checked = false;}
    else
      RlAssign {
        ra_lhs = var;
        ra_rhs = exp;
        ra_numeric = false;
      } in
  List.map mk_rule eq_pairs

let choose_rule_assign goal =
  Debug.no_1 "choose_rule_assign" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_assign goal) goal

let get_node_vars post_cond =
  let post_vars = post_cond |> CF.fv |> List.filter Syn.is_node_var in
  let exists_vars = post_cond |> CF.get_exists |> List.filter Syn.is_node_var in
  let post_vars = post_vars@exists_vars in
  let n_post = Syn.remove_exists post_cond in
  let filter_fun var =
    let var_f = Syn.extract_var_f n_post var in
    match var_f with
    | Some f -> CF.is_emp_formula f |> Syn.negate
    | None -> false in
  post_vars |> List.filter filter_fun

let choose_rule_heap_assign goal =
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let all_vars = goal.gl_vars in
  let pre_nodes = get_node_vars pre in
  let post_nodes = get_node_vars post in
  let pre_pf = CF.get_pure pre in
  let post_pf = CF.get_pure post in
  let ante_pf = CP.mkAnd pre_pf post_pf no_pos in
  let mk_rule lhs rhs =
    if Syn.has_heap_assign lhs rhs goal.Syn.gl_trace then []
    else
      let rule =
        Syn.RlHeapAssign {
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
    let post = Syn.remove_exists post in
    let pre_f = Syn.extract_var_f pre pre_node |> Gen.unsome in
    let post_f = Syn.extract_var_f post post_node |> Gen.unsome in
    let pre_hf = Syn.get_hf pre_f in
    let post_hf = Syn.get_hf post_f in
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
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let all_vars = goal.gl_vars in
  let prog = goal.Syn.gl_prog in
  let pre_nodes = pre |> Syn.get_heap |> Syn.get_heap_nodes in
  let pr_nodes = pr_list (pr_triple Syn.pr_var pr_id Syn.pr_vars) in
  let () = x_tinfo_hp (add_str "pre_nodes" pr_nodes) pre_nodes no_pos in
  let post_nodes = post |> Syn.get_heap |> Syn.get_heap_nodes in
  let () = x_tinfo_hp (add_str "post_nodes" pr_nodes) post_nodes no_pos in
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
  let pr_typed_id (_,b) = b in
  let pr_tuples = pr_list (pr_triple Syn.pr_var Syn.pr_var pr_typed_id) in
  let () = x_tinfo_hp (add_str "tuples" pr_tuples) tuples no_pos in
  let get_new_field_val (cur_var, n_val, cur_field) =
    let replaced_value =
      if List.mem n_val all_vars then n_val
      else
        let eq_type_vars = all_vars |> List.filter (Syn.equal_type n_val) in
        let aux_check_entail replaced_var =
          let conseq = CP.mkEqVar n_val replaced_var no_pos in
          let ante = CF.get_pure post in
          SB.check_pure_entail ante conseq in
        let new_vars = eq_type_vars |> List.filter aux_check_entail in
        if new_vars = [] then n_val
        else new_vars |> List.hd in
    (cur_var, replaced_value, cur_field) in
  let tuples = tuples |> List.map get_new_field_val in
  let filter_tuple (cur_var,n_val, _) =
    (* new field value has to be in the all_vars set *)
    CP.mem n_val all_vars && CP.mem cur_var all_vars in
  let tuples = tuples |> List.filter filter_tuple in
  let () = x_tinfo_hp (add_str "filtered tuples" pr_tuples) tuples no_pos in
  let mk_fwrite_rule (var, n_val, field) =
    Syn.RlFWrite {
      rfw_bound_var = var;
      rfw_field = field;
      rfw_value = n_val;
    } in
  tuples |> List.map mk_fwrite_rule

let choose_rule_fwrite goal =
  Debug.no_1 "choose_rule_fwrite" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_fwrite goal) goal

let rec mk_args_input args = match args with
  | [] -> []
  | [h] -> List.map (fun x -> [x]) h
  | h::t -> let tmp = mk_args_input t in
    let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
    List.concat head_added

let unify_arg goal proc_decl (argument: CP.spec_var) =
  let vars = goal.Syn.gl_vars in
  vars |> List.filter (Syn.equal_type argument)

let check_func_arguments goal proc_decl (args: CP.spec_var list) =
  let prog = goal.Syn.gl_prog in
  let proc_args = proc_decl.CA.proc_args
                  |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let args_called = Syn.is_fcall_called goal.Syn.gl_trace args in
  let called = Syn.is_fcall_ever_called goal.gl_trace proc_decl.CA.proc_name in
  let eq_args = List.for_all2 CP.eq_sv args proc_args in
  let pre_vars = goal.Syn.gl_pre_cond |> CF.fv in
  let post_vars = goal.Syn.gl_post_cond |> CF.fv in
  let non_init = args |> List.exists
                   (fun x -> not(CP.mem x pre_vars) && CP.mem x post_vars) in
  if non_init || args_called || eq_args || called then []
  else
    let () = x_tinfo_hp (add_str "args" Syn.pr_vars) args no_pos in
    let pre_cond = goal.Syn.gl_pre_cond in
    let substs = List.combine proc_args args in
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let specs = Syn.get_pre_post specs in
    let (proc_pre, proc_post) = List.hd specs in
    let () = x_tinfo_hp (add_str "proc_pre" Syn.pr_f) proc_pre no_pos in
    let n_proc_pre = CF.subst substs proc_pre in
    let n_proc_post = CF.subst substs proc_post in
    let () = x_tinfo_hp (add_str "proc_pre" Syn.pr_f) n_proc_pre no_pos in
    let e_vars = n_proc_pre |> CF.fv |> List.filter (fun x -> not(CP.mem x args)) in
    let n_vars = e_vars |> List.map CP.fresh_spec_var in
    let n_substs = List.combine e_vars n_vars in
    let n_proc_pre = CF.subst n_substs n_proc_pre in
    let n_proc_post = CF.subst n_substs n_proc_post in
    let n_proc_pre = Syn.add_exists_vars n_proc_pre n_vars in
    let () = x_tinfo_hp (add_str "goal pre" Syn.pr_f) pre_cond no_pos in
    let () = x_tinfo_hp (add_str "proc_pre" Syn.pr_f) n_proc_pre no_pos in
    let () = x_tinfo_hp (add_str "proc_post" Syn.pr_f) n_proc_post no_pos in
    let check, residue = x_add check_entail_wrapper prog pre_cond n_proc_pre in
    if check then
      let residue = Gen.unsome residue |> Syn.remove_exists in
      let () = x_tinfo_hp (add_str "residue" Syn.pr_f) residue no_pos in
      let n_pre = Syn.add_formula_to_formula n_proc_post residue in
      let () = x_tinfo_hp (add_str "n_pre" Syn.pr_f) n_pre no_pos in
      let n_pre_vars = n_pre |> CF.fv in
      let n_var, n_pre = if List.exists CP.is_res_sv n_pre_vars then
          let res = List.find (fun x -> eq_str (CP.name_of_sv x) res_name)
              n_pre_vars in
          let n_var = CP.mk_typed_sv (CP.type_of_sv res)
              ("rs" ^ (string_of_int !Syn.res_num)) in
          let n_pre = n_pre |> CF.subst [(res, n_var)] in
          let () = Syn.res_num := !Syn.res_num + 1 in
          Some n_var, n_pre
        else None, n_pre in
      let () = x_tinfo_hp (add_str "n_pre" Syn.pr_f) n_pre no_pos in
      let rule = Syn.RlFuncCall {
          rfc_fname = proc_decl.Cast.proc_name;
          rfc_params = args;
          rfc_new_pre = n_pre;
          rfc_return = n_var;
        } in
      [rule]
    else []

let check_func_arguments goal proc_decl args =
  Debug.no_2 "check_func_arguments" Syn.pr_goal Syn.pr_vars Syn.pr_rules
    (fun _ _ -> check_func_arguments goal proc_decl args) goal args

let eq_tuple tuple1 tuple2 =
  let commutative_int tuple1 tuple2 =
    let int_args1 = tuple1 |> List.filter Syn.is_int_var in
    let int_args2 = tuple2 |> List.filter Syn.is_int_var in
    CP.subset int_args1 int_args2 && CP.subset int_args2 int_args1 in
  let commutative_node tuple1 tuple2 =
    let node_args1 = tuple1 |> List.filter Syn.is_node_var in
    let node_args2 = tuple2 |> List.filter Syn.is_node_var in
    CP.subset node_args1 node_args2 && CP.subset node_args2 node_args1 in
  commutative_int tuple1 tuple2 && commutative_node tuple1 tuple2

let check_eq_args prog proc_args proc_pre proc_post args1 args2 =
  let int_args = proc_args |> List.filter Syn.is_int_var in
  let node_args = proc_args |> List.filter Syn.is_node_var in
  if List.length proc_args <= 3
  && (List.length int_args = 2 || List.length node_args = 2) then
    let n_args = (List.rev int_args) @ (List.rev node_args) in
    let n_proc_pre = proc_pre |> CF.subst (List.combine proc_args n_args) in
    let n_proc_post = proc_post |> CF.subst (List.combine proc_args n_args) in
    let () = x_tinfo_hp (add_str "n_proc pre" Syn.pr_f) n_proc_pre no_pos in
    let () = x_tinfo_hp (add_str "n_proc post" Syn.pr_f) n_proc_post no_pos in
    let cond1,_ = x_add check_entail_wrapper prog proc_pre n_proc_pre in
    if cond1 then
      let cond2,_ = x_add check_entail_wrapper prog proc_post n_proc_post in
      if cond2 then
        eq_tuple args1 args2
      else false
    else false
  else false

let unify_fcall proc_decl proc_pre proc_post goal =
  let proc_args = proc_decl.Cast.proc_args |>
                  List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let ss_args = proc_args |> List.map (unify_arg goal proc_decl) in
  let ss_args = mk_args_input ss_args in
  let () = x_tinfo_hp (add_str "proc pre" Syn.pr_f) proc_pre no_pos in
  let () = x_tinfo_hp (add_str "proc pre" Syn.pr_f) proc_post no_pos in
  (* let eq_args args1 args2 = check_eq_args goal.Syn.gl_prog proc_args proc_pre
   *     proc_post args1 args2 in *)
  let pre_nodes = goal.Syn.gl_pre_cond |> Syn.get_heap_variables in
  let filter_nodes args =
    let node_args = args |> List.filter Syn.is_node_var in
    List.for_all (fun x -> CP.mem x pre_nodes) node_args in
  let filter_args args =
    let n_args = args |> CP.remove_dups_svl in
    List.length n_args = List.length args in
  let ss_args = ss_args |> List.filter filter_args in
  (* let ss_args = ss_args |> Gen.BList.remove_dups_eq eq_args in *)
  let ss_args = ss_args |> List.filter filter_nodes in
  let trace_vars = goal.gl_trace |> Syn.get_trace_vars in
  let filter_trace_vars args =
    args |> List.exists (fun x -> CP.mem x trace_vars) |> Syn.negate in
  let ss_args = ss_args |> List.filter filter_trace_vars in
  let rules = ss_args |> List.map (check_func_arguments goal proc_decl) in
  rules |> List.concat

let choose_rule_func_call goal =
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let procs = goal.Syn.gl_proc_decls in
  let aux proc_decl =
    let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
    let spec_pairs = Syn.get_pre_post specs in
    let pre_cond, post_cond = List.hd spec_pairs in
    let () = x_tinfo_hp (add_str "pre" Syn.pr_f) pre_cond no_pos in
    let () = x_tinfo_hp (add_str "post" Syn.pr_f) post_cond no_pos in
    let rules = unify_fcall proc_decl pre_cond post_cond goal in
    rules in
  procs |> List.map aux |> List.concat

let choose_rule_func_call goal =
  Debug.no_1 "choose_rule_func_call" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_func_call goal) goal

let choose_rule_unfold_pre goal =
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let vnodes = Syn.get_unfold_view goal.Syn.gl_vars pre in
  let helper vnode =
    let pr_views, args = Syn.need_unfold_rhs goal.Syn.gl_prog vnode in
    let nf = Syn.do_unfold_view_vnode goal.Syn.gl_prog pr_views args pre in
    let () = x_tinfo_hp (add_str "nf" (pr_list_mln Syn.pr_f)) nf no_pos in
    let pre_list = List.filter (fun x -> check_unsat_wrapper goal.Syn.gl_prog x
                                         |> Syn.negate) nf in
    let () = x_tinfo_hp (add_str "nf after" (pr_list_mln Syn.pr_f)) nf no_pos in
    if pre_list = [] then []
    else if List.length pre_list = 1 then
      let n_pre = pre_list |> List.hd |> Syn.remove_exists |> Syn.rm_emp_formula in
      let rule =
        Syn.RlUnfoldPre {n_pre = n_pre;
                         unfold_pre_var = vnode.CF.h_formula_view_node} in
      [rule]
    else [] in
  vnodes |> List.map helper |> List.concat

let choose_rule_unfold_pre goal =
  Debug.no_1 "choose_rule_unfold_pre" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_unfold_pre goal) goal

let choose_rule_unfold_post goal =
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let prog = goal.Syn.gl_prog in
  let res_vars = CF.fv goal.Syn.gl_post_cond |> List.filter CP.is_res_sv in
  let vars = goal.Syn.gl_vars @ res_vars |> CP.remove_dups_svl in
  let e_vars = CF.get_exists post |> List.filter Syn.is_node_var in
  let () = x_tinfo_hp (add_str "e_vars" Syn.pr_vars) e_vars no_pos in
  let vnodes = Syn.get_unfold_view vars post in
  let e_vnodes = Syn.get_unfold_view e_vars post in
  let pre_pf = CF.get_pure pre in
  let filter_fun formula =
    let n_formula = CF.add_pure_formula_to_formula pre_pf formula in
    check_sat_wrapper prog n_formula in
  (* let helper_exists vnode =
   *   let pr_views, args = need_unfold_rhs goal.Syn.gl_prog vnode in
   *   let nf = do_unfold_view_vnode goal.Syn.gl_prog pr_views args post in
   *   let nf = nf |> List.filter filter_fun in
   *   if List.length nf = 1 then
   *     let case_f = List.hd nf in
   *     let rule =  RlUnfoldPost {
   *         rp_var = vnode.CF.h_formula_view_node;
   *         rp_case_formula = case_f} in
   *     [rule]
   *   else [] in *)
  let helper vnode =
    let pr_views, args = Syn.need_unfold_rhs goal.Syn.gl_prog vnode in
    let nf = Syn.do_unfold_view_vnode goal.Syn.gl_prog pr_views args post in
    let nf = nf |> List.filter filter_fun in
    let () = x_tinfo_hp (add_str "nf" (pr_list_mln Syn.pr_f)) nf no_pos in
    let rules = nf |> List.map (fun f ->
        Syn.RlUnfoldPost {
          rp_var = vnode.CF.h_formula_view_node;
          rp_case_formula = f}) in
    rules |> List.rev in
  if Syn.has_unfold_post goal.gl_trace (* || check_head_allocate_wrapper goal *) then []
  else
    let rules1 = vnodes |> List.map helper |> List.concat in
    let rules2 = e_vnodes |> List.map helper |> List.concat in
    rules1@rules2

let choose_rule_numeric_end goal =
  let vars = goal.Syn.gl_vars |> List.filter Syn.is_int_var in
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let pre_vars = CF.fv pre in
  let post_vars = CF.fv post in
  let post_vars = List.filter Syn.is_int_var post_vars in
  let () = x_tinfo_hp (add_str "post vars" Syn.pr_vars) post_vars no_pos in
  let vars_lhs = List.filter (fun x -> CP.mem x vars || CP.is_res_sv x)
      post_vars in
  let vars_lhs = List.filter (fun x -> CP.mem x pre_vars |> Syn.negate) vars_lhs in
  let () = x_tinfo_hp (add_str "vars_lhs" Syn.pr_vars) vars_lhs no_pos in
  let rec vars2exp vars = match vars with
    | [] -> CP.mkIConst 0 no_pos
    | [h] -> CP.Var (h, no_pos)
    | h::tail ->
      let e2 = vars2exp tail in
      CP.Add ((CP.Var (h, no_pos)), e2, no_pos) in
  let aux_pairs cur_var rhs =
    let rhs = CP.Var (rhs, no_pos) in
    let rhs_one = CP.Add (rhs, CP.mkIConst 1 no_pos, no_pos) in
    let added_pf = CP.mkEqExp (CP.Var (cur_var, no_pos)) rhs_one no_pos in
    let n_pre = CF.add_pure_formula_to_formula added_pf pre in
    let () = x_tinfo_hp (add_str "n_pre" Syn.pr_f) n_pre no_pos in
    if check_entail_exact_wrapper goal.Syn.gl_prog n_pre post then
      let rule = if CP.is_res_sv cur_var then
          Syn.RlReturn { r_exp = rhs_one;
                     r_checked = true;
                   }
        else
          Syn.RlAssign {
            ra_lhs = cur_var;
            ra_rhs = rhs_one;
            ra_numeric = true;
          } in
      [rule]
    else [] in
  let create_templ all_vars cur_var =
    let other_vars = List.filter (fun x -> not(CP.eq_sv x cur_var)) all_vars in
    other_vars |> process_list (aux_pairs cur_var) in
  let list1 = vars_lhs |> process_list (create_templ vars) in
  let aux_list_vars vars_lhs =
    let res_vars = vars_lhs |> List.filter CP.is_res_sv in
    if res_vars != [] then
      let res_var = res_vars |> List.hd in
      let rhs_vars = vars |> List.filter (fun x -> CP.eq_sv x res_var |> Syn.negate) in
      if List.length rhs_vars >= 2 then
        let rhs_exp = vars2exp rhs_vars in
        let rhs_one = CP.Add (rhs_exp, CP.mkIConst 1 no_pos, no_pos) in
        let added_pf = CP.mkEqExp (CP.Var (res_var, no_pos)) rhs_one no_pos in
        let n_pre = CF.add_pure_formula_to_formula added_pf pre in
        if check_entail_exact_wrapper goal.Syn.gl_prog n_pre post then
          let rule =
            Syn.RlReturn { Syn.r_exp = rhs_one;
                           Syn.r_checked = true} in
          [rule]
        else []
      else []
    else [] in
  if list1 = [] then
    aux_list_vars vars_lhs
  else list1

let choose_rule_numeric goal =
  Debug.no_1 "choose_rule_numeric" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_numeric_end goal) goal

let find_instantiate_var goal var =
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let post_vars = CF.fv post in
  let all_vars = CF.fv pre |> List.filter Syn.is_node_var in
  let pf1 = CF.get_pure pre in
  let pf2 = CF.get_pure post in
  let ante = CP.mkAnd pf1 pf2 no_pos |> Syn.remove_exists_vars_pf in
  let () = x_tinfo_hp (add_str "ante" Syn.pr_pf) ante no_pos in
  let helper f1 f2 =
    let f2 = Syn.remove_exists f2 in
    match f1, f2 with
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
      let var1_f = Syn.extract_var_f post var1 in
      let var2_f = Syn.extract_var_f pre var2 in
      match var1_f, var2_f with
      | Some f1, Some f2 -> helper f1 f2
      | _ -> false in
  let () = x_binfo_hp (add_str "all vars" Syn.pr_vars) all_vars no_pos in
  let equal_vars = List.filter (fun x -> compare_two_vars var x) all_vars in
  equal_vars

let find_instantiate_var goal var =
  Debug.no_2 "find_instantiate_var" Syn.pr_goal Syn.pr_var Syn.pr_vars
    (fun _ _ -> find_instantiate_var goal var) goal var

let choose_rule_return goal =
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let post = goal.Syn.gl_post_cond in
  let pre = goal.Syn.gl_pre_cond in
  (* let post_vars = post |> get_node_vars in *)
  let all_vars = goal.Syn.gl_vars in
  let check_return res_var r_var =
    if CP.eq_typed_spec_var res_var r_var then
      let n_pf = CP.mkEqVar res_var r_var no_pos in
      let n_pre = CF.add_pure_formula_to_formula n_pf pre in
      let () = x_tinfo_hp (add_str "post" Syn.pr_f) post no_pos in
      check_entail_exact_wrapper goal.Syn.gl_prog n_pre post
    else false in
  let aux pre_var =
    let rule =
      Syn.RlReturn {
        r_exp = CP.mkVar pre_var no_pos;
        r_checked = true;
      } in
    [rule] in
  let aux_return pre post =
    (* let pre_vars = pre |> Syn.get_heap_variables in *)
    let pre_vars = pre |> CF.fv in
                   (* |> List.filter (fun x -> CP.mem x goal.gl_vars) in *)
    (* let post_vars = post |> Syn.get_heap_variables in *)
    let post_vars = post |> CF.fv in
    let res_vars = post_vars |> List.filter CP.is_res_sv in
    if res_vars != [] then
      let res_var = res_vars |> List.hd in
      let pre_vars = pre_vars |> List.filter (fun x -> not(CP.mem x post_vars)) in
      let pre_vars = pre_vars |> List.filter (fun x -> CP.mem x all_vars) in
      let () = x_binfo_hp (add_str "pre_vars" Syn.pr_vars) pre_vars no_pos in
      let pre_vars = pre_vars |> List.filter (check_return res_var) in
      let () = x_binfo_hp (add_str "pre_vars" Syn.pr_vars) pre_vars no_pos in
      pre_vars |> List.map aux |> List.concat
    else [] in
  aux_return pre post
(* if List.length post_vars = 1 then
 *   let p_var = List.hd post_vars in
 *   if CP.is_res_sv p_var then
 *     let pre = goal.Syn.gl_pre_cond in
 *     let pre_vars = pre |> get_node_vars
 *                    |> List.filter (fun x -> CP.mem x all_vars && not(CP.is_res_sv x)) in
 *     let pre_vars = List.filter (check_return p_var) pre_vars in
 *     pre_vars |> List.map aux |> List.concat
 *   else []
 * else [] *)

let choose_rule_allocate_return goal : Syn.rule list =
  let prog = goal.Syn.gl_prog in
  let all_vars = goal.Syn.gl_vars in
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let () = x_tinfo_hp (add_str "pre" Syn.pr_f) goal.Syn.gl_pre_cond no_pos in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let data_decls = prog.CA.prog_data_decls in
  let others = ["__Exc"; "thrd"; "Object"; "int_ptr"; "barrier"] in
  let filter_fun x = not(List.mem x.CA.data_name others) in
  let data_decls = data_decls |> List.filter filter_fun in
  let rec check_eq_params args = match args with
    | [] -> false
    | h::tail -> if CP.mem h tail then true
      else check_eq_params tail in
  let check_params_end args =
    if check_eq_params args then false
    else
      let args = List.filter Syn.is_node_var args in
      let pre_vars = pre |> Syn.get_heap |> Syn.get_heap_nodes in
      let pre_nodes = pre_vars |> List.map (fun (x,_,y) -> (x,y)) in
      let pre_nodes = pre_nodes |> List.filter (fun (x,_) -> CP.mem x args) in
      let pre_vars = pre_nodes |> List.map fst in
      let other_args = List.filter (fun x -> not(CP.mem x pre_vars)) args in
      let all_vars = pre_nodes |> List.map (fun (x,y) -> x::y) |> List.concat in
      let all_vars = other_args@all_vars in
      let rm_duplicate_vars = CP.remove_dups_svl all_vars in
      if List.length all_vars != List.length rm_duplicate_vars then false
      else true in
  let mk_rule_end data_decl allocate_var args =
    if check_params_end args then
      let data = data_decl.CA.data_name in
      let hf = CF.mkDataNode allocate_var data args no_pos in
      let n_pre = Syn.add_h_formula_to_formula hf goal.Syn.gl_pre_cond in
      if check_entail_exact_wrapper prog n_pre post then
        let rule = {
          Syn.ra_var = allocate_var;
          Syn.ra_data = data;
          Syn.ra_params = args;
          Syn.ra_pre = n_pre;
          Syn.ra_end = true;
          Syn.ra_lookahead = None;
        } in
        [rule]
      else []
    else [] in
  let aux_end allocate_var data_decl =
    let n_eq_var al_var x = CP.eq_sv al_var x |> Syn.negate in
    let all_vars = List.filter (n_eq_var allocate_var) all_vars in
    let pre_heaps = pre |> Syn.get_heap_variables in
    let all_vars = all_vars |> List.filter (fun x ->
        if Syn.is_node_var x then CP.mem x pre_heaps else true) in
    let args = data_decl.CA.data_fields |> List.map fst
               |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let arg_types = List.map CP.type_of_sv args in
    let helper_typ typ =
      all_vars |> List.filter (fun x -> CP.type_of_sv x = typ) in
    let args_list = arg_types |> List.map helper_typ in
    let args_groups = args_list |> mk_args_input in
    let filter_fun list = Syn.has_allocate goal.gl_trace list |> Syn.negate in
    let args_groups = args_groups |> List.filter filter_fun in
    let args_groups = args_groups |> Gen.BList.remove_dups_eq eq_tuple in
    let common_args args =
      let n_args = CP.remove_dups_svl args in
      List.length n_args = List.length args in
    let args_groups = args_groups |> List.filter common_args in
    let pre_vars = pre |> CF.fv in
    let filter_init args = args |> List.for_all (fun x -> CP.mem x pre_vars) in
    let args_groups = args_groups |> List.filter filter_init in
    let past_allocate args =
      let past_list = !Syn.allocate_list in
      List.exists (CP.eq_spec_var_list args) past_list |> Syn.negate in
    let args_groups = args_groups |> List.filter past_allocate in
    let pre_allocated_vars = pre |> Syn.get_heap_args |> List.filter Syn.is_node_var in
    let allocated_var_filter args =
      args |> List.exists (fun x -> CP.mem x pre_allocated_vars) |> Syn.negate in
    let args_groups = args_groups |> List.filter allocated_var_filter in
    let () = x_tinfo_hp (add_str "args list after" (pr_list_mln Syn.pr_vars)) args_groups no_pos in
    let rec process_list list = match list with
      | [] -> []
      | head::tail ->
        let rules = mk_rule_end data_decl allocate_var head in
        if rules != [] then rules
        else process_list tail in
    let rules = args_groups |> process_list in
    let () = Syn.allocate_list := args_groups @ (!Syn.allocate_list) in
    let rules = rules |> List.map (fun x -> Syn.RlAllocate x) in
    rules in
  let allocate_vars = check_head_allocate goal in
  if allocate_vars != [] then
    let allocate_var = List.hd allocate_vars in
    let () = x_tinfo_hp (add_str "var" Syn.pr_var) allocate_var no_pos in
    let rules = data_decls |> List.map (aux_end allocate_var) |> List.concat in
    rules
  else []

let choose_rule_allocate_return goal =
  Debug.no_1 "choose_rule_allocate_return" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_allocate_return goal) goal

let choose_rule_fread goal =
  let vars = goal.Syn.gl_vars in
  let pre_cond = goal.Syn.gl_pre_cond in
  (* let pre_node_vars = pre_cond |> Syn.get_heap |> Syn.get_heap_nodes
   *                     |> List.map (fun (x, _,_) -> x) in *)
  let rec helper_hf (hf:CF.h_formula) = match hf with
    | CF.DataNode dnode -> let dn_var = dnode.CF.h_formula_data_node in
      if List.exists (fun x -> CP.eq_spec_var x dn_var) vars then
        let dn_name = dnode.CF.h_formula_data_name in
        let dn_args = dnode.CF.h_formula_data_arguments in
        [(dn_var, dn_name, dn_args)]
      else []
    | CF.Star sf -> let hf1, hf2 = sf.h_formula_star_h1, sf.h_formula_star_h2 in
      (helper_hf hf1) @ (helper_hf hf2)
    | _ -> [] in
  let rec helper_f (f:CF.formula) = match f with
    | CF.Base bf -> helper_hf bf.CF.formula_base_heap
    | CF.Or bf -> let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
      (helper_f f1) @ (helper_f f2)
    | CF.Exists bf -> helper_hf bf.formula_exists_heap in
  let triples = helper_f pre_cond in
  let trace_vars = goal.gl_trace |> Syn.get_trace_vars in
  let filter_triple (x,_,_) = CP.mem x trace_vars |> Syn.negate in
  let triples = triples |> List.filter filter_triple in
  let pr_triples = pr_list (pr_triple Syn.pr_var pr_id Syn.pr_vars) in
  let () = x_tinfo_hp (add_str "triples" pr_triples) triples no_pos in
  let helper_triple (var, data, args) =
    let prog = goal.Syn.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let filter_fun (x, _) = CP.mem x vars |> Syn.negate in
    let d_arg_pairs = List.filter filter_fun d_arg_pairs in
    let helper_arg (arg, field) =
      let rbind = {
          Syn.rfr_bound_var = var;
          Syn.rfr_field = field;
          Syn.rfr_value = arg;
          Syn.rfr_lookahead = None;
        } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  let filter_fread_int rule =
    let var = rule.Syn.rfr_value in
    let all_vars = goal.Syn.gl_vars in
    if CP.is_int_var var && List.exists CP.is_int_var all_vars then false
    else true in
  let filter_rule rule =
    let var = rule.Syn.rfr_value in
    let () = x_tinfo_hp (add_str "var" Syn.pr_var) var no_pos in
    let n_goal = {goal with Syn.gl_vars = var::goal.Syn.gl_vars;
                            gl_trace = (RlFRead rule)::goal.gl_trace} in
    let n_rules = [] in
    let n_rules = n_rules @ (choose_rule_unfold_pre n_goal) in
    let n_rules = n_rules @ (choose_rule_func_call n_goal) in
    let n_rules = n_rules @ (choose_rule_fwrite n_goal) in
    let n_rules = n_rules @ (choose_rule_allocate_return n_goal) in
    let () = x_binfo_hp (add_str "fread lookahead rules" Syn.pr_rules) n_rules no_pos in
    if List.exists (Syn.rule_use_var var) n_rules then
      let n_goal = { n_goal with gl_lookahead = n_rules} in
      let rule = {rule with rfr_lookahead = Some n_goal} in
      (true, rule)
    else (false, rule) in
  triples |> List.map helper_triple |> List.concat
  |> List.filter (fun x -> Syn.is_fread_called goal.Syn.gl_trace x
                           |> Syn.negate)
  |> List.filter filter_fread_int
  |> List.map filter_rule |> List.filter (fun (x,_) -> x) |> List.map snd
  |> List.map (fun x -> Syn.RlFRead x)

let choose_rule_fread goal =
  Debug.no_1 "choose_rule_fread" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_fread goal) goal

let choose_rule_new_num goal : Syn.rule list =
  if Syn.has_new_num goal.Syn.gl_trace then []
  else
    let int_vars = goal.Syn.gl_vars |> List.filter Syn.is_int_var |> List.rev in
    let aux_int var =
      let n_var = CP.fresh_spec_var var in
      let n_var2 = CP.fresh_spec_var var in
      let one = CP.mkIConst 1 no_pos in
      let n_var_e = CP.mkVar var no_pos in
      let minus_one = CP.mkSubtract n_var_e one no_pos in
      let plus_one = CP.mkAdd n_var_e one no_pos in
      let minus_rule = {
        Syn.rnn_var = n_var;
        Syn.rnn_num = minus_one;
        Syn.rnn_lookahead = None;
      } in
      let plus_rule = {
        Syn.rnn_var = n_var2;
        Syn.rnn_num = plus_one;
        Syn.rnn_lookahead = None;
      } in
      [minus_rule; plus_rule] in
    let filter_rule rule =
      let n_exp = rule.Syn.rnn_num in
      let var = rule.Syn.rnn_var in
      let all_vars = var::goal.Syn.gl_vars in
      let var_e = CP.mkVar var no_pos in
      let pf = CP.mkEqExp var_e n_exp no_pos in
      let n_pre = CF.add_pure_formula_to_formula pf goal.Syn.gl_pre_cond in
      let n_goal = {goal with Syn.gl_vars = all_vars;
                              Syn.gl_pre_cond = n_pre;
                              gl_trace = (RlNewNum rule)::goal.gl_trace} in
      let () = x_tinfo_hp (add_str "var" Syn.pr_var) var no_pos in
      let () = x_tinfo_hp (add_str "exp" Syn.pr_exp) n_exp no_pos in
      let n_rules = choose_rule_allocate_return n_goal in
      let n_rules, early_end = if n_rules = [] then
          let n_rules = n_rules @ (choose_rule_func_call n_goal) in
          let n_rules = n_rules @ (choose_rule_fwrite n_goal) in
          (n_rules, false)
        else (n_rules, true) in
      let () = x_tinfo_hp (add_str "rules" Syn.pr_rules) n_rules no_pos in
      if early_end || List.exists (Syn.rule_use_var var) n_rules then
        let n_goal = {n_goal with Syn.gl_lookahead = n_rules} in
        let n_rule = {rule with Syn.rnn_lookahead = Some n_goal} in
        (true, n_rule, early_end)
      else (false, rule, false) in
    let list = int_vars |> List.map aux_int |> List.concat in
    let rec process_list rules list = match list with
      | [] -> rules
      | head::tail ->
        let (passed, n_rule, early_end) = filter_rule head in
        if early_end then [n_rule]
        else
        if passed then process_list (n_rule::rules) tail
        else process_list rules tail in
    let list = list |> process_list [] in
    list |> List.map (fun x -> Syn.RlNewNum x)

let choose_rule_new_num goal =
  Debug.no_1 "choose_rule_new_num" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_new_num goal) goal

let find_frame_node_var goal all_vars post_var =
  let all_vars = List.filter (fun x -> not(CP.eq_sv x post_var)) all_vars in
  let () = x_tinfo_hp (add_str "post var" Syn.pr_var) post_var no_pos in
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let pre_vars = get_node_vars pre in
  let pre_vars = List.filter (fun x -> not(CP.mem x all_vars)) pre_vars in
  let () = x_tinfo_hp (add_str "pre vars" Syn.pr_vars) pre_vars no_pos in
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
      let () = x_tinfo_hp (add_str "args1" Syn.pr_vars) args1 no_pos in
      let () = x_tinfo_hp (add_str "args2" Syn.pr_vars) args2 no_pos in
      List.exists2 helper_arg args1 args2
    | _ -> false in
  let helper pre_var =
    let pre_f = Syn.extract_var_f pre pre_var in
    let post_f = Syn.extract_var_f post post_var in
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
  (* if check_head_allocate_wrapper goal then []
   * else *)
    let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
    let post_vars = post |> get_node_vars in
    let () = x_tinfo_hp (add_str "post vars" Syn.pr_vars) post_vars no_pos in
    let pairs = post_vars |> List.map (find_frame_node_var goal post_vars)
                |> List.concat in
    let pr_pairs = pr_list (pr_pair Syn.pr_var Syn.pr_var) in
    let () = x_tinfo_hp (add_str "pairs" pr_pairs) pairs no_pos in
    let filter (lhs, rhs) =
      let n_pre, pre_vars = Syn.frame_var_formula pre rhs in
      let n_post, post_vars = Syn.frame_var_formula post lhs in
      let () = x_tinfo_hp (add_str "pre_vars" Syn.pr_vars) pre_vars no_pos in
      let () = x_tinfo_hp (add_str "post_vars" Syn.pr_vars) post_vars no_pos in
      if (List.length pre_vars = List.length post_vars) then
        let pre_cond_vars = pre |> CF.fv in
        if CP.mem lhs pre_cond_vars && not(CP.eq_sv lhs rhs) then []
        else
          let pre_vars = rhs::pre_vars in
          let post_vars = lhs::post_vars in
          let rule = Syn.RlFrameData {
              Syn.rfd_lhs = lhs;
              Syn.rfd_rhs = rhs;
              Syn.rfd_pairs = List.combine pre_vars post_vars;
              Syn.rfd_pre = n_pre;
              Syn.rfd_post = n_post;
            } in [rule]
      else [] in
    pairs |> List.map filter |> List.concat

let choose_rule_allocate goal : Syn.rule list =
  let prog = goal.Syn.gl_prog in
  let all_vars = goal.Syn.gl_vars in
  let pre = goal.Syn.gl_pre_cond in
  let post = goal.Syn.gl_post_cond in
  let () = x_tinfo_hp (add_str "all vars" Syn.pr_vars) all_vars no_pos in
  let () = x_tinfo_hp (add_str "pre" Syn.pr_f) goal.Syn.gl_pre_cond no_pos in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let data_decls = prog.CA.prog_data_decls in
  let others = ["__Exc"; "thrd"; "Object"; "int_ptr"; "barrier"] in
  let filter_fun x = not(List.mem x.CA.data_name others) in
  let data_decls = data_decls |> List.filter filter_fun in
  let filter_rule rule =
    let n_pre = rule.Syn.ra_pre in
    let n_vars = rule.Syn.ra_var::goal.Syn.gl_vars in
    let n_goal = {goal with Syn.gl_vars = n_vars;
                            Syn.gl_pre_cond = n_pre;
                            Syn.gl_trace = (RlAllocate rule)::goal.gl_trace} in
    let n_rules = [] in
    (* let n_rules = (choose_rule_assign n_goal) @ n_rules in *)
    let n_rules = (choose_rule_fwrite n_goal) @ n_rules in
    let n_rules = (choose_rule_return n_goal) @ n_rules in
    let n_rules = (choose_rule_frame_data n_goal) @ n_rules in
    let () = x_tinfo_hp (add_str "arg" Syn.pr_var) rule.ra_var no_pos in
    let () = x_tinfo_hp (add_str "pre" Syn.pr_f) n_pre no_pos in
    let () = x_tinfo_hp (add_str "rules" Syn.pr_rules) n_rules no_pos in
    if List.exists (Syn.rule_use_var rule.Syn.ra_var) n_rules then
      let n_goal = {n_goal with Syn.gl_lookahead = n_rules} in
      let n_rule = {rule with ra_lookahead = Some n_goal} in
      (true, n_rule)
    else (false, rule) in
  let filter_eq_var rule =
    let params = rule.Syn.ra_params in
    let rec aux params = match params with
      | [] -> false
      | h :: tail -> if CP.mem h tail then true
        else aux tail in
    if aux params then false else true in
  let mk_rule data_decl args =
    let data = data_decl.CA.data_name in
    let var_name = fresh_name () in
    let var = CP.mk_typed_sv (Named data) var_name in
    let hf = CF.mkDataNode var data args no_pos in
    let n_pre = Syn.add_h_formula_to_formula hf goal.Syn.gl_pre_cond in
    {
      Syn.ra_var = var;
      Syn.ra_data = data;
      Syn.ra_params = args;
      Syn.ra_pre = n_pre;
      Syn.ra_end = false;
      Syn.ra_lookahead = None;
    } in
  let aux data_decl =
    let args = data_decl.CA.data_fields |> List.map fst
               |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let () = x_tinfo_hp (add_str "args" Syn.pr_vars) args no_pos in
    let arg_types = List.map CP.type_of_sv args in
    let helper_typ typ =
      all_vars |> List.filter (fun x -> CP.type_of_sv x = typ) in
    let args_list = arg_types |> List.map helper_typ in
    let args_groups = args_list |> mk_args_input in
    let filter_fun list = Syn.has_allocate goal.gl_trace list |> Syn.negate in
    let args_groups = args_groups |> List.filter filter_fun in
    let args_groups = args_groups |> Gen.BList.remove_dups_eq eq_tuple in
    let rules = args_groups |> List.map (mk_rule data_decl) in
    rules in
  if check_allocate goal pre post then
    let rules = data_decls |> List.map aux |> List.concat in
    let () = x_binfo_hp (add_str "rules before" (pr_list Syn.pr_rule_alloc)) rules no_pos in
    let rules = rules |> List.filter filter_eq_var in
    let () = x_binfo_hp (add_str "rules after" (pr_list Syn.pr_rule_alloc)) rules no_pos in
    (* let rules = List.map filter_rule rules |> List.filter (fun (x,_) -> x)
     *             |> List.map snd in *)
    rules |> List.map (fun x -> Syn.RlAllocate x)
  else []

let choose_rule_allocate goal : Syn.rule list =
  Debug.no_1 "choose_rule_allocate" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_allocate goal) goal

let aux_post_assign goal =
  let post = goal.Syn.gl_post_cond in
  (* let all_vars = goal.gl_vars in *)
  let e_vars = CF.get_exists post in
  let () = x_tinfo_hp (add_str "e_vars" Syn.pr_vars) e_vars no_pos in
  let post_pf = CF.get_pure post |> Syn.remove_exists_vars_pf in
  let post_conjuncts = CP.split_conjunctions post_pf in
  let () = x_tinfo_hp (add_str "conjuncts" (pr_list Syn.pr_pf)) post_conjuncts
      no_pos in
  let eq_pairs = List.map (Syn.find_exists_substs e_vars) post_conjuncts
                 |> List.concat in
  let pr_pairs = pr_list (pr_pair Syn.pr_var Syn.pr_exp) in
  let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
  let filter_fun (x,y) =
    let vars = CP.afv y in
    vars = [] in
  let filter_eq = Gen.BList.remove_dups_eq
      (fun x1 x2 -> CP.eq_sv (fst x1) (fst x2)) in
  let eq_pairs = eq_pairs |> filter_eq |> List.filter filter_fun in
  let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
  let mk_rule (var, exp) = {
    Syn.rmn_var = var;
    Syn.rmn_null = exp;
    Syn.rmn_lookahead = None;
  } in
  let rules = List.map mk_rule eq_pairs in
  rules

let choose_rule_mk_null goal : Syn.rule list =
  let prog = goal.Syn.gl_prog in
  if Syn.has_mk_null goal.gl_trace then []
  else
    let trace = goal.gl_trace in
    if List.length trace > 2 then []
    else
      let data_decls = prog.CA.prog_data_decls in
      let others = ["__Exc"; "thrd"; "Object"; "__Error"; "__MayError"; "__Fail";
                    "char_star"; "int_ptr_ptr"; "int_ptr"; "lock"; "barrier";
                    "__RET"; "__ArrBoundErr"; "__DivByZeroErr"; "String"] in
      let filter_fun x = not(List.mem x.CA.data_name others) in
      let data_decls = data_decls |> List.filter filter_fun in
      let filter_rule (rule : Syn.rule_mk_null) =
        let var = rule.rmn_var in
        let n_exp = rule.rmn_null in
        let all_vars = var::goal.Syn.gl_vars in
        let var_e = CP.mkVar var no_pos in
        let pf = CP.mkEqExp var_e n_exp no_pos in
        let n_pre = CF.add_pure_formula_to_formula pf goal.Syn.gl_pre_cond in
        let n_post = Syn.remove_exists_vars goal.Syn.gl_post_cond [var] in
        let n_goal = {goal with Syn.gl_vars = all_vars;
                                Syn.gl_pre_cond = n_pre;
                                Syn.gl_post_cond = n_post;
                                gl_trace = (RlMkNull rule)::goal.gl_trace} in
        let () = x_tinfo_hp (add_str "var" Syn.pr_var) var no_pos in
        (* let n_rules = [] in
         * let n_rules = n_rules @ (choose_rule_allocate_return n_goal) in
         * (\* let n_rules = n_rules @ (choose_rule_func_call n_goal) in *\)
         * let n_rules = n_rules @ (choose_rule_fwrite n_goal) in
         * let () = x_tinfo_hp (add_str "rules" Syn.pr_rules) n_rules no_pos in
         * let n_goal = {n_goal with gl_lookahead = n_rules} in
         * let rule = {rule with rmn_lookahead = Some n_goal} in
         * if List.exists (Syn.rule_use_var var) n_rules then *)
        (true, rule)
        (* else (false, rule) *)
      in
      let aux_rule data_decl =
        let data_name = data_decl.CA.data_name in
        let typ = Globals.Named data_name in
        let name = Globals.fresh_name () in
        let var = CP.mk_typed_sv typ name in
        let n_exp = CP.Null no_pos in
        let rule = {
          Syn.rmn_null = n_exp;
          Syn.rmn_var = var;
          Syn.rmn_lookahead = None;
        } in
        rule
      in
      let list1 = data_decls |> List.map aux_rule in
      (* let list2 = aux_post_assign goal in *)
      let list2 = [] in
      let list = list1 @ list2 |> List.map filter_rule
                 |> List.filter (fun (x,y) -> x)
                 |> List.map snd in
      list |> List.map (fun x -> Syn.RlMkNull x)

let choose_rule_mk_null goal : Syn.rule list =
  Debug.no_1 "choose_rule_mk_null" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_mk_null goal) goal

let rec choose_rule_interact goal rules =
  if rules = [] then
    let () = x_binfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
    rules
  else
    let () = x_binfo_hp (add_str "goal" Syn.pr_goal) goal no_pos in
    let () = x_binfo_hp (add_str "Rules\n" Syn.pr_rules) rules no_pos in
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
        let () = x_binfo_hp (add_str "You chose" (pr_list_ln Syn.pr_rule))
            chosen_rules no_pos in
        chosen_rules @ other_rules

(* let choose_rule_free goal =
 *   let pre = goal.Syn.gl_pre_cond in
 *   let post = goal.gl_post_cond in
 *   let sk, residue = check_entail_wrapper goal.Syn.gl_prog pre post in
 *   if sk then
 *     let residue = Gen.unsome residue in
 *     if not(CF.is_emp_formula residue) then
 *       let pre_nodes = goal.Syn.gl_pre_cond |> Syn.get_heap |> Syn.get_heap_nodes in
 *       let post_nodes = goal.gl_post_cond |> Syn.get_heap |> Syn.get_heap_nodes in
 *       let pre_node_vars = pre_nodes |> List.map (fun (x, _,_) -> x) in
 *       let post_node_vars = post_nodes |> List.map (fun (x, _,_) -> x) in
 *       let free_vars = CP.diff_svl pre_node_vars post_node_vars in
 *       let in_vars x = CP.mem x goal.gl_vars in
 *       if List.length free_vars = 1 && List.for_all in_vars free_vars then
 *         let rule = RlFree {
 *             rd_vars = free_vars;
 *           } in
 *         [rule]
 *       else []
 *     else []
 *   else [] *)

let choose_rule_frame_pred goal =
  (* if check_head_allocate_wrapper goal then []
   * else *)
  let pre, post = goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let exists_vars = CF.get_exists post |> List.filter Syn.is_node_var in
  let () = x_tinfo_hp (add_str "exists_var" Syn.pr_vars) exists_vars no_pos in
  let filter (lhs, rhs) =
    let framed_pre, pre_vars = Syn.frame_var_formula pre rhs in
    let framed_post, post_vars = Syn.frame_var_formula post lhs in
    if (List.length pre_vars = List.length post_vars) then
      let pre_vars = rhs::pre_vars in
      let post_vars = lhs::post_vars in
      let eq_pairs = List.combine pre_vars post_vars in
      let eq_pairs = List.map (fun (x,y) -> (y,x)) eq_pairs in
      let exists_vars = CF.get_exists framed_post in
      let n_post = Syn.remove_exists_vars framed_post exists_vars in
      let n_post = CF.subst eq_pairs n_post in
      let n_pf = Syn.mk_pure_form_from_eq_pairs eq_pairs in
      let n_post = CF.add_pure_formula_to_formula n_pf n_post in
      let n_post = Syn.add_exists_vars n_post exists_vars in
      let post_e_vars = n_post |> CF.get_exists in
      let pre_eq_pairs = eq_pairs |> List.filter
                           (fun (x,y) -> not(CP.mem x post_e_vars)) in
      let n_pre_pf = pre_eq_pairs |> Syn.mk_pure_form_from_eq_pairs in
      let n_pre = CF.add_pure_formula_to_formula n_pre_pf framed_pre in
      let prog = goal.Syn.gl_prog in
      if check_unsat_wrapper prog n_pre || check_unsat_wrapper prog n_post
      then []
      else
        let n_post = Syn.remove_exists_vars framed_post exists_vars in
        let n_post = CF.subst eq_pairs n_post in
        let post_vars = eq_pairs |> List.map fst in
        let e_vars = CP.diff_svl exists_vars post_vars in
        let n_post = Syn.add_exists_vars n_post e_vars in
        let () = x_tinfo_hp (add_str "n_pre" Syn.pr_f) n_pre no_pos in
        let () = x_tinfo_hp (add_str "n_post" Syn.pr_f) n_post no_pos in
        let rule =
          Syn.RlFramePred {
            rfp_lhs = lhs;
            rfp_rhs = rhs;
            rfp_pre = framed_pre;
            rfp_post = n_post;
          } in [rule]
    else [] in
  let helper var =
    let eq_vars = find_instantiate_var goal var in
    eq_vars |> List.map (fun x -> (var, x)) in
  let pairs = exists_vars |> List.map helper |> List.concat in
  let () = x_binfo_hp (add_str "instantiate_pairs"
                         (pr_list (pr_pair Syn.pr_var Syn.pr_var))) pairs no_pos in
  let n_pairs = pairs |> List.map filter in
  n_pairs |> List.concat

let choose_rule_frame_pred goal =
  Debug.no_1 "choose_rule_frame_pred" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_rule_frame_pred goal) goal


let choose_rule_free (goal: Syn.goal) residue =
  let free_vars = Syn.get_heap_variables residue in
  if List.length free_vars = 1 &&
     List.for_all (fun x -> List.mem x goal.Syn.gl_vars) free_vars
  then
    let rule = Syn.RlFree {
        rd_vars = free_vars;
      } in
    [rule]
  else []

let choose_rule_skip goal =
  (* if is_code_rule goal.gl_trace then *)
  let prog, pre, post = goal.Syn.gl_prog, goal.Syn.gl_pre_cond, goal.Syn.gl_post_cond in
  let sk, residue = check_entail_wrapper prog pre post in
  if sk then
    let residue = Gen.unsome residue in
    if CF.is_emp_formula residue then
      let rule = Syn.RlSkip in
      [rule]
    else choose_rule_free goal residue
  else []
(* else [] *)

(*********************************************************************
 * Choosing rules
 *********************************************************************)
let choose_rules_after_mk_null rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_new_num rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_allocate rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_func_call goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_allocate goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_fread rs goal =
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  (* let rs = rs @ (choose_rule_allocate goal) in *)
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_all_rules rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_func_call goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_allocate goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_main_rules goal =
  let cur_time = get_time () in
  let duration = cur_time -. goal.Syn.gl_start_time in
  if duration > !synthesis_timeout && not(!enable_i) then []
  else
    let rs = goal.gl_lookahead in
    let () = x_tinfo_hp (add_str "lookahead" Syn.pr_rules) rs no_pos in
    let goal = {goal with gl_lookahead = []} in
    let rs = if goal.gl_trace = [] then
        choose_all_rules rs goal
      else
        let head = List.hd goal.gl_trace in
        match head with
        (* | RlMkNull _ -> choose_rules_after_mk_null rs goal *)
        | RlNewNum _ -> choose_rules_after_new_num rs goal
        | RlAllocate _ -> choose_rules_after_allocate rs goal
        | RlFRead _ -> choose_rules_after_fread rs goal
        | _ -> choose_all_rules rs goal in
    let rs = Syn.eliminate_useless_rules goal rs in
    let rs = Syn.reorder_rules goal rs in
    rs

let choose_synthesis_rules goal : Syn.rule list =
  let rules =
    try
      let rs = goal.Syn.gl_lookahead in
      let _ = rs |> List.filter Syn.is_end_rule |> Syn.raise_rules in
      let _ = choose_rule_skip goal |> Syn.raise_rules in
      let _ = choose_rule_return goal |> Syn.raise_rules in
      let _ = choose_rule_assign_end goal |> Syn.raise_rules in
      let _ = choose_rule_allocate_return goal |> Syn.raise_rules in
      let _ = choose_rule_numeric goal |> Syn.raise_rules in
      let _ = choose_rule_heap_assign goal |> Syn.raise_rules in
      let _ = choose_rule_fwrite goal |> Syn.raise_rules in
      let _ = choose_main_rules goal |> Syn.raise_rules in
      []
    with Syn.ERules rs -> rs in
  rules

let choose_synthesis_rules goal =
  Debug.no_1 "choose_synthesis_rules" Syn.pr_goal Syn.pr_rules
    (fun _ -> choose_synthesis_rules goal) goal

