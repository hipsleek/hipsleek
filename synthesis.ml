#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

module CF = Cformula
module CP = Cpure

let pr_hf = Cprinter.string_of_h_formula
let pr_formula = Cprinter.string_of_formula
let pr_var = Cprinter.string_of_spec_var
let pr_vars = Cprinter.string_of_spec_var_list

(*********************************************************************
 * Data structures
 *********************************************************************)

(* goal *)
type goal = {
  gl_prog : Cast.prog_decl;
  gl_proc_decls: Cast.proc_decl list;
  gl_pre_cond : CF.formula;
  gl_post_cond : CF.formula;
  gl_equiv_vars : (CP.spec_var * CP.spec_var) list;
  gl_vars: CP.spec_var list;
}

(* Synthesis rules
 * TODO: add more synthesis rules here *)
type rule =
  | RlFuncCall of rule_func_call
  | RlAssign of rule_assign
  | RlBindWrite of rule_bind
  (* | RlBindRead of rule_bindread *)

and rule_func_call = {
  rfc_func_name : string;
  rfc_params : CP.exp list;
}

(* TODO: should we rename variables?? *)
and rule_bind = {
  rb_var: CP.spec_var;
  rb_field: typed_ident;
  rb_rhs: CP.spec_var;
}

and rule_assign = {
  ra_lhs : CP.spec_var;
  ra_rhs : CP.spec_var;
}

(* AssignPure *)
(* {x = a} {x = b} --> {x = b} if b \in varSet*)

(* AssignPureSymb *)
(* {x = a & b = t} {x = b} --> x = t when varSet = {x, t} *)

(* Atomic derivation *)
type derivation = {
  drv_kind : derivation_kind;
  drv_rule : rule;
  drv_goal : goal;
}

and derivation_kind =
  | DrvStatus of bool
  | DrvSubgoals of goal list

(* Synthesis tree *)
type synthesis_tree =
  | StSearch of synthesis_tree_search
  | StDerive of synthesis_tree_derive

and synthesis_tree_search = {
  sts_goal : goal;
  sts_sub_trees : synthesis_tree list;
  sts_status : synthesis_tree_status;
}

and synthesis_tree_derive = {
  std_goal : goal;
  std_rule : rule;
  std_sub_trees : synthesis_tree list;
  std_status : synthesis_tree_status;
}

and synthesis_tree_core = {
  stc_goal : goal;
  stc_rule : rule;
  stc_sub_trees : synthesis_tree_core list;
}

and synthesis_tree_status =
  | StValid of synthesis_tree_core
  | StUnkn of string


(*********************************************************************
 * Constructors
 *********************************************************************)

let mk_goal cprog pre post vars =
  { gl_prog = cprog;
    gl_proc_decls = [];
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_equiv_vars = [];
    gl_vars = vars;  }

let mk_goal_w_procs cprog proc_decls pre post vars =
  { gl_prog = cprog;
    gl_proc_decls = proc_decls;
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_equiv_vars = [];
    gl_vars = vars;  }

let mk_derivation_sub_goals goal rule subgoals =
  { drv_kind = DrvSubgoals subgoals;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_success goal rule =
  { drv_kind = DrvStatus true;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_fail goal rule =
  { drv_kind = DrvStatus false;
    drv_rule = rule;
    drv_goal = goal; }

let mk_synthesis_tree_search goal sub_trees status : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = sub_trees;
    sts_status = status; }

let mk_synthesis_tree_derive goal rule sub_trees status : synthesis_tree =
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = sub_trees;
    std_status = status; }

let mk_synthesis_tree_core goal rule sub_trees : synthesis_tree_core =
  { stc_goal = goal;
    stc_rule = rule;
    stc_sub_trees = sub_trees; }

let mk_synthesis_tree_success goal rule : synthesis_tree =
  let stcore = mk_synthesis_tree_core goal rule [] in
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = [];
    std_status = StValid stcore; }

let mk_synthesis_tree_fail goal sub_trees msg : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = sub_trees;
    sts_status = StUnkn msg; }

(*********************************************************************
 * Queries
 *********************************************************************)

let get_synthesis_tree_status stree : synthesis_tree_status =
  match stree with
  | StDerive std -> std.std_status
  | StSearch sts -> sts.sts_status

let is_synthesis_tree_success stree : bool =
  let status = get_synthesis_tree_status stree in
  match status with
  | StValid _ -> true
  | StUnkn _ -> false


(*********************************************************************
 * Printing
 *********************************************************************)

let pr_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_goal goal =
  let vars = goal.gl_vars in
  let pr_svs = Cprinter.string_of_spec_var_list in
  "goal (" ^ "vars:" ^ (pr_svs vars) ^ "\n" ^
  "pre: " ^ (pr_formula goal.gl_pre_cond) ^ "\n" ^
  "post: " ^ (pr_formula goal.gl_post_cond) ^ ")"

let pr_rule_assign rule =
  let lhs = rule.ra_lhs in
  let rhs = rule.ra_rhs in
  (Cprinter.string_of_spec_var lhs) ^ " = " ^ (Cprinter.string_of_spec_var rhs)

let pr_rule_bind rule =
  let exp = rule.rb_var in
  (Cprinter.string_of_spec_var exp) ^ ", " ^ (snd rule.rb_field) ^ ", "
  ^ (Cprinter.string_of_spec_var rule.rb_rhs)

let pr_rule rule = match rule with
  | RlFuncCall fc -> "RlFuncCal"
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlBindWrite rule -> "RlBindWrite " ^ "(" ^ (pr_rule_bind rule) ^ ")"
  (* | RlBindRead rule -> "RlBindRead" *)

let rec pr_st st = match st with
  | StSearch st_search -> "StSearch [" ^ (pr_st_search st_search) ^ "]"
  | StDerive st_derive -> "StDerive [" ^ (pr_st_derive st_derive) ^ "]"

and pr_st_search st =
  let goal = st.sts_goal in
  let sub_trees = st.sts_sub_trees in
  let st_str = (pr_list pr_st) sub_trees in
  (pr_goal goal) ^ st_str

and pr_st_derive st =
  (pr_goal st.std_goal) ^ "\n" ^
  (pr_rule st.std_rule) ^ "\n" ^
  ((pr_list pr_st) st.std_sub_trees)
  (* ^ "\n" ^  (pr_st_status st.std_status) *)

and pr_st_status st_status = match st_status with
  | StUnkn str -> "StUnkn " ^ str
  | StValid st_core -> pr_st_core st_core

and pr_st_core st =
  let goal = st.stc_goal in
  let sub_trees = st.stc_sub_trees in
  (pr_goal goal) ^ "=n" ^
  (pr_rule st.stc_rule) ^
  ((pr_list pr_st_core) sub_trees)

let pr_rules = pr_list pr_rule

(*****************************************************
  * Atomic functions
********************************************************)

(* Get the value of a field *)
let get_field var access_field data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> String.compare x.Cast.data_name name == 0) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let result = List.filter (fun (x,y) -> x = access_field) pairs in
    if result = [] then None
    else Some (snd (List.hd result))
  with Not_found -> None

(* Update a data node with a new value to the field *)
let set_field var access_field (new_val:CP.spec_var) data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> String.compare x.Cast.data_name name == 0) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let update_field (field, old_val) =
      if field = access_field then new_val
      else old_val in
    let new_fields = List.map update_field pairs in
    {var with CF.h_formula_data_arguments = new_fields}
  with Not_found -> report_error no_pos "Synthesis.ml could not find the data decls"

(* get a "fix-point" pure formula for a list of vars *)
let pf_of_vars vars (pf:CP.formula) = match pf with
  | CP.BForm (bf, opt) ->
    let pform, opt2 = bf in
    let rec aux pform = match pform with
      | CP.BVar (sv, bvar_loc) ->
        if List.exists (fun x -> CP.eq_spec_var x sv) vars then pform
        else BConst (true, bvar_loc)
      | CP.Lt (exp1, exp2, loc) ->
        let sv1 = CP.afv exp1 in
        let sv2 = CP.afv exp2 in
        let in_vars var = List.exists (fun x -> CP.eq_spec_var x var) vars in
        if List.exists (fun x -> in_vars x) (sv1@sv2) then pform
        else BConst (true, loc)
      | _ -> pform
    in
    let n_pform = aux pform in
    CP.BForm ((n_pform, opt2), opt)
  | _ -> pf

let is_named_type_var var =
  let typ = CP.type_of_sv var in
  match typ with
  | Named _ -> true
  | _ -> false

let not_identity_assign_rule rule = match rule with
  | RlAssign arule ->
    if CP.eq_spec_var arule.ra_lhs arule.ra_rhs then false
    else true
  | _ -> true

let rec rm_emp_formula formula:CF.formula =
  let rec aux_heap hf = match hf with
    | CF.Star sf ->
      let n_f1 = aux_heap sf.CF.h_formula_star_h1 in
      let n_f2 = aux_heap sf.CF.h_formula_star_h2 in
      if CF.is_empty_heap n_f1 then n_f2
      else if CF.is_empty_heap n_f2 then n_f1
      else hf
    | CF.Phase pf ->
      let n_f1 = aux_heap pf.CF.h_formula_phase_rd in
      let n_f2 = aux_heap pf.CF.h_formula_phase_rw in
      if CF.is_empty_heap n_f1 then n_f2
      else if CF.is_empty_heap n_f2 then n_f1
      else hf
    | _ -> hf in
  match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" pr_hf) hf no_pos in
    let n_hf = aux_heap hf in
    let () = x_tinfo_hp (add_str "n_hf" pr_hf) n_hf no_pos in
    CF.Base {bf with formula_base_heap = n_hf}
  | CF.Or disjs ->
    let n_f1 = rm_emp_formula disjs.CF.formula_or_f1 in
    let n_f2 = rm_emp_formula disjs.CF.formula_or_f2 in
    CF.Or {disjs with formula_or_f1 = n_f1;
                      formula_or_f2 = n_f2; }
  | CF.Exists exists_f ->
    let hf = exists_f.CF.formula_exists_heap in
    Exists {exists_f with formula_exists_heap = aux_heap hf}

let do_unfold_view_vnode cprog fvar =
  let rec helper_vnode vnode vf = match vf with
    | CF.EBase bf ->
      let base_f = bf.CF.formula_struc_base in
      let v_args = vnode.CF.h_formula_view_arguments in
      let vars_f = CF.fv base_f in
      let () = x_tinfo_hp (add_str "base_f" pr_formula) base_f no_pos in
      let () = x_tinfo_hp (add_str "base_vars" pr_vars) vars_f no_pos in
      let v_args = [vnode.CF.h_formula_view_node]@v_args in
      let () = x_tinfo_hp (add_str "vnode_vars" pr_vars) v_args no_pos in
      let sst = List.combine vars_f v_args in
      let n_formula = CF.subst sst base_f in
      let () = x_tinfo_hp (add_str "n_f" pr_formula) n_formula no_pos in
      [n_formula]
    | CF.EList list ->
      let cases = List.map snd list in
      cases |> List.map (helper_vnode vnode) |> List.concat
    | _ -> report_error no_pos
             "Synthesis.do_unfold_view_vnode: not handled cases"
  in
  let helper_hf hf = match hf with
    | CF.ViewNode vnode ->
      let view_decls = cprog.Cast.prog_view_decls in
      let vnode_name = vnode.CF.h_formula_view_name in
      let view_decl = List.find (fun x -> String.compare x.Cast.view_name vnode_name == 0)
          view_decls in
      let view_f = view_decl.Cast.view_formula in
      let pr_struc = Cprinter.string_of_struc_formula in
      let () = x_tinfo_hp (add_str "view_f" pr_struc) view_f no_pos in
      helper_vnode vnode view_f
    | _ -> report_error no_pos "n_hf not handled"
  in

  match fvar with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    helper_hf hf
  | CF.Exists exists_f ->
    let hf = exists_f.CF.formula_exists_heap in
    let n_hf = helper_hf hf in
    let exists_vars = exists_f.CF.formula_exists_qvars in
    let n_formulas = List.map (CF.add_quantifiers exists_vars) n_hf in
    let pure_f = exists_f.CF.formula_exists_pure in
    List.map (CF.add_mix_formula_to_formula pure_f) n_formulas
  | _ -> report_error no_pos
           "Synthesis.do_unfold_view_vnode(formula) not handled case"

let get_pre_cond (struc_f: CF.struc_formula) = match struc_f with
  | CF.EBase bf ->
    let pre_cond = bf.CF.formula_struc_base in
    pre_cond
  | _ -> report_error no_pos "Synthesis.get_pre_post unhandled cases"

let get_post_cond (struc_f: CF.struc_formula) =
  let rec helper sf = match sf with
    | CF.EBase bf ->
      let f = bf.formula_struc_base in
      if CF.is_emp_formula f then
        bf.CF.formula_struc_continuation |> Gen.unsome |> helper
      else f
    | EAssume assume_f ->
      assume_f.formula_assume_struc |> helper
    | _ -> report_error no_pos "Synthesis.get_pre_post.helper unhandled cases"
  in
  match struc_f with
  | CF.EBase bf ->
    bf.formula_struc_continuation |> Gen.unsome |> helper
  | _ -> report_error no_pos "Synthesis.get_pre_post unhandled cases"

let rec simplify_equal_vars (formula:CF.formula) : CF.formula = match formula with
  | Base bf ->
    let pf = bf.formula_base_pure |> Mcpure.pure_of_mix in
    let eq_vars = CP.pure_ptr_equations_aux false pf in
    let () = x_binfo_hp (add_str "eq_vars" (pr_list (pr_pair pr_var pr_var))) eq_vars no_pos in
    let n_f = CF.subst eq_vars formula in
    let () = x_binfo_hp (add_str "n_f" pr_formula) n_f no_pos in
    n_f
  | Or bf -> let f1 = bf.formula_or_f1 in
    let f2 = bf.formula_or_f2 in
    let n_f1 = simplify_equal_vars f1 in
    let n_f2 = simplify_equal_vars f2 in
    Or {bf with formula_or_f1 = n_f1;
                formula_or_f2 = n_f2}
  | Exists bf ->
    let pf = bf.formula_exists_pure |> Mcpure.pure_of_mix in
    let eq_vars = CP.pure_ptr_equations_aux false pf in
    let n_f = CF.subst eq_vars formula in
    n_f

(* let process_exists_var pre_cond post_cond =
 *   match post_cond with
 *   | CF.Exists exists_f ->
 *     let exists_vars = exists_f.CF.formula_exists_qvars in
 *     let () = x_binfo_hp (add_str "exists_vars" pr_vars) exists_vars no_pos in
 *     let aux_process exist_var post_cond =
 *       let fvar = extract_var_f post_cond exist_var in
 *       match fvar with
 *       | Some f_var1 ->
 *         let () = x_binfo_hp (add_str "fvar1" pr_formula) f_var1 no_pos in
 *         let similar_var = find_similar_shape_var f_var1 pre_cond in
 *         if (similar_var != None) then
 *           let s_var = Gen.unsome similar_var in
 *           let () = x_binfo_hp (add_str "similar_v" pr_var) s_var no_pos in
 *           let pf = exists_f.CF.formula_exists_pure in
 *           let hf = exists_f.CF.formula_exists_heap in
 *           let sst = [(exist_var, s_var)] in
 *           let n_hf = CF.h_subst sst hf in
 *           let n_pf = Mcpure.regroup_memo_group (Mcpure.m_apply_par sst pf) in
 *           let vars = (CF.h_fv n_hf) @ (CP.fv (Mcpure.pure_of_mix n_pf)) in
 *           let n_post =
 *             if List.exists (fun x -> CP.eq_spec_var x exist_var) vars
 *             then
 *               CF.Exists {exists_f with formula_exists_heap = n_hf;
 *                                        formula_exists_pure = n_pf;}
 *             else CF.mkBase_simp n_hf n_pf
 *           in
 *           let () = x_binfo_hp (add_str "n_post" pr_formula) n_post no_pos in
 *           n_post
 *         else post_cond
 *       | None -> post_cond
 *     in
 *     let n_post = List.fold_left (fun f var -> aux_process var f) post_cond exists_vars in
 *     n_post
 *   | _ -> post_cond *)

(* let find_similar_shape_var fvar formula =
 *   let () = x_binfo_hp (add_str "similar-shape fvar" pr_formula) fvar no_pos in
 *   let () = x_binfo_hp (add_str "similar-shape formula" pr_formula) formula no_pos in
 *
 *   let rec helper hf name args = match hf with
 *     | CF.DataNode f_dnode ->
 *       let f_name = f_dnode.CF.h_formula_data_name in
 *       let f_args = f_dnode.CF.h_formula_data_arguments in
 *       if List.length f_args = List.length args then
 *         let similar_var = (String.compare f_name name == 0) &&
 *                           List.for_all2 (fun x y -> CP.eq_spec_var x y) f_args args in
 *         if similar_var then Some f_dnode.CF.h_formula_data_node
 *         else None
 *       else None
 *     | CF.ViewNode vnode ->
 *       let v_name = vnode.CF.h_formula_view_name in
 *       let v_args = vnode.CF.h_formula_view_arguments in
 *       if List.length v_args = List.length args then
 *         let similar_var = (String.compare v_name name == 0) &&
 *                           List.for_all2 (fun x y -> CP.eq_spec_var x y) v_args args in
 *         if similar_var then Some vnode.CF.h_formula_view_node
 *         else None
 *       else None
 *     | CF.Star sf ->
 *       let f1 = sf.CF.h_formula_star_h1 in
 *       begin
 *         match helper f1 name args with
 *         | None ->
 *           let f2 = sf.CF.h_formula_star_h2 in
 *           helper f2 name args
 *         | Some sv -> Some sv
 *       end
 *     | _ -> None in
 *   match fvar, formula with
 *     | CF.Base bf_var, CF.Base bf ->
 *       let hf_var = bf_var.CF.formula_base_heap in
 *       let hf_f = bf.CF.formula_base_heap in
 *       begin
 *         match hf_var with
 *         | DataNode dnode ->
 *           let name = dnode.CF.h_formula_data_name in
 *           let args = dnode.CF.h_formula_data_arguments in
 *           helper hf_f name args
 *         | ViewNode vnode ->
 *           let name = vnode.CF.h_formula_view_name in
 *           let args = vnode.CF.h_formula_view_arguments in
 *           helper hf_f name args
 *         | _ -> None
 *       end
 *     | _ -> None *)

(* let choose_framing_rule var goal : rule list =
 *   let pre = goal.gl_pre_cond in
 *   let post = goal.gl_post_cond in
 *   let framed_pre, vars_w_fields = frame_var var pre goal.gl_prog in
 *   let framed_post, _ = frame_var var post goal.gl_prog in
 *   let aux cur_var field_var field goal =
 *     let rules = choose_rassign_data field_var goal in
 *     if rules != [] then
 *       let rule = List.hd rules in
 *       match rule with
 *       | RlAssign assign_rule ->
 *         let final_rule = RlBindWrite {
 *             rb_var = cur_var;
 *             rb_field = field;
 *             rb_rhs = assign_rule.ra_rhs;
 *           }
 *         in [final_rule]
 *       | _ -> []
 *     else [] in
 *   if vars_w_fields != [] then
 *     let () = x_binfo_hp (add_str "framed_pre" pr_formula) framed_pre no_pos in
 *     let () = x_binfo_hp (add_str "framed_post" pr_formula) framed_post no_pos in
 *     let field_vars = vars_w_fields |> List.split |> fst in
 *     let n_vars = goal.gl_vars @ field_vars |> CP.remove_dups_svl in
 *     let n_goal = mk_goal goal.gl_prog framed_pre framed_post n_vars in
 *     let rules = List.map (fun (x,y) -> aux var x y n_goal) vars_w_fields in
 *     List.concat rules
 *   else [] *)

