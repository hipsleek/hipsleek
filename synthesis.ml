#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

module CF = Cformula
module CP = Cpure
module MCP = Mcpure

let pr_hf = Cprinter.string_of_h_formula
let pr_formula = Cprinter.string_of_formula
let pr_var = Cprinter.string_of_spec_var
let pr_vars = Cprinter.string_of_spec_var_list
let rel_num = ref 0
let res_num = ref 0
let unfold_num = ref 0
let unk_hps = ref ([] : Cast.hp_decl list)
(*********************************************************************
 * Data structures
 *********************************************************************)

(* goal *)
type goal = {
  gl_prog : Cast.prog_decl;
  gl_proc_decls: Cast.proc_decl list;
  gl_pre_cond : CF.formula;
  gl_post_cond : CF.formula;
  gl_vars: CP.spec_var list;
}

type priority =
  | PriHigh
  | PriLow
  | PriEqual

exception EPrio of priority

type rule =
  | RlFuncCall of rule_func_call
  | RlAssign of rule_assign
  | RlBind of rule_bind
  (* | RlReturn of rule_return *)
  | RlUnfoldPre of rule_unfold_pre (* Currently assume unfold pre-cond *)


and rule_unfold_pre = {
  n_goals: goal list;
}

(* and rule_return = {
 *   return_var: CP.spec_var;
 * } *)

and rule_func_call = {
  rfc_func_name : string;
  rfc_params : CP.spec_var list;
  rfc_substs : (CP.spec_var * CP.spec_var) list;
}

(* TODO: should we rename variables?? *)
and rule_bind = {
  rb_bound_var: CP.spec_var;
  rb_field: typed_ident;
  rb_other_var: CP.spec_var;
  rb_write: bool;
}

and rule_assign = {
  ra_lhs : CP.spec_var;
  ra_rhs : CP.exp;
}

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

let negate_priority prio = match prio with
  | PriLow -> PriHigh
  | PriEqual -> PriEqual
  | PriHigh -> PriLow

let mk_goal cprog pre post vars =
  { gl_prog = cprog;
    gl_proc_decls = [];
    gl_pre_cond = pre;
    gl_post_cond = post;
    (* gl_equiv_vars = []; *)
    gl_vars = vars;  }

let mk_goal_w_procs cprog proc_decls pre post vars =
  { gl_prog = cprog;
    gl_proc_decls = proc_decls;
    gl_pre_cond = pre;
    gl_post_cond = post;
    (* gl_equiv_vars = []; *)
    gl_vars = vars;  }

let mk_derivation_subgoals goal rule subgoals =
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
  (Cprinter.string_of_spec_var lhs) ^ " = " ^ (Cprinter.string_of_formula_exp rhs)

let pr_func_call rule =
  let fc_name = rule.rfc_func_name in
  let args = rule.rfc_params |> (pr_list Cprinter.string_of_sv) in
  fc_name ^ "(" ^ args ^ ")"

let pr_rule_bind rule =
  let exp = rule.rb_bound_var in
  (Cprinter.string_of_spec_var exp) ^ ", " ^ (snd rule.rb_field) ^ ", "
  ^ (Cprinter.string_of_spec_var rule.rb_other_var)

let pr_rule rule = match rule with
  | RlFuncCall fc -> "RlFuncCall " ^ (pr_func_call fc)
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlBind rule -> if rule.rb_write then
      "RlBind " ^ "(" ^ (pr_rule_bind rule) ^ "," ^ "Write)"
    else "RlBind " ^ "(" ^ (pr_rule_bind rule) ^ "," ^ "Read)"
  (* | RlReturn rule -> "RlReturn" *)
  | RlUnfoldPre _ -> "RlUnfoldPre"

let rec pr_st st = match st with
  | StSearch st_search -> "StSearch [" ^ (pr_st_search st_search) ^ "]"
  | StDerive st_derive -> "StDerive [" ^ (pr_st_derive st_derive) ^ "]"

and pr_st_search st =
  let goal, sub_trees = st.sts_goal, st.sts_sub_trees in
  let st_str = (pr_list pr_st) sub_trees in
  (* "Goal: " ^ (pr_goal goal) ^ "\n" ^ *)
  "Subtrees: " ^  st_str

and pr_st_derive st =
  (pr_goal st.std_goal) ^ "\n" ^
  (pr_rule st.std_rule) ^ "\n" ^
  ((pr_list pr_st) st.std_sub_trees)

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
let rec pf_of_vars vars (pf:CP.formula) = match pf with
  | CP.BForm (bf, opt) ->
    let pform, opt2 = bf in
    let rec aux pform = match pform with
      | CP.Eq (exp1, exp2, loc)
      | CP.Neq (exp1, exp2, loc)
      | CP.Lt (exp1, exp2, loc)
      | CP.Lte (exp1, exp2, loc)
      | CP.Gt (exp1, exp2, loc) ->
        let sv1 = CP.afv exp1 in
        let sv2 = CP.afv exp2 in
        let in_vars var = List.exists (fun x -> CP.eq_spec_var x var) vars in
        if List.exists (fun x -> in_vars x) (sv1@sv2) then pform
        else BConst (true, loc)
      | CP.BVar (sv, bvar_loc) ->
        if List.exists (fun x -> CP.eq_spec_var x sv) vars then pform
        else BConst (true, bvar_loc)
      | _ -> pform
    in
    let n_pform = aux pform in
    CP.BForm ((n_pform, opt2), opt)
  | And (f1, f2, loc) ->
    let n_f1, n_f2 = pf_of_vars vars f1, pf_of_vars vars f2 in
    if CP.is_True n_f1 then n_f2
    else if CP.is_True n_f2 then n_f1
    else And (n_f1, n_f2, loc)
  | AndList list -> AndList (List.map (fun (x,y) -> (x, pf_of_vars vars y)) list)
  | _ -> pf

let is_named_type_var var =
  let typ = CP.type_of_sv var in
  match typ with
  | Named _ -> true
  | _ -> false

let not_identity_assign_rule rule = match rule with
  | RlAssign arule ->
    begin
      match arule.ra_rhs with
      | CP.Var (sv, _) ->
          if CP.eq_spec_var arule.ra_lhs sv then false
          else true
      | _ -> false
    end
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

let do_unfold_view_vnode ?(unfold_vars) cprog fvar =
  let rec helper_vnode subst vf = match vf with
    | CF.EBase bf ->
      let base_f = bf.CF.formula_struc_base in
      let vars_f = CF.fv base_f in
      let () = x_tinfo_hp (add_str "base_f" pr_formula) base_f no_pos in
      let n_formula = CF.subst subst base_f in
      let () = x_tinfo_hp (add_str "n_f" pr_formula) n_formula no_pos in
      [n_formula]
    | CF.EList list ->
      let cases = List.map snd list in
      cases |> List.map (helper_vnode subst) |> List.concat
    | _ -> report_error no_pos
             "Synthesis.do_unfold_view_vnode: not handled cases"  in
  let rec find_subst vnode vf = match vf with
    | CF.EBase bf ->
      let base_f = bf.CF.formula_struc_base in
      let v_args = vnode.CF.h_formula_view_arguments in
      let vars_f = CF.fv base_f in
      let v_args = [vnode.CF.h_formula_view_node]@v_args in
      if List.length vars_f = List.length v_args then
        List.combine vars_f v_args
      else []
    | CF.EList list ->
      let cases = List.map snd list in
      cases |> List.map (find_subst vnode) |> List.concat
      |> Gen.BList.remove_dups_eq (fun x y -> CP.eq_spec_var (fst x) (fst y) &&
                                  CP.eq_spec_var (snd x) (snd y))
    | _ -> report_error no_pos
             "Synthesis.do_unfold_view_vnode.find_subst: not handled cases"  in
  let rec helper_hf hf = match (hf:CF.h_formula) with
    | CF.ViewNode vnode ->
      let view_decls = cprog.Cast.prog_view_decls in
      let vnode_name = vnode.CF.h_formula_view_name in
      let view_decl = List.find (fun x -> String.compare x.Cast.view_name vnode_name == 0)
          view_decls in
      let view_f = view_decl.Cast.view_formula in
      let pr_struc = Cprinter.string_of_struc_formula in
      let v_args = vnode.CF.h_formula_view_arguments in
      let v_args = [vnode.CF.h_formula_view_node]@v_args in
      let subst = find_subst vnode view_f in
      helper_vnode subst view_f
    | _ -> []
  in
  match fvar with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let pf = bf.CF.formula_base_pure in
    hf |> helper_hf |> List.map (CF.add_mix_formula_to_formula pf)
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
        match bf.CF.formula_struc_continuation with
        | None -> CF.mkBase_simp CF.HEmp (mix_of_pure (CP.mkTrue no_pos))
        | Some conti_f -> conti_f |> helper
      else f
    | EAssume assume_f ->
      assume_f.formula_assume_struc |> helper
    | _ -> report_error no_pos "Synthesis.get_pre_post.helper unhandled cases"
  in
  match struc_f with
  | CF.EBase bf ->
    bf.formula_struc_continuation |> Gen.unsome |> helper
  | _ -> report_error no_pos "Synthesis.get_pre_post unhandled cases"

(* let rec simplify_equal_vars (formula:CF.formula) : CF.formula = match formula with
 *   | Base bf ->
 *     let pf = bf.formula_base_pure |> Mcpure.pure_of_mix in
 *     let eq_vars = CP.pure_ptr_equations_aux false pf in
 *     let n_hf = CF.h_subst eq_vars bf.formula_base_heap in
 *     let h_vars = CF.h_fv bf.formula_base_heap in
 *     let n_pf = pf |> CP.subst eq_vars |> CP.elim_idents in
 *     Base {bf with formula_base_heap = n_hf;
 *                   formula_base_pure = mix_of_pure n_pf}
 *   | Or bf -> let f1 = bf.formula_or_f1 in
 *     let f2 = bf.formula_or_f2 in
 *     let n_f1 = simplify_equal_vars f1 in
 *     let n_f2 = simplify_equal_vars f2 in
 *     Or {bf with formula_or_f1 = n_f1;
 *                 formula_or_f2 = n_f2}
 *   | Exists bf ->
 *     let pf = bf.formula_exists_pure |> Mcpure.pure_of_mix in
 *     let eq_vars = CP.pure_ptr_equations_aux false pf in
 *     let n_hf = CF.h_subst eq_vars bf.formula_exists_heap in
 *     let n_pf = pf |> CP.subst eq_vars |> CP.elim_idents in
 *     Exists {bf with formula_exists_heap = n_hf;
 *                   formula_exists_pure = mix_of_pure n_pf} *)

let rec c2iast_exp (exp:Cast.exp) : Iast.exp = match exp with
  | IConst iconst -> Iast.IntLit
                       { exp_int_lit_val = iconst.exp_iconst_val;
                         exp_int_lit_pos = iconst.exp_iconst_pos; }
  | Var var ->
    Var { exp_var_name = var.exp_var_name;
          exp_var_pos = var.exp_var_pos;}
  | Bind bv -> let var = Iast.Var
                   { exp_var_name = bv.exp_bind_bound_var |> snd;
                     exp_var_pos = no_pos; } in
    let lhs = Iast.Member
        { exp_member_base = var;
          exp_member_fields = bv.exp_bind_fields |> List.map snd;
          exp_member_path_id = None;
          exp_member_pos = no_pos;} in
    let rhs = match c2iast_exp bv.exp_bind_body with
      | Assign a_exp -> a_exp.Iast.exp_assign_rhs
      | _ -> report_error no_pos "c2iast_exp not handled" in
    Iast.Assign
      { exp_assign_op = OpAssign;
        exp_assign_lhs = lhs;
        exp_assign_rhs = rhs;
        exp_assign_path_id = None;
        exp_assign_pos = bv.exp_bind_pos;}
  | Assign var -> Assign
                    { exp_assign_op = OpAssign;
                      exp_assign_lhs = Iast.Var
                          { exp_var_name = var.exp_assign_lhs;
                            exp_var_pos = no_pos};
                      exp_assign_rhs = c2iast_exp var.exp_assign_rhs;
                      exp_assign_path_id = None;
                      exp_assign_pos = var.exp_assign_pos;
                    }
  | _ -> report_error no_pos "cast_to_iast_exp not handled"

let add_unk_pred_to_formula (f1:CF.formula) (f2:CF.formula) =
  let collect_pred (f2:CF.formula) = match f2 with
    | Base bf -> bf.formula_base_heap
    | _ -> report_error no_pos "unhandled case" in
  let hf2 = collect_pred f2 in
  let add_hf hf1 hf2 = CF.Star {
      h_formula_star_h1 = hf1;
      h_formula_star_h2 = hf2;
      h_formula_star_pos = no_pos;
    } in
  let rec helper (f1:CF.formula):CF.formula = match f1 with
    | Base bf -> let hf = bf.formula_base_heap in
      let n_hf = add_hf hf hf2 in
      Base {bf with formula_base_heap = n_hf}
    | Exists bf -> let hf = bf.formula_exists_heap in
      let n_hf = add_hf hf hf2 in
      Exists {bf with formula_exists_heap = n_hf}
    | Or bf -> let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
      Or {bf with formula_or_f1 = helper f1;
                  formula_or_f2 = helper f2} in
  helper f1

let rec extract_hf_var hf var =
  match hf with
  | CF.DataNode dnode ->
    let dn_var = dnode.CF.h_formula_data_node in
    if dn_var = var then
      let args = dnode.CF.h_formula_data_arguments in
      Some (hf, [var] @ args)
    else None
  | ViewNode vnode ->
    let vn_var = vnode.CF.h_formula_view_node in
    if vn_var = var then
      let args = vnode.CF.h_formula_view_arguments in
      Some (hf, [var] @ args)
    else None
  | CF.Star sf ->
    let vf1 = extract_hf_var sf.CF.h_formula_star_h1 var in
    let vf2 = extract_hf_var sf.CF.h_formula_star_h2 var in
    begin
      match vf1, vf2 with
      | None, None -> None
      | Some _, None -> vf1
      | None, Some _ -> vf2
      | Some (f1, vars1), Some (f2, vars2) ->
        report_error no_pos "one var cannot appear in two heap fragments"
    end
  | _ -> None

let rec extract_hf_vars hf vars =
  match hf with
  | CF.DataNode dnode ->
    let dn_var = dnode.CF.h_formula_data_node in
    if List.exists (fun x -> CP.eq_spec_var dn_var x) vars then
      let args = dnode.CF.h_formula_data_arguments in
      Some (hf, [dn_var] @ args)
    else None
  | ViewNode vnode ->
    let vn_var = vnode.CF.h_formula_view_node in
    if List.exists (fun x -> CP.eq_spec_var vn_var x) vars then
      let args = vnode.CF.h_formula_view_arguments in
      Some (hf, [vn_var] @ args)
    else None
  | CF.Star sf ->
    let vf1 = extract_hf_vars sf.CF.h_formula_star_h1 vars in
    let vf2 = extract_hf_vars sf.CF.h_formula_star_h2 vars in
    begin
      match vf1, vf2 with
      | None, None -> None
      | Some _, None -> vf1
      | None, Some _ -> vf2
      | Some (f1, vars1), Some (f2, vars2) ->
        let n_hf = CF.Star {sf with h_formula_star_h1 = f1;
                                    h_formula_star_h2 = f2;} in
        Some (n_hf, vars1 @ vars2)
    end
  | _ -> None

let extract_var_f_x f var = match f with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
      let heap_extract = extract_hf_var hf var in
      begin
        match heap_extract with
        | None ->
          let pf_var = pf_of_vars [var] pf |> CP.arith_simplify 1 in
          Some (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var))
        | Some (hf, vars) ->
          let pf_var = pf_of_vars [var] pf |> CP.arith_simplify 1 in
          Some (CF.mkBase_simp hf (Mcpure.mix_of_pure pf_var))
      end
    | CF.Exists exists_f ->
      let hf = exists_f.CF.formula_exists_heap in
      let e_vars = exists_f.CF.formula_exists_qvars in
      let vperms = exists_f.CF.formula_exists_vperm in
      let e_typ = exists_f.CF.formula_exists_type in
      let e_flow = exists_f.CF.formula_exists_flow in
      let pf = Mcpure.pure_of_mix exists_f.CF.formula_exists_pure in
      let heap_extract = extract_hf_var hf var in
      begin
        match heap_extract with
        | None ->
          let pf_var = pf_of_vars [var] pf |> CP.arith_simplify 1 in
          Some (CF.mkExists e_vars CF.HEmp (Mcpure.mix_of_pure pf_var) vperms
                  e_typ e_flow [] no_pos)
        | Some (hf, vars) ->
          let pf_var = pf_of_vars [var] pf |> CP.arith_simplify 1 in
          Some (CF.mkExists e_vars hf (Mcpure.mix_of_pure pf_var) vperms
                  e_typ e_flow [] no_pos)
      end
    | _ -> None

let extract_var_f formula var =
  Debug.no_2 "extract_var_f" pr_formula pr_var
    (fun x -> match x with
       | None -> "None"
       | Some varf -> pr_formula varf)
    (fun _ _ -> extract_var_f_x formula var) formula var

let rec extract_vars_f (f:CF.formula) (vars:CP.spec_var list) = match f with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
    let heap_extract = extract_hf_vars hf vars in
    begin
      match heap_extract with
      | None ->
        let pf_var = pf_of_vars vars pf |> CP.arith_simplify 1 in
        let n_f = (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var)) in
        Some n_f
      | Some (hf, vars) ->
        let pf_var = pf_of_vars vars pf |> CP.arith_simplify 1 in
        Some (CF.mkBase_simp hf (Mcpure.mix_of_pure pf_var))
    end
  | _ -> None

let rec extract_var_pf (f: CP.formula) var = match f with
  | BForm (bf, _) ->
    let (pf, _) = bf in
    (match pf with
     | Eq (e1, e2, _) ->
       begin
         match e1 with
         | Var (sv, _) -> if CP.eq_spec_var sv var then Some e2 else None
         | _ -> None
       end
     | _ -> None
    )
  | And (f1, f2, _) ->
    let res1 = extract_var_pf f1 var in
    if res1 = None then extract_var_pf f2 var
    else res1
  | _ -> None


let create_residue vars prog =
  let name = "T" ^ (string_of_int !rel_num) in
  let () = if !rel_num = 0 then
      unk_hps := prog.Cast.prog_hp_decls @ !unk_hps
    else () in
  let hl_name = CP.mk_spec_var name in
  let () = rel_num := !rel_num + 1 in
  let args = vars |> List.map (fun x -> CP.mkVar x no_pos) in
  let hp_decl = {
    Cast.hp_name = name;
    Cast.hp_vars_inst = vars |> List.map (fun x -> (x, Globals.I));
    Cast.hp_part_vars = [];
    Cast.hp_root_pos = None;
    Cast.hp_is_pre = false;
    Cast.hp_view = None;
    Cast.hp_formula = CF.mkBase_simp (CF.HEmp) (mix_of_pure (CP.mkTrue no_pos))
  } in
  let () = unk_hps := [hp_decl] @ !unk_hps in
  let hrel = CF.HRel (hl_name, args, no_pos) in
  let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  hrel_f

let eq_hp_decl hp1 hp2 =
  let hp1_name,hp2_name = hp1.Cast.hp_name, hp2.Cast.hp_name in
  let hp1_args = hp1.Cast.hp_vars_inst |> List.map (fun (x,y) -> x) in
  let hp2_args = hp2.Cast.hp_vars_inst |> List.map (fun (x,y) -> x) in
  if List.length hp1_args = List.length hp2_args && hp1_name = hp2_name then
    let args = List.combine hp1_args hp2_args in
    List.for_all (fun (x,y) -> CP.eq_spec_var x y) args
  else false

let add_formula_to_formula f1 f2 =
  let hf, pf, _, _, _,_ = CF.split_components f1 in
  let hf2, pf2, _, _, _,_ = CF.split_components f2 in
  let n_pf = mix_of_pure (CP.mkAnd (pure_of_mix pf) (pure_of_mix pf2) no_pos) in
  let n_hf = CF.mkStarH hf hf2 no_pos in
  CF.mkBase_simp n_hf n_pf

let need_unfold_rhs prog vn=
  let rec look_up_view vn0=
    let vdef = x_add Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls
        vn0.CF.h_formula_view_name in
    let fs = List.map fst vdef.view_un_struc_formula in
    let hv_opt = CF.is_only_viewnode false (CF.formula_of_disjuncts fs) in
    match hv_opt with
    | Some vn1 -> look_up_view vn1
    | None -> vdef
  in
  let vdef = look_up_view vn in
  [(vn.CF.h_formula_view_name,vdef.Cast.view_un_struc_formula, vdef.Cast.view_vars)]

