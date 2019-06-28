#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure
open Exc.GTable

module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module I = Iast
module C = Cast

(** Printing  **********)
let pr_hf = Cprinter.string_of_h_formula
let pr_formula = Cprinter.string_of_formula
let pr_formulas = Cprinter.string_of_formula_list_ln
let pr_exp = Cprinter.string_of_formula_exp
let pr_var = Cprinter.string_of_spec_var
let pr_vars = Cprinter.string_of_typed_spec_var_list
let pr_pf = Cprinter.string_of_pure_formula
let pr_sv = Cprinter.string_of_spec_var
let pr_hps = pr_list Cprinter.string_of_hp_decl
let pr_struc_f = Cprinter.string_of_struc_formula
let pr_substs = pr_list (pr_pair pr_var pr_var)

(*** Reference variable***********)
let rel_num = ref 0
let res_num = ref 0
let sb_num = ref 0
let fail_branch_num = ref 0
let check_entail_num = ref 0

let repair_pos = ref (None : VarGen.loc option)
let repair_res = ref (None : Iast.prog_decl option)
let is_return_cand = ref false
let check_post_list = ref ([]: bool list)
let unk_hps = ref ([] : Cast.hp_decl list)
let block_var_decls = ref ([]: CP.spec_var list)
let repair_proc = ref (None : Cast.proc_decl option)
let syn_iprog = ref (None: I.prog_decl option)
let syn_cprog = ref (None: C.prog_decl option)
let tmpl_proc_name = ref (None: string option)
let entailments = ref ([] : (CF.formula * CF.formula) list)
let syn_pre = ref (None : CF.formula option)
let syn_res_vars = ref ([] : CP.spec_var list)

(*********************************************************************
 * Data structures
 *********************************************************************)

type priority =
  | PriHigh
  | PriLow
  | PriEqual

exception EPrio of priority

type rule =
  | RlExistsLeft of rule_exists_left
  | RlExistsRight of rule_exists_right
  | RlFrameData of rule_frame_data
  | RlFramePred of rule_frame_pred
  | RlFoldLeft of rule_fold_left
  | RlUnfoldPre of rule_unfold_pre
  | RlUnfoldPost of rule_unfold_post
  | RlSkip
  | RlAssign of rule_assign
  | RlPreAssign of rule_pre_assign
  | RlReturn of rule_return
  | RlBranch of rule_branch
  | RlFRead of rule_field_read
  | RlFWrite of rule_field_write
  | RlFuncCall of rule_func_call
  | RlFuncRes of rule_func_res

and rule_pre_assign = {
  rpa_lhs : CP.spec_var;
  rpa_rhs : CP.exp
}

and rule_branch = {
  rb_cond: CP.formula;
  rb_if_pre: CF.formula;
  rb_else_pre: CF.formula;
}

and rule_fold_left = {
  rfl_pre: CF.formula
}

and rule_exists_left = {
  exists_vars : CP.spec_var list;
}

and rule_exists_right = {
  n_post: CF.formula;
}

and rule_vinit = {
  rvi_var: CP.spec_var;
  rvi_rhs: CP.exp;
}

and rule_frame_pred = {
  rfp_lhs: CP.spec_var;
  rfp_rhs: CP.spec_var;
  rfp_pairs: (CP.spec_var * CP.spec_var) list;
  rfp_pre: CF.formula;
  rfp_post: CF.formula
}

and rule_frame_data = {
  rfd_lhs: CP.spec_var;
  rfd_rhs: CP.spec_var;
  rfd_pairs: (CP.spec_var * CP.spec_var) list;
  rfd_pre: CF.formula;
  rfd_post: CF.formula
}

and rule_unfold_pre = {
  n_pre: CF.formula;
}

and rule_unfold_post = {
  rp_var: CP.spec_var;
  rp_case_formula: CF.formula;
}

and rule_func_call = {
  rfc_fname : string;
  rfc_params : CP.spec_var list;
  rfc_substs : (CP.spec_var * CP.spec_var) list;
}

and rule_func_res = {
  rfr_fname : string;
  rfr_params : CP.spec_var list;
  rfr_substs : (CP.spec_var * CP.spec_var) list;
  rfr_return : CP.spec_var;
}

and rule_field_write = {
  rfw_bound_var: CP.spec_var;
  rfw_field: typed_ident;
  rfw_value: CP.spec_var;
}

and rule_field_read = {
  rfr_bound_var: CP.spec_var;
  rfr_field: typed_ident;
  rfr_value: CP.spec_var;
}

and rule_assign = {
  ra_lhs : CP.spec_var;
  ra_rhs : CP.exp;
}

and rule_return = {
  r_exp : CP.exp
}

type goal = {
  gl_prog : Cast.prog_decl;
  gl_proc_decls: Cast.proc_decl list;
  gl_pre_cond : CF.formula;
  gl_post_cond : CF.formula;
  gl_vars: CP.spec_var list;
  gl_trace: rule list;
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
  stc_subtrees : synthesis_tree_core list;
}

and synthesis_tree_status =
  | StValid of synthesis_tree_core
  | StUnkn of string

(*****************************************************************)
(*******************         Exception         *******************)
exception ERules of rule list

let raise_rules rs = if rs != [] then raise (ERules rs) else ()

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
let pr_c_exp exp = Cprinter.string_of_exp exp

let pr_iast_exp = Iprinter.string_of_exp_repair
let pr_iast_exp_opt = Iprinter.string_of_exp_repair

let pr_iast_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Iprinter.string_of_exp_repair e

let pr_c_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_goal goal =
  let vars = goal.gl_vars in
  let pr_svs = pr_list Cprinter.string_of_typed_spec_var in
  "synthesize " ^ (pr_svs vars) ^ "\n" ^
  (pr_formula goal.gl_pre_cond) ^ "\n" ^
  "~>\n" ^ (pr_formula goal.gl_post_cond) ^ "."

let pr_rule_assign rule =
  let lhs, rhs = rule.ra_lhs, rule.ra_rhs in
  (Cprinter.string_of_typed_spec_var lhs) ^ " = " ^ (pr_exp rhs)

let pr_rule_pre_assign rule =
  let lhs, rhs = rule.rpa_lhs, rule.rpa_rhs in
  (Cprinter.string_of_typed_spec_var lhs) ^ " = " ^ (pr_exp rhs)

let pr_func_call rule =
  let fc_name = rule.rfc_fname in
  let args = rule.rfc_params |> (pr_list Cprinter.string_of_sv) in
  fc_name ^ "(" ^ args ^ ")"

let pr_func_res rule =
  let fc_name = rule.rfr_fname in
  let args = rule.rfr_params |> (pr_list Cprinter.string_of_sv) in
  fc_name ^ "(" ^ args ^ ")"

let pr_rule_bind rule =
  let exp = rule.rfw_bound_var in
  (Cprinter.string_of_spec_var exp) ^ ", " ^ (snd rule.rfw_field) ^ ", "
  ^ (Cprinter.string_of_spec_var rule.rfw_value)

let pr_fread rule =
  "(" ^ (pr_var rule.rfr_bound_var) ^ "." ^ (snd rule.rfr_field) ^ ", "
  ^ (pr_var rule.rfr_value) ^ ")"

let pr_instantiate rule =
  "(" ^ (pr_var rule.rfp_lhs) ^ ", " ^ (pr_var rule.rfp_rhs) ^ ")"

let pr_frame_data rcore =
  "(" ^ (pr_var rcore.rfd_lhs) ^ ", " ^ (pr_var rcore.rfd_rhs) ^ ")"

let pr_var_init rule =
  "(" ^ (pr_var rule.rvi_var) ^ ", " ^ (pr_exp rule.rvi_rhs) ^ ")"

let pr_rule rule = match rule with
  | RlSkip -> "RlSkip"
  | RlFoldLeft r -> "RlFoldLeft " ^ (pr_formula r.rfl_pre)
  | RlFuncCall fc -> "RlFuncCall " ^ (pr_func_call fc)
  | RlFuncRes fc -> "RlFuncRes " ^ (pr_func_res fc)
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlPreAssign rule -> "RlPreAssign" ^ "(" ^ (pr_rule_pre_assign rule) ^ ")"
  | RlReturn rule -> "RlReturn " ^ "(" ^ (pr_exp rule.r_exp) ^ ")"
  | RlFWrite rule -> "RlFWrite " ^ (pr_rule_bind rule)
  | RlFRead rule -> "RlFRead" ^ (pr_fread rule)
  | RlUnfoldPre rule -> "RlUnfoldPre " ^ (rule.n_pre |> pr_formula)
  | RlUnfoldPost rule -> "RlUnfoldPost\n" ^ (rule.rp_case_formula |> pr_formula)
  | RlFramePred rule -> "RlFramePred" ^ (pr_instantiate rule)
  | RlFrameData rcore -> "RlFrameData" ^ (pr_frame_data rcore)
  | RlExistsLeft rule -> "RlExistsLeft" ^ (pr_vars rule.exists_vars)
  | RlExistsRight rule -> "RlExistsRight" ^ (pr_formula rule.n_post)
  | RlBranch rule -> "RlBranch (" ^ (pr_pf rule.rb_cond) ^ ", " ^
                     (pr_formula rule.rb_if_pre) ^ ", " ^
                     (pr_formula rule.rb_else_pre)  ^ ")"

let pr_trace = pr_list pr_rule

let rec pr_st st = match st with
  | StSearch st_search -> "StSearch [" ^ (pr_st_search st_search) ^ "]"
  | StDerive st_derive -> "StDerive [" ^ (pr_st_derive st_derive) ^ "]"

and pr_st_search st =
  let goal, sub_trees = st.sts_goal, st.sts_sub_trees in
  let st_str = (pr_list pr_st) sub_trees in
  "Subtrees: " ^  st_str

and pr_st_derive st =
  (pr_rule st.std_rule) ^ "\n" ^
  ((pr_list pr_st) st.std_sub_trees)

and pr_st_status st_status = match st_status with
  | StUnkn str -> "StUnkn " ^ str
  | StValid st_core -> pr_st_core st_core

and pr_st_core st =
  let sub_trees = st.stc_subtrees in
  (pr_rule st.stc_rule) ^ "\n" ^
  ((pr_list pr_st_core) sub_trees)

let pr_rules = pr_list_ln pr_rule

(* Basic functions  *)

let rec add_exists_vars (formula:CF.formula) (vars: CP.spec_var list) =
  match formula with
  | CF.Base {
      formula_base_heap = heap;
      formula_base_vperm = vp;
      formula_base_pure = pure;
      formula_base_type = t;
      formula_base_and = a;
      formula_base_flow = fl;
      formula_base_label = lbl;
      formula_base_pos = pos } ->
    CF.mkExists_w_lbl vars heap pure vp t fl a pos lbl
  | CF.Exists ({formula_exists_qvars = qvars;
             formula_exists_heap =  h;
             formula_exists_vperm = vp;
             formula_exists_pure = p;
             formula_exists_type = t;
             formula_exists_and = a;
             formula_exists_flow = fl;
             formula_exists_label = lbl;
             formula_exists_pos = pos } as bf) ->
    let n_qvars = CP.remove_dups_svl (qvars @ vars) in
    CF.mkExists_w_lbl n_qvars h p vp t fl a pos lbl
  | CF.Or bf -> let n_f1 = add_exists_vars bf.formula_or_f1 vars in
    let n_f2 = add_exists_vars bf.formula_or_f2 vars in
    CF.Or {bf with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2}

let elim_bool_constraint_pf (pf:CP.p_formula) = match pf with
  | CP.BVar (_, loc) -> (true, CP.BConst (true, loc))
  | _ -> (false, pf)

let elim_bool_constraint (pf:CP.formula) =
  let rec aux pf = match pf with
    | CP.BForm (bf, opt1) as org ->
      let pf,opt2 = bf in
      let is_bool, n_pf = elim_bool_constraint_pf pf in
      if is_bool then (true, CP.BForm ((n_pf, opt2), opt1))
      else (false, org)
    | CP.Not (f, _, _) as org ->
      let is_bool, n_f = aux f in
      if is_bool then (true, n_f) else (false, org)
    | CP.And (f1, f2, pos) ->
      let is_b1, n_f1 = aux f1 in
      let is_b2, n_f2 = aux f2 in
      (is_b1 && is_b2, CP.And (n_f1, n_f2, pos))
    | _ -> (false, pf) in
  aux pf |> snd

let rec elim_idents (f:CF.formula) = match f with
  | CF.Base bf ->
    let pf = bf.CF.formula_base_pure |> pure_of_mix in
    let n_pf = pf |> CP.elim_idents_node (* |> elim_bool_constraint *) in
    CF.Base {bf with formula_base_pure = mix_of_pure n_pf}
  | CF.Exists bf ->
    let pf = bf.CF.formula_exists_pure |> pure_of_mix in
    let n_pf = pf |> CP.elim_idents_node (* |> elim_bool_constraint *) in
    CF.Exists {bf with formula_exists_pure = mix_of_pure n_pf}
  | CF.Or bf -> CF.Or {bf with formula_or_f1 = elim_idents bf.CF.formula_or_f1;
                               formula_or_f2 = elim_idents bf.CF.formula_or_f2}

let rec remove_exists_vars (formula:CF.formula) (vars: CP.spec_var list) =
  match formula with
  | Base _ -> formula
  | Exists ({formula_exists_qvars = qvars;
             formula_exists_heap =  h;
             formula_exists_vperm = vp;
             formula_exists_pure = p;
             formula_exists_type = t;
             formula_exists_and = a;
             formula_exists_flow = fl;
             formula_exists_label = lbl;
             formula_exists_pos = pos } as bf) ->
    let n_qvars = List.filter (fun x -> not(CP.mem_svl x vars)) qvars in
    if n_qvars = [] then CF.mkBase_w_lbl h p vp t fl a pos lbl
    else Exists {bf with CF.formula_exists_qvars = n_qvars}
  | Or bf -> let n_f1 = remove_exists_vars bf.formula_or_f1 vars in
    let n_f2 = remove_exists_vars bf.formula_or_f2 vars in
    Or {bf with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2}

let is_equality_pair (formula: CP.formula) =
  let aux_pf (pf:CP.p_formula) = match pf with
    | CP.Eq (e1, e2, _) ->
      begin
        match e1, e2 with
        | CP.Var (v1, _) , CP.Var (v2, _) -> Some (v1, v2)
        | _ -> None
      end
    | _ -> None in
  let rec aux f = match f with
    | CP.BForm (bf, _) ->
      let (pf, _) = bf in
      aux_pf pf
    | CP.Exists (_, exists_f, _, _) -> aux exists_f
    | _ -> None in
  aux formula

let rec remove_exists_pf pf = match pf with
  | CP.Exists (_, exists_f, _ , _) -> remove_exists_pf exists_f
  | _ -> pf

let get_equality_pairs (formula: CP.formula) =
  let conjuncts = formula |> remove_exists_pf |> CP.split_conjunctions in
  let check_eq = List.map is_equality_pair conjuncts in
  check_eq |> List.filter (fun x -> x != None)
  |> List.map Gen.unsome

let simplify_equality gl_vars pre_cond post_cond =
  let pre_pf = CF.get_pure pre_cond in
  let post_pf = CF.get_pure post_cond in
  let pre_eq = get_equality_pairs pre_pf in
  let post_eq = get_equality_pairs post_pf in
  let pr_pairs = pr_list (pr_pair pr_var pr_var) in
  let () = x_tinfo_hp (add_str "pre_eq" pr_pairs) pre_eq no_pos in
  let () = x_tinfo_hp (add_str "post_eq" pr_pairs) post_eq no_pos in
  let eq_pair (x1, y1) (x2, y2)= CP.eq_sv x1 x2 && CP.eq_sv y1 y2 in
  let common_eq = Gen.BList.intersect_eq eq_pair pre_eq post_eq in
  let helper (v1, v2) =
    if CP.mem v1 gl_vars then
      if CP.mem v2 gl_vars then (v1, v2)
      else (v2, v1)
    else (v1, v2) in
  if common_eq != [] then
    let () = x_tinfo_hp (add_str "common_eq" pr_pairs) common_eq no_pos in
    let common_eq = List.map helper common_eq in
    let () = x_tinfo_hp (add_str "common_eq" pr_pairs) common_eq no_pos in
    let n_pre = CF.subst common_eq pre_cond |> elim_idents in
    let n_post = CF.subst common_eq post_cond |> elim_idents in
    (n_pre, n_post)
  else
    (pre_cond, post_cond)

let simplify_post_x post_cond =
  let exists_vars = CF.get_exists post_cond in
  let pf = CF.get_pure post_cond in
  let filter_fun (x,y) = CP.mem x exists_vars || CP.mem y exists_vars in
  let pr_pairs = pr_list (pr_pair pr_var pr_var) in
  let () = x_tinfo_hp (add_str "pf" pr_pf) pf no_pos in
  let eq_pairs = get_equality_pairs pf in
  let () = x_tinfo_hp (add_str "eq_pairs" pr_pairs) eq_pairs no_pos in
  let eq_pairs = eq_pairs |> List.filter filter_fun in
  if eq_pairs = [] then post_cond
  else
    let post_cond = remove_exists_vars post_cond exists_vars in
    let () = x_tinfo_hp (add_str "post" pr_formula) post_cond no_pos in
    let helper_fun (x, y) = if CP.mem x exists_vars then (x,y) else (y,x) in
    let eq_pairs = eq_pairs |> List.map helper_fun in
    let n_post = CF.subst eq_pairs post_cond |> elim_idents in
    let () = x_tinfo_hp (add_str "post" pr_formula) n_post no_pos in
    let rm_exists_vars = eq_pairs |> List.map (fun (x,y) -> [x;y]) |> List.concat
                         |> CP.remove_dups_svl in
    let exists_vars = CP.diff_svl exists_vars rm_exists_vars in
    add_exists_vars n_post exists_vars

let simplify_post post_cond =
  Debug.no_1 "simplify_post" pr_formula pr_formula
    (fun _ -> simplify_post_x post_cond) post_cond

let simplify_goal goal =
  let n_pre = CF.elim_exists goal.gl_pre_cond in
  let n_pre = elim_idents n_pre in
  let n_post = elim_idents goal.gl_post_cond in
  let (n_pre, n_post) = simplify_equality goal.gl_vars n_pre n_post in
  let n_post = simplify_post n_post in
  {goal with gl_pre_cond = n_pre;
             gl_post_cond = n_post}

let mkAndList pf_list =
  let rec aux pf_list = match pf_list with
  | [] -> CP.mkTrue no_pos
  | h :: t -> let pf2 = aux t in
    CP.mkAnd h pf2 no_pos in
  let pf = aux pf_list in
  CP.remove_redundant_constraints pf

(* get a "fix-point" pure formula for a list of vars *)
let extract_var_pf_x (pf:CP.formula) vars =
  let rec helper pf vars = match pf with
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
          if List.exists (fun x -> CP.mem_svl x vars) (sv1@sv2) then pform
          else BConst (true, loc)
        | CP.BVar (sv, bvar_loc) ->
          if List.exists (fun x -> CP.eq_spec_var x sv) vars then pform
          else BConst (true, bvar_loc)
        | _ -> pform in
      let n_pform = aux pform in
      CP.BForm ((n_pform, opt2), opt)
    | And (f1, f2, loc) ->
      let n_f1, n_f2 = helper f1 vars, helper f2 vars in
      if CP.is_True n_f1 then n_f2
      else if CP.is_True n_f2 then n_f1
      else And (n_f1, n_f2, loc)
    | AndList list -> AndList (List.map (fun (x,y) -> (x, helper y vars)) list)
    | _ -> pf in
  let n_pf = helper pf vars in
  let n_vars = CP.fv n_pf in
  if Gen.BList.list_equiv_eq CP.eq_sv vars n_vars then n_pf
  else helper pf n_vars

let extract_var_pf pf vars =
  Debug.no_2 "extract_var_pf" pr_pf pr_vars pr_pf
    (fun _ _ -> extract_var_pf_x pf vars) pf vars

let rec extract_hf_var_x hf var =
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
    let vf1 = extract_hf_var_x sf.CF.h_formula_star_h1 var in
    let vf2 = extract_hf_var_x sf.CF.h_formula_star_h2 var in
    begin
      match vf1, vf2 with
      | None, None -> None
      | Some _, None -> vf1
      | None, Some _ -> vf2
      | Some _, Some _ ->
        let hf_str = pr_hf hf in
        let str = "extract_hf_var error: " ^ hf_str in
        report_error no_pos str
    end
  | _ -> None

let extract_hf_var hf var =
  Debug.no_2 "extract_hf_var" pr_hf pr_var (fun x -> match x with
      | None -> "None"
      | Some (_, vars) -> pr_vars vars)
    (fun x y -> extract_hf_var_x x y) hf var

let extract_var_f_x f var = match f with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
      let heap_extract = extract_hf_var hf var in
      begin
        match heap_extract with
        | None ->
          let pf_var = extract_var_pf pf [var] |> CP.arith_simplify 1 in
          Some (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var))
        | Some (hf, vars) ->
          let h_vars = CF.h_fv hf in
          let vars = [var] @ h_vars |> CP.remove_dups_svl in
          let pf_var = extract_var_pf pf vars |> CP.arith_simplify 1 in
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
          let pf_var = extract_var_pf pf [var] in
          Some (CF.mkExists e_vars CF.HEmp (Mcpure.mix_of_pure pf_var) vperms
                  e_typ e_flow [] no_pos)
        | Some (hf, vars) ->
          let h_vars = CF.h_fv hf in
          let vars = vars @ h_vars |> CP.remove_dups_svl in
          let pf_var = extract_var_pf pf vars in
          Some (CF.mkExists e_vars hf (Mcpure.mix_of_pure pf_var) vperms
                  e_typ e_flow [] no_pos)
      end
    | _ -> report_error no_pos "extract_var_f: cannot be OR"

let extract_var_f formula var =
  Debug.no_2 "extract_var_f" pr_formula pr_var
    (fun x -> match x with
       | None -> "None"
       | Some varf -> pr_formula varf)
    (fun _ _ -> extract_var_f_x formula var) formula var


(*****************************************************
  * Atomic functions
 ********************************************************)
let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let rec add_h_formula_to_formula_x h_formula (formula:CF.formula) : CF.formula =
  match formula with
  | Base bf ->
    let hf = bf.formula_base_heap in
    let n_hf = CF.mkStarH hf h_formula no_pos in
    CF.Base {bf with formula_base_heap = n_hf}
  | Exists bf ->
    let hf = bf.formula_exists_heap in
    let n_hf = CF.mkStarH hf h_formula no_pos in
    Exists {bf with formula_exists_heap = n_hf}
  | Or bf ->
    let n_f1 = add_h_formula_to_formula_x h_formula bf.formula_or_f1 in
    let n_f2 = add_h_formula_to_formula_x h_formula bf.formula_or_f2 in
    Or {bf with formula_or_f1 = n_f1;
                formula_or_f2 = n_f2}

let add_h_formula_to_formula added_hf formula =
  Debug.no_2 "add_h_formula_to_formula" pr_hf pr_formula pr_formula
    (fun _ _ -> add_h_formula_to_formula_x added_hf formula) added_hf formula

let rec simpl_f (f:CF.formula) = match f with
  | Or bf -> (simpl_f bf.formula_or_f1) @ (simpl_f bf.formula_or_f2)
  | _ -> [f]

let check_var_mem mem list = List.exists (fun x -> CP.eq_sv x mem) list

(* Get the value of a field *)
let get_field var access_field data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> eq_str x.Cast.data_name name) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let result = List.filter (fun (x,y) -> x = access_field) pairs in
    if result = [] then None
    else Some (snd (List.hd result))
  with Not_found -> None

(* Update a data node with a new value to the field *)
let set_field var access_field (n_val:CP.spec_var) data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> eq_str x.Cast.data_name name) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.Cast.data_fields in
    let pairs = List.combine data_fields fields in
    let update_field (field, old_val) =
      if field = access_field then n_val
      else old_val in
    let new_fields = List.map update_field pairs in
    {var with CF.h_formula_data_arguments = new_fields}
  with Not_found ->
    report_error no_pos "Synthesis.ml could not find the data decls"

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
      if CF.is_empty_heap n_f1 then aux_heap n_f2
      else if CF.is_empty_heap n_f2 then aux_heap n_f1
      else Star {sf with h_formula_star_h1 = aux_heap n_f1;
                         h_formula_star_h2 = aux_heap n_f2}
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

let do_unfold_view_hf_vn_x cprog pr_views args (hf:CF.h_formula) =
  let rec look_up_vdef ls_pr_views vname =
    match ls_pr_views with
    | [] -> raise Not_found
    | (vname1, def, vars)::rest ->
      if eq_str vname vname1 then (vname, def, vars) else
        look_up_vdef rest vname in
  let fresh_var args f =
    let qvars, base1 = CF.split_quantifiers f in
    let fr_qvars = CP.fresh_spec_vars qvars in
    let ss = List.combine qvars fr_qvars in
    let nf = x_add CF.subst ss base1 in
    CF.add_quantifiers fr_qvars nf in
  let helper_vnode (hv:CF.h_formula_view) =
    try
      let (v_name,v_un_struc_formula, v_vars) =
        look_up_vdef pr_views hv.h_formula_view_name in
      let f_args = (CP.SpecVar (Named v_name,self, Unprimed))::v_vars in
      let fs = List.map (fun (f,_) -> fresh_var f_args f) v_un_struc_formula in
      let a_args = hv.h_formula_view_node::hv.h_formula_view_arguments in
      let ss = List.combine f_args a_args in
      let fs1 = List.map (x_add CF.subst ss) fs in
      fs1
    with _ -> report_error no_pos ("SYN.do_unfold_view_hf: can not find view "
                                   ^ hv.h_formula_view_name) in
  let rec helper (hf:CF.h_formula) = match hf with
    | ViewNode hv ->
      if check_var_mem hv.h_formula_view_node args then
        Some (helper_vnode hv)
      else None
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;
             h_formula_star_pos = pos} ->
      let unfold1 = helper hf1 in
      let unfold2 = helper hf2 in
      begin
        match unfold1, unfold2 with
        | Some l1, Some l2 -> report_error no_pos "only unfold once"
        | Some l1, None -> Some (List.map (add_h_formula_to_formula hf2) l1)
        | None, Some l2 -> Some (List.map (add_h_formula_to_formula hf1) l2)
        | None, None -> None
      end
    | _ -> None in
  match helper hf with
  | None -> [(CF.mkBase_simp hf (MCP.mkMTrue no_pos))]
  | Some list -> list

let do_unfold_view_hf_vn cprog pr_views args (hf:CF.h_formula) =
  let pr1 = pr_formula in
  Debug.no_2 "do_unfold_view_hf_vn" pr_hf pr_vars
    (fun x -> x |> pr_list pr1)
    (fun _ _ -> do_unfold_view_hf_vn_x cprog pr_views args hf) hf args

let rec remove_heap_var var hf = match hf with
  | CF.DataNode dn -> if CP.eq_sv var dn.CF.h_formula_data_node then
      CF.HEmp else hf
  | CF.ViewNode vn -> if CP.eq_sv var vn.CF.h_formula_view_node then
      CF.HEmp else hf
  | CF.Star sf -> let hf1 = remove_heap_var var sf.CF.h_formula_star_h1 in
    let hf2 = remove_heap_var var sf.CF.h_formula_star_h2 in
    CF.Star {sf with h_formula_star_h1 = hf1;
                     h_formula_star_h2 = hf2}
  | _ -> hf

let rec remove_heap_var_f var formula = match formula with
  | CF.Base bf -> let hf = bf.CF.formula_base_heap in
    let nf = CF.Base {bf with formula_base_heap = remove_heap_var var hf} in
    rm_emp_formula nf
  | CF.Exists bf -> let hf = bf.CF.formula_exists_heap in
    let nf = CF.Exists {bf with formula_exists_heap = remove_heap_var var hf} in
    rm_emp_formula nf
  | CF.Or bf -> let n_f1 = remove_heap_var_f var bf.CF.formula_or_f1 in
    let n_f2 = remove_heap_var_f var bf.CF.formula_or_f2 in
    let nf = CF.Or {bf with formula_or_f1 = n_f1;
                            formula_or_f2 = n_f2} in
    rm_emp_formula nf

let do_unfold_view_vnode_x cprog pr_views args (formula:CF.formula) =
  let rec helper (f:CF.formula) = match f with
    | Base fb ->
      let unfold_hf = do_unfold_view_hf_vn cprog pr_views args
          fb.CF.formula_base_heap in
      let pf = fb.CF.formula_base_pure in
      let tmp = List.map (CF.add_mix_formula_to_formula pf) unfold_hf in
      tmp |> List.map simpl_f |> List.concat
    | Exists _ ->
      let qvars, base1 = CF.split_quantifiers f in
      let nf = helper base1 |> List.map simpl_f |> List.concat in
      let () = x_tinfo_hp (add_str "nf" (pr_list pr_formula)) nf no_pos in
      nf |> List.map (CF.add_quantifiers qvars)
    | Or orf  ->
      let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      nf1 @ nf2 in
  if pr_views = [] then [formula] else helper formula

let do_unfold_view_vnode cprog pr_views args (f0: CF.formula) =
  let pr1 = pr_formula in
  Debug.no_2 "do_unfold_view_vnode" pr1 pr_vars (pr_list pr1)
    (fun _ _ -> do_unfold_view_vnode_x cprog pr_views args f0) f0 args

let get_pre_cond (struc_f: CF.struc_formula) = match struc_f with
  | CF.EBase bf ->
    let pre_cond = bf.CF.formula_struc_base in
    pre_cond
  | _ -> report_error no_pos "Synthesis.get_pre_cond unhandled cases"

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
    | _ -> report_error no_pos
             "Synthesis.get_post_cond.helper unhandled cases" in
  match struc_f with
  | CF.EBase bf ->
    bf.formula_struc_continuation |> Gen.unsome |> helper
  | _ -> report_error no_pos "Synthesis.get_pre_post unhandled cases"

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
    | Base bf ->
      let hf = bf.formula_base_heap in
      let n_hf = add_hf hf hf2 in
      Base {bf with formula_base_heap = n_hf}
    | Exists bf ->
      let hf = bf.formula_exists_heap in
      let n_hf = add_hf hf hf2 in
      Exists {bf with formula_exists_heap = n_hf}
    | Or bf ->
      let f1,f2 = bf.formula_or_f1, bf.formula_or_f2 in
      Or {bf with formula_or_f1 = helper f1;
                  formula_or_f2 = helper f2} in
  helper f1

let create_residue vars prog conseq =
  if !Globals.check_post then
    let residue = CF.mkBase_simp (CF.HEmp) (Mcpure.mkMTrue no_pos) in
    residue, conseq
  else
    let name = "T" ^ (string_of_int !rel_num) in
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
      Cast.hp_formula =
        CF.mkBase_simp (CF.HEmp) (mix_of_pure (CP.mkTrue no_pos))
    } in
    let () = unk_hps := hp_decl::(!unk_hps) in
    let hrel = CF.HRel (hl_name, args, no_pos) in
    let n_conseq = add_h_formula_to_formula hrel conseq in
    let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
    hrel_f, n_conseq

let create_pred vars =
  let name = "T" ^ (string_of_int !rel_num) in
  let () = rel_num := !rel_num + 1 in
  let hl_name = CP.mk_spec_var name in
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
  let () = unk_hps := hp_decl::(!unk_hps) in
  let hrel = CF.HRel (hl_name, args, no_pos) in
  let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  hrel_f

let create_spec_pred vars pred_name =
  let name = pred_name in
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
  let () = unk_hps := hp_decl::(!unk_hps) in
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

let need_unfold_rhs prog vn=
  let rec look_up_view vn0=
    let vdef = x_add Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls
        vn0.CF.h_formula_view_name in
    let fs = List.map fst vdef.view_un_struc_formula in
    let hv_opt = CF.is_only_viewnode false (CF.formula_of_disjuncts fs) in
    match hv_opt with
    | Some vn1 -> look_up_view vn1
    | None -> vdef in
  let vdef = look_up_view vn in
  [(vn.CF.h_formula_view_name,vdef.Cast.view_un_struc_formula,
    vdef.Cast.view_vars)], [(vn.CF.h_formula_view_node)]

let is_node_var (var: CP.spec_var) = match CP.type_of_sv var with
  | Named _ -> true
  | _ -> false

let is_int_var (var: CP.spec_var) = match CP.type_of_sv var with
  | Int -> true
  | _ -> false

let is_node_or_int_var x = is_node_var x || is_int_var x

let equal_type (var1:CP.spec_var) (var2:CP.spec_var) =
  (CP.type_of_sv var1) = (CP.type_of_sv var2)

let find_exists_substs sv_list conjunct =
  let aux pf = match pf with
    | CP.Eq (e1, e2, _) ->
      let l1 =
        match e1 with
        | CP.Var (sv, _) ->
          if CP.mem sv sv_list then [(sv, e2)] else  []
        | _ -> [] in
      begin
        match e2 with
        | CP.Var (sv, _) ->
          if CP.mem sv sv_list then (sv, e1)::l1 else l1
        | _ -> l1
      end
    | _ -> [] in
  match conjunct with
  | CP.BForm (bf, _) ->
    let pf, _ = bf in
    aux pf
  | _ -> []

let add_formula_to_formula f1 f2 =
  let bf = CF.mkStar f1 f2 CF.Flow_combine no_pos in
  let evars = (CF.get_exists f1) @ (CF.get_exists f2) |> CP.remove_dups_svl in
  if evars = [] then bf
    else add_exists_vars bf evars

let remove_exists (formula:CF.formula) =
  let vars = CF.get_exists formula in
  remove_exists_vars formula vars

let remove_boolean_constraints (ante:CF.formula) =
  let conjuncts = ante |> CF.get_pure |> remove_exists_pf
                  |> CP.split_conjunctions
                  |> List.filter (fun x -> not(CP.is_bool_formula x)) in
  x_tinfo_hp (add_str "conjuncts" (pr_list pr_pf)) conjuncts no_pos;
  let n_pf = CP.join_conjunctions conjuncts in
  let h, _, _, _, _, _ = CF.split_components ante in
  CF.mkBase_simp h (MCP.mix_of_pure n_pf)

let is_emp_conseq conseq =
  let is_True cp = match cp with
    | CP.BForm (p,_) ->
      let p_formula, _ = p in
      begin
        match p_formula with
        | CP.BConst (b,_) -> b
        | CP.LexVar _ -> true
        | _ -> false
      end
    | _ -> false in
  if CF.is_emp_formula conseq then
    let pf = CF.get_pure conseq in
    x_tinfo_hp (add_str "conseq pf" pr_pf) pf no_pos;
    is_True pf
  else false

let rec get_unfold_view_hf vars (hf1:CF.h_formula) = match hf1 with
  | CF.ViewNode vnode -> let var = vnode.CF.h_formula_view_node in
    if CP.mem var vars then [vnode] else []
  | CF.Star sf -> let f1, f2 = sf.h_formula_star_h1, sf.h_formula_star_h2 in
    let vn1,vn2 = get_unfold_view_hf vars f1, get_unfold_view_hf vars f2 in
    vn1@vn2
  | _ -> []

let get_unfold_view vars (f1:CF.formula) = match f1 with
  | CF.Base bf1 -> get_unfold_view_hf vars bf1.formula_base_heap
  | CF.Exists bf -> get_unfold_view_hf vars bf.formula_exists_heap
  | _ -> []

let unprime_formula_x (formula:CF.formula) =
  let vars = CF.fv formula |> List.filter CP.is_primed in
  let substs = vars |> List.map (fun x -> (x, CP.to_unprimed x)) in
  CF.subst substs formula

let unprime_formula (formula:CF.formula) : CF.formula =
  Debug.no_1 "unprime_formula" pr_formula pr_formula
    (fun _ -> unprime_formula_x formula) formula

let simplify_ante_x (ante: CF.formula) =
  let ante = remove_exists ante in
  let ante = unprime_formula ante in
  (* let pf = ante |> CF.get_pure |> remove_exists_pf in
   * let filter_fun (x,y) = CP.is_primed x &&
   *                        eq_str (CP.name_of_sv x) (CP.name_of_sv y) in
   * let eq_pairs = get_equality_pairs pf |> List.filter filter_fun in
   * let n_ante = CF.subst eq_pairs ante |> elim_idents in
   * let pr_pairs = pr_list (pr_pair pr_var pr_var) in
   * x_tinfo_hp (add_str "eq_pairs" pr_pairs) eq_pairs no_pos; *)
  (* let deleted_vars = eq_pairs |> List.map fst in
   * let rec aux n_ante =
   *   let vars = CF.fv n_ante in
   *   if CP.intersect_svl vars deleted_vars = [] then n_ante
   *   else
   *     let n_ante = CF.subst eq_pairs n_ante |> elim_idents in
   *     aux n_ante in *)
  ante |> remove_boolean_constraints

let simplify_ante ante =
  Debug.no_1 "simplify_ante" pr_formula pr_formula
    (fun _ -> simplify_ante_x ante) ante

let rec has_unfold_pre trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlUnfoldPre r -> true
      | _ -> has_unfold_pre t
    end

let has_unfold_post trace =
  let rec aux trace num = match trace with
  | [] -> false
  | h::t ->
    begin
      match h with
      | RlUnfoldPost _ -> if num = 1 then true
        else aux t (num - 1)
      | _ -> aux t num
    end in
  aux trace 2

let rec remove_exists_vars_pf (formula:CP.formula) = match formula with
  | Exists (_, x,_,_) -> remove_exists_vars_pf x
  | BForm _ -> formula
  | And (f1, f2, loc) -> let nf1 = remove_exists_vars_pf f1 in
    let nf2 = remove_exists_vars_pf f2 in
    And (nf1, nf2, loc)
  | AndList list ->
    let nlist = List.map (fun (x,y) -> (x, remove_exists_vars_pf y)) list in
    AndList nlist
  | Not (f, opt, loc) -> Not (remove_exists_vars_pf f, opt, loc)
  | Or (f1, f2, opt, loc) -> let nf1 = remove_exists_vars_pf f1 in
    let nf2 = remove_exists_vars_pf f2 in
    Or (nf1, nf2, opt, loc)
  | Forall (_, f, _, _) -> remove_exists_vars_pf f

(*****************************************************
  * Synthesize CAST and IAST exp
 ********************************************************)
let var_to_iast sv loc =
  Iast.Var { exp_var_name = CP.name_of_sv sv;
             exp_var_pos = loc }

let var_to_cast sv loc =
  C.Var {
    C.exp_var_name = CP.name_of_sv sv;
    C.exp_var_type = CP.type_of_sv sv;
    C.exp_var_pos = loc }

let num_to_iast num loc =
  Iast.IntLit { exp_int_lit_val = num;
                exp_int_lit_pos = loc}

let num_to_cast num loc =
  C.IConst {
    C.exp_iconst_val = num;
    C.exp_iconst_pos = loc
  }

let rec exp_to_iast (exp: CP.exp) = match exp with
  | CP.Var (sv, loc) ->  var_to_iast sv loc
  | CP.Null loc -> I.Null loc
  | CP.IConst (num, loc) -> num_to_iast num loc
  | CP.Add (e1, e2, loc) ->
    let n_e1, n_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.Binary { I.exp_binary_op = I.OpPlus;
               I.exp_binary_oper1 = n_e1;
               I.exp_binary_oper2 = n_e2;
               I.exp_binary_path_id = None;
               I.exp_binary_pos = loc}
  | CP.Subtract (e1, e2, loc) ->
    let n_e1, n_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.Binary { I.exp_binary_op = I.OpMinus;
               I.exp_binary_oper1 = n_e1;
               I.exp_binary_oper2 = n_e2;
               I.exp_binary_path_id = None;
               I.exp_binary_pos = loc}
  | CP.Mult (e1, e2, loc) ->
    let n_e1, n_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.Binary { I.exp_binary_op = I.OpMult;
               I.exp_binary_oper1 = n_e1;
               I.exp_binary_oper2 = n_e2;
               I.exp_binary_path_id = None;
               I.exp_binary_pos = loc}
  | CP.Div (e1, e2, loc) ->
    let n_e1, n_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.Binary { I.exp_binary_op = I.OpDiv;
               I.exp_binary_oper1 = n_e1;
               I.exp_binary_oper2 = n_e2;
               I.exp_binary_path_id = None;
               I.exp_binary_pos = loc}
  | _ -> report_error no_pos ("exp_to_iast:" ^ (pr_exp exp) ^"not handled")

let mkCSeq exp1 exp2 = C.mkSeq Void exp1 exp2 no_pos

let rec exp2cast (exp: CP.exp) = match exp with
  | CP.Var (sv, loc) -> var_to_cast sv loc
  | CP.Null loc -> C.Null loc
  | CP.IConst (num, loc) ->
    let num = num_to_cast num loc in
    num
  | CP.Add (e1, e2, loc) ->
    let helper e1 =
      let n_e1 = exp2cast e1 in
      match n_e1 with
      | C.Var var -> (n_e1, var.C.exp_var_name)
      | _ ->
        let n_var = fresh_name() in
        let var = C.VarDecl {
            C.exp_var_decl_type = CP.get_exp_type e1;
            C.exp_var_decl_name = n_var;
            C.exp_var_decl_pos = no_pos;
          } in
        let assign = C.Assign {
            C.exp_assign_lhs = n_var;
            C.exp_assign_rhs = n_e1;
            C.exp_assign_pos = no_pos;
          } in
        let seq = mkCSeq var assign in
        (seq, n_var) in
    let n_e1, name1 = helper e1 in
    let n_e2, name2 = helper e2 in
    let name = C.mingle_name "add" [Int; Int] in
    let call = C.SCall {
        C.exp_scall_type = Int;
        C.exp_scall_method_name = name;
        C.exp_scall_lock = None;
        C.exp_scall_arguments = [name1; name2];
        C.exp_scall_ho_arg = None;
        C.exp_scall_is_rec = false;
        C.exp_scall_path_id = None;
        C.exp_scall_pos = no_pos
      } in
    begin
      match n_e1, n_e2 with
      | C.Var _, C.Var _ -> call
      | C.Var _, _ -> mkCSeq n_e2 call
      | _, C.Var _ -> mkCSeq n_e1 call
      | _ ->
        let seq = mkCSeq n_e1 n_e2 in
        mkCSeq seq call
    end
  | CP.Subtract (e1, e2, loc) ->
    let e1 = CP.norm_exp e1 in
    let e2 = CP.norm_exp e2 in
    let helper e1 =
      let n_e1 = exp2cast e1 in
      match n_e1 with
      | C.Var var -> (n_e1, var.C.exp_var_name)
      | _ ->
        let n_var = fresh_name() in
        let var = C.VarDecl {
            C.exp_var_decl_type = CP.get_exp_type e1;
            C.exp_var_decl_name = n_var;
            C.exp_var_decl_pos = no_pos;
          } in
        let assign = C.Assign {
            C.exp_assign_lhs = n_var;
            C.exp_assign_rhs = n_e1;
            C.exp_assign_pos = no_pos;
          } in
        let seq = mkCSeq var assign in
        (seq, n_var) in
    let n_e1, name1 = helper e1 in
    let n_e2, name2 = helper e2 in
    let name = C.mingle_name "minus" [Int; Int] in
    let call = C.SCall {
        C.exp_scall_type = Int;
        C.exp_scall_method_name = name;
        C.exp_scall_lock = None;
        C.exp_scall_arguments = [name1; name2];
        C.exp_scall_ho_arg = None;
        C.exp_scall_is_rec = false;
        C.exp_scall_path_id = None;
        C.exp_scall_pos = no_pos
      } in
    begin
      match n_e1, n_e2 with
      | C.Var _, C.Var _ -> call
      | C.Var _, _ -> mkCSeq n_e2 call
      | _, C.Var _ -> mkCSeq n_e1 call
      | _ ->
        let seq = mkCSeq n_e1 n_e2 in
        mkCSeq seq call
    end
  | CP.Mult (e1, e2, loc) ->
    let e1 = CP.norm_exp e1 in
    let e2 = CP.norm_exp e2 in
    let helper e1 =
      let n_e1 = exp2cast e1 in
      match n_e1 with
      | C.Var var -> (n_e1, var.C.exp_var_name)
      | _ ->
        let n_var = fresh_name() in
        let var = C.VarDecl {
            C.exp_var_decl_type = CP.get_exp_type e1;
            C.exp_var_decl_name = n_var;
            C.exp_var_decl_pos = no_pos;
          } in
        let assign = C.Assign {
            C.exp_assign_lhs = n_var;
            C.exp_assign_rhs = n_e1;
            C.exp_assign_pos = no_pos;
          } in
        let seq = mkCSeq var assign in
        (seq, n_var) in
    let n_e1, name1 = helper e1 in
    let n_e2, name2 = helper e2 in
    let name = C.mingle_name "mult" [Int; Int] in
    let call = C.SCall {
        C.exp_scall_type = Int;
        C.exp_scall_method_name = name;
        C.exp_scall_lock = None;
        C.exp_scall_arguments = [name1; name2];
        C.exp_scall_ho_arg = None;
        C.exp_scall_is_rec = false;
        C.exp_scall_path_id = None;
        C.exp_scall_pos = no_pos
      } in
    begin
      match n_e1, n_e2 with
      | C.Var _, C.Var _ -> call
      | C.Var _, _ -> mkCSeq n_e2 call
      | _, C.Var _ -> mkCSeq n_e1 call
      | _ ->
        let seq = mkCSeq n_e1 n_e2 in
        mkCSeq seq call
    end
  | _ -> report_error no_pos ("exp2cast:" ^ (pr_exp exp) ^"not handled")

let pf_to_iast (pf: CP.p_formula) = match pf with
  | CP.Eq (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpEq i_e1 i_e2 None loc
  | CP.Neq (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpNeq i_e1 i_e2 None loc
  | CP.Lt (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpLt i_e1 i_e2 None loc
  | CP.Lte (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpLte i_e1 i_e2 None loc
  | CP.Gt (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpGt i_e1 i_e2 None loc
  | CP.Gte (e1, e2, loc) ->
    let i_e1, i_e2 = exp_to_iast e1, exp_to_iast e2 in
    I.mkBinary I.OpGte i_e1 i_e2 None loc
  | _ -> report_error no_pos ("pf_to_iast: not handled")

let pure_to_iast (pf:CP.formula) = match pf with
  | BForm (bf, _) -> let (pf, _) = bf in
    pf_to_iast pf
  | _ -> report_error no_pos ("pure_to_iast:" ^ (pr_pf pf) ^"not handled")

let rec get_var_decls_x pos (exp:I.exp) = match exp with
  | I.VarDecl var ->
    let v_pos = var.I.exp_var_decl_pos in
    if get_start_lnum v_pos <= get_start_lnum pos then
      let typ = var.I.exp_var_decl_type in
      var.I.exp_var_decl_decls |> List.map (fun (x, _, _) -> x)
      |> List.map (CP.mk_typed_sv typ)
    else []
  | I.Seq seq -> (get_var_decls_x pos seq.I.exp_seq_exp1) @
                 (get_var_decls_x pos seq.I.exp_seq_exp2)
  | I.Cond cond -> (get_var_decls_x pos cond.I.exp_cond_then_arm) @
                   (get_var_decls_x pos cond.I.exp_cond_else_arm)
  | I.Block b -> get_var_decls_x pos b.I.exp_block_body
  | I.Label (_, e) -> get_var_decls_x pos e
  | _ -> []

let get_var_decls pos (exp:I.exp) : CP.spec_var list =
  Debug.no_1 "get_var_decls" Iprinter.string_of_exp pr_vars
    (fun _ -> get_var_decls_x pos exp) exp

let mkVar sv = I.mkVar (CP.name_of_sv sv) no_pos

let mkAssign exp1 exp2 = I.mkAssign I.OpAssign exp1 exp2 None no_pos

let mkSeq exp1 exp2 = I.mkSeq exp1 exp2 no_pos

let rec st_core2cast st : Cast.exp option = match st.stc_rule with
  | RlSkip -> None
  | RlExistsLeft _ | RlExistsRight _ | RlFramePred _ | RlFrameData _
  | RlUnfoldPost _ | RlUnfoldPre _ ->
    begin
      let sts = List.map st_core2cast st.stc_subtrees in
      match sts with
      | [] -> None
      | [h] -> h
      | _ -> report_error no_pos "st_core2cast: no more than one st"
    end
  | RlAssign rule ->
    let var = rule.ra_lhs in
    let rhs = rule.ra_rhs in
    let c_rhs = exp2cast rhs in
    let assign = C.Assign {
      C.exp_assign_lhs = CP.name_of_sv var;
      C.exp_assign_rhs = c_rhs;
      C.exp_assign_pos = no_pos
    } in
    aux_c_subtrees st assign
  | RlPreAssign rule ->
    let var = rule.rpa_lhs in
    let rhs = rule.rpa_rhs in
    let c_rhs = exp2cast rhs in
    let var_exp = C.VarDecl {
        C.exp_var_decl_type = CP.type_of_sv var;
        C.exp_var_decl_name = CP.name_of_sv var;
        C.exp_var_decl_pos = no_pos;
      } in
    let seq = mkCSeq var_exp c_rhs in
    let assign = C.Assign {
      C.exp_assign_lhs = CP.name_of_sv var;
      C.exp_assign_rhs = c_rhs;
      C.exp_assign_pos = no_pos
    } in
    let seq = mkCSeq seq assign in
    aux_c_subtrees st seq
  | RlFRead rcore ->
    let lhs = rcore.rfr_value in
    let bvar = rcore.rfr_bound_var in
    let (typ, f_name) = rcore.rfr_field in
    let n_name = f_name ^ (string_of_int (fresh_int())) in
    let exp_decl = C.VarDecl {
        C.exp_var_decl_type = CP.type_of_sv lhs;
        C.exp_var_decl_name = CP.name_of_sv lhs;
        exp_var_decl_pos = no_pos;
      } in
    let body = C.Var {
        exp_var_type = typ;
        exp_var_name = n_name;
        exp_var_pos = no_pos;
      } in
    let bind = C.Bind {
        exp_bind_type = Void;
        exp_bind_bound_var = (CP.type_of_sv bvar, CP.name_of_sv bvar);
        exp_bind_fields = [(typ, n_name)];
        exp_bind_body = body;
        exp_bind_imm = CP.NoAnn;
        exp_bind_param_imm = [];
        exp_bind_read_only = true;
        exp_bind_path_id = (3, "bind");
        exp_bind_pos = no_pos
      } in
    let assign = C.Assign {
        C.exp_assign_lhs = CP.name_of_sv lhs;
        C.exp_assign_rhs = bind;
        C.exp_assign_pos = no_pos;
      } in
    let bind = mkCSeq exp_decl assign in
    aux_c_subtrees st bind

  | RlFWrite rcore ->
    let lhs = rcore.rfw_bound_var in
    let (typ, f_name) = rcore.rfw_field in
    let n_name = f_name ^ (string_of_int (fresh_int())) in
    let rhs = rcore.rfw_value in
    let rhs_exp = C.Var {
        exp_var_type = typ;
        exp_var_name = CP.name_of_sv rhs;
        exp_var_pos = no_pos
      } in
    let body = C.Assign {
        exp_assign_lhs = n_name;
        exp_assign_rhs = rhs_exp;
        exp_assign_pos = no_pos
      } in
    let bind = C.Bind {
        exp_bind_type = Void;
        exp_bind_bound_var = (CP.type_of_sv lhs, CP.name_of_sv lhs);
        exp_bind_fields = [(typ, n_name)];
        exp_bind_body = body;
        exp_bind_imm = CP.NoAnn;
        exp_bind_param_imm = [];
        exp_bind_read_only = false;
        exp_bind_path_id = (3, "bind");
        exp_bind_pos = no_pos
      } in
    aux_c_subtrees st bind

  | RlFuncRes rule ->
    let fname = rule.rfr_fname in
    let params = rule.rfr_params |> List.map CP.name_of_sv in
    let r_var = rule.rfr_return in
    let f_call = C.SCall {
        C.exp_scall_type = CP.type_of_sv r_var;
        C.exp_scall_method_name = fname;
        C.exp_scall_lock = None;
        C.exp_scall_arguments = params;
        C.exp_scall_ho_arg = None;
        C.exp_scall_is_rec = true;
        C.exp_scall_path_id = None;
        C.exp_scall_pos = no_pos
      } in
    let r_name = CP.name_of_sv r_var in
    let res_var = C.VarDecl {
        C.exp_var_decl_type = CP.type_of_sv r_var;
        C.exp_var_decl_name = r_name;
        C.exp_var_decl_pos = no_pos
      } in
    let assign = C.Assign {
        C.exp_assign_lhs = r_name;
        C.exp_assign_rhs = f_call;
        C.exp_assign_pos = no_pos;
      } in
    let seq2 = mkCSeq res_var assign in
    aux_c_subtrees st seq2

  | RlFuncCall rule ->
    let fname = rule.rfc_fname in
    let params = rule.rfc_params |> List.map CP.name_of_sv in
    let f_call = C.SCall {
        C.exp_scall_type = Void;
        C.exp_scall_method_name = fname;
        C.exp_scall_lock = None;
        C.exp_scall_arguments = params;
        C.exp_scall_ho_arg = None;
        C.exp_scall_is_rec = true;
        C.exp_scall_path_id = None;
        C.exp_scall_pos = no_pos
      } in
    aux_c_subtrees st f_call

  | RlReturn rule ->
    let typ = CP.get_exp_type rule.r_exp in
    let name = fresh_name() in
    let var = C.VarDecl {
        C.exp_var_decl_type = typ;
        C.exp_var_decl_name = name;
        C.exp_var_decl_pos = no_pos;
      } in
    let exp = exp2cast rule.r_exp in
    let assign = C.Assign {
        C.exp_assign_lhs = name;
        C.exp_assign_rhs = exp;
        C.exp_assign_pos = no_pos;
      } in
    let return = C.Sharp {
        exp_sharp_type = typ;
        exp_sharp_flow_type = C.Sharp_ct {
            CF.formula_flow_interval = !ret_flow_int;
            CF.formula_flow_link = None};
        exp_sharp_val = C.Sharp_var (typ, name);
        exp_sharp_unpack = false;
        exp_sharp_path_id = None;
        exp_sharp_pos = no_pos;
      } in
    let seq = mkCSeq var assign in
    let seq = mkCSeq seq return in
    Some seq
  | _ -> report_error no_pos ("st_core2cast unhandled" ^ (pr_rule st.stc_rule))

and aux_c_subtrees st cur_codes =
  let st_code = List.map st_core2cast st.stc_subtrees in
  match st_code with
  | [] -> Some cur_codes
  | [h] ->
    if h = None then Some cur_codes
    else
      let st_code = Gen.unsome h in
      let seq = mkCSeq cur_codes st_code in Some seq
  | _ -> report_error no_pos "aux_c_subtrees: not consider more than one subtree"

let rec synthesize_st_core st : Iast.exp option=
  match st.stc_rule with
  | RlSkip -> None
  | RlExistsLeft _ | RlExistsRight _ | RlFramePred _ | RlFrameData _
  | RlUnfoldPost _ | RlUnfoldPre _ ->
    begin
      let sts = List.map synthesize_st_core st.stc_subtrees in
      match sts with
      | [] -> None
      | [h] -> h
      | _ -> report_error no_pos "syn_st_core: no more than one st"
    end
  | RlAssign rassign ->
    let lhs, rhs = rassign.ra_lhs, rassign.ra_rhs in
    let c_exp = exp_to_iast rhs in
    let assgn = mkAssign (mkVar lhs) c_exp in
    aux_subtrees st assgn
  | RlPreAssign rcore ->
    let lhs = rcore.rpa_lhs in
    let rhs = rcore.rpa_rhs in
    let v_decl = I.VarDecl {
        exp_var_decl_type = CP.type_of_sv lhs;
        exp_var_decl_decls = [(CP.name_of_sv lhs, None, no_pos)];
        exp_var_decl_pos = no_pos;
      } in
    let rhs_exp = exp_to_iast rhs in
    let seq = mkSeq v_decl rhs_exp in
    aux_subtrees st seq

  | RlReturn rcore -> let c_exp = exp_to_iast rcore.r_exp in
    Some (I.Return {
      exp_return_val = Some c_exp;
      exp_return_path_id = None;
      exp_return_pos = no_pos})
  | RlFWrite rbind ->
    let bvar, (typ, f_name) = rbind.rfw_bound_var, rbind.rfw_field in
    let rhs = rbind.rfw_value in
    let rhs_var, mem_var = mkVar rhs,  mkVar bvar in
    let exp_mem = I.Member {
        exp_member_base = mem_var;
        exp_member_fields = [f_name];
        exp_member_path_id = None;
        exp_member_pos = no_pos
      } in
    let bind = mkAssign exp_mem rhs_var in
    aux_subtrees st bind
  | RlFRead rcore -> let lhs = rcore.rfr_value in
    let bvar, (typ, f_name) = rcore.rfr_bound_var, rcore.rfr_field in
    let exp_decl = I.VarDecl {
        exp_var_decl_type = CP.type_of_sv lhs;
        exp_var_decl_decls = [(CP.name_of_sv lhs, None, no_pos)];
       exp_var_decl_pos = no_pos;
      } in
    let bound_var = mkVar bvar in
    let mem_var = Iast.Member {
        exp_member_base = bound_var;
        exp_member_fields = [f_name];
        exp_member_path_id = None;
        exp_member_pos = no_pos;
      } in
    let lhs = mkVar lhs in
    let body = mkAssign lhs mem_var in
    let seq = mkSeq exp_decl body in aux_subtrees st seq
  | RlFuncCall rcore ->
    let args = rcore.rfc_params |> List.map mkVar in
    let fcall = Iast.CallNRecv {
        exp_call_nrecv_method = rcore.rfc_fname |> Cast.unmingle_name;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_arguments = args;
        exp_call_nrecv_path_id = None;
        exp_call_nrecv_pos = no_pos} in
    aux_subtrees st fcall
  | RlFuncRes rcore ->
    let args = rcore.rfr_params |> List.map mkVar in
    let fcall = Iast.CallNRecv {
        exp_call_nrecv_method = rcore.rfr_fname |> Cast.unmingle_name;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_arguments = args;
        exp_call_nrecv_path_id = None;
        exp_call_nrecv_pos = no_pos} in
    let rvar = rcore.rfr_return in
    let r_var = I.VarDecl {
        exp_var_decl_type = CP.type_of_sv rvar;
        exp_var_decl_decls = [(CP.name_of_sv rvar, None, no_pos)];
       exp_var_decl_pos = no_pos;
      } in
    let asgn = mkAssign (mkVar rvar) fcall in
    let seq = mkSeq r_var asgn in aux_subtrees st seq
  | RlBranch rcore ->
    let cond_e = pure_to_iast rcore.rb_cond in
    let sts = List.map synthesize_st_core st.stc_subtrees in
    let if_b = sts |> List.hd |> Gen.unsome in
    let else_b = sts |> List.tl |> List.hd |> Gen.unsome in
    Some (I.mkCond cond_e if_b else_b None no_pos)
  | _ -> report_error no_pos "synthesize_st_core: this case unhandled"

and aux_subtrees st cur_codes =
  let st_code = List.map synthesize_st_core st.stc_subtrees in
  match st_code with
  | [] -> Some cur_codes
  | [h] ->
    if h = None then Some cur_codes
    else let st_code = Gen.unsome h in
      let seq = mkSeq cur_codes st_code in Some seq
  | _ -> report_error no_pos "aux_subtrees: not consider more than one subtree"

let rec replace_exp_aux nexp exp : I.exp = match (exp:I.exp) with
  | I.Assign e -> let n_e1 = replace_exp_aux nexp e.I.exp_assign_lhs in
    let n_e2 = replace_exp_aux nexp e.I.exp_assign_rhs in
    I.Assign {e with exp_assign_lhs = n_e1;
                   exp_assign_rhs = n_e2}
  | I.Bind e -> let n_body = replace_exp_aux nexp e.I.exp_bind_body in
    I.Bind {e with exp_bind_body = n_body}
  | I.Block e -> let n_body = replace_exp_aux nexp e.I.exp_block_body in
    I.Block {e with exp_block_body = n_body}
  | I.Cast e -> let n_body = replace_exp_aux nexp e.I.exp_cast_body in
    I.Cast {e with exp_cast_body = n_body;}
  | I.CallNRecv e ->
    let name = e.I.exp_call_nrecv_method in
    let () = x_tinfo_hp (add_str "name" pr_id) name no_pos in
    if name = "fcode" then nexp
    else exp
  | I.UnkExp _ -> let () = x_tinfo_pp "marking" no_pos in
    exp
  | I.Cond e ->
    let () = x_tinfo_pp "marking" no_pos in
    let r1 = replace_exp_aux nexp e.exp_cond_then_arm in
    let r2 = replace_exp_aux nexp e.exp_cond_else_arm in
    I.Cond {e with exp_cond_then_arm = r1;
                 exp_cond_else_arm = r2}
  | I.Label (a, body) -> Label (a, replace_exp_aux nexp body)
  | I.Seq e ->
    let n_e1 = replace_exp_aux nexp e.I.exp_seq_exp1 in
    let n_e2 = replace_exp_aux nexp e.I.exp_seq_exp2 in
    I.Seq {e with exp_seq_exp1 = n_e1;
                exp_seq_exp2 = n_e2}
  | _ -> exp

let rec replace_cexp_aux nexp exp : C.exp =
  match (exp:C.exp) with
  | C.Assign e ->
    let n_e2 = replace_cexp_aux nexp e.C.exp_assign_rhs in
    C.Assign {e with C.exp_assign_rhs = n_e2}
  | Bind e ->
    let n_body = replace_cexp_aux nexp e.C.exp_bind_body in
    C.Bind {e with C.exp_bind_body = n_body}
  | C.Block e ->
    let n_body = replace_cexp_aux nexp e.C.exp_block_body in
    C.Block {e with C.exp_block_body = n_body}
  | C.Cast e ->
    let n_body = replace_cexp_aux nexp e.C.exp_cast_body in
    C.Cast {e with C.exp_cast_body = n_body;}
  | C.SCall e ->
    let name = e.C.exp_scall_method_name in
    if is_substr fcode_str name then nexp
    else exp
  | C.Cond e ->
    let r1 = replace_cexp_aux nexp e.C.exp_cond_then_arm in
    let r2 = replace_cexp_aux nexp e.C.exp_cond_else_arm in
    C.Cond {e with C.exp_cond_then_arm = r1;
                   C.exp_cond_else_arm = r2}
  | C.Label e ->
    let n_e = replace_cexp_aux nexp e.C.exp_label_exp in
    C.Label {e with C.exp_label_exp = n_e}
  | C.Seq e ->
    let n_e1 = replace_cexp_aux nexp e.C.exp_seq_exp1 in
    let n_e2 = replace_cexp_aux nexp e.C.exp_seq_exp2 in
    C.Seq {e with C.exp_seq_exp1 = n_e1;
                C.exp_seq_exp2 = n_e2}
  | _ -> exp

let replace_exp_proc n_exp proc =
  let n_body = match proc.Iast.proc_body with
    | None -> None
    | Some exp -> Some (replace_exp_aux n_exp exp) in
  let () = x_tinfo_hp (add_str "n_exp" pr_iast_exp) n_exp no_pos in
  let () = x_binfo_hp (add_str "n_body" pr_iast_exp_opt) n_body no_pos in
  {proc with I.proc_body = n_body}

let replace_exp_cproc n_exp proc =
  let body = proc.C.proc_body |> Gen.unsome in
  let rec aux (exp: C.exp) = match exp with
    | C.Label l -> C.Label {l with C.exp_label_exp = aux l.C.exp_label_exp}
    | C.Block e -> C.Block {e with C.exp_block_body = aux e.C.exp_block_body}
    | C.Seq e ->
      let n_e1 = aux e.C.exp_seq_exp1 in
      let n_e2 = aux e.C.exp_seq_exp2 in
      C.Seq {e with C.exp_seq_exp1 = n_e1;
                    C.exp_seq_exp2 = n_e2;}
    | C.Cond e ->
      let n_e1 = aux e.C.exp_cond_then_arm in
      let n_e2 = aux e.C.exp_cond_else_arm in
      C.Cond {e with C.exp_cond_then_arm = n_e1;
                     C.exp_cond_else_arm = n_e2;}
    | C.SCall e ->
      let name = e.C.exp_scall_method_name in
      if is_substr fcode_str name then
        n_exp
      else exp
    | _ -> exp in
  let n_body = aux body in
  {proc with C.proc_body = Some n_body}


let rec subst_term_formula sst (formula:CF.formula) = match formula with
  | CF.Base bf ->
    let pf = bf.CF.formula_base_pure |> pure_of_mix in
    let n_pf = CP.subst_term sst pf in
    CF.Base {bf with CF.formula_base_pure = mix_of_pure n_pf}
  | CF.Exists bf ->
    let pf = bf.CF.formula_exists_pure |> pure_of_mix in
    let n_pf = CP.subst_term sst pf in
    CF.Exists {bf with CF.formula_exists_pure = mix_of_pure n_pf}
  | CF.Or bf ->
    let n_f1 = subst_term_formula sst bf.CF.formula_or_f1 in
    let n_f2 = subst_term_formula sst bf.CF.formula_or_f2 in
    CF.Or {bf with CF.formula_or_f1 = n_f1;
                CF.formula_or_f2 = n_f2}

let get_heap (formula:CF.formula) = match formula with
  | CF.Base bf -> bf.CF.formula_base_heap
  | CF.Exists bf -> bf.CF.formula_exists_heap
  | CF.Or bf -> report_error no_pos ("faulty formula" ^ (pr_formula formula))

let get_heap_nodes (hf:CF.h_formula) =
  let rec aux hf = match hf with
    | CF.Star bf -> (aux bf.CF.h_formula_star_h1) @ (aux bf.CF.h_formula_star_h2)
    | CF.DataNode dn ->
      let var = dn.CF.h_formula_data_node in
      let args = dn.CF.h_formula_data_arguments in
      let data_name = dn.CF.h_formula_data_name in
      [(var, data_name, args)]
    | _ -> [] in
  aux hf

let frame_var_formula formula var =
  let rec helper hf = match hf with
    | CF.DataNode dnode ->
      let dnode_var = dnode.CF.h_formula_data_node in
      if CP.eq_spec_var dnode_var var
      then (CF.HEmp, dnode.CF.h_formula_data_arguments)
      else (hf, [])
    | CF.ViewNode vn ->
      let vn_var = vn.CF.h_formula_view_node in
      if CP.eq_spec_var vn_var var
      then (CF.HEmp, vn.CF.h_formula_view_arguments)
      else (hf, [])
    | CF.Star sf -> let n_f1 = helper sf.CF.h_formula_star_h1 in
      let n_f2 = helper sf.CF.h_formula_star_h2 in
      let n_hf = if fst n_f1 = CF.HEmp then fst n_f2
        else if fst n_f2 = CF.HEmp then fst n_f1
        else CF.Star {sf with CF.h_formula_star_h1 = fst n_f1;
                              CF.h_formula_star_h2 = fst n_f2} in
      (n_hf, (snd n_f1)@(snd n_f2))
    | _ -> (hf,[]) in
  match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let n_hf = helper hf in
    (CF.Base {bf with CF.formula_base_heap = fst n_hf}, snd n_hf)
  | CF.Exists bf ->
    let hf = bf.CF.formula_exists_heap in
    let n_hf, vars = helper hf in
    (CF.Exists {bf with CF.formula_exists_heap = n_hf}, vars)
  | _ -> report_error no_pos "frame_var_formula: CF.Or unhandled"

let get_hf (f:CF.formula) = match f with
  | CF.Base bf -> bf.CF.formula_base_heap
  | CF.Exists bf -> bf.CF.formula_exists_heap
  | CF.Or _ -> report_error no_pos "get_hf unhandled"

let is_res_sv_syn sv = match sv with
  | CP.SpecVar (_,n,_) -> is_substr "rs" n

let negate b = not b

(*********************************************************************
 * Rule utilities
 *********************************************************************)

let is_used_after (var:CP.spec_var) st_subtrees =
  let aux var st_core =
    let rule = st_core.stc_rule in
    match rule with
    | RlReturn rule ->
      let vars = CP.afv rule.r_exp in
      CP.mem_svl var vars
    | RlAssign rule ->
      let vars = (rule.ra_lhs)::(CP.afv rule.ra_rhs) in
      CP.mem_svl var vars
    | RlBranch rule ->
      let vars = (CP.fv (rule.rb_cond)) @ (CF.fv rule.rb_if_pre)
                 @ (CF.fv rule.rb_else_pre) in
      CP.mem_svl var vars
    | RlFWrite rule ->
      let vars = rule.rfw_bound_var::[rule.rfw_value] in
      CP.mem_svl var vars
    | _ -> false in
  List.exists (fun x -> aux var x) st_subtrees

let rec rm_useless_stc (st_core:synthesis_tree_core) =
  let rule = st_core.stc_rule in
  match rule with
  | RlFRead r -> if is_used_after r.rfr_value st_core.stc_subtrees then
      {st_core with stc_subtrees = List.map rm_useless_stc st_core.stc_subtrees}
    else st_core.stc_subtrees |> List.hd |> rm_useless_stc
  | _ -> {st_core with stc_subtrees = List.map rm_useless_stc st_core.stc_subtrees}

let rec is_fwrite_called trace rcore : bool  =
  match trace with
  | [] -> false
  | head::tail ->
    begin
      match head with
      | RlFWrite r ->
        let (t1, n1) = rcore.rfw_field in
        let (t2, n2) = r.rfw_field in
        let compare = CP.eq_sv rcore.rfw_bound_var r.rfw_bound_var &&
                      t1 = t2 && n1 = n2 in
        if compare then true
        else is_fwrite_called tail rcore
      | _ -> is_fwrite_called tail rcore
    end

let rec is_fcall_called trace args : bool =
  match trace with
  | [] -> false
  | head::tail ->
    begin
      match head with
      | RlFuncCall rcore ->
        let params = rcore.rfc_params in
        if (List.length args = List.length params) then
          if List.for_all2 (fun x y -> CP.eq_spec_var x y) args params
          then true
          else is_fcall_called tail args
        else is_fcall_called tail args
      | _ -> is_fcall_called tail args
    end

let is_fcall_ever_called trace : bool =
  let rec aux trace num =
    match trace with
    | [] -> false
    | head::tail ->
      begin
        match head with
        | RlFuncRes _ | RlFuncCall _ ->
          if num - 1 = 0 then true
          else aux tail (num-1)
        | _ -> aux tail num
      end in
  aux trace 2

let rec is_fres_called trace args : bool =
  match trace with
  | [] -> false
  | head::tail ->
    begin
      match head with
      | RlFuncRes rcore ->
        let params = rcore.rfr_params in
        if (List.length args = List.length params) then
          if List.for_all2 (fun x y -> CP.eq_spec_var x y) args params
          then true
          else is_fres_called tail args
        else is_fres_called tail args
      | _ -> is_fcall_called tail args
    end

let rec is_fread_called trace rcore : bool  =
  match trace with
  | [] -> false
  | head::tail ->
    begin
      match head with
      | RlFRead r ->
        let (t1, n1) = rcore.rfr_field in
        let (t2, n2) = r.rfr_field in
        let compare = CP.eq_sv rcore.rfr_bound_var r.rfr_bound_var &&
                      t1 = t2 && n1 = n2 in
        if compare then true
        else is_fread_called tail rcore
      | _ -> is_fread_called tail rcore
    end

let is_rule_fread_usable goal r =
  let var = r.rfr_value in
  let post_vars = CF.fv goal.gl_post_cond in
  if List.exists (fun x -> CP.eq_sv x var) post_vars then true
  else let arg_f = extract_var_f goal.gl_pre_cond var in
      match arg_f with
      | None -> false
      | Some arg_f -> if CF.is_emp_formula arg_f then false
        else true

let eliminate_useless_rules goal rules =
  let contain_sym_rules rule = match rule with
    | RlFRead _ -> true
    (* | RlUnfoldPre _ -> true *)
    | _ -> false in
  let is_rule_unfold_post_usable rules =
    not (List.exists contain_sym_rules rules) in
  let n_rules = rules in
  let n_rules = List.filter (fun rule -> match rule with
      | RlFRead r -> is_rule_fread_usable goal r
      | _ -> true) rules in
  (* let n_rules = List.filter (fun rule -> match rule with
   *     | RlUnfoldPost _ -> is_rule_unfold_post_usable n_rules
   *     | _ -> true) n_rules in *)
  n_rules

let compare_rule_assign_vs_assign goal r1 r2 =
  if CP.is_res_spec_var r1.ra_lhs then PriHigh
  else if CP.is_res_spec_var r2.ra_lhs then PriLow
  else PriEqual

let compare_rule_assign_vs_other goal r1 r2 = match r2 with
    | RlAssign r2 -> compare_rule_assign_vs_assign goal r1 r2
    | _ ->
      if CP.is_res_spec_var r1.ra_lhs then PriHigh
      else PriEqual

let compare_rule_frame_data_vs_other r1 r2 =
  match r2 with
  | RlFramePred _
  | RlFrameData _ -> if CP.is_res_sv r1.rfd_lhs then PriHigh
    else PriLow
  | _ -> PriLow

let compare_rule_frame_pred_vs_other r1 r2 =
  match r2 with
  | RlFramePred _
  | RlFrameData _ -> if CP.is_res_sv r1.rfp_lhs then PriHigh
    else PriLow
  | RlFuncRes _
  | RlFuncCall _ -> PriHigh
  | _ -> PriLow

let compare_rule_fun_res_vs_other r1 r2 = match r2 with
  | RlReturn _ -> PriLow
  | _ -> PriHigh

let compare_rule_fun_call_vs_other r1 r2 = match r2 with
  | RlReturn _ -> PriLow
  | _ -> PriHigh

let compare_rule_unfold_post_vs_other r1 r2 = match r2 with
  | RlUnfoldPost r2 -> if CP.is_res_sv r1.rp_var then PriHigh
    else if CP.is_res_sv r2.rp_var then PriLow
    else PriEqual
  | _ -> PriLow

let compare_rule goal r1 r2 =
  match r1 with
  | RlUnfoldPre _ -> PriHigh
  | RlAssign r1 -> compare_rule_assign_vs_other goal r1 r2
  | RlFrameData r -> compare_rule_frame_data_vs_other r r2
  | RlFramePred r -> compare_rule_frame_pred_vs_other r r2
  | RlReturn _ -> PriHigh
  | RlFuncRes r1 -> compare_rule_fun_res_vs_other r1 r2
  | RlFuncCall r1 -> compare_rule_fun_call_vs_other r1 r2
  | RlUnfoldPost r1 -> compare_rule_unfold_post_vs_other r1 r2
  | RlPreAssign _ -> PriLow
  | _ -> PriEqual

let is_code_rule trace = match trace with
  | [] -> false
  | h::_ ->
    match h with
    | RlAssign _ | RlReturn _ | RlFWrite _ | RlFuncRes _
    | RlFuncCall _ -> true
    | _ -> false

let reorder_rules goal rules =
  let cmp_rule r1 r2 =
    let prio = compare_rule goal r1 r2 in
    match prio with
    | PriEqual -> 0
    | PriLow -> +1
    | PriHigh -> -1 in
  List.sort cmp_rule rules
(* List.sort sorts list increasing order *)

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
    gl_trace = [];
    gl_vars = vars;  }

let mk_goal_w_procs cprog proc_decls pre post vars =
  let pre = unprime_formula pre in
  let post = unprime_formula post in
  { gl_prog = cprog;
    gl_proc_decls = proc_decls;
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_trace = [];
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
    stc_subtrees = sub_trees; }

let mk_synthesis_tree_success goal rule : synthesis_tree =
  let stcore = mk_synthesis_tree_core goal rule [] in
  StDerive { std_goal = goal;
             std_rule = rule;
             std_sub_trees = [];
             std_status = StValid stcore; }

let mk_synthesis_tree_fail goal sub_trees msg : synthesis_tree =
  StSearch { sts_goal = goal;
             sts_sub_trees = sub_trees;
             sts_status = StUnkn msg; }

(*********************************************************************
 * Normalization rules
 *********************************************************************)

let choose_rule_exists_left goal =
  let vars = CF.get_exists goal.gl_pre_cond in
  if vars = [] then []
  else let rule = RlExistsLeft { exists_vars = vars} in
    [rule]

let rm_redundant_constraint (goal: goal) : goal =
  let pf_pre = CF.get_pure goal.gl_pre_cond in
  let n_pf_pre = CP.elim_idents pf_pre in
  let n_pre = CF.repl_pure_formula n_pf_pre goal.gl_pre_cond in
  let pf_post = CF.get_pure goal.gl_post_cond in
  let n_pf_post = CP.elim_idents pf_post in
  let n_post = CF.repl_pure_formula n_pf_post goal.gl_post_cond in
  {goal with gl_pre_cond = n_pre;
             gl_post_cond = n_post}

let process_rule_exists_left goal rule =
  let n_pre = remove_exists_vars goal.gl_pre_cond rule.exists_vars in
  let n_goal = {goal with gl_pre_cond = n_pre} in
  mk_derivation_subgoals goal (RlExistsLeft rule) [n_goal]

let process_rule_exists_right goal rule =
  let n_goal = {goal with gl_post_cond = rule.n_post} in
  mk_derivation_subgoals goal (RlExistsRight rule) [n_goal]

let process_rule_branch goal rule =
  let if_goal = {goal with gl_pre_cond = rule.rb_if_pre} in
  let else_goal = {goal with gl_pre_cond = rule.rb_else_pre} in
  mk_derivation_subgoals goal (RlBranch rule) [if_goal; else_goal]

