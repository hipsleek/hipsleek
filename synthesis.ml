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
let pr_ctxs = Cprinter.string_of_list_context
let pr_int = string_of_int
let pr_hf = Cprinter.string_of_h_formula
let pr_f = Cprinter.string_of_formula
let pr_ent (x,y) = (pr_f x)^ " |- " ^ (pr_f y)
let pr_exp = Cprinter.string_of_formula_exp
let pr_var = Cprinter.string_of_typed_spec_var
let pr_vars = Cprinter.string_of_typed_spec_var_list
let pr_pf = Cprinter.string_of_pure_formula
let pr_sv = Cprinter.string_of_spec_var
let pr_hp = Cprinter.string_of_hp_decl
let pr_hps = pr_list pr_hp
let pr_struc_f = Cprinter.string_of_struc_formula
let pr_substs = pr_list (pr_pair pr_var pr_var)
let pr_failesc_list = Cprinter.string_of_list_failesc_context
let pr_f_opt f = match f with
  | None -> ""
  | Some f -> pr_f f

(*** Reference variable***********)
let rel_num = ref 0
let res_num = ref 0
let sb_num = ref 0
let sb_ent_num = ref 0
let sb_ent_time = ref 0.0
let fail_branch_num = ref 0
let check_entail_num = ref 0
let r_pre = ref 0

let inference_time = ref 0.0
let synthesis_time = ref 0.0
let allocate_list = ref ([]: CP.spec_var list list)

let max_triples = ref ([] : (CP.exp * CP.exp * CP.exp) list)
let min_triples = ref ([] : (CP.exp * CP.exp * CP.exp) list)
let repair_pos = ref (None : VarGen.loc option)
let repair_pos_fst = ref (None : VarGen.loc option)
let repair_pos_snd = ref (None : VarGen.loc option)
let repair_res = ref (None : Iast.prog_decl option)
let r_pre_vars = ref ([] : CP.spec_var list)
let is_return_cand = ref false
let is_return_fst = ref false
let is_return_snd = ref false
let check_post_list = ref ([]: bool list)
let unk_hps = ref ([] : C.hp_decl list)
let block_var_decls = ref ([]: CP.spec_var list)
let block_var_decls_snd = ref ([]: CP.spec_var list)
let repair_proc = ref (None : C.proc_decl option)
let syn_iprog = ref (None: I.prog_decl option)
let syn_cprog = ref (None: C.prog_decl option)
let tmpl_proc_name = ref (None: string option)
let entailments = ref ([] : (CF.formula * CF.formula) list)
let syn_pre = ref (None : CF.formula option)
let syn_res_vars = ref ([] : CP.spec_var list)
let syn_ref_vars = ref ([] : CP.spec_var list)
let syn_is_call_stmt = ref false
(*********************************************************************
 * Data structures
 *********************************************************************)

type priority =
  | PriHigh
  | PriLow
  | PriEqual

exception EPrio of priority

type rule =
  | RlSkip
  | RlReturn of rule_return
  | RlUnfoldPre of rule_unfold_pre
  | RlUnfoldPost of rule_unfold_post
  | RlFrameData of rule_frame_data
  | RlFramePred of rule_frame_pred
  | RlAllocate of rule_allocate
  | RlFree of rule_free
  | RlMkNull of rule_mk_null
  | RlNewNum of rule_new_num
  | RlAssign of rule_assign
  | RlHeapAssign of rule_heap_assign
  | RlFRead of rule_field_read
  | RlFWrite of rule_field_write
  | RlFuncCall of rule_func_call

and rule_heap_assign = {
  rha_left : CP.spec_var;
  rha_right : CP.spec_var;
}

and rule_mk_null ={
  rmn_null: CP.exp;
  rmn_var : CP.spec_var;
  rmn_lookahead : goal option;
}

and rule_new_num = {
  rnn_num: CP.exp;
  rnn_var : CP.spec_var;
  rnn_lookahead : goal option;
}

and rule_pre_assign = {
  rpa_lhs : CP.spec_var;
  rpa_rhs : CP.exp
}

and rule_allocate = {
  ra_data: string;
  ra_pre : CF.formula;
  ra_var : CP.spec_var;
  ra_params: CP.spec_var list;
  ra_end : bool;
  ra_lookahead : goal option;
}

and rule_free = {
  rd_vars: CP.spec_var list;
}

and rule_post_assign = {
  rapost_lhs : CP.spec_var;
  rapost_rhs : CP.exp;
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

and rule_frame_pred = {
  rfp_lhs: CP.spec_var;
  rfp_rhs: CP.spec_var;
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
  unfold_pre_var: CP.spec_var;
}

and rule_unfold_post = {
  rp_var: CP.spec_var;
  rp_case_formula: CF.formula;
}

and rule_func_call = {
  rfc_fname : string;
  rfc_params : CP.spec_var list;
  rfc_new_pre : CF.formula;
  rfc_return: CP.spec_var option;
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
  rfr_lookahead: goal option;
}

and rule_assign = {
  ra_lhs : CP.spec_var;
  ra_rhs : CP.exp;
  ra_numeric : bool;
}

and rule_return = {
  r_exp : CP.exp;
  r_checked: bool;
}

and goal = {
  gl_prog : C.prog_decl;
  gl_proc_decls: C.proc_decl list;
  gl_pre_cond : CF.formula;
  gl_post_cond : CF.formula;
  gl_start_time : float;
  gl_vars: CP.spec_var list;
  gl_trace: rule list;
  gl_lookahead: rule list;
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

let pr_priority pr = match pr with
  | PriHigh -> "PriHigh"
  | PriLow -> "PriLow"
  | PriEqual -> "PriEqual"

let negate_priority prio = match prio with
  | PriLow -> PriHigh
  | PriEqual -> PriEqual
  | PriHigh -> PriLow

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

let pr_i_exp = Iprinter.string_of_exp_repair
let pr_i_exp_opt = Iprinter.string_of_exp_repair

let pr_i_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Iprinter.string_of_exp_repair e

let pr_c_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_goal goal =
  let vars = goal.gl_vars in
  let pr_svs = pr_list Cprinter.string_of_typed_spec_var in
  "synthesize " ^ (pr_svs vars) ^ "\n" ^
  (pr_f goal.gl_pre_cond) ^ "\n" ^
  "~>\n" ^ (pr_f goal.gl_post_cond) ^ "."

let pr_rule_assign rule =
  let lhs, rhs = rule.ra_lhs, rule.ra_rhs in
  (Cprinter.string_of_typed_spec_var lhs) ^ " = " ^ (pr_exp rhs)
  ^ ";" ^ (string_of_bool rule.ra_numeric)


let pr_rule_pre_assign rule =
  let lhs, rhs = rule.rpa_lhs, rule.rpa_rhs in
  (Cprinter.string_of_typed_spec_var lhs) ^ " = " ^ (pr_exp rhs)

let pr_rule_post_assign rule =
  let lhs, rhs = rule.rapost_lhs, rule.rapost_rhs in
  (Cprinter.string_of_typed_spec_var lhs) ^ " = " ^ (pr_exp rhs)

let pr_func_call rule =
  let fc_name = rule.rfc_fname in
  let args = rule.rfc_params |> pr_vars in
  match rule.rfc_return with
  | None -> fc_name ^ "(" ^ args ^ ")"
  | Some var ->
    (pr_var var) ^ " = " ^ fc_name ^ "(" ^ args ^ ")"

let pr_rule_bind rule =
  let exp = rule.rfw_bound_var in
  (Cprinter.string_of_spec_var exp) ^ ", " ^ (snd rule.rfw_field) ^ ", "
  ^ (Cprinter.string_of_spec_var rule.rfw_value)

let pr_fread rule =
  "FREAD (" ^ (pr_var rule.rfr_bound_var) ^ "." ^ (snd rule.rfr_field) ^ ", "
  ^ (pr_var rule.rfr_value) ^ ")"

let pr_instantiate rule =
  "(" ^ (pr_var rule.rfp_lhs) ^ ", " ^ (pr_var rule.rfp_rhs) ^ ")"

let pr_frame_data rcore =
  "(" ^ (pr_var rcore.rfd_lhs) ^ ", " ^ (pr_var rcore.rfd_rhs) ^ ")"

let pr_rule_alloc r =
  let data = r.ra_data in
  let params = r.ra_params in
  data ^ "(" ^ (pr_vars params) ^ ")"

let pr_rule_mk_null r =
  let var = r.rmn_var in
  let e = r.rmn_null in
  (pr_var var) ^ ", " ^ (pr_exp e)

let pr_rule_new_num r =
  let var = r.rnn_var in
  let e = r.rnn_num in
  (pr_var var) ^ ", " ^ (pr_exp e)

let pr_rule rule = match rule with
  | RlSkip -> "RlSkip"
  | RlMkNull r -> "RlMkNull " ^ (pr_rule_mk_null r)
  | RlNewNum r -> "RlNewNum " ^ (pr_rule_new_num r)
  | RlAllocate r -> "RlAllocate " ^ (pr_rule_alloc r)
  | RlFree r -> "RlFree " ^ (pr_vars r.rd_vars)
  | RlHeapAssign r -> "RlHeapAssign (" ^ (pr_var r.rha_left) ^ ", " ^ (pr_var r.rha_right)
  | RlFuncCall fc -> "RlFuncCall " ^ (pr_func_call fc)
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlReturn rule -> "RlReturn " ^ "(" ^ (pr_exp rule.r_exp) ^ ")"
  | RlFWrite rule -> "RlFWrite " ^ (pr_rule_bind rule)
  | RlFRead rule -> pr_fread rule
  | RlUnfoldPre rule -> "RlUnfoldPre " ^ (rule.n_pre |> pr_f)
  | RlUnfoldPost rule -> "RlUnfoldPost<" ^ (rule.rp_case_formula |> pr_f) ^ ">"
  | RlFramePred rule -> "RlFramePred" ^ (pr_instantiate rule)
  | RlFrameData rcore -> "RlFrameData" ^ (pr_frame_data rcore)

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

let pr_rules = pr_list_mln pr_rule

(* Basic functions  *)

let negate b = not b

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
             formula_exists_pos = pos }) ->
    let n_qvars = CP.remove_dups_svl (qvars @ vars) in
    CF.mkExists_w_lbl n_qvars h p vp t fl a pos lbl
  | CF.Or bf -> let n_f1 = add_exists_vars bf.formula_or_f1 vars in
    let n_f2 = add_exists_vars bf.formula_or_f2 vars in
    CF.Or {bf with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2}

let contains_lseg prog =
  let view_decls = prog.C.prog_view_decls in
  List.exists (fun x -> eq_str x.C.view_name "lseg") view_decls

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

let remove_exists_pf pf =
  let rec aux pf = match pf with
    | CP.BForm _ -> pf
    | CP.And (f1, f2, loc) ->
      let n_f1 = aux f1 in
      let n_f2 = aux f2 in
      CP.And (n_f1, n_f2, loc)
    | CP.AndList list ->
      let n_list = list |> List.map (fun (x, y) -> (x, aux y)) in
      CP.AndList n_list
    | CP.Or (f1, f2, lbl, loc) ->
      let n_f1 = aux f1 in
      let n_f2 = aux f2 in
      CP.Or (n_f1, n_f2, lbl, loc)
    | CP.Not (pf, lbl, loc) ->
      let n_pf = aux pf in
      CP.Not (n_pf, lbl, loc)
    | CP.Exists (_, exists_f, _ , _) -> aux exists_f
    | CP.Forall _ -> pf in
  let conjuncts = pf |> CP.split_conjunctions in
  conjuncts |> List.map aux |> CP.join_conjunctions

let remove_exists_pf pf =
  Debug.no_1 "remove_exists_pf" pr_pf pr_pf
    (fun _ -> remove_exists_pf pf) pf

let mk_pure_form_from_eq_pairs eq_pairs =
  let aux (fst, snd) =
    CP.mkEqVar fst snd no_pos in
  let eq_pairs = eq_pairs |> List.map aux in
  eq_pairs |> CP.join_conjunctions

let mk_pure_form_from_eq_pairs eq_pairs =
  Debug.no_1 "mk_pure_form_from_eq_pairs" pr_substs pr_pf
    (fun _ -> mk_pure_form_from_eq_pairs eq_pairs) eq_pairs

let rename_primed_vars formula =
  let primed_vars = formula |> CF.fv |> List.filter CP.is_primed in
  let n_vars = primed_vars |> List.map CP.fresh_spec_var in
  let pairs = List.combine primed_vars n_vars in
  let unprimed_vars = primed_vars |> List.map CP.to_unprimed in
  let eq_pairs = List.combine n_vars unprimed_vars in
  let n_pf = mk_pure_form_from_eq_pairs eq_pairs in
  let n_f = formula |> CF.subst pairs in
  CF.add_pure_formula_to_formula n_pf n_f

let remove_exists_vars_pf vars pf =
  let rec aux pf = match pf with
    | CP.Exists (var, exists_f, _, _) ->
      if CP.mem var vars then aux exists_f
      else pf
    | CP.And (f1, f2, loc) ->
      let n_f1 = aux f1 in
      let n_f2 = aux f2 in
      CP.And (n_f1, n_f2, loc)
    | CP.AndList list ->
      let n_list = list |> List.map (fun (x, y) -> (x, aux y)) in
      CP.AndList n_list
    | CP.Or (f1, f2, lbl, loc) ->
      let n_f1 = aux f1 in
      let n_f2 = aux f2 in
      CP.Or (n_f1, n_f2, lbl, loc)
    | _ -> pf in
  let conjuncts = pf |> CP.split_conjunctions in
  conjuncts |> List.map aux |> CP.join_conjunctions

let rec remove_exists_vars (formula:CF.formula) (vars: CP.spec_var list) =
  match formula with
  | CF.Base bf ->
    let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
    let n_pf = remove_exists_vars_pf vars pf in
    CF.Base {bf with CF.formula_base_pure = MCP.mix_of_pure n_pf}
  | CF.Exists ({formula_exists_qvars = qvars;
                formula_exists_heap =  h;
                formula_exists_vperm = vp;
                formula_exists_pure = p;
                formula_exists_type = t;
                formula_exists_and = a;
                formula_exists_flow = fl;
                formula_exists_label = lbl;
                formula_exists_pos = pos } as bf) ->
    let n_qvars = List.filter (fun x -> not(CP.mem_svl x vars)) qvars in
    let n_pf = remove_exists_vars_pf vars (MCP.pure_of_mix p) in
    let n_pf = MCP.mix_of_pure n_pf in
    if n_qvars = [] then CF.mkBase_w_lbl h n_pf vp t fl a pos lbl
    else CF.Exists {bf with CF.formula_exists_qvars = n_qvars;
                            CF.formula_exists_pure = n_pf}
  | CF.Or bf -> let n_f1 = remove_exists_vars bf.formula_or_f1 vars in
    let n_f2 = remove_exists_vars bf.formula_or_f2 vars in
    CF.Or {bf with CF.formula_or_f1 = n_f1;
                   CF.formula_or_f2 = n_f2}

let remove_exists_vars formula e_vars=
  Debug.no_2 "remove_exists_vars" pr_f pr_vars pr_f
    (fun _ _ -> remove_exists_vars formula e_vars) formula e_vars

let remove_exists formula =
  let rec aux formula = match formula with
    | CF.Base bf ->
      let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
      let n_pf = remove_exists_pf pf in
      CF.Base {bf with CF.formula_base_pure = MCP.mix_of_pure n_pf}
    | CF.Exists {formula_exists_qvars = qvars;
                  formula_exists_heap =  h;
                  formula_exists_vperm = vp;
                  formula_exists_pure = p;
                  formula_exists_type = t;
                  formula_exists_and = a;
                  formula_exists_flow = fl;
                  formula_exists_label = lbl;
                  formula_exists_pos = pos } ->
      let n_pf = remove_exists_pf (MCP.pure_of_mix p) in
      let n_pf = MCP.mix_of_pure n_pf in
      CF.mkBase_w_lbl h n_pf vp t fl a pos lbl
    | CF.Or bf ->
      let n_f1 = aux bf.CF.formula_or_f1 in
      let n_f2 = aux bf.CF.formula_or_f2 in
      CF.Or {bf with CF.formula_or_f1 = n_f1;
                     CF.formula_or_f2 = n_f2} in
  aux formula

let remove_exists formula =
  Debug.no_1 "remove_exists" pr_f pr_f
    (fun _ -> remove_exists formula) formula

let get_heap (formula:CF.formula) = match formula with
  | CF.Base bf -> bf.CF.formula_base_heap
  | CF.Exists bf -> bf.CF.formula_exists_heap
  | CF.Or bf -> report_error no_pos ("faulty formula" ^ (pr_f formula))

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

let get_heap_views (hf:CF.h_formula) =
  let rec aux hf = match hf with
    | CF.Star bf -> (aux bf.CF.h_formula_star_h1) @ (aux bf.CF.h_formula_star_h2)
    | CF.ViewNode vn ->
      let var = vn.CF.h_formula_view_node in
      let args = vn.CF.h_formula_view_arguments in
      let view_name = vn.CF.h_formula_view_name in
      [(var, view_name, args)]
    | _ -> [] in
  aux hf

let get_heap_variables (f:CF.formula) : CP.spec_var list =
  let f_nodes = f |> get_heap |> get_heap_nodes
                |> List.map (fun (x,_,_) -> x) in
  let f_views = f |> get_heap |> get_heap_views
                  |> List.map (fun (x,_,_) -> x) in
  f_nodes @ f_views

let get_heap_args (f:CF.formula) : CP.spec_var list =
  let node_args = f |> get_heap |> get_heap_nodes
                |> List.map (fun (_,_,x) -> x) |> List.concat in
  let view_args = f |> get_heap |> get_heap_views
                  |> List.map (fun (_,_,x) -> x) |> List.concat in
  node_args @ view_args

let rec elim_idents (f:CF.formula) = match f with
  | CF.Base bf ->
    let pf = bf.CF.formula_base_pure |> pure_of_mix in
    let n_pf = pf |> CP.elim_idents_node in
    CF.Base {bf with formula_base_pure = mix_of_pure n_pf}
  | CF.Exists bf ->
    let pf = bf.CF.formula_exists_pure |> pure_of_mix in
    let n_pf = pf |> CP.elim_idents_node in
    CF.Exists {bf with formula_exists_pure = mix_of_pure n_pf}
  | CF.Or bf -> CF.Or {bf with formula_or_f1 = elim_idents bf.CF.formula_or_f1;
                               formula_or_f2 = elim_idents bf.CF.formula_or_f2}

let elim_idents formula =
  Debug.no_1 "elim_idents" pr_f pr_f
    (fun _ -> elim_idents formula) formula

let get_equality_pairs (formula: CP.formula) =
  let aux_pf (pf:CP.p_formula) = match pf with
    | CP.Eq (e1, e2, _) ->
      begin
        match e1, e2 with
        | CP.Var (v1, _) , CP.Var (v2, _) -> [(v1, v2)]
        | _ -> []
      end
    | _ -> [] in
  let rec aux f = match f with
    | CP.BForm (bf, _) ->
      let (pf, _) = bf in
      aux_pf pf
    | CP.And (f1, f2, _) -> (aux f2) @ (aux f2)
    | CP.Or _ -> []
    | CP.AndList list -> list |> List.map snd |> List.map aux |> List.concat
    | CP.Not _ -> []
    | CP.Forall (_, pf, _, _) -> aux pf
    | CP.Exists (_, exists_f, _, _) -> aux exists_f in
  let conjuncts = formula |> CP.split_conjunctions in
  conjuncts |> List.map aux |> List.concat

let get_equality_pairs (formula: CP.formula) =
  Debug.no_1 "get_equality_pairs" pr_pf pr_substs
    (fun _ -> get_equality_pairs formula) formula

(* let get_eq_max (pf: CP.formula) =
 *   let aux_pf pf = match (pf: CP.p_formula) with
 *     | CP.EqMax (e1, e2, e3,_) -> [(e1, e2, e3)]
 *     | _ -> [] in
 *   let rec aux pf = match pf with
 *     | CP.BForm (bf, _) ->
 *       let (p_f,_) = bf in
 *       aux_pf p_f
 *     | CP.And (pf1, pf2,_) ->
 *       (aux pf1) @ (aux pf2)
 *     | CP.AndList list ->
 *       list |> List.map snd |> List.map aux |> List.concat
 *     | CP.Or (pf1, pf2,_,_) ->
 *       (aux pf1) @ (aux pf2)
 *     | CP.Not (n_pf, _,_) -> aux n_pf
 *     | CP.Forall (_, a_pf,_,_) -> aux a_pf
 *     | CP.Exists (_, a_pf,_,_) -> aux a_pf in
 *   aux pf *)

(* let replace_eq_max (pf: CP.formula) (o_e1, o_e2, o_e3) =
 *   let eq_exp e1 e2 = match e1, e2 with
 *     | CP.Var (sv1, _), CP.Var (sv2, _) -> CP.eq_sv sv1 sv2
 *     | _ -> false in
 *   let eq_pair_exp (fst1, snd1) (fst2, snd2) =
 *     match fst1, snd1, fst2, snd2 with
 *     | CP.Var (sv1, _), CP.Var (sv2, _), CP.Var (sv3, _), CP.Var (sv4, _) ->
 *       CP.eq_spec_var_list [sv1; sv2] [sv3; sv4]
 *     | _ -> false in
 *   let aux_pf pf = match (pf: CP.p_formula) with
 *     | CP.EqMax (e1, e2, e3,loc) ->
 *       if not(eq_exp e1 o_e1) && (eq_pair_exp (e2, e3) (o_e2, o_e3)) then
 *         CP.Eq (e1, o_e1, loc)
 *       else pf
 *     | _ -> pf in
 *   let rec aux (pf: CP.formula) = match pf with
 *     | CP.BForm (bf, lbl1) ->
 *       let (p_f,lbl2) = bf in
 *       let n_p_f = aux_pf p_f in
 *       CP.BForm ((n_p_f, lbl2), lbl1)
 *     | CP.And (pf1, pf2,loc) ->
 *       let n_pf1 = aux pf1 in
 *       let n_pf2 = aux pf2 in
 *       CP.And (n_pf1, n_pf2, loc)
 *     | CP.AndList list ->
 *       let n_list = list |> List.map (fun (x, y) -> (x, aux y)) in
 *       CP.AndList n_list
 *     | CP.Or (pf1, pf2,opt,loc) ->
 *       let n_pf1 = aux pf1 in
 *       let n_pf2 = aux pf2 in
 *       CP.Or (n_pf1, n_pf2, opt, loc)
 *     | CP.Not (n_pf, a,b) -> CP.Not(aux n_pf, a, b)
 *     | CP.Forall (a, a_pf,b,c) -> CP.Forall (a, aux a_pf, b,c)
 *     | CP.Exists (a, a_pf,b,c) -> CP.Exists (a, aux a_pf, b,c) in
 *   aux pf *)

(* remove common equality in the post-condition *)
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

let simplify_post post_cond =
  let get_exists_pf (pf:CP.formula) =
    let rec aux pf = match pf with
    | CP.BForm _ -> []
    | CP.And (f1, f2, _) -> (aux f1) @ (aux f2)
    | CP.AndList list -> list |> List.map snd |> List.map aux |> List.concat
    | CP.Or (f1,f2,_,_) -> (aux f1) @ (aux f2)
    | CP.Not (n_f,_,_) ->aux n_f
    | CP.Forall _ -> []
    | CP.Exists (e_var, e_f, _, _) -> e_var::(aux e_f) in
    pf |> CP.split_conjunctions |> List.map aux |> List.concat in
  let rec move_exists_pf (formula: CF.formula) = match formula with
    | CF.Base bf ->
      let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
      let e_vars = get_exists_pf pf in
      let n_pf = remove_exists_pf pf |> MCP.mix_of_pure in
      let n_f = CF.Base {bf with CF.formula_base_pure = n_pf} in
      add_exists_vars n_f e_vars
    | CF.Exists bf ->
      let pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
      let e_vars = get_exists_pf pf in
      let n_pf = remove_exists_pf pf |> MCP.mix_of_pure in
      let n_f = CF.Exists {bf with CF.formula_exists_pure = n_pf} in
      add_exists_vars n_f e_vars
    | CF.Or bf ->
      let n_f1 = move_exists_pf bf.CF.formula_or_f1 in
      let n_f2 = move_exists_pf bf.CF.formula_or_f2 in
      CF.Or { bf with CF.formula_or_f1 = n_f1;
                      CF.formula_or_f2 = n_f2} in
  let post_cond = move_exists_pf post_cond in
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
    let () = x_tinfo_hp (add_str "post" pr_f) post_cond no_pos in
    let helper_fun (x, y) = if CP.mem x exists_vars then (x,y) else (y,x) in
    let eq_pairs = eq_pairs |> List.map helper_fun in
    let n_post = CF.subst eq_pairs post_cond |> elim_idents in
    let () = x_tinfo_hp (add_str "post" pr_f) n_post no_pos in
    let rm_exists_vars = eq_pairs |> List.map (fun (x,y) -> [x;y]) |> List.concat
                         |> CP.remove_dups_svl in
    let exists_vars = CP.diff_svl exists_vars rm_exists_vars in
    add_exists_vars n_post exists_vars

let simplify_post post_cond =
  Debug.no_1 "simplify_post" pr_f pr_f
    (fun _ -> simplify_post post_cond) post_cond

let mkAndList pf_list =
  let rec aux pf_list = match pf_list with
  | [] -> CP.mkTrue no_pos
  | h :: t ->
    let pf2 = aux t in
    CP.mkAnd h pf2 no_pos in
  let pf = aux pf_list in
  pf

(* get a "fix-point" pure formula for a list of vars *)
let extract_var_pf (pf:CP.formula) vars =
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
    | CP.AndList list ->
      CP.AndList (List.map (fun (x,y) -> (x, helper y vars)) list)
    | _ -> pf in
  let n_pf = helper pf vars in
  let n_vars = CP.fv n_pf in
  if Gen.BList.list_equiv_eq CP.eq_sv vars n_vars then n_pf
  else helper pf n_vars

let extract_var_pf pf vars =
  Debug.no_2 "extract_var_pf" pr_pf pr_vars pr_pf
    (fun _ _ -> extract_var_pf pf vars) pf vars

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
      | Some _, None -> vf1
      | None, Some _ -> vf2
      | _ -> None
    end
  | _ -> None

let extract_hf_var hf var =
  Debug.no_2 "extract_hf_var" pr_hf pr_var (fun x -> match x with
      | None -> "None"
      | Some (_, vars) -> pr_vars vars)
    (fun x y -> extract_hf_var x y) hf var

let extract_var_f f var = match f with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
      let heap_extract = extract_hf_var hf var in
      begin
        match heap_extract with
        | None ->
          let pf_var = extract_var_pf pf [var] in
          Some (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var))
        | Some (hf, vars) ->
          let h_vars = CF.h_fv hf in
          let vars = [var] @ h_vars |> CP.remove_dups_svl in
          let pf_var = extract_var_pf pf vars in
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
  Debug.no_2 "extract_var_f" pr_f pr_var
    (fun x -> match x with
       | None -> "None"
       | Some varf -> pr_f varf)
    (fun _ _ -> extract_var_f formula var) formula var


(*****************************************************
  * Atomic functions
 ********************************************************)
let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let add_h_formula_to_formula h_formula (formula:CF.formula) : CF.formula =
  match formula with
  | CF.Base bf ->
    let hf = bf.formula_base_heap in
    let n_hf = CF.mkStarH hf h_formula no_pos in
    CF.Base {bf with formula_base_heap = n_hf}
  | CF.Exists bf ->
    let hf = bf.formula_exists_heap in
    let n_hf = CF.mkStarH hf h_formula no_pos in
    CF.Exists {bf with formula_exists_heap = n_hf}
  | CF.Or bf -> report_error no_pos "the formula cannot be disjunctive"

let add_h_formula_to_formula added_hf formula =
  Debug.no_2 "add_h_formula_to_formula" pr_hf pr_f pr_f
    (fun _ _ -> add_h_formula_to_formula added_hf formula) added_hf formula

let add_h_formula_list_to_formula hf_list formula =
  let rec aux hf_list f = match hf_list with
    | [] -> f
    | head::tail ->
      let n_f = add_h_formula_to_formula head f in
      aux tail n_f in
  aux hf_list formula

let rec simpl_f (f:CF.formula) = match f with
  | Or bf -> (simpl_f bf.formula_or_f1) @ (simpl_f bf.formula_or_f2)
  | _ -> [f]

let check_var_mem mem list = List.exists (fun x -> CP.eq_sv x mem) list

(* Get the value of a field *)
let get_field var access_field data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> eq_str x.C.data_name name) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.C.data_fields in
    let pairs = List.combine data_fields fields in
    let result = List.filter (fun (x,y) -> x = access_field) pairs in
    if result = [] then None
    else Some (snd (List.hd result))
  with Not_found -> None

(* Update a data node with a new value to the field *)
let set_field var access_field (n_val:CP.spec_var) data_decls =
  let name = var.CF.h_formula_data_name in
  try
    let data = List.find (fun x -> eq_str x.C.data_name name) data_decls in
    let fields = var.CF.h_formula_data_arguments in
    let data_fields = List.map fst data.C.data_fields in
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

let rec rm_emp_hf hf = match hf with
    | CF.Star sf ->
      let n_f1 = rm_emp_hf sf.CF.h_formula_star_h1 in
      let n_f2 = rm_emp_hf sf.CF.h_formula_star_h2 in
      if CF.is_empty_heap n_f1 then rm_emp_hf n_f2
      else if CF.is_empty_heap n_f2 then rm_emp_hf n_f1
      else Star {sf with h_formula_star_h1 = rm_emp_hf n_f1;
                         h_formula_star_h2 = rm_emp_hf n_f2}
    | CF.Phase pf ->
      let n_f1 = rm_emp_hf pf.CF.h_formula_phase_rd in
      let n_f2 = rm_emp_hf pf.CF.h_formula_phase_rw in
      if CF.is_empty_heap n_f1 then n_f2
      else if CF.is_empty_heap n_f2 then n_f1
      else hf
    | _ -> hf

let rec rm_emp_formula formula:CF.formula =
  match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" pr_hf) hf no_pos in
    let n_hf = rm_emp_hf hf in
    let () = x_tinfo_hp (add_str "n_hf" pr_hf) n_hf no_pos in
    CF.Base {bf with formula_base_heap = n_hf}
  | CF.Or disjs ->
    let n_f1 = rm_emp_formula disjs.CF.formula_or_f1 in
    let n_f2 = rm_emp_formula disjs.CF.formula_or_f2 in
    CF.Or {disjs with formula_or_f1 = n_f1;
                      formula_or_f2 = n_f2; }
  | CF.Exists exists_f ->
    let hf = exists_f.CF.formula_exists_heap in
    Exists {exists_f with formula_exists_heap = rm_emp_hf hf}

let do_unfold_view_hf_vn cprog pr_views args (hf:CF.h_formula) =
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
        | Some l1, Some l2 -> report_error no_pos ("only unfold once" ^ (pr_hf hf))
        | Some l1, None -> Some (List.map (add_h_formula_to_formula hf2) l1)
        | None, Some l2 -> Some (List.map (add_h_formula_to_formula hf1) l2)
        | None, None -> None
      end
    | _ -> None in
  match helper hf with
  | None -> [(CF.mkBase_simp hf (MCP.mkMTrue no_pos))]
  | Some list -> list

let do_unfold_view_hf_vn cprog pr_views args (hf:CF.h_formula) =
  let pr1 = pr_f in
  Debug.no_2 "do_unfold_view_hf_vn" pr_hf pr_vars
    (fun x -> x |> pr_list pr1)
    (fun _ _ -> do_unfold_view_hf_vn cprog pr_views args hf) hf args

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

let do_unfold_view_vnode cprog pr_views args (formula:CF.formula) =
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
      let () = x_tinfo_hp (add_str "nf" (pr_list pr_f)) nf no_pos in
      nf |> List.map (CF.add_quantifiers qvars)
    | Or orf  ->
      let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      nf1 @ nf2 in
  if pr_views = [] then [formula] else helper formula

let do_unfold_view_vnode cprog pr_views args (f0: CF.formula) =
  let pr1 = pr_f in
  Debug.no_2 "do_unfold_view_vnode" pr1 pr_vars (pr_list pr1)
    (fun _ _ -> do_unfold_view_vnode cprog pr_views args f0) f0 args

let get_pre_post (struc_f: CF.struc_formula) =
  let rec get_post struc_f = match struc_f with
    | CF.EBase bf ->
      let f = bf.CF.formula_struc_base in
      if CF.is_emp_formula f then
        bf.CF.formula_struc_continuation |> Gen.unsome |> get_post
      else f
    | CF.EAssume assume_f ->
      assume_f.CF.formula_assume_simpl
    | _ -> report_error no_pos ("get_post unhandled " ^ (pr_struc_f struc_f)) in
  let rec aux struc_f = match struc_f with
    | CF.EBase bf ->
      let pre = bf.CF.formula_struc_base in
      let post = bf.CF.formula_struc_continuation |> Gen.unsome |> get_post in
      let pre = pre |> rm_emp_formula in
      let post = post |> rm_emp_formula in
      [(pre, post)]
    | CF.ECase cases ->
      let branches = cases.CF.formula_case_branches in
      let aux (pf, case) =
        let pairs = aux case in
        List.map (fun (x,y) ->
            let n_formula = CF.add_pure_formula_to_formula pf x in
          (n_formula, y)) pairs in
      branches |> List.map aux |> List.concat
    | CF.EList list ->
      let struct_list = list |> List.map snd in
      struct_list |> List.map aux |> List.concat
    | _ -> report_error no_pos ("get_specs unhandled " ^ (pr_struc_f struc_f)) in
  aux struc_f

let get_pre_post (struc_f: CF.struc_formula) =
  Debug.no_1 "get_pre_post" pr_struc_f (pr_list (pr_pair pr_f pr_f))
    (fun _ -> get_pre_post struc_f) struc_f

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
    let () = x_tinfo_hp (add_str "check_post" string_of_bool) (!check_post) no_pos in
    let residue = CF.mkBase_simp (CF.HEmp) (Mcpure.mkMTrue no_pos) in
    residue, conseq
  else
    let name = "T" ^ (string_of_int !rel_num) in
    let hl_name = CP.mk_spec_var name in
    let () = rel_num := !rel_num + 1 in
    let args = vars |> List.map (fun x -> CP.mkVar x no_pos) in
    let hp_decl = {
      C.hp_name = name;
      C.hp_vars_inst = vars |> List.map (fun x -> (x, Globals.I));
      C.hp_part_vars = [];
      C.hp_root_pos = None;
      C.hp_is_pre = false;
      C.hp_view = None;
      C.hp_formula =
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
    C.hp_name = name;
    C.hp_vars_inst = vars |> List.map (fun x -> (x, Globals.I));
    C.hp_part_vars = [];
    C.hp_root_pos = None;
    C.hp_is_pre = false;
    C.hp_view = None;
    C.hp_formula = CF.mkBase_simp (CF.HEmp) (mix_of_pure (CP.mkTrue no_pos))
  } in
  let () = unk_hps := hp_decl::(!unk_hps) in
  let hrel = CF.HRel (hl_name, args, no_pos) in
  let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  hrel_f

let create_spec_pred vars pred_name =
  let vars = vars |> CP.remove_dups_svl in
  let () = x_tinfo_hp (add_str "predicate name" pr_id) pred_name no_pos in
  let () = x_tinfo_hp (add_str "predicate vars" pr_vars) vars no_pos in
  let all_predicates = !unk_hps in
  let name = pred_name in
  let hl_name = CP.mk_spec_var name in
  let args = vars |> List.map (fun x -> CP.mkVar x no_pos) in
  let hp_decl =
    try
      List.find (fun x -> eq_str x.C.hp_name pred_name) all_predicates
    with _ ->
      let () = rel_num := !rel_num + 1 in
      let hp_decl = {
        C.hp_name = name;
        C.hp_vars_inst = vars |> List.map (fun x -> (x, Globals.I));
        C.hp_part_vars = [];
        C.hp_root_pos = None;
        C.hp_is_pre = false;
        C.hp_view = None;
        C.hp_formula = CF.mkBase_simp (CF.HEmp) (mix_of_pure (CP.mkTrue no_pos))
      } in
      let () = unk_hps := hp_decl::!unk_hps in
      hp_decl in
  let () = x_tinfo_hp (add_str "hp_decl" pr_hp) hp_decl no_pos in
  let hrel = CF.HRel (hl_name, args, no_pos) in
  let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  hrel_f

let eq_hp_decl hp1 hp2 =
  let hp1_name,hp2_name = hp1.C.hp_name, hp2.C.hp_name in
  let hp1_args = hp1.C.hp_vars_inst |> List.map (fun (x,y) -> x) in
  let hp2_args = hp2.C.hp_vars_inst |> List.map (fun (x,y) -> x) in
  if List.length hp1_args = List.length hp2_args && hp1_name = hp2_name then
    let args = List.combine hp1_args hp2_args in
    List.for_all (fun (x,y) -> CP.eq_spec_var x y) args
  else false

let need_unfold_rhs prog vn=
  let rec look_up_view vn0=
    let vdef = x_add C.look_up_view_def_raw x_loc prog.C.prog_view_decls
        vn0.CF.h_formula_view_name in
    let fs = List.map fst vdef.view_un_struc_formula in
    let hv_opt = CF.is_only_viewnode false (CF.formula_of_disjuncts fs) in
    match hv_opt with
    | Some vn1 -> look_up_view vn1
    | None -> vdef in
  let vdef = look_up_view vn in
  [(vn.CF.h_formula_view_name,vdef.C.view_un_struc_formula,
    vdef.C.view_vars)], [(vn.CF.h_formula_view_node)]

let is_node_var (var: CP.spec_var) = match CP.type_of_sv var with
  | Named _ -> true
  | _ -> false

let is_unk_type_var (var: CP.spec_var) = match CP.type_of_sv var with
  | UNK -> true
  | _ -> false

let is_bool_var (var: CP.spec_var) = match CP.type_of_sv var with
  | Bool -> true
  | _ -> false

let is_int_var (var: CP.spec_var) = match CP.type_of_sv var with
  | Int | NUM -> true
  | _ -> false

let is_unk_var (var: CP.spec_var) = match CP.type_of_sv var with
  | UNK -> true
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

let rec add_pure_formula_to_formula (n_pf: CP.formula) (f2:CF.formula)
  : CF.formula =
  match f2 with
  | CF.Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos} ->
    CF.Or {formula_or_f1 = add_pure_formula_to_formula n_pf f1;
           formula_or_f2 = add_pure_formula_to_formula n_pf f2;
           formula_or_pos = pos}
  | CF.Base b ->
    let pf = b.CF.formula_base_pure |> MCP.pure_of_mix in
    let n_pf = CP.mkAnd pf n_pf no_pos in
    CF.Base { b with CF.formula_base_pure = MCP.mix_of_pure n_pf;}
  | CF.Exists b ->
    let pf = b.CF.formula_exists_pure |> MCP.pure_of_mix in
    let n_pf = CP.mkAnd pf n_pf no_pos in
    CF.Exists {b with CF.formula_exists_pure = MCP.mix_of_pure n_pf}

let add_pure_formula_to_formula (n_pf: CP.formula) (f2:CF.formula) =
    Debug.no_2 "add_pf_to_formula" pr_pf pr_f pr_f
    (fun _ _ -> add_pure_formula_to_formula n_pf f2) n_pf f2

let add_formula_to_formula f1 f2 =
  let bf = CF.mkStar f1 f2 CF.Flow_combine no_pos in
  let evars = (CF.get_exists f1) @ (CF.get_exists f2) |> CP.remove_dups_svl in
  if evars = [] then bf
    else add_exists_vars bf evars

let rec simplify_arithmetic (formula: CF.formula) =
  match formula with
  | CF.Base b ->
    let n_pf = b.CF.formula_base_pure |> MCP.pure_of_mix in
    let n_pf = CP.arith_simplify_new n_pf in
    let n_pf = CP.norm_form n_pf in
    CF.Base {b with CF.formula_base_pure = MCP.mix_of_pure n_pf}
  | CF.Exists bf ->
    let n_pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
    let n_pf = CP.arith_simplify_new n_pf in
    let n_pf = CP.norm_form n_pf in
    CF.Exists {bf with CF.formula_exists_pure = MCP.mix_of_pure n_pf}
  | CF.Or bf ->
    let n_f1 = simplify_arithmetic bf.CF.formula_or_f1 in
    let n_f2 = simplify_arithmetic bf.CF.formula_or_f2 in
    CF.Or {bf with CF.formula_or_f1 = n_f1;
                   CF.formula_or_f2 = n_f2}

let simplify_arithmetic formula =
  Debug.no_1 "simplify_arithmetic" pr_f pr_f
    (fun _ -> simplify_arithmetic formula) formula

let rm_ident_constraint_pf pre_pf post_pf =
  let pre_constraints = pre_pf |> remove_exists_pf |> CP.split_conjunctions in
  let post_constraints = post_pf |> remove_exists_pf |> CP.split_conjunctions in
  x_tinfo_hp (add_str "pre conjuncts" (pr_list pr_pf)) pre_constraints no_pos;
  x_tinfo_hp (add_str "post conjuncts" (pr_list pr_pf)) post_constraints no_pos;
  let filter_fun pf =
    List.exists (CP.equalFormula pf) pre_constraints |> negate in
  let post_constraints = post_constraints |> List.filter filter_fun in
  x_tinfo_hp (add_str "post conjuncts" (pr_list pr_pf)) post_constraints no_pos;
  CP.join_conjunctions post_constraints

let rm_ident_constraint_pf pre_pf post_pf =
  Debug.no_2 "rm_ident_constraint_pf" pr_pf pr_pf pr_pf
    (fun _ _ -> rm_ident_constraint_pf pre_pf post_pf) pre_pf post_pf

let rm_ident_constraints pre post =
  let aux pre post = match pre, post with
    | CF.Base bf1, CF.Exists bf2 ->
      let pf1 = bf1.CF.formula_base_pure |> MCP.pure_of_mix in
      let pf2 = bf2.CF.formula_exists_pure |> MCP.pure_of_mix in
      let n_pf2 = rm_ident_constraint_pf pf1 pf2 in
      CF.Exists {bf2 with CF.formula_exists_pure = MCP.mix_of_pure n_pf2}
    | CF.Base bf1, CF.Base bf2 ->
      let pf1 = bf1.CF.formula_base_pure |> MCP.pure_of_mix in
      let pf2 = bf2.CF.formula_base_pure |> MCP.pure_of_mix in
      let n_pf2 = rm_ident_constraint_pf pf1 pf2 in
      CF.Base {bf2 with CF.formula_base_pure = MCP.mix_of_pure n_pf2}
    | _ -> post in
  let n_post = aux pre post in
  n_post

let rm_duplicate_constraint_pf (pf: CP.formula) : (CP.spec_var list * CP.formula) =
  let rec get_exists (pf: CP.formula) = match pf with
    | CP.Exists (e_vars, e_pf, _, _) ->
      let (e2, pf2) = get_exists e_pf in
      (e_vars::e2, pf2)
    | CP.And (f1, f2, loc) ->
      let e1, n_f1 = get_exists f1 in
      let e2, n_f2 = get_exists f2 in
      (e1@e2, CP.And (n_f1, n_f2, loc))
    | _ -> ([], pf) in
  let pf = remove_exists_pf pf in
  let constraints = CP.split_conjunctions pf in
  let constraints = constraints |> Gen.BList.remove_dups_eq CP.equalFormula in
  x_tinfo_hp (add_str "constraints" (pr_list pr_pf)) constraints no_pos;
  let e_constraints = List.map get_exists constraints in
  let f_constraints = List.map snd e_constraints in
  x_tinfo_hp (add_str "constraints" (pr_list pr_pf)) f_constraints no_pos;
  let n_pf = CP.join_conjunctions f_constraints in
  let e_vars = e_constraints |> List.map fst |> List.concat in
  (e_vars, n_pf)

let simplify_min_max_pf pf =
  let eq_find (fst1, snd1) (token, fst2, snd2) =
    match fst1, snd1, fst2, snd2 with
    | CP.Var (sv1, _), CP.Var (sv2, _), CP.Var (sv3, _), CP.Var (sv4, _) ->
      CP.eq_spec_var_list [sv1; sv2] [sv3; sv4]
    | _ -> false in
  let conjuncts = pf |> remove_exists_pf |> CP.split_conjunctions in
  let rec aux_exp e = match e with
    | CP.Max (e1,e2,loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e, n_vars, add_formula =
        try
          let n_e,_,_ = List.find (eq_find (n_e1, n_e2)) !max_triples in
          n_e, var1@var2, orig1@orig2
        with _ ->
          let n_name = fresh_any_name "max" in
          let n_var = CP.SpecVar (Int, n_name, VarGen.Unprimed) in
          let n_e = CP.Var (n_var, loc) in
          let add_formula = CP.EqMax (n_e, n_e1, n_e2, no_pos) in
          let () = max_triples := (n_e, n_e1, n_e2)::!max_triples in
          n_e, n_var::var1@var2, add_formula::orig1@orig2 in
      (n_e, n_vars, add_formula)
    | CP.Min (e1,e2,loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e, n_vars, add_formula =
        try
          let n_e,_,_ = List.find (eq_find (n_e1, n_e2)) !min_triples in
          n_e, var1@var2, orig1@orig2
        with _ ->
          let n_name = fresh_any_name "min" in
          let n_var = CP.SpecVar (Int, n_name, VarGen.Unprimed) in
          let n_e = CP.Var (n_var, loc) in
          let add_formula = CP.EqMin (n_e, n_e1, n_e2, no_pos) in
          let () = max_triples := (n_e, n_e1, n_e2)::!max_triples in
          n_e, n_var::var1@var2, add_formula::orig1@orig2 in
      (n_e, n_vars, add_formula)
    (* | CP.Min (e1,e2,loc) ->
     *   let n_e1, var1, orig1 = aux_exp e1 in
     *   let n_e2, var2, orig2 = aux_exp e2 in
     *   let n_e, n_vars, add_formula =
     *     try
     *       let n_e,_,_ = List.find (eq_find (n_e1, n_e2)) !min_triples in
     *       n_e, var1@var2, orig1@orig2
     *     with _ ->
     *       let n_name = fresh_any_name "min" in
     *       let n_var = CP.SpecVar (Int, n_name, VarGen.Unprimed) in
     *       let n_e = CP.Var (n_var, loc) in
     *       let add_formula = CP.EqMin (n_e, n_e1, n_e2, no_pos) in
     *       let () = min_triples := (n_e, n_e1, n_e2)::!min_triples in
     *       n_e, n_var::var1@var2, add_formula::orig1@orig2 in
     *   (n_e, n_vars, orig1@orig2) *)
    | CP.Add (e1, e2, pos) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e = CP.Add (n_e1, n_e2, pos) in
      (n_e, var1@var2, orig1@orig2)
    | CP.Subtract (e1, e2, pos) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e = CP.Subtract (n_e1, n_e2, pos) in
      (n_e, var1@var2, orig1@orig2)
    | CP.Mult (e1, e2, pos) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e = CP.Mult (n_e1, n_e2, pos) in
      (n_e, var1@var2, orig1@orig2)
    | CP.Div (e1, e2, pos) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_e = CP.Div (n_e1, n_e2, pos) in
      (n_e, var1@var2, orig1@orig2)
    | _ -> (e, [], []) in
  let aux_pf pf = match pf with
    | CP.EqMin (exp1, exp2, exp3, loc) ->
      let n_e2, var1, orig1 = aux_exp exp2 in
      let n_e3, var2, orig2 = aux_exp exp3 in
      let n_pf = CP.EqMin (exp1, n_e2, n_e3, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.EqMax (exp1, exp2, exp3, loc) ->
      let n_e2, var1, orig1 = aux_exp exp2 in
      let n_e3, var2, orig2 = aux_exp exp3 in
      let n_pf = CP.EqMax (exp1, n_e2, n_e3, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Lt (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Lt (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Lte (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Lte (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Gt (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Gt (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Gte (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Gte (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Eq (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Eq (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | CP.Neq (e1, e2, loc) ->
      let n_e1, var1, orig1 = aux_exp e1 in
      let n_e2, var2, orig2 = aux_exp e2 in
      let n_pf = CP.Neq (n_e1, n_e2, loc) in
      (n_pf, var1@var2, orig1@orig2)
    | _ -> (pf, [], []) in
  let aux_bf bf =
    let (pf, lbl) = bf in
    let n_pf, vars, added = aux_pf pf in
    let added = List.map (fun x -> (x, None)) added in
    ((n_pf, lbl), vars, added) in
  let rec aux pf = match pf with
    | CP.BForm (bf, lbl) ->
      let n_bf, vars, added = aux_bf bf in
      let added = added |> List.map (fun x -> CP.BForm (x, None)) in
      let n_f = CP.BForm (n_bf, lbl) in
      let added = mkAndList added in
      let n_f = CP.mkAnd n_f added no_pos in
      n_f, vars
    | CP.Exists (sv, e_formula, opt, loc) ->
      let n_f, vars = aux e_formula in
      let n_f = CP.Exists (sv, n_f, opt, loc) in
      (n_f, vars)
    | _ -> pf, [] in
  let n_conjuncts = conjuncts |> List.map aux in
  let n_list = List.map fst n_conjuncts in
  let e_vars = List.map snd n_conjuncts |> List.concat in
  let n_pf = CP.join_conjunctions n_list in
  (n_pf, e_vars)

let simplify_min_max_pf (formula: CP.formula) =
  Debug.no_1 "simplify_min_max_pf" pr_pf (pr_pair pr_pf pr_vars)
    (fun _ -> simplify_min_max_pf formula) formula

let remove_min_max_in_both_sides (formula: CP.formula) : CP.formula =
  let conjuncts = formula |> CP.split_conjunctions in
  let is_max_min_exp (pf_exp: CP.exp) = match pf_exp with
    | CP.Max _ -> true
    | CP.Min _ -> true
    | _ -> false in
  let rec aux_pf pf = match pf with
    | CP.BForm (bf, lbl) ->
      let (p_formula, bf_annot) = bf in
      (* let () = x_binfo_hp (add_str "single constrant" pr_pf) pf no_pos in *)
      begin
        match p_formula with
        | CP.EqMax (e1, e2, e3, loc) ->
          if is_max_min_exp e1 then
            let n_name = fresh_any_name "mm" in
            let n_var = CP.SpecVar (Int, n_name, VarGen.Unprimed) in
            let n_e = CP.Var (n_var, loc) in
            let n_pf = CP.EqMax (n_e, e2, e3, loc) in
            let added_pf = CP.Eq (n_e, e1, loc) in
            let n_bf = (n_pf, bf_annot) in
            let added_bf = (added_pf, bf_annot) in
            let n_pf = CP.BForm (n_bf, lbl) in
            let added_pf = CP.BForm (added_bf, lbl) in
            CP.mkAnd n_pf added_pf no_pos
          else pf
        | CP.EqMin (e1, e2, e3, loc) ->
          if is_max_min_exp e1 then
            let n_name = fresh_any_name "mm" in
            let n_var = CP.SpecVar (Int, n_name, VarGen.Unprimed) in
            let n_e = CP.Var (n_var, loc) in
            let n_pf = CP.EqMin (n_e, e2, e3, loc) in
            let added_pf = CP.Eq (n_e, e1, loc) in
            let n_bf = (n_pf, bf_annot) in
            let added_bf = (added_pf, bf_annot) in
            let n_pf = CP.BForm (n_bf, lbl) in
            let added_pf = CP.BForm (added_bf, lbl) in
            CP.mkAnd n_pf added_pf no_pos
          else pf
        | _ -> pf
      end
    | CP.Exists (sv, e_formula, opt, loc) ->
      let n_f = aux_pf e_formula in
      let n_f = CP.Exists (sv, n_f, opt, loc) in
      n_f
    | CP.And (f1, f2, loc) ->
      let n_f1 = aux_pf f1 in
      let n_f2 = aux_pf f2 in
      CP.And (n_f1, n_f2, loc)
    | CP.AndList list ->
      let n_list = list |> List.map (fun (x,y) -> (x, aux_pf y)) in
      CP.AndList n_list
    | CP.Not (neg_pf, opt, loc) ->
      let n_pf = aux_pf neg_pf in
      CP.Not (n_pf, opt, loc)
    | _ -> pf in
  conjuncts |> List.map aux_pf |> CP.join_conjunctions

let remove_min_max_in_both_sides (formula: CP.formula) =
  Debug.no_1 "remove_min_max_in_both_sides" pr_pf pr_pf
    (fun _ -> remove_min_max_in_both_sides formula) formula

let simplify_min_max formula =
  let rec aux formula = match formula with
  | CF.Base bf ->
    let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
    let n_pf = pf |> remove_min_max_in_both_sides in
    let n_pf, e_vars = simplify_min_max_pf n_pf in
    let n_formula = CF.Base {bf with CF.formula_base_pure = MCP.mix_of_pure n_pf} in
    add_exists_vars n_formula e_vars
  | CF.Exists bf ->
    let pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
    let n_pf = pf |> remove_min_max_in_both_sides in
    let n_pf, e_vars = simplify_min_max_pf n_pf in
    let n_formula = CF.Exists {bf with CF.formula_exists_pure = MCP.mix_of_pure n_pf} in
    add_exists_vars n_formula e_vars
  | CF.Or bf ->
    let n_f1 = aux bf.CF.formula_or_f1 in
    let n_f2 = aux bf.CF.formula_or_f2 in
    CF.Or {bf with CF.formula_or_f1 = n_f1;
                   CF.formula_or_f2 = n_f2} in
  aux formula

let simplify_min_max formula =
  Debug.no_1 "simplify_min_max" pr_f pr_f
    (fun _ -> simplify_min_max formula) formula

let simplify_min_max_entailment ante conseq =
  let () = min_triples := [] in
  let () = max_triples := [] in
  let ante = simplify_min_max ante in
  let conseq = simplify_min_max conseq in
  let () = min_triples := [] in
  let () = max_triples := [] in
  (ante, conseq)

let simplify_min_max_entailment ante conseq =
  Debug.no_2 "simplify_min_max_entailment" pr_f pr_f pr_ent
    (fun _ _ -> simplify_min_max_entailment ante conseq) ante conseq

let rm_duplicate_constraints (formula: CF.formula) : CF.formula =
  let rec aux (formula: CF.formula) = match formula with
    | CF.Base bf ->
      let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
      let e_vars, pf = rm_duplicate_constraint_pf pf in
      let base = CF.Base  {bf with CF.formula_base_pure = MCP.mix_of_pure pf} in
      add_exists_vars base e_vars
    | CF.Exists bf ->
      let pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
      let e_vars, pf = rm_duplicate_constraint_pf pf in
      let base = CF.Exists {bf with CF.formula_exists_pure = MCP.mix_of_pure pf} in
      add_exists_vars base e_vars
    | CF.Or bf ->
      let n_f1 = aux bf.CF.formula_or_f1 in
      let n_f2 = aux bf.CF.formula_or_f2 in
      CF.Or {bf with CF.formula_or_f1 = n_f1;
                     CF.formula_or_f2 = n_f2} in
  aux formula

let get_equal_pairs_pre_cond_pf vars heap_vars pf =
  let eq_pairs = get_equality_pairs pf in
  let () = x_tinfo_hp (add_str "eq_pairs" pr_substs) eq_pairs no_pos in
  let swap (x,y) = if CP.mem y heap_vars && not(CP.mem y vars)
    then (y, x) else (x,y) in
  let eq_pairs = eq_pairs |> List.map swap in
  let filter_fun (x,y) = CP.mem x heap_vars && not(CP.mem x vars)
                         && (CP.mem y vars) in
  let eq_pairs = eq_pairs |> List.filter filter_fun in
  eq_pairs

let get_equal_pairs_pre_cond_pf vars heap_vars pf =
  Debug.no_3 "get_equal_pairs_pre_cond_pf" pr_vars pr_vars pr_pf pr_substs
    (fun _ _ _ -> get_equal_pairs_pre_cond_pf vars heap_vars pf) vars heap_vars pf

let simplify_goal_pre_cond goal pre_cond post_cond =
  let pre_cond = pre_cond |> remove_exists in
  let all_vars = goal.gl_vars in
  let heap_vars = pre_cond |> get_heap_variables in
  let aux pre_cond = match pre_cond with
    | CF.Base bf ->
      let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
      get_equal_pairs_pre_cond_pf all_vars heap_vars pf
    | CF.Exists bf ->
      let pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
      get_equal_pairs_pre_cond_pf all_vars heap_vars pf
    | _ -> [] in
  let eq_pairs = aux pre_cond in
  let n_pre = pre_cond |> CF.subst eq_pairs in
  let n_post = post_cond |> CF.subst eq_pairs in
  (n_pre, n_post)

let simplify_goal_pre_cond goal pre_cond post_cond =
  Debug.no_1 "simplify_goal_pre_cond" pr_f (pr_pair pr_f pr_f)
    (fun _ -> simplify_goal_pre_cond goal pre_cond post_cond) pre_cond

let simplify_goal goal =
  let n_pre = goal.gl_pre_cond in
  let n_post = goal.gl_post_cond in
  let n_post = simplify_post n_post in
  let (n_pre, n_post) = simplify_min_max_entailment n_pre n_post in
  let n_pre = remove_exists n_pre in
  let n_pre = elim_idents n_pre in
  let n_post = elim_idents n_post in
  let (n_pre, n_post) = simplify_equality goal.gl_vars n_pre n_post in
  let n_post = rm_ident_constraints n_pre n_post in
  let n_pre = simplify_arithmetic n_pre in
  let n_post = simplify_arithmetic n_post in
  let n_pre = rm_duplicate_constraints n_pre in
  let n_post = rm_duplicate_constraints n_post in
  let (n_pre, n_post) = simplify_goal_pre_cond goal n_pre n_post in
  {goal with gl_pre_cond = n_pre;
             gl_post_cond = n_post}

let simplify_goal goal =
  Debug.no_1 "simplify_goal" pr_goal pr_goal
    (fun _ -> simplify_goal goal) goal

let mkTrue_pf_formula (formula:CF.formula) =
  match formula with
  | CF.Base base ->
    let pos = base.CF.formula_base_pure |> MCP.pure_of_mix
              |> CP.pos_of_formula in
    CF.Base {base with CF.formula_base_pure = CP.mkTrue pos |> MCP.mix_of_pure}
  | CF.Exists base ->
    let pos = base.CF.formula_exists_pure |> MCP.pure_of_mix
              |> CP.pos_of_formula in
    CF.Exists {base with CF.formula_exists_pure = CP.mkTrue pos |> MCP.mix_of_pure}
  | CF.Or _ -> report_error no_pos "mkTrue_pf_formula: unhandled"

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

let rec get_unfold_view vars (f1:CF.formula) = match f1 with
  | CF.Base bf1 -> get_unfold_view_hf vars bf1.formula_base_heap
  | CF.Exists bf -> get_unfold_view_hf vars bf.formula_exists_heap
  | CF.Or bf -> []

let unprime_formula (formula:CF.formula) =
  let vars = CF.fv formula |> List.filter CP.is_primed in
  let substs = vars |> List.map (fun x -> (x, CP.to_unprimed x)) in
  CF.subst substs formula

let unprime_formula (formula:CF.formula) : CF.formula =
  Debug.no_1 "unprime_formula" pr_f pr_f
    (fun _ -> unprime_formula formula) formula

let simplify_predicate_vars (vars : CP.spec_var list) =
  let unprimed = vars |> List.filter CP.is_unprimed in
  let unprimed_names = unprimed |> List.map CP.name_of_sv in
  let helper_fun var =
    let name = CP.name_of_sv var in
    CP.is_primed var && Gen.BList.mem_eq eq_str name unprimed_names in
  vars |> List.filter (fun x -> helper_fun x |> negate)

let rec has_new_num trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlNewNum _ -> true
      | _ -> has_new_num t
    end

let rec has_mk_null trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlMkNull _ -> true
      | _ -> has_mk_null t
    end

let rec has_unfold_pre trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlUnfoldPre r -> true
      | _ -> has_unfold_pre t
    end

let rec has_allocate trace cur_params = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlAllocate r ->
        let params = r.ra_params in
        let var = r.ra_var in
        if CP.mem var cur_params ||
           CP.eq_spec_var_list params cur_params then true
        else has_allocate t cur_params
      | _ -> has_allocate t cur_params
    end

let has_heap_assign lhs rhs trace =
  let rec aux trace = match trace with
    | [] -> false
    | head::tail ->
      begin
        match head with
        | RlHeapAssign r ->
          let r_lhs = r.rha_left in
          let r_rhs = r.rha_right in
          if CP.eq_sv lhs r_lhs && CP.eq_sv rhs r_rhs then true
          else aux tail
        | _ -> aux tail
      end in
  aux trace

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

let remove_exists_vars_pf (formula:CP.formula) =
  let rec aux formula = match formula with
    | CP.Exists (_, x,_,_) -> aux x
    | CP.BForm _ -> formula
    | CP.And (f1, f2, loc) -> let nf1 = aux f1 in
      let nf2 = aux f2 in
      CP.And (nf1, nf2, loc)
    | CP.AndList list ->
      let nlist = List.map (fun (x,y) -> (x, aux y)) list in
      CP.AndList nlist
    | CP.Not (f, opt, loc) -> Not (aux f, opt, loc)
    | CP.Or (f1, f2, opt, loc) ->
      let nf1 = aux f1 in
      let nf2 = aux f2 in
      CP.Or (nf1, nf2, opt, loc)
    | CP.Forall _ -> formula in
  let conjuncts = formula |> CP.split_conjunctions in
  conjuncts |> List.map aux |> CP.join_conjunctions

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
  | CP.Var (sv, loc) ->
    let typ = CP.type_of_sv sv in
    if is_null_type typ then I.Null loc
    else var_to_iast sv loc
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

let rec get_var_decls pos (exp:I.exp) = match exp with
  | I.VarDecl var ->
    let v_pos = var.I.exp_var_decl_pos in
    if get_start_lnum v_pos <= get_start_lnum pos then
      let typ = var.I.exp_var_decl_type in
      var.I.exp_var_decl_decls |> List.map (fun (x, _, _) -> x)
      |> List.map (CP.mk_typed_sv typ)
    else []
  | I.Seq seq -> (get_var_decls pos seq.I.exp_seq_exp1) @
                 (get_var_decls pos seq.I.exp_seq_exp2)
  | I.Cond cond -> (get_var_decls pos cond.I.exp_cond_then_arm) @
                   (get_var_decls pos cond.I.exp_cond_else_arm)
  | I.Block b -> get_var_decls pos b.I.exp_block_body
  | I.Label (_, e) -> get_var_decls pos e
  | _ -> []

let get_var_decls pos (exp:I.exp) : CP.spec_var list =
  Debug.no_1 "get_var_decls" Iprinter.string_of_exp pr_vars
    (fun _ -> get_var_decls pos exp) exp

let mkVar sv = I.mkVar (CP.name_of_sv sv) no_pos

let mkAssign exp1 exp2 = I.mkAssign I.OpAssign exp1 exp2 None no_pos

let mkSeq exp1 exp2 = I.mkSeq exp1 exp2 no_pos

let rec st_core2cast st : C.exp option = match st.stc_rule with
  | RlSkip -> None
  (* | RlExistsRight _ *)
  | RlFramePred _ | RlFrameData _
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

let rec mk_exp_list e_list = match e_list with
  | [] -> I.Null no_pos
  | [h] -> h
  | h::tail -> let n_exp = mk_exp_list tail in
    mkSeq h n_exp

let rec synthesize_st_core st : Iast.exp option =
  let helper st =
    let sts = List.map synthesize_st_core st.stc_subtrees in
    match sts with
    | [] -> None
    | [h] -> h
    | _ -> report_error no_pos "syn_st_core: no more than one st" in
  match st.stc_rule with
  | RlSkip ->
    let i_exp = I.Empty no_pos in
    Some i_exp
  (* | RlExistsRight _ *)
  | RlFramePred _ | RlFrameData _ | RlFree _
  | RlUnfoldPost _ | RlUnfoldPre _ -> helper st
  | RlHeapAssign rc ->
    let lhs = rc.rha_left in
    let rhs = rc.rha_right in
    let assign = I.Assign {
        I.exp_assign_op = OpAssign;
        I.exp_assign_lhs = mkVar lhs;
        I.exp_assign_rhs = mkVar rhs;
        I.exp_assign_path_id = None;
        I.exp_assign_pos = no_pos;
      } in
    aux_subtrees st assign
  (* | RlFree rc ->
   *   let vars = rc.rd_vars in
   *   let mk_rule var =
   *     I.Free {
   *       exp_free_exp = mkVar var;
   *       exp_free_pos = no_pos
   *     } in
   *   let exp_list = List.map mk_rule vars in
   *   let d_exp = mk_exp_list exp_list in
   *   aux_subtrees st d_exp *)
  | RlAllocate rc ->
    let r_data = rc.ra_data in
    let r_var = rc.ra_var in
    let r_params = rc.ra_params in
    let params = List.map (mkVar) r_params in
    let e_new = I.New {
        I.exp_new_class_name = r_data;
        I.exp_new_arguments = params;
        I.exp_new_pos = no_pos;
      } in
    let assign = if CP.is_res_sv r_var then
        I.Return { I.exp_return_val = Some e_new;
                   I.exp_return_path_id = None;
                   I.exp_return_pos = no_pos}
      else
        I.Assign { I.exp_assign_op = I.OpAssign;
                   I.exp_assign_lhs = mkVar r_var;
                   I.exp_assign_path_id = None;
                   I.exp_assign_rhs = e_new;
                   I.exp_assign_pos = no_pos} in
    let seq = if rc.ra_end then assign
      else
        let lhs = I.VarDecl {
            I.exp_var_decl_type = CP.type_of_sv r_var;
            I.exp_var_decl_decls = [(CP.name_of_sv r_var, None, no_pos)];
            I.exp_var_decl_pos = no_pos;
          } in
        mkSeq lhs assign in
    aux_subtrees st seq
  | RlNewNum rc ->
    let var = rc.rnn_var in
    let null_e = rc.rnn_num in
    let n_e = exp_to_iast null_e in
    let v_decl = I.VarDecl {
        exp_var_decl_type = CP.type_of_sv var;
        exp_var_decl_decls = [(CP.name_of_sv var, None, no_pos)];
        exp_var_decl_pos = no_pos;
      } in
    let assign = mkAssign (mkVar var) n_e in
    let seq = mkSeq v_decl assign in
    aux_subtrees st seq
  | RlMkNull rc ->
    let var = rc.rmn_var in
    let var_typ = CP.type_of_sv var in
    if is_null_type var_typ then helper st
    else
      let null_e = rc.rmn_null in
      let n_e = exp_to_iast null_e in
      let v_decl = I.VarDecl {
          exp_var_decl_type = CP.type_of_sv var;
          exp_var_decl_decls = [(CP.name_of_sv var, None, no_pos)];
          exp_var_decl_pos = no_pos;
        } in
      let assign = mkAssign (mkVar var) n_e in
      let seq = mkSeq v_decl assign in
      aux_subtrees st seq
  | RlAssign rassign ->
    let lhs, rhs = rassign.ra_lhs, rassign.ra_rhs in
    let c_exp = exp_to_iast rhs in
    let assgn = mkAssign (mkVar lhs) c_exp in
    aux_subtrees st assgn
  | RlReturn rcore ->
    let c_exp = exp_to_iast rcore.r_exp in
    Some (I.Return {
        exp_return_val = Some c_exp;
        exp_return_path_id = None;
        exp_return_pos = no_pos})
  | RlFWrite rbind ->
    let bvar, (typ, f_name) = rbind.rfw_bound_var, rbind.rfw_field in
    let rhs = rbind.rfw_value in
    let rhs_var =
      let rhs_typ = CP.type_of_sv rhs in
      if is_null_type rhs_typ then I.Null no_pos
      else mkVar rhs in
    let mem_var = mkVar bvar in
    let exp_mem = I.Member {
        exp_member_base = mem_var;
        exp_member_fields = [f_name];
        exp_member_path_id = None;
        exp_member_pos = no_pos
      } in
    let bind = mkAssign exp_mem rhs_var in
    aux_subtrees st bind
  | RlFRead rc ->
    let lhs = rc.rfr_value in
    let bvar, (typ, f_name) = rc.rfr_bound_var, rc.rfr_field in
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
  | RlFuncCall rc ->
    let args = rc.rfc_params |> List.map mkVar in
    let fcall = Iast.CallNRecv {
        exp_call_nrecv_method = rc.rfc_fname |> C.unmingle_name;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_arguments = args;
        exp_call_nrecv_path_id = None;
        exp_call_nrecv_pos = no_pos} in
    let seq = match rc.rfc_return with
      | None -> fcall
      | Some rvar ->
        let r_var = I.VarDecl {
            I.exp_var_decl_type = CP.type_of_sv rvar;
            I.exp_var_decl_decls = [(CP.name_of_sv rvar, None, no_pos)];
            I.exp_var_decl_pos = no_pos;
          } in
        let asgn = mkAssign (mkVar rvar) fcall in
        mkSeq r_var asgn in
    aux_subtrees st seq

and aux_subtrees st cur_codes =
  let st_code = List.map synthesize_st_core st.stc_subtrees in
  match st_code with
  | [] -> Some cur_codes
  | [h] ->
    if h = None then Some cur_codes
    else let st_code = Gen.unsome h in
      let seq = mkSeq cur_codes st_code in Some seq
  | _ -> report_error no_pos "aux_subtrees: not consider more than one subtree"

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

let replace_exp_proc n_exp proc num =
  let replace_exp_aux nexp exp num : I.exp =
    let rec aux exp = match (exp:I.exp) with
      | I.Assign e ->
        let n_e1 = aux e.I.exp_assign_lhs in
        let n_e2 = aux e.I.exp_assign_rhs in
        I.Assign {e with exp_assign_lhs = n_e1;
                         exp_assign_rhs = n_e2}
      | I.Bind e ->
        let n_body = aux e.I.exp_bind_body in
        I.Bind {e with exp_bind_body = n_body}
      | I.Block e ->
        let n_body = aux e.I.exp_block_body in
        I.Block {e with exp_block_body = n_body}
      | I.Cast e ->
        let n_body = aux e.I.exp_cast_body in
        I.Cast {e with exp_cast_body = n_body;}
      | I.CallNRecv e ->
        let name = e.I.exp_call_nrecv_method in
        let () = x_tinfo_hp (add_str "name" pr_id) name no_pos in
        let fc = "fcode" ^ (pr_int num) in
        if name = fc then nexp
        else exp
      | I.UnkExp _ -> let () = x_tinfo_pp "marking" no_pos in
        exp
      | I.Cond e ->
        let () = x_tinfo_pp "marking" no_pos in
        let r1 = aux e.exp_cond_then_arm in
        let r2 = aux e.exp_cond_else_arm in
        I.Cond {e with exp_cond_then_arm = r1;
                       exp_cond_else_arm = r2}
      | I.Label (a, body) -> Label (a, aux body)
      | I.Seq e ->
        let n_e1 = aux e.I.exp_seq_exp1 in
        let n_e2 = aux e.I.exp_seq_exp2 in
        I.Seq {e with exp_seq_exp1 = n_e1;
                      exp_seq_exp2 = n_e2}
      | _ -> exp in
    aux exp in
  let body = proc.I.proc_body |> Gen.unsome in
  let () = x_tinfo_hp (add_str "proc body" pr_i_exp) body no_pos in
  let () = x_tinfo_hp (add_str "num" pr_int) num no_pos in
  let n_body = Some (replace_exp_aux n_exp body num) in
  let () = x_tinfo_hp (add_str "n_exp" pr_i_exp) n_exp no_pos in
  let () = x_tinfo_hp (add_str "n_body" pr_i_exp_opt) n_body no_pos in
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


let get_heap_vars (hf:CF.h_formula) : CP.spec_var list =
  let rec aux hf = match hf with
    | CF.Star bf -> (aux bf.CF.h_formula_star_h1) @ (aux bf.CF.h_formula_star_h2)
    | CF.DataNode dn ->
      let var = dn.CF.h_formula_data_node in
      [var]
    | CF.ViewNode vn ->
      let var = vn.CF.h_formula_view_node in
      [var]
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

let rec check_hp_hf hp_names hf =
  let hf = rm_emp_hf hf in
  match hf with
  | CF.HVar _ | CF.DataNode _ | CF.ViewNode _ | CF.HEmp | CF.HTrue
  | CF.HFalse -> false
  | CF.Phase phase ->
    check_hp_hf hp_names phase.CF.h_formula_phase_rd ||
    check_hp_hf hp_names phase.CF.h_formula_phase_rw
  | CF.HRel (sv, args, _) -> let sv_name = CP.name_of_sv sv in
    if List.exists (fun x -> eq_str x sv_name) hp_names
    then true else false
  | CF.Star sf -> (check_hp_hf hp_names sf.CF.h_formula_star_h1) ||
               (check_hp_hf hp_names sf.CF.h_formula_star_h2)
  | _ -> report_error no_pos ("unhandled case of check_conseq_hp" ^ (pr_hf hf))

let rec rm_hp_hf hf =
  let hf = rm_emp_hf hf in
  match hf with
  | CF.HVar _ | CF.DataNode _ | CF.ViewNode _ | CF.HEmp | CF.HTrue
  | CF.HFalse -> hf
  | CF.HRel (sv, args, _) -> CF.HEmp
  | CF.Star sf ->
    let n_sf1 = rm_hp_hf sf.CF.h_formula_star_h1 in
    let n_sf2 = rm_hp_hf sf.CF.h_formula_star_h2 in
    CF.Star {sf with CF.h_formula_star_h1 = n_sf1;
                     CF.h_formula_star_h2 = n_sf2}
  | _ -> report_error no_pos ("unhandled case of rm_conseq_hp" ^ (pr_hf hf))

let rec get_hp_hf hp_names hf =
  let hf = rm_emp_hf hf in
  match hf with
  | CF.HVar _ | CF.DataNode _ | CF.ViewNode _ | CF.HEmp | CF.HTrue
  | CF.HFalse -> []
  | CF.HRel (sv, args, _) ->
    let sv_name = CP.name_of_sv sv in
    if List.exists (fun x -> eq_str x sv_name) hp_names
    then [sv_name] else []
  | CF.Star sf -> (get_hp_hf hp_names sf.CF.h_formula_star_h1) @
               (get_hp_hf hp_names sf.CF.h_formula_star_h2)
  | _ -> report_error no_pos ("unhandled case of get_conseq_hp" ^ (pr_hf hf))

let rec get_all_hp_hf hf =
  match hf with
  | CF.HVar _ | CF.DataNode _ | CF.ViewNode _ | CF.HEmp | CF.HTrue
  | CF.HFalse -> []
  | CF.HRel (sv, args, _) -> [CP.name_of_sv sv]
  | CF.Star sf  -> (get_all_hp_hf sf.CF.h_formula_star_h1) @
               (get_all_hp_hf sf.CF.h_formula_star_h2)
  | _ -> report_error no_pos "unhandled case of get_conseq_hp"

let check_hp_hf hp_names hf =
  Debug.no_1 "check_hp_hf" pr_hf string_of_bool
    (fun _ -> check_hp_hf hp_names hf) hf

let rec check_hp_formula hp_names formula = match (formula:CF.formula) with
  | CF.Base bf -> check_hp_hf hp_names bf.CF.formula_base_heap
  | CF.Exists ef -> check_hp_hf hp_names ef.CF.formula_exists_heap
  | CF.Or f -> (check_hp_formula hp_names f.CF.formula_or_f1) ||
               (check_hp_formula hp_names f.CF.formula_or_f2)

let rec rm_hp_formula formula = match (formula:CF.formula) with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let n_hf = rm_hp_hf hf |> rm_emp_hf in
    CF.Base {bf with CF.formula_base_heap = n_hf}
  | CF.Exists ef ->
    let hf = ef.CF.formula_exists_heap in
    let n_hf = rm_hp_hf hf |> rm_emp_hf in
    CF.Exists {ef with CF.formula_exists_heap = n_hf}
  | CF.Or f ->
    let n_f1 = rm_hp_formula f.CF.formula_or_f1 in
    let n_f2 = rm_hp_formula f.CF.formula_or_f2 in
    CF.Or {f with CF.formula_or_f1 = n_f1;
                  CF.formula_or_f2 = n_f2}

let rec get_hp_formula hp_names formula = match (formula:CF.formula) with
  | CF.Base bf -> get_hp_hf hp_names bf.CF.formula_base_heap
  | CF.Exists ef -> get_hp_hf hp_names ef.CF.formula_exists_heap
  | CF.Or f -> (get_hp_formula hp_names f.CF.formula_or_f1) @
               (get_hp_formula hp_names f.CF.formula_or_f2)

let rec get_all_hp formula = match (formula:CF.formula) with
  | CF.Base bf -> get_all_hp_hf bf.CF.formula_base_heap
  | CF.Exists ef -> get_all_hp_hf ef.CF.formula_exists_heap
  | CF.Or f -> (get_all_hp f.CF.formula_or_f1) @
               (get_all_hp f.CF.formula_or_f2)

let check_hp_formula hp_names formula =
  Debug.no_1 "check_hp_formula" pr_f string_of_bool
    (fun _ -> check_hp_formula hp_names formula) formula


let isHFalse (formula : CF.formula) : bool =
  let is_hfalse hf = match hf with
    | CF.HFalse -> true
    (* | CF.HEmp -> true *)
    | _ -> false in
  let rec aux formula = match formula with
    | CF.Base base ->
      let hf = base.CF.formula_base_heap in
      is_hfalse hf
    | CF.Exists base ->
      let hf = base.CF.formula_exists_heap in
      is_hfalse hf
    | CF.Or base -> aux base.CF.formula_or_f1 || aux base.CF.formula_or_f2 in
  aux formula

let isHEmp (formula : CF.formula) : bool =
  let is_hfalse hf = match hf with
    | CF.HEmp -> true
    | _ -> false in
  let rec aux formula = match formula with
    | CF.Base base ->
      let hf = base.CF.formula_base_heap in
      is_hfalse hf
    | CF.Exists base ->
      let hf = base.CF.formula_exists_heap in
      is_hfalse hf
    | CF.Or base -> aux base.CF.formula_or_f1 || aux base.CF.formula_or_f2 in
  aux formula

let isHFalseOrEmp pre (post : CF.formula) =
  if isHFalse post then true
  else
  if isHEmp post then
    if isHEmp pre then false
    else true
  else false
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
  let rec aux trace = match trace with
    | [] -> false
    | head::tail ->
      begin
        match head with
        | RlFuncCall rcore ->
          let params = rcore.rfc_params in
          if (List.length args = List.length params) then
            if List.for_all2 (fun x y -> CP.eq_spec_var x y) args params
            then true
            else aux tail
          else aux tail
        | _ -> aux tail
      end in
  aux trace

let is_fcall_called trace args : bool =
  Debug.no_2 "is_fcall_called" pr_rules pr_vars string_of_bool
    (fun _ _ -> is_fcall_called trace args) trace args

let is_fcall_ever_called trace fun_name : bool =
  let rec aux trace num =
    match trace with
    | [] -> false
    | head::tail ->
      begin
        match head with
        | RlFuncCall rc->
          let n_num = if eq_str rc.rfc_fname fun_name then num -1
            else num in
          if n_num = 0 then true
          else aux tail n_num
        | _ -> aux tail num
      end in
  aux trace 2

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

let rule_use_var var rule = match rule with
  | RlFree rc ->
    let params = rc.rd_vars in
    CP.mem var params
  | RlFuncCall rc ->
    let params = rc.rfc_params in
    CP.mem var params
  | RlFWrite rc ->
    let var1 = rc.rfw_bound_var in
    let var2 = rc.rfw_value in
    CP.eq_sv var1 var || CP.eq_sv var2 var
  | RlAllocate rc ->
    let r_var = rc.ra_var in
    let r_params = rc.ra_params in
    CP.eq_sv var r_var || CP.mem var r_params
  | RlAssign rc ->
    let var1 = rc.ra_lhs in
    let vars2 = CP.afv rc.ra_rhs in
    CP.eq_sv var var1 || CP.mem var vars2
  | RlReturn rc ->
    let vars = rc.r_exp |> CP.afv in
    CP.mem var vars
  | RlFrameData rc ->
    CP.eq_sv rc.rfd_rhs var
  | RlUnfoldPre rc ->
    CP.eq_sv rc.unfold_pre_var var
  | _ -> false

let rule_use_var var rule =
  Debug.no_2 "rule_use_var" pr_var pr_rule string_of_bool
    (fun _ _ -> rule_use_var var rule) var rule

let eliminate_useless_rules goal rules =
  (* let contain_sym_rules rule = match rule with
   *   | RlFRead _ -> true
   *     | _ -> false in *)
  (* let is_rule_unfold_post_usable rules =
   *   not (List.exists contain_sym_rules rules) in *)
  let n_rules = rules in
  (* DELETE FUNCTION-CALL RULE WHEN IT'S NOT FUNCTION STATEMENT *)


  (* let get_func_calls rules =
   *   let rec aux rules set = match rules with
   *     | [] -> set
   *     | h::tail ->
   *       begin
   *         match h with
   *         | RlFuncCall rc -> aux tail (rc::set)
   *         | _ -> aux tail set
   *       end in
   *   aux rules [] in
   * let call_rules = get_func_calls n_rules in
   * let get_useless_calls rules =
   *   let rec aux rules set = match rules with
   *     | [] -> set
   *     | [h] -> set
   *     | h::tail ->
   *       let params = h.rfc_params in
   *       let other_params = List.map (fun x -> x.rfc_params) tail |> List.concat in
   *       if List.for_all (fun x -> not(CP.mem x other_params)) params then
   *         aux tail (h::set)
   *       else aux tail set in
   *   let fc_rules = aux rules [] in
   *   fc_rules |> List.map (fun x -> RlFuncCall x) in
   * let () = x_tinfo_hp (add_str "funcall rules" (pr_list pr_func_call)) call_rules no_pos in
   * let useless_calls = get_useless_calls call_rules in
   * let () = x_tinfo_hp (add_str "useless func" pr_rules) useless_calls no_pos in
   * let n_rules = List.filter (fun x -> not(List.mem x useless_calls)) n_rules in *)
  n_rules

let eliminate_useless_rules goal rules =
  Debug.no_2 "eliminate_useless_rules" pr_goal pr_rules pr_rules
    (fun _ _ -> eliminate_useless_rules goal rules) goal rules

let compare_rule_assign_vs_assign goal r1 r2 =
  if CP.is_res_spec_var r1.ra_lhs then PriHigh
  else if CP.is_res_spec_var r2.ra_lhs then PriLow
  else PriEqual

let compare_rule_unfold_post_vs_mk_null r1 r2 =
  PriLow

let compare_rule_assign_vs_other goal r1 r2 = match r2 with
  | RlAssign r2 -> compare_rule_assign_vs_assign goal r1 r2
  | RlReturn _ -> PriLow
  | _ ->
    if CP.is_res_spec_var r1.ra_lhs then PriHigh
    else PriEqual

let compare_two_frame_pred goal r1 r2 =
  let vars = goal.gl_vars in
  let var1 = r1.rfp_rhs in
  let var2 = r2.rfp_rhs in
  if CP.mem var1 vars then PriHigh
  else if CP.mem var2 vars then PriLow
  else PriEqual

let compare_rule_frame_data_vs_other r1 r2 =
  match r2 with
  | RlFramePred _
  | RlFrameData _ -> if CP.is_res_sv r1.rfd_lhs then PriHigh
    else PriLow
  | RlSkip
  | RlAllocate _ -> PriLow
  | RlMkNull _ -> PriLow
  | RlReturn _ -> PriLow
  | RlFree _ -> PriLow
  | RlFRead _ -> PriLow
  (* | RlMkNull _ -> PriLow *)
  | _ -> PriHigh

let compare_rule_fun_call_vs_other r1 r2 = match r2 with
  | RlReturn _ -> PriLow
  | RlMkNull _ -> PriLow
  | RlUnfoldPre _ -> PriHigh
  | _ -> PriHigh

let compare_rule_unfold_post_vs_unfold_post r1 r2 =
  if CP.is_res_sv r1.rp_var then PriHigh
  else if CP.is_res_sv r2.rp_var then PriLow
  else PriEqual

let compare_rule_unfold_post_vs_other r1 r2 = match r2 with
  | RlUnfoldPost r2 -> compare_rule_unfold_post_vs_unfold_post r1 r2
  | RlMkNull r2 -> compare_rule_unfold_post_vs_mk_null r1 r2
  | RlReturn _ -> PriLow
  | RlAllocate r2 -> if r2.ra_end then PriLow else PriHigh
  | _ -> PriLow

let compare_rule_fread_vs_fread r1 r2 =
  let contain_allocate rule = match rule with
    | RlAllocate rc -> rc.ra_end
    | _ -> false in
  match r1.rfr_lookahead, r2.rfr_lookahead with
  | Some g1, Some g2 ->
    let rules1 = g1.gl_lookahead in
    let rules2 = g2.gl_lookahead in
    if List.exists contain_allocate rules1 then PriHigh
    else if List.exists contain_allocate rules2 then PriLow
    else PriEqual
  | _ -> PriEqual

let compare_rule_fread_vs_fread r1 r2 =
  Debug.no_2 "compare_rule_fread_vs_fread" pr_fread pr_fread pr_priority
    (fun _ _ -> compare_rule_fread_vs_fread r1 r2) r1 r2

let compare_rule_unfold_pre_vs_other r1 r2 = match r2 with
  | RlReturn _ -> PriLow
  | RlMkNull _ -> PriLow
  | RlNewNum _ -> PriLow
  | RlFuncCall _ -> PriLow
  | RlAllocate r2 -> if r2.ra_end then PriLow else PriHigh
  | RlUnfoldPre r2 -> PriEqual
  | _ -> PriHigh

let compare_rule_allocate_vs_other r1 r2 = match r2 with
  | RlAllocate r2 ->
    if r2.ra_end then PriLow else PriEqual
  | _ -> PriLow

let compare_rule_return_vs_other r r2 = match r2 with
  | RlReturn _ -> PriEqual
  | _ -> PriHigh

let compare_rule_post_assign_vs_other r1 r2 = match r2 with
  | RlSkip | RlReturn _ -> PriLow
  | RlFramePred _ | RlFrameData _
  | _ -> PriHigh

let compare_rule_fread_vs_frame_pred r1 r2 =
  (* let frame_var = r2.rfp_rhs in *)
  (* let fread_var = r1.rfr_value in *)

  (* if CP.eq_sv frame_var fread_var then PriLow
   * else PriHigh *)
  PriHigh

let compare_rule_fread_vs_other r1 r2 = match r2 with
  | RlSkip | RlReturn _ -> PriLow
  | RlFRead r2 -> compare_rule_fread_vs_fread r1 r2
  | RlFramePred r2 -> compare_rule_fread_vs_frame_pred r1 r2
  | _ -> PriHigh

let compare_rule_frame_pred_vs_other goal r1 r2 =
  match r2 with
  | RlFramePred r2 -> compare_two_frame_pred goal r1 r2
  | RlFrameData r2 -> if CP.is_res_sv r2.rfd_lhs then PriLow
    else PriHigh
  | RlAllocate _ -> PriLow
  | RlFRead r2 -> compare_rule_fread_vs_frame_pred r2 r1 |> negate_priority
  | RlFree _ -> PriLow
  | RlReturn _ -> PriLow
  | RlNewNum _ -> PriLow
  (* | RlMkNull _ -> PriLow *)
  (* | RlUnfoldPost _
   * | RlFuncCall _ -> PriLow *)
  | _ -> PriHigh


let compare_rule_mk_null_vs_other r1 r2 = match r2 with
  | RlMkNull r2 ->
    if CP.is_int_type (CP.get_exp_type r1.rmn_null) then PriHigh
    else if CP.is_int_type (CP.get_exp_type r2.rmn_null) then PriLow
    else PriEqual
  | _ -> PriHigh

let compare_rule goal r1 r2 =
  match r1 with
  | RlSkip -> PriHigh
  | RlReturn r -> compare_rule_return_vs_other r r2
  | RlUnfoldPre r1 -> compare_rule_unfold_pre_vs_other r1 r2
  | RlUnfoldPost r1 -> compare_rule_unfold_post_vs_other r1 r2
  | RlFrameData r -> compare_rule_frame_data_vs_other r r2
  | RlFramePred r1 -> compare_rule_frame_pred_vs_other goal r1 r2
  | RlAllocate r1 ->
    if r1.ra_end then PriHigh
    else compare_rule_allocate_vs_other r1 r2
  | RlMkNull r1 -> compare_rule_mk_null_vs_other r1 r2
  | RlFree _ -> PriHigh
  | RlAssign r1 -> compare_rule_assign_vs_other goal r1 r2
  | RlHeapAssign _ -> PriEqual
  | RlFRead r1 -> compare_rule_fread_vs_other r1 r2
  | RlFWrite _ -> PriHigh
  | RlFuncCall r1 -> compare_rule_fun_call_vs_other r1 r2
  | RlNewNum _ -> PriHigh

let is_code_rule trace = match trace with
  | [] -> false
  | h::_ ->
    match h with
    | RlAssign _ | RlReturn _ | RlFWrite _ | RlHeapAssign _ | RlFree _
    (* | RlFuncRes _ *)
    | RlFuncCall _ -> true
    | _ -> false

let is_code_rule trace =
  Debug.no_1 "is_code_rule" pr_trace string_of_bool
    (fun _ -> is_code_rule trace) trace

let is_end_rule rule =
  match rule with
  | RlSkip | RlReturn _ -> true
  | RlAllocate rc -> rc.ra_end
  | RlAssign rc -> rc.ra_numeric
  | RlFWrite rc -> true
  | _ -> false

let is_generate_code_rule rule = match rule with
    | RlAssign _ | RlReturn _ | RlFWrite _ (* | RlFuncRes _ *)
    | RlFuncCall _ -> true
    | _ -> false

let get_rule_vars rule = match rule with
  | RlAssign rc ->
    let lhs = rc.ra_lhs in
    let rhs = CP.afv rc.ra_rhs in
    lhs::rhs
  | RlFWrite rc ->
    let bv = rc.rfw_bound_var in
    let value = rc.rfw_value in
    [bv; value]
  | RlAllocate rc -> rc.ra_params
  | RlReturn rc ->
    let rhs = CP.afv rc.r_exp in
    rhs
  | RlFuncCall rc -> rc.rfc_params
  | _ -> []

let stop_mk_null trace : bool =
  let trace = trace |> List.rev in
  let aux_check null_var list =
    if List.length list == 2 then
      let tail_vars = List.map get_rule_vars list
                      |> List.concat in
      if List.exists (CP.eq_sv null_var) tail_vars
      then false
      else true
    else false in
  match trace with
  | [] -> false
  | head::tail ->
    begin
      match head with
      | RlMkNull rl ->
        aux_check rl.rmn_var tail
      | _ -> false
    end

let num_of_code_rules trace =
  let trace = List.filter is_generate_code_rule trace in
  List.length trace

let check_trace_consistence trace =
  let rec aux trace vars = match trace with
    | [] -> true
    | h::tail ->
      if is_generate_code_rule h then
        let rule_vars = get_rule_vars h in
        if vars = [] then aux tail rule_vars
        else if CP.intersect vars rule_vars = [] then false
        else
          let n_vars = rule_vars@vars |> CP.remove_dups_svl in
          aux tail n_vars
      else aux tail vars in
  let trace = List.rev trace in
  aux trace []

let get_trace_vars (trace: rule list) =
  let aux rule = match rule with
    | RlFuncCall rc ->
      (match rc.rfc_return with
       | None -> []
       | Some var -> [var])
    (* | RlFWrite rc -> [rc.rfw_value]
     * | RlFRead rc -> [rc.rfr_value] *)
    | _ -> [] in
  trace |> List.map aux |> List.concat

let check_trace_consistence trace =
  Debug.no_1 "check_trace_consistence" pr_rules string_of_bool
    (fun _ -> check_trace_consistence trace) trace

let length_of_trace trace =
  let is_simplify_rule rule = match rule with
    | RlFRead _
    | RlUnfoldPre _ | RlUnfoldPost _
    | RlFrameData _ | RlFramePred _ -> true
    | _ -> false in
  let trace = trace |> List.filter (fun x -> is_simplify_rule x |> negate) in
  List.length trace

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

let mk_goal cprog pre post vars =
  (* let primed_vars = vars |> List.map CP.to_primed in
   * let vars = vars @ primed_vars |> CP.remove_dups_svl in *)
  let () = allocate_list := [] in
  { gl_prog = cprog;
    gl_start_time = get_time ();
    gl_lookahead = [];
    gl_proc_decls = [];
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_trace = [];
    gl_vars = vars;  }

let mk_goal_w_procs cprog proc_decls pre post vars =
  (* let primed_vars = vars |> List.map CP.to_primed in
   * let vars = vars @ primed_vars |> CP.remove_dups_svl in *)
  let () = fail_branch_num := 0 in
  let pre = unprime_formula pre in
  let post = unprime_formula post in
  let () = allocate_list := [] in
  { gl_prog = cprog;
    gl_lookahead = [];
    gl_proc_decls = proc_decls;
    gl_start_time = get_time ();
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

let rm_redundant_constraint (goal: goal) : goal =
  let pf_pre = CF.get_pure goal.gl_pre_cond in
  let n_pf_pre = CP.elim_idents pf_pre in
  let n_pre = CF.repl_pure_formula n_pf_pre goal.gl_pre_cond in
  let pf_post = CF.get_pure goal.gl_post_cond in
  let n_pf_post = CP.elim_idents pf_post in
  let n_post = CF.repl_pure_formula n_pf_post goal.gl_post_cond in
  {goal with gl_pre_cond = n_pre;
             gl_post_cond = n_post}

(* let process_rule_exists_right goal rule =
 *   let n_goal = {goal with gl_post_cond = rule.n_post;
 *                           gl_trace = (RlExistsRight rule)::goal.gl_trace} in
 *   mk_derivation_subgoals goal (RlExistsRight rule) [n_goal] *)

let free_var_hf (hf:CF.h_formula) vars =
  let rec aux (hf : CF.h_formula) = match hf with
    | CF.DataNode dn ->
      let dn_var = dn.CF.h_formula_data_node in
      if CP.mem dn_var vars then
        (CF.HEmp, true, false)
      else (hf, false, false)
    | CF.ViewNode vn ->
      let vn_var = vn.CF.h_formula_view_node in
      if CP.mem vn_var vars then
        (hf, false, true)
      else (hf, false, false)
    | CF.Star bf ->
      let (hf1, t1, u1) = aux bf.CF.h_formula_star_h1 in
      let (hf2, t2, u2) = aux bf.CF.h_formula_star_h2 in
      let n_hf = CF.Star {bf with CF.h_formula_star_h1 = hf1;
                                  CF.h_formula_star_h2 = hf2} in
      (n_hf, t1 || t2, u1 || u2)
    | _ -> (hf, false, false) in
  aux hf

let free_var_formula prog formula var =
  let rec get_eq_vars vars pf =
    let eq_pairs = get_equality_pairs pf in
    let eq_pairs = eq_pairs |> List.filter (fun (x,y) -> CP.mem x vars ||
                                                         CP.mem y vars) in
    let eq_vars = (List.map fst eq_pairs) @ (List.map snd eq_pairs) in
    let n_vars = CP.remove_dups_svl eq_vars in
    if CP.diff_svl n_vars vars = [] then n_vars
    else get_eq_vars n_vars pf in
  let rec aux formula = match formula with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let pf = bf.CF.formula_base_pure |> MCP.pure_of_mix in
      let eq_vars = get_eq_vars [var] pf in
      let (n_hf, is_f, unfold) = free_var_hf hf eq_vars in
      if is_f then
        let n_f = CF.Base {bf with CF.formula_base_heap = n_hf} in
        (n_f, is_f, unfold)
      else if unfold then
        let vnodes = get_unfold_view [var] formula in
        if List.length vnodes = 1 then
          let vnode = List.hd vnodes in
          let pr_views, args = need_unfold_rhs prog vnode in
          let nf = do_unfold_view_vnode prog pr_views args formula in
          let fv_list = List.map aux nf in
          if List.for_all (fun (_,x,_) -> x) fv_list && List.length fv_list = 2
          then
            let f_list = List.map (fun (x,_,_) -> x) fv_list in
            let fst_f = f_list |> List.hd in
            let snd_f = f_list |> List.rev |> List.hd in
            let n_f = CF.Or {CF.formula_or_f1 = fst_f;
                             CF.formula_or_f2 = snd_f;
                             CF.formula_or_pos = no_pos} in
            (n_f, true, false)
          else (formula, is_f, unfold)
        else (formula, is_f, unfold)
      else (formula, is_f, unfold)
    | CF.Exists bf ->
      let hf = bf.CF.formula_exists_heap in
      let pf = bf.CF.formula_exists_pure |> MCP.pure_of_mix in
      let eq_vars = get_eq_vars [var] pf in
      let (n_hf, is_f, unfold) = free_var_hf hf eq_vars in
      if is_f then
        let n_f = CF.Exists {bf with CF.formula_exists_heap = n_hf} in
        (n_f, is_f, unfold)
      else if unfold then
        let vnodes = get_unfold_view [var] formula in
        if List.length vnodes = 1 then
          let vnode = List.hd vnodes in
          let pr_views, args = need_unfold_rhs prog vnode in
          let nf = do_unfold_view_vnode prog pr_views args formula in
          let fv_list = List.map aux nf in
          if List.for_all (fun (_,x,_) -> x) fv_list && List.length fv_list = 2
          then
            let f_list = List.map (fun (x,_,_) -> x) fv_list in
            let fst_f = f_list |> List.hd in
            let snd_f = f_list |> List.rev |> List.hd in
            let n_f = CF.Or {CF.formula_or_f1 = fst_f;
                             CF.formula_or_f2 = snd_f;
                             CF.formula_or_pos = no_pos} in
            (n_f, true, false)
          else (formula, is_f, unfold)
        else (formula, is_f, unfold)
      else (formula, is_f, unfold)
    | CF.Or bf ->
      let (f1, fr1, unfold1) = aux bf.CF.formula_or_f1 in
      let (f2, fr2, unfold2) = aux bf.CF.formula_or_f2 in
      let n_f = CF.Or {bf with CF.formula_or_f1 = f1;
                               CF.formula_or_f2 = f2} in
      (n_f, fr1 || fr2, unfold1 || unfold2) in
  let (n_f, fr, unfold) = aux formula in
  if fr then (n_f, true)
  else (n_f, false)

let free_entail_state prog (ent_state:CF.entail_state) (typ, name) =
  let es_f = ent_state.CF.es_formula in
  let var = CP.mk_typed_sv typ name |> CP.to_primed in
  let (n_f, fr) = free_var_formula prog es_f var in
  let n_f = rm_emp_formula n_f in
  if fr then
    let n_es = {ent_state with CF.es_formula = n_f} in
    (n_es, fr)
  else (ent_state, false)

let free_ctx prog (ctx: CF.list_failesc_context) (typ, name) =
  let () = x_tinfo_hp (add_str "ctx" pr_failesc_list) ctx no_pos in
  let () = x_tinfo_hp (add_str "var" pr_id) name no_pos in
  let rec aux_contex (ctx: CF.context) = match ctx with
    | CF.Ctx ent_state ->
      let n_ent, fr = free_entail_state prog ent_state (typ, name) in
      (CF.Ctx n_ent, fr)
    | CF.OCtx (ctx1, ctx2) ->
      let (n_ctx1, fr1) = aux_contex ctx1 in
      let (n_ctx2, fr2) = aux_contex ctx2 in
      let n_ctx = CF.OCtx (n_ctx1, n_ctx2) in
      (n_ctx, fr1 && fr2) in
  let aux_branch_ctx (b_ctx: CF.branch_ctx) =
    let (path, ctx, fail_typ) = b_ctx in
    let (n_ctx, res) = aux_contex ctx in
    ((path, n_ctx, fail_typ), res) in
  let aux_failesc_ctx (failesc_ctx: CF.failesc_context) =
    let b_fail, stack, b_ctx_list = failesc_ctx in
    let ctx_list_res = List.map aux_branch_ctx b_ctx_list in
    let res =
      let res_list = List.map snd ctx_list_res in
      List.for_all (fun x -> x) res_list in
    if res then
      let n_ctx_list = List.map fst ctx_list_res in
      let n_failesc_ctx = (b_fail, stack, n_ctx_list) in
      (n_failesc_ctx, true)
    else (failesc_ctx, false) in
  let res_list = List.map aux_failesc_ctx ctx in
  let res =
    let res_list = List.map snd res_list in
    List.for_all (fun x -> x) res_list in
  if res then
    let n_failesc_list = List.map fst res_list in
    let () = x_tinfo_hp (add_str "ctx" pr_failesc_list) n_failesc_list no_pos in
    (n_failesc_list, true)
  else
    (ctx, false)

let get_hf_type prog hf =
  let rec aux hf = match hf with
    | CF.DataNode dn ->
      let d_name = dn.CF.h_formula_data_name in
      let data = List.find (fun x -> eq_str d_name x.C.data_name) prog.C.prog_data_decls in
      let d_args = data.C.data_fields |> List.map (fun (x,_) -> x) in
      let c_args = dn.CF.h_formula_data_arguments in
      List.map2 (fun x y ->
          let CP.SpecVar (t, name, primed) = x in
          let (n_t, _) = y in
          CP.SpecVar (n_t, name, primed)) c_args d_args
    | CF.ViewNode vn ->
      let v_name = vn.CF.h_formula_view_name in
      let view = List.find (fun x -> eq_str v_name x.C.view_name) prog.C.prog_view_decls in
      let v_args = view.C.view_vars in
      let c_args = vn.CF.h_formula_view_arguments in
      List.map2 (fun x y ->
          let CP.SpecVar (t, name, primed) = x in
          let CP.SpecVar (n_t, _, _) = y in
          CP.SpecVar (n_t, name, primed)) c_args v_args
    | CF.Star hf ->
      let hf1 = hf.CF.h_formula_star_h1 in
      let hf2 = hf.CF.h_formula_star_h2 in
      (aux hf1) @ (aux hf2)
    | _ -> [] in
  aux hf

let rm_unk_type_formula prog formula =
  let rec collect_type formula = match formula with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      get_hf_type prog hf
    | CF.Exists bf ->
      let hf = bf.CF.formula_exists_heap in
      get_hf_type prog hf
    | CF.Or bf ->
      (collect_type bf.CF.formula_or_f1) @ (collect_type bf.CF.formula_or_f2) in
  let e_vars = CF.get_exists formula  in
  let e_vars, others = e_vars |> List.partition is_unk_type_var in
  if e_vars = [] then formula
  else
    let all_vars = collect_type formula in
    let create_subst all_vars var =
      begin
        try
          let n_var = List.find (fun x ->
              eq_str (CP.name_of_sv x) (CP.name_of_sv var)) all_vars in
          (var, n_var)
        with _ -> (var, var)
      end in
    let subst = e_vars |> List.map (create_subst all_vars) in
    let n_formula = remove_exists formula in
    let n_formula = CF.subst subst n_formula in
    let n_exists = e_vars |> List.map (CP.subs_one subst) in
    let n_exists = n_exists @ others in
    add_exists_vars n_formula n_exists

let rm_unk_type_formula prog formula =
  Debug.no_1 "rm_unk_type_formula" pr_f pr_f
    (fun _ -> rm_unk_type_formula prog formula) formula
