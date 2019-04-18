#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

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
let fc_args = ref ([]: CP.spec_var list list)
let repair_pos = ref (None : VarGen.loc option)
let repair_res = ref (None : Iast.prog_decl option)
let unk_hps = ref ([] : Cast.hp_decl list)
let repair_proc = ref (None : Cast.proc_decl option)
let entailments = ref ([] : (CF.formula * CF.formula) list)
let syn_pre = ref (None : CF.formula option)

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
  | RlFramePred of rule_frame_pred
  | RlFoldLeft of rule_fold_left
  | RlUnfoldPre of rule_unfold_pre
  | RlUnfoldPost of rule_unfold_post
  | RlSkip
  | RlAssign of rule_assign
  | RlReturn of rule_return
  | RlBranch of rule_branch
  | RlFRead of rule_field_read
  | RlFWrite of rule_field_write
  | RlFuncCall of rule_func_call
  | RlFuncRes of rule_func_res

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
  rli_lhs: CP.spec_var;
  rli_rhs: CP.spec_var;
}

and rule_unfold_pre = {
  n_pre: CF.formula;
}

and rule_unfold_post = {
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

let pr_cast_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_iast_exp = Iprinter.string_of_exp_repair
let pr_iast_exp_opt = Iprinter.string_of_exp_repair
let pr_cast_exp exp = match exp with
  | None -> "None"
  | Some e -> Cprinter.string_of_exp e

let pr_iast_exp_opt exp = match exp with
  | None -> "None"
  | Some e -> Iprinter.string_of_exp_repair e

let pr_goal goal =
  let vars = goal.gl_vars in
  (* let pr_svs = Cprinter.string_of_spec_var_list in *)
  let pr_svs = pr_list Cprinter.string_of_typed_spec_var in
  "synthesize " ^ (pr_svs vars) ^ "\n" ^
  (pr_formula goal.gl_pre_cond) ^ "\n" ^
  "~>\n" ^ (pr_formula goal.gl_post_cond) ^ "."

let pr_rule_assign rule =
  let lhs, rhs = rule.ra_lhs, rule.ra_rhs in
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
  "(" ^ (pr_var rule.rli_lhs) ^ ", " ^ (pr_var rule.rli_rhs) ^ ")"

let pr_var_init rule =
  "(" ^ (pr_var rule.rvi_var) ^ ", " ^ (pr_exp rule.rvi_rhs) ^ ")"

let pr_rule rule = match rule with
  | RlSkip -> "RlSkip"
  | RlFoldLeft r -> "RlFoldLeft " ^ (pr_formula r.rfl_pre)
  | RlFuncCall fc -> "RlFuncCall\n" ^ (pr_func_call fc)
  | RlFuncRes fc -> "RlFuncRes\n" ^ (pr_func_res fc)
  | RlAssign rule -> "RlAssign\n" ^ "(" ^ (pr_rule_assign rule) ^ ")"
  | RlReturn rule -> "RlReturn\n" ^ "(" ^ (pr_exp rule.r_exp) ^ ")"
  | RlFWrite rule -> "RlFWrite\n" ^ (pr_rule_bind rule)
  | RlFRead rule -> "RlFRead" ^ (pr_fread rule)
  | RlUnfoldPre rule -> "RlUnfoldPre " ^ (rule.n_pre |> pr_formula)
  | RlUnfoldPost rule -> "RlUnfoldPost\n" ^ (rule.rp_case_formula |> pr_formula)
  | RlFramePred rule -> "RlFramePred" ^ (pr_instantiate rule)
  | RlExistsLeft rule -> "RlExistsLeft" ^ (pr_vars rule.exists_vars)
  | RlExistsRight rule -> "RlExistsRight" ^ (pr_formula rule.n_post)
  | RlBranch rule -> "RlBranch (" ^ (pr_formula rule.rb_if_pre) ^ ", " ^
                     (pr_formula rule.rb_else_pre)  ^ ")"

let rec pr_st st = match st with
  | StSearch st_search -> "StSearch [" ^ (pr_st_search st_search) ^ "]"
  | StDerive st_derive -> "StDerive [" ^ (pr_st_derive st_derive) ^ "]"

and pr_st_search st =
  let goal, sub_trees = st.sts_goal, st.sts_sub_trees in
  let st_str = (pr_list pr_st) sub_trees in
  (* "Goal: " ^ (pr_goal goal) ^ "\n" ^ *)
  "Subtrees: " ^  st_str

and pr_st_derive st =
  (* (pr_goal st.std_goal) ^ "\n" ^ *)
  (pr_rule st.std_rule) ^ "\n" ^
  ((pr_list pr_st) st.std_sub_trees)

and pr_st_status st_status = match st_status with
  | StUnkn str -> "StUnkn " ^ str
  | StValid st_core -> pr_st_core st_core

and pr_st_core st =
  let sub_trees = st.stc_subtrees in
  (pr_rule st.stc_rule) ^
  ((pr_list pr_st_core) sub_trees)

let pr_rules = pr_list pr_rule

(* Basic functions  *)
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
      Some (hf, [var] @ args, dnode.CF.h_formula_data_name)
    else None
  | ViewNode vnode ->
    let vn_var = vnode.CF.h_formula_view_node in
    if vn_var = var then
      let args = vnode.CF.h_formula_view_arguments in
      Some (hf, [var] @ args, vnode.CF.h_formula_view_name)
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
        report_error no_pos "extract_hf_var: one var cannot appear in two heap fragments"
    end
  | _ -> None

let extract_hf_var hf var =
  Debug.no_2 "extract_hf_var" pr_hf pr_var (fun x -> match x with
      | None -> "None"
      | Some (_, vars, _) -> pr_vars vars)
    (fun x y -> extract_hf_var_x x y) hf var

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
          let pf_var = extract_var_pf pf [var] |> CP.arith_simplify 1 in
          Some (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var))
        | Some (hf, vars, _) ->
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
        | Some (hf, vars, _) ->
          let h_vars = CF.h_fv hf in
          let vars = vars @ h_vars |> CP.remove_dups_svl in
          let pf_var = extract_var_pf pf vars in
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


(*****************************************************
  * Atomic functions
 ********************************************************)
let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let rec add_h_formula_to_formula_x added_hf (formula:CF.formula) : CF.formula =
  match formula with
  | Base bf -> let hf = bf.formula_base_heap in
    let n_hf = CF.mkStarH hf added_hf no_pos in
    CF.Base {bf with formula_base_heap = n_hf}
  | Exists bf -> let hf = bf.formula_exists_heap in
    let n_hf = CF.mkStarH hf added_hf no_pos in
    Exists {bf with formula_exists_heap = n_hf}
  | Or bf -> let n_f1 = add_h_formula_to_formula_x added_hf bf.formula_or_f1 in
    let n_f2 = add_h_formula_to_formula_x added_hf bf.formula_or_f2 in
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
        let unfold_hf = do_unfold_view_hf_vn cprog pr_views args fb.CF.formula_base_heap in
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

let rec c2iast_exp (exp:Cast.exp) : Iast.exp = match exp with
  | IConst iconst -> Iast.IntLit{ exp_int_lit_val = iconst.exp_iconst_val;
                                  exp_int_lit_pos = iconst.exp_iconst_pos}
  | Var var -> Var { exp_var_name = var.exp_var_name;
                     exp_var_pos = var.exp_var_pos}
  | Bind bv -> c2iast_bind bv bv.exp_bind_read_only

  | Seq seq -> I.Seq { exp_seq_exp1 = c2iast_exp seq.exp_seq_exp1;
                       exp_seq_exp2 = c2iast_exp seq.exp_seq_exp2;
                       exp_seq_pos = seq.exp_seq_pos}
  | VarDecl vd -> let id = vd.exp_var_decl_name in
    I.VarDecl { exp_var_decl_type = vd.exp_var_decl_type;
                exp_var_decl_decls = [(id, None, no_pos)];
                exp_var_decl_pos = vd.exp_var_decl_pos}
  | SCall sc ->
    let args = sc.exp_scall_arguments in
    let arg_vars = args |> List.map (fun x -> I.Var {
        exp_var_name = x;
        exp_var_pos = no_pos;}) in
    I.CallNRecv {
      exp_call_nrecv_method = sc.exp_scall_method_name |> Cast.unmingle_name;
      exp_call_nrecv_lock = None;
      exp_call_nrecv_ho_arg = None;
      exp_call_nrecv_arguments = arg_vars;
      exp_call_nrecv_path_id = None;
      exp_call_nrecv_pos = sc.exp_scall_pos}
  | Assign var ->
    let lhs = Iast.Var  { exp_var_name = var.exp_assign_lhs;
                          exp_var_pos = no_pos} in
    Assign{ exp_assign_op = OpAssign;
            exp_assign_lhs = lhs;
            exp_assign_rhs = c2iast_exp var.exp_assign_rhs;
            exp_assign_path_id = None;
            exp_assign_pos = var.exp_assign_pos}
  | _ -> report_error no_pos "cast_to_iast_exp not handled"

and c2iast_bind bv read =
  let var = Iast.Var{ exp_var_name = bv.exp_bind_bound_var |> snd;
                      exp_var_pos = no_pos} in
  let node = Iast.Member{ exp_member_base = var;
                         exp_member_fields = bv.exp_bind_fields |> List.map snd;
                         exp_member_path_id = None;
                         exp_member_pos = no_pos;} in
  if not read then
    let rhs = match c2iast_exp bv.exp_bind_body with
      | Assign a_exp -> a_exp.Iast.exp_assign_rhs
      | _ -> report_error no_pos "c2iast_exp not handled" in
    Iast.Assign{ exp_assign_op = OpAssign;
                 exp_assign_lhs = node;
                 exp_assign_rhs = rhs;
                 exp_assign_path_id = None;
                 exp_assign_pos = bv.exp_bind_pos;}
  else
    let lhs = match c2iast_exp bv.exp_bind_body with
      | Assign a_exp -> a_exp.Iast.exp_assign_lhs
      | _ -> report_error no_pos "c2iast_exp not handled" in
    Iast.Assign { exp_assign_op = OpAssign;
                  exp_assign_lhs = lhs;
                  exp_assign_rhs = node;
                  exp_assign_path_id = None;
                  exp_assign_pos = bv.exp_bind_pos}

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
      Cast.hp_formula = CF.mkBase_simp (CF.HEmp) (mix_of_pure (CP.mkTrue no_pos))
    } in
    let () = unk_hps := hp_decl::(!unk_hps) in
    let hrel = CF.HRel (hl_name, args, no_pos) in
    let n_conseq = add_h_formula_to_formula hrel conseq in
    let hrel_f = CF.mkBase_simp hrel (MCP.mix_of_pure (CP.mkTrue no_pos)) in
    hrel_f, n_conseq

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

let equal_type var1 var2 = match CP.type_of_sv var1 with
  | Int -> is_int_var var2
  | Named _ | TVar _ -> is_node_var var2
  | _ -> CP.type_of_sv var1 = CP.type_of_sv var2

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
    let n_qvars = List.filter
        (fun x -> not(List.exists (fun y -> CP.eq_sv x y) vars)) qvars in
    if n_qvars = [] then CF.mkBase_w_lbl h p vp t fl a pos lbl
    else Exists {bf with CF.formula_exists_qvars = n_qvars}
  | Or bf -> let n_f1 = remove_exists_vars bf.formula_or_f1 vars in
    let n_f2 = remove_exists_vars bf.formula_or_f2 vars in
    Or {bf with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2}

let rec add_exists_vars (formula:CF.formula) (vars: CP.spec_var list) =
  match formula with
  | Base {
      formula_base_heap = heap;
      formula_base_vperm = vp;
      formula_base_pure = pure;
      formula_base_type = t;
      formula_base_and = a;
      formula_base_flow = fl;
      formula_base_label = lbl;
      formula_base_pos = pos } ->
    CF.mkExists_w_lbl vars heap pure vp t fl a pos lbl
  | Exists ({formula_exists_qvars = qvars;
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
  | Or bf -> let n_f1 = add_exists_vars bf.formula_or_f1 vars in
    let n_f2 = add_exists_vars bf.formula_or_f2 vars in
    Or {bf with CF.formula_or_f1 = n_f1; CF.formula_or_f2 = n_f2}

let add_formula_to_formula f1 f2 =
  let bf = CF.mkStar f1 f2 CF.Flow_combine no_pos in
  let evars = (CF.get_exists f1) @ (CF.get_exists f2) |> CP.remove_dups_svl in
  if evars = [] then bf
    else add_exists_vars bf evars

let remove_exists (formula:CF.formula) =
  let vars = CF.get_exists formula in
  remove_exists_vars formula vars

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

let unprime_formula (formula:CF.formula) =
  let vars = CF.fv formula |> List.filter CP.is_primed in
  let substs = vars |> List.map (fun x -> (x, CP.to_unprimed x)) in
  CF.subst substs formula

let rec has_unfold_pre trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlUnfoldPre r -> true
      | _ -> has_unfold_pre t
    end

let rec has_fcall_trace trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlFuncCall _ -> true
      | _ -> has_unfold_pre t
    end

let rec has_unfold_post trace = match trace with
  | [] -> false
  | h::t -> begin
      match h with
      | RlUnfoldPost _ -> true
      | _ -> has_unfold_post t
    end

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
let var_to_cast sv loc =
  Iast.Var { exp_var_name = CP.name_of_sv sv;
             exp_var_pos = loc }

let num_to_cast num loc =
  Iast.IntLit { exp_int_lit_val = num;
                exp_int_lit_pos = loc}

let rec exp_to_iast (exp: CP.exp) = match exp with
  | CP.Var (sv, loc) ->  var_to_cast sv loc
  | CP.Null loc -> I.Null loc
  | CP.IConst (num, loc) -> num_to_cast num loc
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

let get_start_lnum pos = pos.VarGen.start_pos.Lexing.pos_lnum

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

let mkVar sv = I.Var { I.exp_var_name = CP.name_of_sv sv;
                       I.exp_var_pos = no_pos}

let mkSeq exp1 exp2 = I.Seq {
    exp_seq_exp1 = exp1;
    exp_seq_exp2 = exp2;
    exp_seq_pos = no_pos}

let mkAssign exp1 exp2 = I.Assign {
    I.exp_assign_op = I.OpAssign;
    I.exp_assign_lhs = exp1;
    I.exp_assign_rhs = exp2;
    I.exp_assign_path_id = None;
    I.exp_assign_pos = no_pos}

let rec synthesize_st_core st : Iast.exp option=
  match st.stc_rule with
  | RlSkip -> None
  | RlExistsLeft _ | RlExistsRight _ | RlFramePred _
  | RlUnfoldPost _ | RlUnfoldPre _ -> synthesize_subtrees st.stc_subtrees
  | RlAssign rassign ->
    let lhs, rhs = rassign.ra_lhs, rassign.ra_rhs in
    let c_exp = exp_to_iast rhs in
    let assgn = mkAssign (mkVar lhs) c_exp in
    aux_subtrees st assgn
  | RlReturn rule -> let c_exp = exp_to_iast rule.r_exp in
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
    let bind = mkAssign exp_mem rhs_var in aux_subtrees st bind
  | RlFRead rule -> let lhs = rule.rfr_value in
    let bvar, (typ, f_name) = rule.rfr_bound_var, rule.rfr_field in
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
    let bind = I.Bind {
        exp_bind_bound_var = CP.name_of_sv bvar;
        exp_bind_fields = [f_name];
        exp_bind_body = body;
        exp_bind_path_id = None;
        exp_bind_pos = no_pos} in
    let seq = mkSeq exp_decl bind in aux_subtrees st seq
  | RlFuncCall rule ->
    let args = rule.rfc_params |> List.map mkVar in
    let fcall = Iast.CallNRecv {
        exp_call_nrecv_method = rule.rfc_fname;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_arguments = args;
        exp_call_nrecv_path_id = None;
        exp_call_nrecv_pos = no_pos} in
    aux_subtrees st fcall
  | RlFuncRes rule ->
    let args = rule.rfr_params |> List.map mkVar in
    let fcall = Iast.CallNRecv {
        exp_call_nrecv_method = rule.rfr_fname;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_arguments = args;
        exp_call_nrecv_path_id = None;
        exp_call_nrecv_pos = no_pos} in
    let rvar = rule.rfr_return in
    let r_var = I.Var { I.exp_var_name = CP.name_of_sv rvar;
                        I.exp_var_pos = no_pos} in
    let asgn = mkAssign (mkVar rvar) fcall in
    let seq = mkSeq r_var asgn in aux_subtrees st seq
  | _ -> report_error no_pos "synthesize_st_core: this case unhandled"

and aux_subtrees st cur_codes =
  let st_code = synthesize_subtrees st.stc_subtrees in
  match st_code with
  | None -> Some cur_codes
  | Some st_code ->
    let seq = mkSeq cur_codes st_code in
    Some seq

and synthesize_subtrees subtrees = match subtrees with
  | [] -> None
  | [h] -> synthesize_st_core h
  | h::t -> let fst = synthesize_st_core h in
    begin
      match fst with
      | Some fst ->
        let snd = synthesize_subtrees t in
        (match snd with | None -> None
                        | Some snd -> Some (mkSeq fst snd))
      | None -> None
    end

let rec replace_exp_aux nexp exp : I.exp = match (exp:I.exp) with
  | Assign e -> let n_e1 = replace_exp_aux nexp e.I.exp_assign_lhs in
    let n_e2 = replace_exp_aux nexp e.I.exp_assign_rhs in
    Assign {e with exp_assign_lhs = n_e1;
                   exp_assign_rhs = n_e2}
  | Bind e -> let n_body = replace_exp_aux nexp e.I.exp_bind_body in
    Bind {e with exp_bind_body = n_body}
  | Block e -> let n_body = replace_exp_aux nexp e.I.exp_block_body in
    Block {e with exp_block_body = n_body}
  | Cast e -> let n_body = replace_exp_aux nexp e.I.exp_cast_body in
    Cast {e with exp_cast_body = n_body;}
  | CallNRecv e -> let name = e.I.exp_call_nrecv_method in
    let () = x_tinfo_hp (add_str "name" pr_id) name no_pos in
    if name = "fcode" then nexp
    else exp
  | UnkExp _ -> let () = x_tinfo_pp "marking" no_pos in
    exp
  | Cond e ->
    let () = x_tinfo_pp "marking" no_pos in
    let r1 = replace_exp_aux nexp e.exp_cond_then_arm in
    let r2 = replace_exp_aux nexp e.exp_cond_else_arm in
    Cond {e with exp_cond_then_arm = r1;
                 exp_cond_else_arm = r2}
  | Label (a, body) -> Label (a, replace_exp_aux nexp body)
  | Seq e -> let n_e1 = replace_exp_aux nexp e.I.exp_seq_exp1 in
    let n_e2 = replace_exp_aux nexp e.I.exp_seq_exp2 in
    Seq {e with exp_seq_exp1 = n_e1;
                exp_seq_exp2 = n_e2}
  | _ -> exp

let replace_exp_proc n_exp proc =
  let n_body = match proc.Iast.proc_body with
    | None -> None
    | Some exp -> Some (replace_exp_aux n_exp exp) in
  let () = x_tinfo_hp (add_str "n_exp" pr_iast_exp) n_exp no_pos in
  let () = x_binfo_hp (add_str "n_body" pr_iast_exp_opt) n_body no_pos in
  {proc with I.proc_body = n_body}

let rec get_heap (formula:CF.formula) = match formula with
  | Base bf -> [bf.CF.formula_base_heap]
  | Exists bf -> [bf.CF.formula_exists_heap]
  | Or bf -> (get_heap bf.CF.formula_or_f1) @ (get_heap bf.CF.formula_or_f2)

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
        else Star {sf with h_formula_star_h1 = fst n_f1;
                           h_formula_star_h2 = fst n_f2} in
      (n_hf, (snd n_f1)@(snd n_f2))
    | _ -> (hf,[]) in
  match formula with
  | CF.Base bf -> let hf = bf.CF.formula_base_heap in
    let n_hf = helper hf in
    (CF.Base {bf with formula_base_heap = fst n_hf}, snd n_hf)
  | CF.Exists bf -> let hf = bf.CF.formula_exists_heap in
    let n_hf, vars = helper hf in
    let exists_vars = bf.CF.formula_exists_qvars
                      |> List.filter (fun x -> not (CP.eq_sv var x)) in
    (CF.Exists {bf with formula_exists_heap = n_hf;
                        formula_exists_qvars = exists_vars}, vars)
  | _ -> report_error no_pos "frame_var_formula: CF.Or unhandled"

let get_hf (f:CF.formula) = match f with
  | Base bf -> bf.formula_base_heap
  | Exists bf -> bf.formula_exists_heap
  | Or _ -> report_error no_pos "get_hf unhandled"

let is_res_sv_syn sv = match sv with
  | CP.SpecVar (_,n,_) -> is_substr "rs" n

let negate b = not b

(*********************************************************************
 * Rule utilities
 *********************************************************************)

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

let is_rule_fread_useless goal r =
  let var = r.rfr_value in
  let post_vars = CF.fv goal.gl_post_cond in
  if List.exists (fun x -> CP.eq_sv x var) post_vars then true
  else let arg_f = extract_var_f goal.gl_pre_cond var in
      match arg_f with
      | None -> false
      | Some arg_f -> if CF.is_emp_formula arg_f then false
        else true

let eliminate_useless_rules goal rules =
  List.filter (fun rule -> match rule with
      | RlFRead r -> is_rule_fread_useless goal r
      | _ -> true) rules

let compare_rule_assign_vs_other r1 r2 =
  if CP.is_res_spec_var r1.ra_lhs then PriHigh
  else PriEqual

let compare_rule r1 r2 =
  match r1 with
  | RlAssign r1 -> compare_rule_assign_vs_other r1 r2
  | _ -> PriEqual


let reorder_rules goal rules =
  let cmp_rule r1 r2 =
    let prio = compare_rule r1 r2 in
    match prio with
    | PriEqual -> 0
    | PriLow -> +1
    | PriHigh -> -1 in
  List.sort cmp_rule rules
(* List.sort sorts list increasing order *)

(*********************************************************************
 * Normalization rules
 *********************************************************************)

let choose_rule_exists_left goal =
  let vars = CF.get_exists goal.gl_pre_cond in
  if vars = [] then []
  else let rule = RlExistsLeft { exists_vars = vars} in
    [rule]

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

