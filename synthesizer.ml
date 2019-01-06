#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure
open Cformula

open Synthesis

module CA = Cast
module CF = Cformula

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)

(*********************************************************************
 * Choosing rules
 *********************************************************************)

let choose_rule_func_call goal : rule list =
  []

let rec extract_hf_var hf var =
  let pr_hf = Cprinter.string_of_h_formula in
  let () = x_binfo_hp (add_str "hf: " pr_hf) hf no_pos in
  match hf with
  | CF.DataNode dnode ->
    let dn_var = dnode.CF.h_formula_data_node in
    if dn_var = var then [dnode]
    else []
  | CF.Star sf ->
    let f1 = extract_hf_var sf.CF.h_formula_star_h1 var in
    let f2 = extract_hf_var sf.CF.h_formula_star_h2 var in
    f1 @ f2
    (* (match f1, f2 with
     *  | Some _, Some _
     *  | None, None -> None
     *  | None, Some hf2 -> Some hf2
     *  | Some hf1, None -> Some hf1) *)
  (* | CF.ViewNode vnode ->
   *   let vnode_var = vnode.CF.h_formula_view_node in
   *   if vnode_var = var then Some hf else None *)
  | _ -> []

  let extract_var_f f var = match f with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let hf_var = extract_hf_var hf var in
      hf_var
      (* (match hf_var with
       *  | Some hf -> Some (CF.formula_of_heap hf no_pos)
       *  | None -> None) *)
    | _ -> []

(* implement simple rules first *)
(* {x -> node{a} * y -> node{b}}{x -> node{y} * y -> node{b}} --> x.next = b *)
let choose_rule_assign goal : rule list =
  let vars = goal.gl_vars in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let prog = goal.gl_prog in
  let datas = prog.Cast.prog_data_decls in
  let var = List.hd vars in
  let f_var1 = extract_var_f pre var in
  let f_var2 = extract_var_f post var in
  let pr_formula = Cprinter.string_of_formula in
  let pr_hf = Cprinter.string_of_h_formula in
  let pr_sv = Cprinter.string_of_spec_var in
  let () = x_binfo_hp (add_str "var: " pr_sv) var no_pos in
  let () = x_binfo_hp (add_str "fvar1" (pr_list pr_hf))
      (List.map (fun x -> CF.DataNode x) f_var1) no_pos in
  let () = x_binfo_hp (add_str "fvar2" (pr_list pr_hf))
      (List.map (fun x -> CF.DataNode x) f_var2) no_pos in
  if f_var1 != [] && f_var2 != [] then
    let bef_node = List.hd f_var1 in
    let aft_node = List.hd f_var2 in
    if bef_node != aft_node then
      let () = x_binfo_pp "marking \n" no_pos in
      let bef_args = bef_node.CF.h_formula_data_arguments in
      let aft_args = aft_node.CF.h_formula_data_arguments in
      let name = bef_node.CF.h_formula_data_name in
      let data = List.find (fun x -> x.Cast.data_name = name) datas in
      let () = x_binfo_hp (add_str "data" Cprinter.string_of_data_decl) data no_pos in
      let pre_post = List.combine bef_args aft_args in
      let fields = data.Cast.data_fields in
      let triple = List.combine pre_post fields in
      let triple = List.filter (fun ((pre,post),_) -> pre!=post) triple in
      (* let compared_fields = List.map (fun (_, field) -> field) triple in *)
      let dif_field = if List.length triple = 1 then
          List.hd triple
        else report_error no_pos "more then 1 diff fields"
      in
      let dif_field_name = dif_field |> snd |> fst in
      let new_field_name = Cpure.fresh_old_name (snd dif_field_name) in
      let new_field = (fst dif_field_name, new_field_name) in
      let dif_field_val = dif_field |> fst |> snd in
      let n_var = Cast.Var {
          exp_var_type = Cpure.type_of_spec_var dif_field_val;
          exp_var_name = Cpure.name_of_sv dif_field_val;
          exp_var_pos = no_pos;
        }
      in
      let assign_exp = Cast.Assign {
          exp_assign_lhs = new_field_name;
          exp_assign_rhs = n_var;
          exp_assign_pos = no_pos;
        } in

      let bind = Cast.Bind {
            exp_bind_type = Void;
            exp_bind_bound_var = (Cpure.type_of_spec_var var, Cpure.name_of_sv var);
            exp_bind_fields = [new_field];
            exp_bind_body = assign_exp;
            exp_bind_imm = Cpure.NoAnn;
            exp_bind_param_imm = [];
            exp_bind_read_only = false;
            exp_bind_path_id = (1, "new");
            exp_bind_pos = no_pos
          } in
      let () = x_binfo_hp (add_str "data" Cprinter.string_of_exp) bind no_pos in

        []
    else []
  else
  (* let () = x_binfo_hp (add_str "f_var1: " pr_formula) (Gen.unsome f_var1) no_pos in
   * let () = x_binfo_hp (add_str "f_var2: " pr_formula) (Gen.unsome f_var2) no_pos in *)

  (* compare pre/post conds *)
  []

let choose_synthesis_rules goal : rule list =
  let rs = choose_rule_func_call goal in
  let rs2 = choose_rule_assign goal in
  rs

(*********************************************************************
 * Processing rules
 *********************************************************************)

let process_rule_func_call goal rcore : derivation =
  mk_derivation_sub_goals goal (RlFuncCall rcore) []

(* let process_rule_assign goal rassign : derivation = *)

let process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore
  | RlAssign rassign -> report_error no_pos "rassign not handled"


(*********************************************************************
 * The search procedure
 *********************************************************************)

let rec synthesize_one_goal goal : synthesis_tree =
  let rules = choose_synthesis_rules goal in
  process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  try
    List.iter (fun rule ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      if is_synthesis_tree_success stree then raise_stree stree
    ) rules;
    (* no rule can be applied *)
    mk_synthesis_tree_fail goal "no rule"
  with EStree st -> st

and process_conjunctive_subgoals goal rule sub_goals : synthesis_tree =
  (* TODO *)
  mk_synthesis_tree_success goal rule

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs


(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)

let synthesize_program goal : CA.exp option =
  None

let foo = ()
