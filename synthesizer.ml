#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure
open Cformula

open Synthesis

module CA = Cast
module CF = Cformula
module CP = Cpure

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)
let pr_hf = Cprinter.string_of_h_formula
let pr_pf = Cprinter.string_of_pure_formula

(*********************************************************************
 * Choosing rules
 *********************************************************************)

let choose_rule_func_call goal : rule list =
  []

let rec extract_hf_var hf var =
  let () = x_tinfo_hp (add_str "hf: " pr_hf) hf no_pos in
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
             then Some e2
             else if CP.eq_spec_var sv2 sv
                  && List.exists (fun x -> CP.eq_spec_var x sv1) cur_vars
             then Some e1
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

(* implement simple rules first *)
(* {x -> node{a} * y -> node{b}}{x -> node{y} * y -> node{b}} --> x.next = b *)
let choose_rassign_pure var cur_vars pre post : rule list =
  let () = x_binfo_pp "marking \n" no_pos in
  let pre_pf = CF.get_pure pre in
  let () = x_binfo_hp (add_str "pre_pf" pr_pf) pre_pf no_pos in
  let post_pf = CF.get_pure post in
  let pre_f = extract_var_pf pre_pf var in
  let pr_exp = Cprinter.string_of_formula_exp in
  (* let () = x_binfo_hp (add_str "pre_f" pr_exp) (Gen.unsome pre_f) no_pos in *)
  let post_f = extract_var_pf post_pf var in
  match pre_f, post_f with
  | Some e1, Some e2 ->
    (match e2 with
     | Var (sv, _) ->
       if List.exists (fun x -> CP.eq_spec_var x sv) cur_vars then
         let rule = RlAssign {
             ra_lhs = var;
             ra_rhs = e2;
           } in
         [rule]
       else
         let () = x_binfo_pp "marking \n" no_pos in
         let cur_vars = List.filter (fun x -> x != var) cur_vars in
         let pr_var = Cprinter.string_of_spec_var in
         let pr_vars = pr_list pr_var in
         let () = x_binfo_hp (add_str "vars: " pr_vars) cur_vars no_pos in
         let () = x_binfo_hp (add_str "var: " pr_var) sv no_pos in
         let find_var = find_sub_var sv cur_vars pre_pf in
         begin
           match find_var with
           | None -> []
           | Some sub_var ->
             let rule = RlAssign {
                 ra_lhs = var;
                 ra_rhs = sub_var;
               } in
             [rule]
         end
     | _ -> []
    )
  | _ -> []

let choose_rassign_data var cur_vars datas pre post =
  let f_var1 = extract_var_f pre var in
  let f_var2 = extract_var_f post var in
  let () = x_binfo_hp (add_str "fvar1" (pr_list pr_hf))
      (List.map (fun x -> CF.DataNode x) f_var1) no_pos in
  let () = x_binfo_hp (add_str "fvar2" (pr_list pr_hf))
      (List.map (fun x -> CF.DataNode x) f_var2) no_pos in
  if f_var1 != [] && f_var2 != [] then
    let bef_node = List.hd f_var1 in
    let aft_node = List.hd f_var2 in
    if bef_node != aft_node then
      let bef_args = bef_node.CF.h_formula_data_arguments in
      let aft_args = aft_node.CF.h_formula_data_arguments in
      let name = bef_node.CF.h_formula_data_name in
      let data = List.find (fun x -> x.Cast.data_name = name) datas in
      let () = x_binfo_hp (add_str "data" Cprinter.string_of_data_decl) data no_pos in
      let pre_post = List.combine bef_args aft_args in
      let fields = data.Cast.data_fields in
      let triple = List.combine pre_post fields in
      let triple = List.filter (fun ((pre,post),_) -> not(CP.eq_spec_var pre post)) triple in
      if List.length triple = 1 then
        let dif_field = List.hd triple in
        let df_name = dif_field |> snd |> fst in
        (* let rule = RlBind {
         *     rb_var = var;
         *     rb_field = (fst df_name, CP.fresh_old_name (snd df_name));
         *   } in *)
        (* let n_name = CP.fresh_old_name (snd df_name) in *)
        let n_name = snd df_name in
        let n_var = CP.mk_typed_spec_var (fst df_name) n_name in
        let cur_vars = cur_vars @ [n_var] in
        let pre_val = dif_field |> fst |> fst in
        let post_val = dif_field |> fst |> snd in
        let n_pre_pure = CP.mkEqVar n_var pre_val no_pos in
        let n_post_pure = CP.mkEqVar n_var post_val no_pos in
        let n_pre = CF.add_pure_formula_to_formula n_pre_pure pre in
        let n_post = CF.add_pure_formula_to_formula n_post_pure post in
        let n_rule = choose_rassign_pure n_var cur_vars n_pre n_post in
        if n_rule = [] then []
        else
          let eq_rule = List.hd n_rule in
          match eq_rule with
          | RlAssign rassgn ->
            let rule = RlBindWrite {
                rb_var = var;
                rb_field = (fst df_name, n_name);
                rb_rhs = rassgn.ra_rhs;
              }
            in [rule]
          | _ -> []
      else []
    else []
  else []

let choose_rule_assign goal : rule list =
  let vars = goal.gl_vars in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let prog = goal.gl_prog in
  let datas = prog.Cast.prog_data_decls in
  let pr_formula = Cprinter.string_of_formula in
  let pr_sv = Cprinter.string_of_spec_var in
  let () = x_binfo_hp (add_str "vars: " (pr_list pr_sv)) vars no_pos in
  let choose_rule var = match CP.type_of_sv var with
    | Int -> choose_rassign_pure var vars pre post
    | Named _ -> choose_rassign_data var vars datas pre post
    | _ -> let () = x_binfo_pp "marking \n" no_pos in
      []  in
  let rules = List.map choose_rule vars in
  List.concat rules

let choose_synthesis_rules goal : rule list =
  (* let rs = choose_rule_func_call goal in *)
  let rs2 = choose_rule_assign goal in
  let () = x_binfo_hp (add_str "rules" (pr_list pr_rule)) rs2 no_pos in
  rs2

let split_hf (f: CF.formula) = match f with
  | Base bf -> let hf = bf.CF.formula_base_heap in
    let rec helper hf =
      match hf with
      | CF.DataNode dnode ->
        [(dnode.CF.h_formula_data_node, hf)]
      | CF.ViewNode vnode ->
        [(vnode.CF.h_formula_view_node, hf)]
      | CF.Star sf ->
        let f1 = helper sf.CF.h_formula_star_h1 in
        let f2 = helper sf.CF.h_formula_star_h2 in
        f1@f2
      | _ -> []
    in helper hf
  | _ -> []

let choose_framing goal : goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let pre_hfs = split_hf pre in
  let post_hfs = split_hf post in
  let framing_heaps = List.filter (fun x -> List.mem x post_hfs) pre_hfs in
  let remaining_heaps = List.map snd framing_heaps in
  let n_hf = CF.join_star_conjunctions remaining_heaps in
  let () = x_binfo_hp (add_str "hf: " pr_hf) n_hf no_pos in
  goal

(*********************************************************************
 * Processing rules
 *********************************************************************)

let process_rule_func_call goal rcore : derivation =
  mk_derivation_sub_goals goal (RlFuncCall rcore) []

let process_rule_assign goal rassign =
  let pre = goal.gl_pre_cond in
  let lhs = rassign.ra_lhs in
  let rhs = rassign.ra_rhs in
  let res_var = CP.mkRes (CP.type_of_sv lhs) in
  let n_rhs = CP.mkEqExp (CP.mkVar res_var no_pos) rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_rhs pre in
  let tmp_lhs = CP.fresh_spec_var lhs in
  let n_post = CF.subst [(lhs, tmp_lhs); (res_var, lhs)] n_pre in
  let pr_formula = Cprinter.string_of_formula in
  let () = x_binfo_hp (add_str "post_cond " pr_formula) n_post no_pos in
  let ent_check = Songbird.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlAssign rassign)
  | false ->
    let post = goal.gl_post_cond in
    let sub_goal = mk_goal goal.gl_prog n_post post goal.gl_vars in
    mk_derivation_sub_goals goal (RlAssign rassign) [sub_goal]

let subs_bind_write formula var field data_decls =
  let helper formula = match formula with
    | Base bf ->
      let hf = bf.CF.formula_base_heap in
      (match hf with
       | DataNode dnode -> None
       | _ -> None
      )
    | _ -> None
  in
  None

let process_rule_bind goal rbind =
  let pre = goal.gl_pre_cond in
  let var = rbind.rb_var in
  let field = rbind.rb_field in
  let rhs = rbind.rb_rhs in
  let prog = goal.gl_prog in
  let data_decls = prog.prog_data_decls in
  mk_derivation_sub_goals goal (RlBindWrite rbind) []

let process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore
  | RlAssign rassign -> process_rule_assign goal rassign
  | RlBindWrite rbind -> process_rule_bind goal rbind

(*********************************************************************
 * The search procedure
 *********************************************************************)

let rec synthesize_one_goal goal : synthesis_tree =
  let goal = choose_framing goal in
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
    | [] -> mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_conjunctive_subgoals goal rule sub_goals : synthesis_tree =
  (* TODO *)
  mk_synthesis_tree_success goal rule

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal [] "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs


(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)
let exp_to_cast (exp: CP.exp) = match exp with
  | Var (sv, loc) ->
    Cast.Var {
      exp_var_type = CP.type_of_sv sv;
      exp_var_name = CP.name_of_sv sv;
      exp_var_pos = loc
    }
  | IConst (num, loc) ->
    Cast.IConst {
      exp_iconst_val = num;
      exp_iconst_pos = loc;
    }
  (* | Add (e1, e2, loc) -> *)
  | _ -> report_error no_pos "exp_to_cast: not handled"


let synthesize_st_core st =
  let rule = st.stc_rule in
  match rule with
  | RlAssign rassign->
    let lhs = rassign.ra_lhs in
    let rhs = rassign.ra_rhs in
    let c_exp = exp_to_cast rhs in
    let assign = Cast.Assign {
        exp_assign_lhs = CP.name_of_sv lhs;
        exp_assign_rhs = c_exp;
        exp_assign_pos = no_pos;
      }
    in Some assign
  | _ -> None

let synthesize_program goal : CA.exp option =
  let st = synthesize_one_goal goal in
  let () = x_binfo_hp (add_str "syn_tree: " pr_st) st no_pos in
  let st_status = get_synthesis_tree_status st in
  match st_status with
  | StValid st_core ->
    let res = synthesize_st_core st_core in
    let () = x_binfo_hp (add_str "res" pr_exp_opt) res no_pos in
    res
  | StUnkn _ -> None
