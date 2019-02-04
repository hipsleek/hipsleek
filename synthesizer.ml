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
let pr_formula = Cprinter.string_of_formula
let pr_hf = Cprinter.string_of_h_formula
let pr_pf = Cprinter.string_of_pure_formula
let pr_sv = Cprinter.string_of_spec_var
let pr_var = Cprinter.string_of_spec_var
let pr_vars = pr_list pr_var

(*********************************************************************
 * Choosing rules
 *********************************************************************)

let choose_rule_func_call goal : rule list =
  (* step 1: unfolding views *)

  []

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

let extract_var_f f var = match f with
    | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
      let heap_extract = extract_hf_var hf var in
      begin
        match heap_extract with
        | None ->
          let pf_var = pf_of_vars [var] pf in
          Some (CF.mkBase_simp CF.HEmp (Mcpure.mix_of_pure pf_var))
        | Some (hf, vars) ->
          let pf_var = pf_of_vars vars pf in
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

(* implement simple rules first *)
(* {x -> node{a} * y -> node{b}}{x -> node{y} * y -> node{b}} --> x.next = b *)
let choose_rassign_pure var goal : rule list =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let cur_vars = goal.gl_vars in
  let () = x_binfo_hp (add_str "var" pr_sv) var no_pos in
  let () = x_binfo_hp (add_str "vars" (pr_list pr_sv)) cur_vars no_pos in
  let pre_pf = CF.get_pure pre in
  let () = x_binfo_hp (add_str "pre_pf" pr_pf) pre_pf no_pos in
  let post_pf = CF.get_pure post in
  let () = x_binfo_hp (add_str "post_pf" pr_pf) post_pf no_pos in
  let pre_f = extract_var_pf pre_pf var in
  let pr_exp = Cprinter.string_of_formula_exp in
  let post_f = extract_var_pf post_pf var in
  match pre_f, post_f with
  | Some e1, Some e2 ->
    (match e2 with
     | Var (sv, _) ->
       let () = x_binfo_pp "marking" no_pos in
       if List.exists (fun x -> CP.eq_spec_var x sv) cur_vars then
         let rule = RlAssign {
             ra_lhs = var;
             ra_rhs = sv;
           } in
         [rule]
       else
         let () = x_binfo_pp "marking \n" no_pos in
         let cur_vars = List.filter (fun x -> x != var) cur_vars in
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

let choose_rule_field_dnode dn1 dn2 var goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let var_list = goal.gl_vars in
  let prog = goal.gl_prog in
  let data_decls = prog.Cast.prog_data_decls in
  let () = x_binfo_hp (add_str "pre-dnode" pr_formula) pre no_pos in
  let () = x_binfo_hp (add_str "post-dnode" pr_formula) post no_pos in
  let bef_args = dn1.CF.h_formula_data_arguments in
  let aft_args = dn2.CF.h_formula_data_arguments in
  let name = dn1.CF.h_formula_data_name in
  let data = List.find (fun x -> x.Cast.data_name = name) data_decls in
  let () = x_tinfo_hp (add_str "data" Cprinter.string_of_data_decl) data no_pos in
  let pre_post = List.combine bef_args aft_args in
  let fields = data.Cast.data_fields in
  let triple = List.combine pre_post fields in
  let triple = List.filter (fun ((pre,post),_) -> not(CP.eq_spec_var pre post)) triple in
  if List.length triple = 1 then
    let dif_field = List.hd triple in
    let df_name = dif_field |> snd |> fst in
    let n_name = snd df_name in
    let n_var = CP.mk_typed_spec_var (fst df_name) n_name in
    let var_list = var_list @ [n_var] in
    let pre_val = dif_field |> fst |> fst in
    let post_val = dif_field |> fst |> snd in
    let n_pre_pure = CP.mkEqVar n_var pre_val no_pos in
    let n_post_pure = CP.mkEqVar n_var post_val no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pre_pure pre in
    let n_post = CF.add_pure_formula_to_formula n_post_pure post in
    let n_goal = mk_goal prog n_pre n_post var_list in
    let n_rule = choose_rassign_pure n_var n_goal in
    if n_rule = [] then []
    else
      let () = x_binfo_hp (add_str "rules" (pr_list pr_rule)) n_rule no_pos in
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

let subtract_var var formula = match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let rec helper hf = match hf with
      | CF.DataNode dnode ->
        let dnode_var = dnode.CF.h_formula_data_node in
        if CP.eq_spec_var dnode_var var then HEmp
        else hf
      | Star sf ->
        let f1 = sf.CF.h_formula_star_h1 in
        let f2 = sf.CF.h_formula_star_h2 in
        let n_f1 = helper f1 in
        let n_f2 = helper f2 in
        Star {sf with h_formula_star_h1 = n_f1;
                      h_formula_star_h2 = n_f2}
      | _ -> hf in
    let n_hf = helper hf in
    CF.Base {bf with formula_base_heap = n_hf}
  | _ -> formula

let choose_rule_dnode dn1 dn2 var goal =
  let field_rules = choose_rule_field_dnode dn1 dn2 var goal in
  if field_rules != [] then field_rules
  else []

let rec choose_rassign_data cur_var goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let () = x_binfo_hp (add_str "var" pr_sv) cur_var no_pos in
  let () = x_binfo_hp (add_str "PRE" pr_formula) pre no_pos in
  let () = x_binfo_hp (add_str "POST" pr_formula) post no_pos in
  let rec helper hf name args = match hf with
    | CF.DataNode f_dnode ->
      let f_name = f_dnode.CF.h_formula_data_name in
      let f_args = f_dnode.CF.h_formula_data_arguments in
      if List.length f_args = List.length args then
        let similar_var = (String.compare f_name name == 0) &&
                          List.for_all2 (fun x y -> CP.eq_spec_var x y) f_args args in
        if similar_var then Some f_dnode.CF.h_formula_data_node
        else None
      else None
    | CF.ViewNode vnode ->
      let v_name = vnode.CF.h_formula_view_name in
      let v_args = vnode.CF.h_formula_view_arguments in
      if List.length v_args = List.length args then
        let similar_var = (String.compare v_name name == 0) &&
                          List.for_all2 (fun x y -> CP.eq_spec_var x y) v_args args in
        if similar_var then Some vnode.CF.h_formula_view_node
        else None
      else None
    | CF.Star sf ->
      let f1 = sf.CF.h_formula_star_h1 in
      begin
        match helper f1 name args with
        | None ->
          let f2 = sf.CF.h_formula_star_h2 in
          helper f2 name args
        | Some sv -> Some sv
      end
    | _ -> None in
  let find_similar_shape_var fvar formula = match fvar, formula with
    | CF.Base bf_var, CF.Base bf ->
      let hf_var = bf_var.CF.formula_base_heap in
      let hf_f = bf.CF.formula_base_heap in
      begin
        match hf_var with
        | DataNode dnode ->
          let name = dnode.CF.h_formula_data_name in
          let args = dnode.CF.h_formula_data_arguments in
          helper hf_f name args
        | ViewNode vnode ->
          let name = vnode.CF.h_formula_view_name in
          let args = vnode.CF.h_formula_view_arguments in
          helper hf_f name args
        | _ -> None
      end
    | _ -> None
  in
  match pre, post with
  | CF.Base bf1, CF.Base bf2 ->
    let var_list = goal.gl_vars in
    let prog = goal.gl_prog in
    let data_decls = prog.Cast.prog_data_decls in
    let f_var1 = extract_var_f pre cur_var in
    let f_var2 = extract_var_f post cur_var in
    if f_var1 != None && f_var2 != None then
      let f_var1 = Gen.unsome f_var1 in
      let f_var2 = Gen.unsome f_var2 in
      let () = x_binfo_hp (add_str "fvar1" pr_formula) f_var1 no_pos in
      let () = x_binfo_hp (add_str "fvar2" pr_formula) f_var2 no_pos in
      let field_rules =
        match f_var1, f_var2 with
        | CF.Base bf1, CF.Base bf2 ->
          let hf1 = bf1.CF.formula_base_heap in
          let hf2 = bf2.CF.formula_base_heap in
          begin
            match hf1, hf2 with
            | CF.DataNode dnode1, CF.DataNode dnode2 ->
              choose_rule_dnode dnode1 dnode2 cur_var goal
            | CF.DataNode dnode, CF.ViewNode vnode ->
              let view_name = vnode.CF.h_formula_view_name in
              let views = prog.Cast.prog_view_decls in
              let n_f2 = Lemma.do_unfold_view prog post in
              let () = x_binfo_hp (add_str "n_f2" (pr_formula)) n_f2 no_pos in
              let n_goal = mk_goal prog f_var1 n_f2 var_list in
              choose_rassign_data cur_var n_goal
            | _ -> []
          end
        | _ -> [] in
      let similar_var = find_similar_shape_var f_var2 pre in
      let shape_rule = match similar_var with
        | Some eq_var ->
          if List.exists (fun x -> CP.eq_spec_var x eq_var) var_list then
            let rule = RlAssign {
                ra_lhs = cur_var;
                ra_rhs = eq_var;
              } in
            [rule]
          else []
        | None -> []
      in
      field_rules @ shape_rule
    else []
  | CF.Base _, CF.Or disjs ->
    let f1 = disjs.CF.formula_or_f1 in
    let f2 = disjs.CF.formula_or_f2 in
    let goal1 = {goal with gl_post_cond = f1} in
    let goal2 = {goal with gl_post_cond = f2} in
    let rule1 = choose_rassign_data cur_var goal1 in
    let rule2 = choose_rassign_data cur_var goal2 in
    rule1@rule2
  | _ -> []

let frame_var var formula prog = match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let rec helper hf = match hf with
      | CF.DataNode dnode ->
        let dnode_var = dnode.CF.h_formula_data_node in
        if CP.eq_spec_var dnode_var var then
          let args = dnode.CF.h_formula_data_arguments in
          let data_name = dnode.CF.h_formula_data_name in
          let data_decls = prog.Cast.prog_data_decls in
          let data = List.find (fun x -> x.Cast.data_name = data_name)
              data_decls in
          let data_fields = data.Cast.data_fields |> List.split |> fst in
          let args_w_fields = List.combine args data_fields in
          let args_w_fields = List.filter (fun (x,y) -> is_named_type_var x)
              args_w_fields in
          (CF.HEmp, args_w_fields)
        else (hf, [])
      | CF.Star sf ->
        let n_f1, vars1 = helper sf.CF.h_formula_star_h1 in
        let n_f2, vars2 = helper sf.CF.h_formula_star_h2 in
        (Star {sf with h_formula_star_h1 = n_f1;
                      h_formula_star_h2 = n_f2}, vars1@vars2)
      | _ -> (hf, []) in
    let n_hf, vars = helper hf in
    (CF.Base {bf with formula_base_heap = n_hf}, vars)
  | _ -> (formula, [])

let choose_framing_rule var goal : rule list =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let framed_pre, vars_w_fields = frame_var var pre goal.gl_prog in
  let framed_post, _ = frame_var var post goal.gl_prog in
  let aux cur_var field_var field goal =
    let rules = choose_rassign_data field_var goal in
    if rules != [] then
      let rule = List.hd rules in
      match rule with
      | RlAssign assign_rule ->
        let final_rule = RlBindWrite {
            rb_var = cur_var;
            rb_field = field;
            rb_rhs = assign_rule.ra_rhs;
          }
        in [final_rule]
      | _ -> []
    else [] in
  if vars_w_fields != [] then
    let () = x_binfo_hp (add_str "framed_pre" pr_formula) framed_pre no_pos in
    let () = x_binfo_hp (add_str "framed_post" pr_formula) framed_post no_pos in
    let field_vars = vars_w_fields |> List.split |> fst in
    let n_vars = goal.gl_vars @ field_vars |> CP.remove_dups_svl in
    let n_goal = mk_goal goal.gl_prog framed_pre framed_post n_vars in
    let rules = List.map (fun (x,y) -> aux var x y n_goal) vars_w_fields in
    List.concat rules
  else []

let choose_rule_assign goal : rule list =
  let vars = goal.gl_vars in
  let pr_sv = Cprinter.string_of_spec_var in
  let () = x_tinfo_hp (add_str "vars: " (pr_list pr_sv)) vars no_pos in
  let choose_rule var = match CP.type_of_sv var with
    | Int -> choose_rassign_pure var goal
    | Named _ ->
      let framing_rules = choose_framing_rule var goal in
      let assign_rules = choose_rassign_data var goal in
      framing_rules @ assign_rules
    | _ -> let () = x_binfo_pp "marking \n" no_pos in
      []  in
  let rules = List.map choose_rule vars in
  List.concat rules

let choose_synthesis_rules goal : rule list =
  let rs = choose_rule_assign goal in
  let rs = List.filter not_identity_assign_rule rs in
  let () = x_binfo_hp (add_str "rules" (pr_list pr_rule)) rs no_pos in
  rs

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
  let n_rhs = CP.mkEqExp (CP.mkVar res_var no_pos) (CP.mkVar rhs no_pos) no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_rhs pre in
  let tmp_lhs = CP.fresh_spec_var lhs in
  let n_post = CF.subst [(lhs, tmp_lhs); (res_var, lhs)] n_pre in
  let () = x_binfo_hp (add_str "post_cond " pr_formula) n_post no_pos in
  let ent_check = Songbird.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlAssign rassign)
  | false -> mk_derivation_fail goal (RlAssign rassign)
    (* let post = goal.gl_post_cond in
     * let sub_goal = mk_goal goal.gl_prog n_post post goal.gl_vars in
     * mk_derivation_sub_goals goal (RlAssign rassign) [sub_goal] *)

let subs_bind_write formula var field new_val data_decls =
  match formula with
  | Base bf ->
    let hf = bf.CF.formula_base_heap in
    let () = x_binfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper hf =
      match hf with
      | DataNode dnode ->
        let data_var = dnode.h_formula_data_node in
        let () = x_binfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf
            no_pos in
        if CP.eq_spec_var data_var var then
          let n_dnode = set_field dnode field new_val data_decls in
          (DataNode n_dnode)
        else hf 
      | Star sf ->
        let n_h1 = helper sf.CF.h_formula_star_h1 in
        let n_h2 = helper sf.CF.h_formula_star_h2 in
        Star {sf with h_formula_star_h1 = n_h1;
                      h_formula_star_h2 = n_h2}
      | _ -> hf
    in Base {bf with formula_base_heap = helper hf}
  | _ -> formula

let process_rule_wbind goal (wbind:rule_bind) =
  let pre = goal.gl_pre_cond in
  let var = wbind.rb_var in
  let field = wbind.rb_field in
  let rhs = wbind.rb_rhs in
  let prog = goal.gl_prog in
  let data_decls = prog.prog_data_decls in
  let n_post = subs_bind_write pre var field rhs data_decls in
  let () = x_binfo_hp (add_str "after applied:" pr_formula) n_post no_pos in
  let ent_check = Songbird.check_entail goal.gl_prog n_post goal.gl_post_cond in
  match ent_check with
  | true -> mk_derivation_success goal (RlBindWrite wbind)
  | false -> mk_derivation_fail goal (RlBindWrite wbind)

(* let process_rule_rbind goal (rbind:rule_bindread) =
 *   mk_derivation_sub_goals goal (RlBindRead rbind) [] *)

let process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore
  | RlAssign rassign -> process_rule_assign goal rassign
  | RlBindWrite wbind -> process_rule_wbind goal wbind
  (* | RlBindRead rbind -> process_rule_rbind goal rbind *)

(*********************************************************************
 * The search procedure
 *********************************************************************)

let rec synthesize_one_goal goal : synthesis_tree =
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
  | _ -> report_error no_pos "exp_to_cast: not handled"


let synthesize_st_core st =
  let rule = st.stc_rule in
  match rule with
  | RlAssign rassign ->
    let lhs = rassign.ra_lhs in
    let rhs = rassign.ra_rhs in
    let c_exp = exp_to_cast (CP.mkVar rhs no_pos) in
    let assign = Cast.Assign {
        exp_assign_lhs = CP.name_of_sv lhs;
        exp_assign_rhs = c_exp;
        exp_assign_pos = no_pos;
      }
    in Some assign
  | RlBindWrite rbind ->
    let bvar = rbind.rb_var in
    let bfield = rbind.rb_field in
    let rhs = rbind.rb_rhs in
    let typ = CP.type_of_sv rhs in
    let rhs_var = Cast.Var {
        Cast.exp_var_type = CP.type_of_sv rhs;
        Cast.exp_var_name = CP.name_of_sv rhs;
        Cast.exp_var_pos = no_pos;
      } in
    let (typ, f_name) = bfield in
    let body = Cast.Assign {
        Cast.exp_assign_lhs = f_name;
        Cast.exp_assign_rhs = rhs_var;
        Cast.exp_assign_pos = no_pos;
      } in
    let bexp = Cast.Bind {
        exp_bind_type = typ;
        exp_bind_bound_var = (CP.type_of_sv bvar, CP.name_of_sv bvar);
        exp_bind_fields = [bfield];
        exp_bind_body = body;
        exp_bind_imm = CP.NoAnn;
        exp_bind_param_imm = [];
        exp_bind_read_only = false;
        exp_bind_path_id = (-1, "bind");
        exp_bind_pos = no_pos;
      } in
    Some bexp
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
