#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

open Synthesis
open Rule_synthesis

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
             if CP.eq_spec_var sv1 sv &&
                List.exists (fun x -> CP.eq_spec_var x sv2) cur_vars
             then Some sv2
             else if CP.eq_spec_var sv2 sv &&
                     List.exists (fun x -> CP.eq_spec_var x sv1) cur_vars
             then Some sv1 else None
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

(* let choose_rule_pre_assign goal : rule list =
 *   let all_vars = goal.gl_vars in
 *   let post = goal.gl_post_cond in
 *   let pre = goal.gl_pre_cond in
 *   let pre_vars = CF.fv pre in
 *   let pre_pf = CF.get_pure pre in
 *   let pre_conjuncts = CP.split_conjunctions pre_pf in
 *   let eq_pairs = List.map (find_exists_substs pre_vars) pre_conjuncts
 *                  |> List.concat in
 *   let pr_pairs = pr_list (pr_pair pr_var pr_exp) in
 *   let filter_fun (x,y) =
 *     let vars = CP.afv y in
 *     not(CP.mem x all_vars) && vars != [] && CP.subset vars all_vars in
 *   let filter_eq = Gen.BList.remove_dups_eq
 *       (fun x1 x2 -> CP.eq_sv (fst x1) (fst x2)) in
 *   let eq_pairs = eq_pairs |> filter_eq |> List.filter filter_fun in
 *   let () = x_tinfo_hp (add_str "pairs" pr_pairs) eq_pairs no_pos in
 *   let mk_rule (var, exp) =
 *     RlPreAssign {
 *       rpa_lhs = var;
 *       rpa_rhs = exp
 *     } in
 *   List.map mk_rule eq_pairs *)

 (* let get_cond_exp prog formula base recursive puref vars =
  *  let conjuncs = CP.split_conjunctions puref in
  *  let aux pf =
  *    let n_bf = CF.add_pure_formula_to_formula pf formula in
  *    let n_pf = CP.mkNot_s pf in
  *    let n_rc = CF.add_pure_formula_to_formula n_pf formula in
  *    let fst = SB.check_entail_exact prog n_bf base in
  *    let snd = SB.check_entail_exact prog n_rc recursive in
  *    fst && snd in
  *  conjuncs |> List.filter (fun x -> CP.subset (CP.fv x) vars)
  *  |> List.filter aux *)


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
    if SB.check_unsat goal.gl_prog n_post then []
    else if (List.length pre_vars = List.length post_vars) (* &&
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

let find_frame_node_var goal all_vars post_var =
  let all_vars = List.filter (fun x -> not(CP.eq_sv x post_var)) all_vars in
  let () = x_tinfo_hp (add_str "post var" pr_var) post_var no_pos in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let pre_vars = get_node_vars pre in
  let pre_vars = List.filter (fun x -> not(CP.mem x all_vars)) pre_vars in
  let () = x_tinfo_hp (add_str "pre vars" pr_vars) pre_vars no_pos in
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
      let () = x_tinfo_hp (add_str "args1" pr_vars) args1 no_pos in
      let () = x_tinfo_hp (add_str "args2" pr_vars) args2 no_pos in
      List.exists2 helper_arg args1 args2
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
          let hf1 = bf1.CF.formula_base_heap in
          let hf2 = bf2.CF.formula_exists_heap in
          helper_hf hf1 hf2
        | _ -> false
      end
    | _ -> false in
  let frame_vars = pre_vars |> List.filter helper in
  frame_vars |> List.map (fun x -> (post_var, x))

let choose_rule_frame_data goal =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let post_vars = post |> get_node_vars in
  let () = x_tinfo_hp (add_str "post vars" pr_vars) post_vars no_pos in
  let pairs = post_vars |> List.map (find_frame_node_var goal post_vars)
              |> List.concat in
  let pr_pairs = pr_list (pr_pair pr_var pr_var) in
  let () = x_tinfo_hp (add_str "pairs" pr_pairs) pairs no_pos in
  let filter (lhs, rhs) =
    let n_pre, pre_vars = frame_var_formula pre rhs in
    let n_post, post_vars = frame_var_formula post lhs in
    let () = x_tinfo_hp (add_str "pre_vars" pr_vars) pre_vars no_pos in
    let () = x_tinfo_hp (add_str "post_vars" pr_vars) post_vars no_pos in
    if (List.length pre_vars = List.length post_vars) then
      let pre_cond_vars = pre |> CF.fv in
      if CP.mem lhs pre_cond_vars && not(CP.eq_sv lhs rhs) then []
      else
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

(* let choose_rule_exists_right goal =
 *   let post = goal.gl_post_cond in
 *   let exists_vars = CF.get_exists post in
 *   if exists_vars = [] then []
 *   else
 *     let post_pf = CF.get_pure goal.gl_post_cond in
 *     let post_conjuncts = CP.split_conjunctions post_pf in
 *     let eq_pairs = List.map (find_exists_substs exists_vars) post_conjuncts
 *                    |> List.concat in
 *     let collected_exists_vars = eq_pairs |> List.map fst |> CP.remove_dups_svl in
 *     if collected_exists_vars = [] then []
 *     else
 *       let n_post = remove_exists_vars post collected_exists_vars in
 *       let n_post = subst_term_formula eq_pairs n_post in
 *       let rule = RlExistsRight {n_post = n_post} in
 *       [rule] *)

let rec choose_rule_interact goal rules =
  if rules = [] then
    let () = x_binfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
    rules
  else
    let str = pr_list_ln pr_rule rules in
    let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
    let () = x_binfo_hp (add_str "Rules" pr_rules) rules no_pos in
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
        let () = x_binfo_hp (add_str "You chose" (pr_list_ln pr_rule))
            chosen_rules no_pos in
        chosen_rules @ other_rules

let choose_rule_free goal =
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let sk, residue = check_entail_wrapper goal.gl_prog pre post in
  if sk then
    let residue = Gen.unsome residue in
    if not(CF.is_emp_formula residue) then
      let pre_nodes = goal.gl_pre_cond |> get_heap |> get_heap_nodes in
      let post_nodes = goal.gl_post_cond |> get_heap |> get_heap_nodes in
      let pre_node_vars = pre_nodes |> List.map (fun (x, _,_) -> x) in
      let post_node_vars = post_nodes |> List.map (fun (x, _,_) -> x) in
      let free_vars = CP.diff_svl pre_node_vars post_node_vars in
      let in_vars x = CP.mem x goal.gl_vars in
      if free_vars != [] && List.for_all in_vars free_vars then
        let rule = RlFree {
            rd_vars = free_vars;
          } in
        [rule]
      else []
    else []
  else []

let choose_rule_fread_x goal =
  let vars, pre_cond = goal.gl_vars, goal.gl_pre_cond in
  let pre_node_vars = pre_cond |> get_heap |> get_heap_nodes
                      |> List.map (fun (x, _,_) -> x) in
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
  let pr_triples = pr_list (pr_triple pr_var pr_id pr_vars) in
  let () = x_tinfo_hp (add_str "triples" pr_triples) triples no_pos in
  let filter_rule rule =
    let var = rule.rfr_value in
    let () = x_tinfo_hp (add_str "var" pr_var) var no_pos in
    let n_goal = {goal with gl_vars = [var]} in
    let n_goal2 = {goal with gl_vars = var::goal.gl_vars} in
    let unfold_rules = choose_rule_unfold_pre n_goal in
    let fcall_rules = choose_rule_func_call n_goal2 in
    let fwrite_rules = choose_rule_fwrite n_goal2 in
    List.mem var pre_node_vars ||
    List.exists (rule_use_var var) fwrite_rules ||
    unfold_rules != [] || (List.exists (rule_use_var var) fcall_rules) in
  let helper_triple (var, data, args) =
    let prog = goal.gl_prog in
    let data = List.find (fun x -> x.Cast.data_name = data)
        prog.Cast.prog_data_decls in
    let d_args = data.Cast.data_fields |> List.map fst in
    let d_arg_pairs = List.combine args d_args in
    let filter_fun (x, _) = CP.mem x vars |> negate in
    let d_arg_pairs = List.filter filter_fun d_arg_pairs in
    let helper_arg (arg, field) =
      let rbind = {
          rfr_bound_var = var;
          rfr_field = field;
          rfr_value = arg;
        } in [rbind] in
    d_arg_pairs |> List.map helper_arg |> List.concat in
  List.map helper_triple triples |> List.concat
  |> List.filter (fun x -> is_fread_called goal.gl_trace x |> negate)
  |> List.filter filter_rule
  |> List.map (fun x -> RlFRead x) |> List.rev

let choose_rule_fread goal =
  Debug.no_1 "choose_rule_fread" pr_goal pr_rules
    (fun _ -> choose_rule_fread_x goal) goal

let choose_rule_allocate goal : rule list =
  let prog = goal.gl_prog in
  let all_vars = goal.gl_vars in
  let pre = goal.gl_pre_cond in
  let post = goal.gl_post_cond in
  let () = x_tinfo_hp (add_str "all vars" pr_vars) all_vars no_pos in
  let () = x_tinfo_hp (add_str "pre" pr_formula) goal.gl_pre_cond no_pos in
  let rec mk_args_input args = match args with
    | [] -> []
    | [h] -> List.map (fun x -> [x]) h
    | h::t -> let tmp = mk_args_input t in
      let head_added = List.map (fun x -> List.map (fun y -> [x]@y) tmp) h in
      List.concat head_added in
  let data_decls = prog.C.prog_data_decls in
  let others = ["__Exc"; "thrd"; "Object"; "int_ptr"; "barrier"] in
  let filter_fun x = not(List.mem x.C.data_name others) in
  let data_decls = data_decls |> List.filter filter_fun in
  let filter_rule rule =
    let n_pre = rule.ra_pre in
    let n_vars = rule.ra_var::goal.gl_vars in
    let n_goal = {goal with gl_vars = n_vars;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlAllocate rule)::goal.gl_trace} in
    let n_rules = [] in
    let n_rules = (choose_rule_assign n_goal) @ n_rules in
    let n_rules = (choose_rule_fwrite n_goal) @ n_rules in
    let n_rules = (choose_rule_return n_goal) @ n_rules in
    let n_rules = (choose_rule_frame_data n_goal) @ n_rules in
    let () = x_tinfo_hp (add_str "arg" pr_var) rule.ra_var no_pos in
    let () = x_tinfo_hp (add_str "pre" pr_formula) n_pre no_pos in
    let () = x_tinfo_hp (add_str "rules" pr_rules) n_rules no_pos in
    if List.exists (rule_use_var rule.ra_var) n_rules then
      let n_goal = {n_goal with gl_lookahead = n_rules} in
      let n_rule = {rule with ra_lookahead = Some n_goal} in
      (true, n_rule)
    else (false, rule) in
  let filter_eq_var rule =
    let params = rule.ra_params in
    let rec aux params = match params with
      | [] -> false
      | h :: tail -> if CP.mem h tail then true
        else aux tail in
    if aux params then false else true in
  let mk_rule data_decl args =
    let data = data_decl.C.data_name in
    let var_name = fresh_name () in
    let var = CP.mk_typed_sv (Named data) var_name in
    let hf = CF.mkDataNode var data args no_pos in
    let n_pre = add_h_formula_to_formula hf goal.gl_pre_cond in
    {
      ra_var = var;
      ra_data = data;
      ra_params = args;
      ra_pre = n_pre;
      ra_end = false;
      ra_lookahead = None;
    } in
  let eq_tuple tuple1 tuple2 =
    let commutative_int tuple1 tuple2 =
      let int_args1 = tuple1 |> List.filter is_int_var in
      let int_args2 = tuple2 |> List.filter is_int_var in
      CP.subset int_args1 int_args2 && CP.subset int_args2 int_args1 in
    let commutative_node tuple1 tuple2 =
      let node_args1 = tuple1 |> List.filter is_node_var in
      let node_args2 = tuple2 |> List.filter is_node_var in
      CP.subset node_args1 node_args2 && CP.subset node_args2 node_args1 in
    commutative_int tuple1 tuple2 && commutative_node tuple1 tuple2 in
  let aux data_decl =
    let args = data_decl.C.data_fields |> List.map fst
               |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let () = x_tinfo_hp (add_str "args" pr_vars) args no_pos in
    let arg_types = List.map CP.type_of_sv args in
    let helper_typ typ =
      all_vars |> List.filter (fun x -> CP.type_of_sv x = typ) in
    let args_list = arg_types |> List.map helper_typ in
    let args_groups = args_list |> mk_args_input in
    let filter_fun list = has_allocate goal.gl_trace list |> negate in
    let args_groups = args_groups |> List.filter filter_fun in
    let args_groups = args_groups |> Gen.BList.remove_dups_eq eq_tuple in
    let rules = args_groups |> List.map (mk_rule data_decl) in
    rules in
  if check_allocate goal pre post then
    let rules = data_decls |> List.map aux |> List.concat in
    let rules = rules |> List.filter filter_eq_var in
    let () = x_tinfo_hp (add_str "rules" (pr_list pr_rule_alloc)) rules no_pos in
    let rules = List.map filter_rule rules |> List.filter (fun (x,_) -> x)
                |> List.map snd in
    rules |> List.map (fun x -> RlAllocate x)
  else []

let choose_rule_mk_null goal : rule list =
  if has_mk_null goal.gl_trace then []
  else let trace = goal.gl_trace in
  if List.length trace > 2 then []
  else
    let pre = goal.gl_pre_cond in
    let post = goal.gl_post_cond in
    let prog = goal.gl_prog in
    let data_decls = prog.C.prog_data_decls in
    let others = ["__Exc"; "thrd"; "Object"; "__Error"; "__MayError"; "__Fail";
                  "char_star"; "int_ptr_ptr"; "int_ptr"; "lock"; "barrier";
                  "__RET"; "__ArrBoundErr"; "__DivByZeroErr"; "String"] in
    let filter_fun x = not(List.mem x.C.data_name others) in
    let data_decls = data_decls |> List.filter filter_fun in
    let aux_rule data_decl =
      let data_name = data_decl.C.data_name in
      let typ = Globals.Named data_name in
      let name = Globals.fresh_name () in
      let var = CP.mk_typed_sv typ name in
      let n_exp = CP.Null no_pos in
      let all_vars = var::goal.gl_vars in
      let var_e = CP.mkVar var no_pos in
      let pf = CP.mkEqExp var_e n_exp no_pos in
      let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
      let rule = {
        rmn_null = n_exp;
        rmn_var = var;
        rmn_lookahead = None;
      } in
      let n_goal = {goal with gl_vars = all_vars;
                              gl_pre_cond = n_pre;
                              gl_trace = (RlMkNull rule)::goal.gl_trace} in
      let () = x_tinfo_hp (add_str "var" pr_var) var no_pos in
      let n_rules = [] in
      let n_rules = n_rules @ (choose_rule_allocate n_goal) in
      let n_rules = n_rules @ (choose_rule_func_call n_goal) in
      let n_rules = n_rules @ (choose_rule_fwrite n_goal) in
      let n_goal = {n_goal with gl_lookahead = n_rules} in
      let () = x_tinfo_hp (add_str "rules" pr_rules) n_rules no_pos in
      let rule = {rule with rmn_lookahead = Some n_goal} in
      if List.exists (rule_use_var var) n_rules then
        (true, rule)
      else (false, rule) in
    let list = data_decls |> List.map aux_rule
               |> List.filter (fun (x,y) -> x)
               |> List.map snd in
    list |> List.map (fun x -> RlMkNull x)

let choose_rule_new_num goal : rule list =
  if has_new_num goal.gl_trace then []
  else
    let pre = goal.gl_pre_cond in
    let post = goal.gl_post_cond in
    let prog = goal.gl_prog in
    let int_vars = goal.gl_vars |> List.filter is_int_var in
    let aux_int var =
      let n_var = CP.fresh_spec_var var in
      let one = CP.mkIConst 1 no_pos in
      let n_var_e = CP.mkVar var no_pos in
      let minus_one = CP.mkSubtract n_var_e one no_pos in
      let plus_one = CP.mkAdd n_var_e one no_pos in
      let minus_rule = {
        rnn_var = n_var;
        rnn_num = minus_one;
        rnn_lookahead = None;
      } in
      let plus_rule = {
        rnn_var = n_var;
        rnn_num = plus_one;
        rnn_lookahead = None;
      } in
      [minus_rule; plus_rule] in
    let filter_rule rule =
      let n_exp = rule.rnn_num in
      let var = rule.rnn_var in
      let all_vars = var::goal.gl_vars in
      let var_e = CP.mkVar var no_pos in
      let pf = CP.mkEqExp var_e n_exp no_pos in
      let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
      let n_goal = {goal with gl_vars = all_vars;
                              gl_pre_cond = n_pre;
                              gl_trace = (RlNewNum rule)::goal.gl_trace} in
      let () = x_tinfo_hp (add_str "var" pr_var) var no_pos in
      let n_rules = choose_rule_allocate n_goal in
      let n_rules = n_rules @ (choose_rule_allocate_return n_goal) in
      let n_rules = n_rules @ (choose_rule_func_call n_goal) in
      let n_rules = n_rules @ (choose_rule_fwrite n_goal) in
      let () = x_tinfo_hp (add_str "rules" pr_rules) n_rules no_pos in
      if List.exists (rule_use_var var) n_rules then
        let n_goal = {n_goal with gl_lookahead = n_rules} in
        let n_rule = {rule with rnn_lookahead = Some n_goal} in
        (true, n_rule)
      else (false, rule) in
    let list = int_vars |> List.map aux_int |> List.concat in
    let list = list |> List.map filter_rule |> List.filter (fun (x,_) -> x)
               |> List.map snd in
    list |> List.map (fun x -> RlNewNum x)

let choose_all_rules rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_fwrite goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_func_call goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_post_assign goal) in
  let rs = rs @ (choose_rule_allocate goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_heap_assign goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_mk_null rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_post_assign goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_heap_assign goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_new_num rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_assign goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_post_assign goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_heap_assign goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_rules_after_allocate rs goal =
  let rs = rs @ (choose_rule_unfold_pre goal) in
  let rs = rs @ (choose_rule_frame_pred goal) in
  let rs = rs @ (choose_rule_fread goal) in
  let rs = rs @ (choose_rule_numeric goal) in
  let rs = rs @ (choose_rule_func_call goal) in
  let rs = rs @ (choose_rule_frame_data goal) in
  let rs = rs @ (choose_rule_post_assign goal) in
  let rs = rs @ (choose_rule_allocate goal) in
  let rs = rs @ (choose_rule_mk_null goal) in
  let rs = rs @ (choose_rule_new_num goal) in
  let rs = rs @ (choose_rule_heap_assign goal) in
  let rs = rs @ (choose_rule_unfold_post goal) in
  rs

let choose_main_rules goal =
  let cur_time = get_time () in
  let duration = cur_time -. goal.gl_start_time in
  if duration > !synthesis_timeout && not(!enable_i) then
    []
  else
    let rs = goal.gl_lookahead in
    let rs = if goal.gl_trace = [] then
        choose_all_rules rs goal
      else
        let head = List.hd goal.gl_trace in
        match head with
        | RlMkNull _ -> choose_rules_after_mk_null rs goal
        | RlNewNum _ -> choose_rules_after_new_num rs goal
        | RlAllocate _ -> choose_rules_after_allocate rs goal
        | _ -> choose_all_rules rs goal in
    let rs = eliminate_useless_rules goal rs in
    let rs = reorder_rules goal rs in
    rs


let mk_rule_free goal residue =
  let post = goal.gl_post_cond in
  let all_vars = goal.gl_vars in
  let pre_nodes = goal.gl_pre_cond |> get_heap |> get_heap_nodes in
  let post_nodes = goal.gl_post_cond |> get_heap |> get_heap_nodes in
  let pre_node_vars = pre_nodes |> List.map (fun (x, _,_) -> x) in
  let post_node_vars = post_nodes |> List.map (fun (x, _,_) -> x) in
  let free_vars = CP.diff_svl pre_node_vars post_node_vars in
  if free_vars != [] then
    let rule = RlFree {
        rd_vars = free_vars;
      } in
    [rule]
  else []

let choose_rule_skip goal =
  if is_code_rule goal.gl_trace then
    let prog, pre, post = goal.gl_prog, goal.gl_pre_cond, goal.gl_post_cond in
    try
      let sk, residue = check_entail_wrapper prog pre post in
      if sk then
        let residue = Gen.unsome residue in
        if CF.is_emp_formula residue then
          let rule = RlSkip in
          [rule]
        else mk_rule_free goal residue
      else []
    with _ -> []
  else []

let choose_synthesis_rules_x goal : rule list =
  let rules =
    try
      let _ = choose_rule_skip goal |> raise_rules in
      let _ = choose_rule_return goal |> raise_rules in
      let _ = choose_rule_allocate_return goal |> raise_rules in
      let _ = choose_main_rules goal |> raise_rules in
      []
    with ERules rs -> rs in
  rules

let choose_synthesis_rules goal =
  Debug.no_1 "choose_synthesis_rules" pr_goal pr_rules
    (fun _ -> choose_synthesis_rules_x goal) goal

(*********************************************************************
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rc =
  if rc.ra_numeric then   mk_derivation_success goal (RlAssign rc)
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let lhs, rhs = rc.ra_lhs, rc.ra_rhs in
    let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rhs no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pf pre in
    let post_vars = CF.fv post in
    let sub_goal = {goal with gl_pre_cond = n_pre;
                              gl_trace = (RlAssign rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlAssign rc) [sub_goal]

let process_rule_post_assign goal rc =
  let lhs = rc.rapost_lhs in
  let rhs = rc.rapost_rhs in
  let n_vars = lhs::goal.gl_vars in
  let n_post = remove_exists_vars goal.gl_post_cond [lhs] in
  let e_var = CP.mkVar lhs no_pos in
  let n_pf = CP.mkEqExp e_var rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf goal.gl_pre_cond in
  let sub_goal = {goal with gl_vars = n_vars;
                            gl_post_cond = n_post;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlPostAssign rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlPostAssign rc) [sub_goal]

let process_rule_return goal rc =
  let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
  let lhs = goal.gl_post_cond |> CF.fv |> List.find CP.is_res_sv in
  let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rc.r_exp no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf pre in
  let ent_check = check_entail_exact_wrapper goal.gl_prog n_pre post in
  match ent_check with
  | true ->
    let n_trace = (RlReturn rc)::goal.gl_trace in
    if check_trace_consistence n_trace then
      mk_derivation_success goal (RlReturn rc)
    else mk_derivation_fail goal (RlReturn rc)
  | false ->  mk_derivation_fail goal (RlReturn rc)

let subs_fwrite formula var field new_val data_decls =
  match (formula:CF.formula) with
  | Base bf -> let hf = bf.CF.formula_base_heap in
    let () = x_tinfo_hp (add_str "hf" Cprinter.string_of_h_formula) hf no_pos in
    let rec helper (hf:CF.h_formula) = match hf with
      | DataNode dnode ->
        let data_var = dnode.h_formula_data_node in
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

let process_rule_fwrite goal rc =
  let pre, var = goal.gl_pre_cond, rc.rfw_bound_var in
  let field, prog = rc.rfw_field, goal.gl_prog in
  let rhs, data_decls = rc.rfw_value, prog.prog_data_decls in
  let n_pre = subs_fwrite pre var field rhs data_decls in
  let n_goal = {goal with gl_pre_cond = n_pre;
                          gl_trace = (RlFWrite rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlFWrite rc) [n_goal]

let process_rule_fread goal rc =
    let vars = [rc.rfr_value] @ goal.gl_vars |> CP.remove_dups_svl in
    let n_goal = {goal with gl_vars = vars;
                            gl_trace = (RlFRead rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlFRead rc) [n_goal]

let aux_func_call goal rule fname params subst res_var residue =
  let residue = residue |> rm_emp_formula in
  let pre_cond, post_cond = goal.gl_pre_cond, goal.gl_post_cond in
  let proc_decl = goal.gl_proc_decls
                  |> List.find (fun x -> eq_str x.Cast.proc_name fname) in
  let specs = (proc_decl.Cast.proc_stk_of_static_specs # top) in
  (* TODO: fix this one *)
  let spec_pairs = get_pre_post specs in
  let post_proc = List.hd spec_pairs |> snd in
  let fun_args = proc_decl.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let substs = (List.combine fun_args params) @ subst in
  let params_post = CF.subst substs post_proc in
  let () = x_tinfo_hp (add_str "param_post" pr_formula) params_post no_pos in
  let evars = CF.get_exists params_post in
  let post_state = add_formula_to_formula residue params_post |> rm_emp_formula in
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

let process_rule_func_call goal rc : derivation =
  let fname, params = rc.rfc_fname, rc.rfc_params in
  let residue = rc.rfc_residue |> rm_emp_formula in
  aux_func_call goal (RlFuncCall rc) fname params rc.rfc_substs None residue

let process_rule_func_res goal rc : derivation =
  let fname, params = rc.rfr_fname, rc.rfr_params in
  let res_var = Some rc.rfr_return in
  let residue = rc.rfr_residue |> rm_emp_formula in
  aux_func_call goal (RlFuncRes rc) fname params rc.rfr_substs res_var residue

let process_rule_unfold_pre goal rc =
  let n_pres = rc.n_pre in
  let n_goal = {goal with gl_pre_cond = rc.n_pre;
                          gl_trace = (RlUnfoldPre rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPre rc) [n_goal]

let process_rule_frame_pred goal rc =
  let eq_pairs = rc.rfp_pairs in
  let eq_pairs = List.map (fun (x,y) -> (y,x)) eq_pairs in
  let () = x_tinfo_hp (add_str "substs" pr_substs) eq_pairs no_pos in
  let post = rc.rfp_post in
  let e_vars = eq_pairs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = remove_exists_vars post exists_vars in
  let n_post = CF.subst eq_pairs n_post in
  let n_exists_vars = CP.diff_svl exists_vars e_vars in
  let n_post = add_exists_vars n_post n_exists_vars in
  (* if SB.check_unsat goal.gl_prog n_post then
   *   mk_derivation_fail goal (RlFramePred rc)
   * else *)
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  let subgoal = {goal with gl_post_cond = n_post;
                           gl_trace = (RlFramePred rc)::goal.gl_trace;
                           gl_pre_cond = rc.rfp_pre} in
  mk_derivation_subgoals goal (RlFramePred rc) [subgoal]

let process_rule_frame_data goal rc =
  let substs = rc.rfd_pairs in
  let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) substs in
  let eq_pf = mkAndList eq_pairs in
  let post = rc.rfd_post in
  let substs = substs |> List.map (fun (x,y) -> (y,x)) in
  let () = x_tinfo_hp (add_str "substs" pr_substs) substs no_pos in
  let e_vars = substs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = remove_exists_vars post exists_vars in
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  let n_post = CF.subst substs n_post in
  let e_vars = CP.diff_svl exists_vars e_vars in
  let n_post = add_exists_vars n_post e_vars in
  let () = x_tinfo_hp (add_str "n_post" pr_formula) n_post no_pos in
  let subgoal = {goal with gl_post_cond = n_post;
                           gl_trace = (RlFrameData rc)::goal.gl_trace;
                           gl_pre_cond = rc.rfd_pre} in
  mk_derivation_subgoals goal (RlFrameData rc) [subgoal]

let process_rule_unfold_post goal rc =
  let n_goal = {goal with gl_post_cond = rc.rp_case_formula;
                          gl_trace = (RlUnfoldPost rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPost rc) [n_goal]

let process_rule_skip goal =
  if is_code_rule goal.gl_trace then
    mk_derivation_success goal RlSkip
  else mk_derivation_fail goal RlSkip

let process_rule_free goal rc =
  mk_derivation_success goal (RlFree rc)

let process_rule_mk_null goal rc =
  match rc.rmn_lookahead with
  | Some n_goal -> mk_derivation_subgoals goal (RlMkNull rc) [n_goal]
  | None ->
    let n_exp = rc.rmn_null in
    let var = rc.rmn_var in
    let all_vars = var::goal.gl_vars in
    let var_e = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_e n_exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
    let n_goal = {goal with gl_vars = all_vars;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlMkNull rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlMkNull rc) [n_goal]

let process_rule_new_num goal rc =
  match rc.rnn_lookahead with
  | Some n_goal -> mk_derivation_subgoals goal (RlNewNum rc) [n_goal]
  | None ->
    let n_exp = rc.rnn_num in
    let var = rc.rnn_var in
    let all_vars = var::goal.gl_vars in
    let var_e = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_e n_exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
    let n_goal = {goal with gl_vars = all_vars;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlNewNum rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlNewNum rc) [n_goal]

let process_rule_allocate goal rc =
  if rc.ra_end then
    mk_derivation_success goal (RlAllocate rc)
  else
    match rc.ra_lookahead with
    | Some n_goal -> mk_derivation_subgoals goal (RlAllocate rc) [n_goal]
    | None ->
      let data = rc.ra_data in
      let params = rc.ra_params in
      let var = rc.ra_var in
      let hf = CF.mkDataNode var data params no_pos in
      let n_pre = add_h_formula_to_formula hf goal.gl_pre_cond in
      let n_goal = {goal with gl_vars = var::goal.gl_vars;
                              gl_pre_cond = n_pre;
                              gl_trace = (RlAllocate rc)::goal.gl_trace} in
      mk_derivation_subgoals goal (RlAllocate rc) [n_goal]

let process_rule_heap_assign goal rc =
  let lhs = rc.rha_left in
  let rhs = rc.rha_right in
  let n_pf = CP.mkEqVar lhs rhs no_pos in
  let n_pre = CF.add_pure_formula_to_formula n_pf goal.gl_pre_cond in
  let n_goal = {goal with gl_trace = (RlHeapAssign rc)::goal.gl_trace;
                          gl_pre_cond = n_pre} in
  mk_derivation_subgoals goal (RlHeapAssign rc) [n_goal]

(*********************************************************************
 * The search procedure
 *********************************************************************)
let rec synthesize_one_goal goal : synthesis_tree =
  let goal = simplify_goal goal in
  let trace = goal.gl_trace in
  if num_of_code_rules trace > 2 || length_of_trace trace > 3
     || List.length trace > 8
  then
    let () = x_binfo_pp "MORE THAN NUMBER OF RULES ALLOWED" no_pos in
    mk_synthesis_tree_fail goal [] "more than number of rules allowed"
  else
    let cur_time = get_time () in
    let duration = cur_time -. goal.gl_start_time in
    if duration > !synthesis_timeout && not(!enable_i) then
      mk_synthesis_tree_fail goal [] "TIMEOUT"
    else
      let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
      let rules = choose_synthesis_rules goal in
      process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  let rec process atrees rules =
    let rules = if !enable_i then choose_rule_interact goal rules
      else rules in
    match rules with
    | rule::other_rules ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      let atrees = atrees @ [stree] in
      if is_synthesis_tree_success stree then
        let pts = get_synthesis_tree_status stree in
        mk_synthesis_tree_search goal atrees pts
      else process atrees other_rules
    | [] ->
      let () = fail_branch_num := !fail_branch_num + 1 in
      let () = x_tinfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
      mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_one_rule goal rule : derivation =
  let () = x_tinfo_hp (add_str "processing rule" pr_rule) rule no_pos in
  let cur_time = get_time () in
  let duration = cur_time -. goal.gl_start_time in
  let () = x_tinfo_pp "marking" no_pos in
  if duration > !synthesis_timeout && not(!enable_i) then
    mk_derivation_fail goal rule
  else
    match rule with
    | RlFuncCall rc -> process_rule_func_call goal rc
    | RlAllocate rc -> process_rule_allocate goal rc
    | RlFuncRes rc -> process_rule_func_res goal rc
    | RlPostAssign rc -> process_rule_post_assign goal rc
    | RlAssign rc -> process_rule_assign goal rc
    | RlReturn rc -> process_rule_return goal rc
    | RlFWrite rc -> process_rule_fwrite goal rc
    | RlUnfoldPre rc -> process_rule_unfold_pre goal rc
    | RlUnfoldPost rc -> process_rule_unfold_post goal rc
    | RlFRead rc -> process_rule_fread goal rc
    | RlFramePred rc -> process_rule_frame_pred goal rc
    | RlFrameData rc -> process_rule_frame_data goal rc
    | RlSkip -> process_rule_skip goal
    | RlMkNull rc -> process_rule_mk_null goal rc
    | RlNewNum rc -> process_rule_new_num goal rc
    | RlHeapAssign rc -> process_rule_heap_assign goal rc
    | RlFree rc -> process_rule_free goal rc

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
  let goal = simplify_goal goal in
  let () = x_binfo_hp (add_str "goal" pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = get_synthesis_tree_status st in
  let () = x_tinfo_hp (add_str "synthesis tree " pr_st) st no_pos in
  match st_status with
  | StValid st_core ->
    (* let st_core = rm_useless_stc st_core in *)
    let () = x_binfo_hp (add_str "tree_core " pr_st_core) st_core no_pos in
    let i_exp = synthesize_st_core st_core in
    let () = x_tinfo_hp (add_str "iast exp" pr_i_exp_opt) i_exp no_pos in
    i_exp
  | StUnkn _ -> let () = x_binfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
    let () = x_binfo_hp (add_str "fail branches" pr_int) (!fail_branch_num) no_pos in
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

let synthesize_wrapper iprog prog proc pre_cond post_cond vars called_procs num =
  let goal = mk_goal_w_procs prog called_procs pre_cond post_cond vars in
  let () = x_tinfo_hp (add_str "goal" pr_goal) goal no_pos in
  let start_time = get_time () in
  let iast_exp = synthesize_program goal in
  let duration = get_time () -. start_time in
  let () = synthesis_time := (!synthesis_time) +. duration in
  let pname, i_procs = proc.Cast.proc_name, iprog.Iast.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.Iast.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, false)
    | Some exp0 -> (replace_exp_proc exp0 i_proc num, true) in
  let n_iprocs = List.map (fun x -> if contains pname x.Iast.proc_name
                            then n_proc else x) i_procs in
  ({iprog with I.prog_proc_decls = n_iprocs}, res)

let synthesize_block_wrapper prog orig_proc proc pre_cond post_cond vars =
  (* let all_vars = (CF.fv pre_cond) @ (CF.fv post_cond) in *)
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

let get_spec_from_hps prog hps =
  let post_hp = List.find (fun x -> x.Cast.hp_name = "N_Q1") hps in
  let pre_hp = List.find (fun x -> x.Cast.hp_name = "N_P1") hps in
  let post = post_hp.Cast.hp_formula in
  let pre = pre_hp.Cast.hp_formula |> remove_exists in
  let post = rm_unk_type_formula prog post in
  let () = x_tinfo_hp (add_str "pre" pr_formula) pre no_pos in
  let () = x_tinfo_hp (add_str "post" pr_formula) post no_pos in
  (pre,post)

let compare_spec (pre1, _) (pre2, _) =
  let hf1 = get_hf pre1 in
  let hf2 = get_hf pre2 in
  let hf1_vars = CF.h_fv hf1 in
  let hf2_vars = CF.h_fv hf2 in
  if List.length hf1_vars > List.length hf2_vars then PriHigh
  else if List.length hf2_vars > List.length hf1_vars then PriLow
  else PriEqual

let synthesize_entailments_one (iprog:IA.prog_decl) prog proc proc_names =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  match hps with
  | None -> ()
  | Some hps_list ->
    let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
        iprog.IA.prog_proc_decls in
    let decl_vars = match iproc.IA.proc_body with
      | None -> []
      | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
    let syn_vars = proc.Cast.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let stop = ref false in
    let helper (pre, post) =
      if !stop then ()
      else
        if isHFalse post then
          let () = x_binfo_hp (add_str "post" pr_formula) post no_pos in
          ()
        else
          let all_procs = CA.list_of_procs prog in
          let filter_fun proc =
            let proc_name = proc.CA.proc_name |> CA.unmingle_name in
            List.mem proc_name proc_names in
          let called_procs = List.filter filter_fun all_procs in
          let (n_iprog, res) = synthesize_wrapper iprog prog proc
              pre post syn_vars called_procs 1 in
          if res then
            try
              let cprog, _ = Astsimp.trans_prog n_iprog in
              let () = Typechecker.check_prog_wrapper n_iprog cprog in
              let () = stop := true in
              repair_res := Some n_iprog
            with _ -> ()
          else () in
    if hps_list = [] then ()
    else
      (* let hps = List.hd hps_list in
       * helper hps *)
      let spec_list = List.map (get_spec_from_hps prog) hps_list in
      let ranking_specs specs =
        let cmp_spec spec1 spec2 =
          let prio = compare_spec spec1 spec2 in
          match prio with
          | PriEqual -> 0
          | PriLow -> +1
          | PriHigh -> -1 in
        List.sort cmp_spec specs in
      let spec_list = ranking_specs spec_list in
      let spec = List.hd spec_list in
      (* List.iter helper spec_list *)
      helper spec

let synthesize_entailments_two (iprog:IA.prog_decl) prog proc proc_names =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_two prog entailments in
  let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
      iprog.IA.prog_proc_decls in
  let decl_vars = match iproc.IA.proc_body with
    | None -> []
    | Some exp -> get_var_decls (Gen.unsome !repair_pos) exp in
  let syn_vars = proc.Cast.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
  let helper iprog hps num =
    let post_hp = if num = 1 then
        List.find (fun x -> x.Cast.hp_name = "N_Q1") hps
      else List.find (fun x -> x.Cast.hp_name = "N_Q2") hps in
    let pre_hp = if num = 1 then
        List.find (fun x -> x.Cast.hp_name = "N_P1") hps
      else List.find (fun x -> x.Cast.hp_name = "N_P2") hps in
    let post = post_hp.Cast.hp_formula in
    let post = rm_unk_type_formula prog post in
    let pre = pre_hp.Cast.hp_formula |> remove_exists in
    let all_procs = CA.list_of_procs prog in
    let filter_fun proc =
      let proc_name = proc.CA.proc_name |> CA.unmingle_name in
      List.mem proc_name proc_names in
    let called_procs = List.filter filter_fun all_procs in
    let (n_iprog, res) = synthesize_wrapper iprog prog proc
        pre post syn_vars called_procs num in
    (n_iprog, res) in
  match hps with
  | None -> None
  | Some (hps1, hps2) ->
    let hp1 = List.hd hps1 in
    let (n_iprog, res) = helper iprog hp1 1 in
    if res then
      let hp2 = List.hd hps2 in
      let (n_iprog, res) = helper n_iprog hp2 2 in
      if res then Some n_iprog
      else None
    else None


let statement_search (iprog: IA.prog_decl) prog proc (suspicious: I.exp)
    candidates =
  (* let ents = !Synthesis.entailments |> List.rev in *)
  (* let triples = !Synthesis.triples |> List.rev in *)
  (* let hps = prog.CA.prog_hp_decls @ !unk_hps in
   * let hps = Gen.BList.remove_dups_eq eq_hp_decl hps in
   * let s_goal = Searcher.mk_search_goal iprog prog proc triples in
   * let _ = Searcher.solve_unknown_hp s_goal candidates in *)
  None

let synthesize_block_statements iprog prog orig_proc proc decl_vars =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
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
        x_tinfo_hp (add_str "o_body" pr_c_exp) orig_body no_pos;
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
    let hp = hps_list |> List.hd in
    helper None hp
(* List.fold_left helper None hps_list *)

let infer_block_specs (iprog:IA.prog_decl) prog proc =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
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

