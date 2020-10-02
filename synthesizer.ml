#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Mcpure

(* open Synthesis *)
open Rule_synthesis

module CA = Cast
module IA = Iast
module CF = Cformula
module CP = Cpure
module SB = Songbird
module Syn = Synthesis

(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of Syn.synthesis_tree

let raise_stree st = raise (EStree st)


(*********************************************************************
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rc =
  if rc.Syn.ra_numeric then Syn.mk_derivation_success goal (RlAssign rc)
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let lhs, rhs = rc.ra_lhs, rc.ra_rhs in
    let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rhs no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pf pre in
    let sub_goal = {goal with gl_pre_cond = n_pre;
                              gl_trace = (RlAssign rc)::goal.gl_trace} in
    Syn.mk_derivation_subgoals goal (RlAssign rc) [sub_goal]

let process_rule_return goal rc =
  let checked = rc.Syn.r_checked in
  if checked then
    Syn.mk_derivation_success goal (RlReturn rc)
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let lhs = goal.gl_post_cond |> CF.fv |> List.find CP.is_res_sv in
    let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rc.r_exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pf pre in
    let ent_check = check_entail_exact_wrapper goal.gl_prog n_pre post in
    match ent_check with
    | true ->
      let n_trace = (Syn.RlReturn rc)::goal.gl_trace in
      if Syn.check_trace_consistence n_trace then
        Syn.mk_derivation_success goal (RlReturn rc)
      else Syn.mk_derivation_fail goal (RlReturn rc)
    | false -> Syn.mk_derivation_fail goal (RlReturn rc)

let process_rule_fwrite goal rc =
  let aux_fun formula var field new_val data_decls =
    match (formula:CF.formula) with
    | CF.Base bf -> let hf = bf.CF.formula_base_heap in
      let () = x_tinfo_hp (add_str "hf" Syn.pr_hf) hf no_pos in
      let rec helper (hf:CF.h_formula) = match hf with
        | CF.DataNode dnode ->
          let data_var = dnode.h_formula_data_node in
          if CP.eq_spec_var data_var var then
            let n_dnode = Syn.set_field dnode field new_val data_decls in
            (CF.DataNode n_dnode)
          else hf
        | CF.Star sf ->
          let n_h1 = helper sf.CF.h_formula_star_h1 in
          let n_h2 = helper sf.CF.h_formula_star_h2 in
          CF.Star {sf with CF.h_formula_star_h1 = n_h1;
                           CF.h_formula_star_h2 = n_h2}
        | _ -> hf in
      CF.Base {bf with formula_base_heap = helper hf}
    | _ -> formula in
  let pre, var = goal.Syn.gl_pre_cond, rc.Syn.rfw_bound_var in
  let field, prog = rc.Syn.rfw_field, goal.Syn.gl_prog in
  let rhs, data_decls = rc.rfw_value, prog.prog_data_decls in
  let n_pre = aux_fun pre var field rhs data_decls in
  let ent, _ = check_entail_wrapper goal.gl_prog
      n_pre goal.gl_post_cond in
  if ent then
    (* let residue = Gen.unsome residue in
     * if CF.is_emp_formula residue then *)
      Syn.mk_derivation_success goal (Syn.RlFWrite rc)
    (* else
     *   let free_vars = Syn.get_heap_variables residue in
     *   let n_rc = {rc with rfw_fvars = free_vars} in
     *   Syn.mk_derivation_success goal (Syn.RlFWrite n_rc) *)
  else
    Syn.mk_derivation_fail goal (Syn.RlFWrite rc)

let process_rule_fread goal rc =
  match rc.Syn.rfr_lookahead with
  | Some n_goal -> Syn.mk_derivation_subgoals goal (Syn.RlFRead rc) [n_goal]
  | None ->
    let vars = [rc.rfr_value] @ goal.gl_vars |> CP.remove_dups_svl in
    let n_goal = {goal with Syn.gl_vars = vars;
                            Syn.gl_trace = (RlFRead rc)::goal.Syn.gl_trace} in
    Syn.mk_derivation_subgoals goal (RlFRead rc) [n_goal]

let process_rule_func_call goal rc : Syn.derivation =
  let n_pre = rc.Syn.rfc_new_pre |> Syn.remove_exists in
  (* if check_entail_exact_wrapper goal.gl_prog n_pre goal.gl_post_cond then
   *   mk_derivation_success goal (RlFuncCall rc)
   * else *)
  let n_vars = match rc.rfc_return with
    | None -> goal.Syn.gl_vars
    | Some var -> var::goal.Syn.gl_vars in
  let n_goal = {goal with gl_trace = (RlFuncCall rc)::goal.gl_trace;
                          gl_lookahead = [];
                          gl_vars = n_vars;
                          gl_pre_cond = n_pre} in
  match rc.Syn.rfc_return with
  | Some _ ->
    Syn.mk_derivation_subgoals goal (RlFuncCall rc) [n_goal]
  | None ->
    let prog, pre, post = n_goal.Syn.gl_prog,
                          n_goal.Syn.gl_pre_cond,
                          n_goal.Syn.gl_post_cond in
    let sk, residue = check_entail_wrapper prog pre post in
    if sk then
      let residue = Gen.unsome residue in
      if CF.is_emp_formula residue then
        Syn.mk_derivation_success goal (RlFuncCall rc)
      else
        Syn.mk_derivation_fail goal (RlFuncCall rc)
    else
      Syn.mk_derivation_fail goal (RlFuncCall rc)

let process_rule_unfold_pre goal rc =
  (* let n_pres = rc.Syn.n_pre in *)
  let n_goal = {goal with Syn.gl_pre_cond = rc.Syn.n_pre;
                          Syn.gl_lookahead = [];
                          Syn.gl_trace = (Syn.RlUnfoldPre rc)::goal.Syn.gl_trace} in
  Syn.mk_derivation_subgoals goal (RlUnfoldPre rc) [n_goal]

let process_rule_frame_pred goal rc =
  (* let eq_pairs = rc.rfp_pairs in
   * let eq_pairs = List.map (fun (x,y) -> (y,x)) eq_pairs in
   * let post = rc.rfp_post in
   * let e_vars = eq_pairs |> List.map fst in
   * let exists_vars = CF.get_exists post in
   * let n_post = remove_exists_vars post exists_vars in
   * let n_post = CF.subst eq_pairs n_post in
   * let n_exists_vars = CP.diff_svl exists_vars e_vars in
   * let n_post = add_exists_vars n_post n_exists_vars in
   * let () = x_tinfo_hp (add_str "n_post" pr_f) n_post no_pos in *)
  let subgoal = {goal with Syn.gl_post_cond = rc.Syn.rfp_post;
                           Syn.gl_trace = (RlFramePred rc)::goal.Syn.gl_trace;
                           Syn.gl_pre_cond = rc.Syn.rfp_pre} in
  Syn.mk_derivation_subgoals goal (Syn.RlFramePred rc) [subgoal]

let process_rule_frame_data goal rc =
  let substs = rc.Syn.rfd_pairs in
  (* let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) substs in *)
  (* let eq_pf = Syn.mkAndList eq_pairs in *)
  let post = rc.Syn.rfd_post in
  let substs = substs |> List.map (fun (x,y) -> (y,x)) in
  let e_vars = substs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = Syn.remove_exists_vars post exists_vars in
  let n_post = CF.subst substs n_post in
  let e_vars = CP.diff_svl exists_vars e_vars in
  let n_post = Syn.add_exists_vars n_post e_vars in
  let subgoal = {goal with Syn.gl_post_cond = n_post;
                           Syn.gl_trace = (Syn.RlFrameData rc)::goal.Syn.gl_trace;
                           Syn.gl_pre_cond = rc.rfd_pre} in
  Syn.mk_derivation_subgoals goal (RlFrameData rc) [subgoal]

let process_rule_unfold_post goal rc =
  let n_goal = {goal with Syn.gl_post_cond = rc.Syn.rp_case_formula;
                          Syn.gl_trace = (Syn.RlUnfoldPost rc)::goal.Syn.gl_trace} in
  Syn.mk_derivation_subgoals goal (RlUnfoldPost rc) [n_goal]

let process_rule_skip goal =
  (* in case trace is [], then deleting the buggy statement is sufficient to fix
     it *)
  match goal.Syn.gl_trace with
  | [] -> Syn.mk_derivation_success goal Syn.RlSkip
  | _ ->
    if Syn.is_code_rule goal.Syn.gl_trace then
      Syn.mk_derivation_success goal Syn.RlSkip
    else Syn.mk_derivation_fail goal Syn.RlSkip

let process_rule_free goal rc =
  Syn.mk_derivation_success goal (Syn.RlFree rc)

let process_rule_mk_null goal rc =
  match rc.Syn.rmn_lookahead with
  | Some n_goal -> Syn.mk_derivation_subgoals goal (RlMkNull rc) [n_goal]
  | None ->
    let n_exp = rc.Syn.rmn_null in
    let var = rc.Syn.rmn_var in
    let all_vars = var::goal.Syn.gl_vars in
    let var_e = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_e n_exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
    let n_post = Syn.remove_exists_vars goal.gl_post_cond [var] in
    let n_goal = {goal with gl_vars = all_vars;
                            gl_pre_cond = n_pre;
                            gl_post_cond = n_post;
                            gl_trace = (RlMkNull rc)::goal.gl_trace} in
    Syn.mk_derivation_subgoals goal (RlMkNull rc) [n_goal]

let process_rule_new_num goal rc =
  match rc.Syn.rnn_lookahead with
  | Some n_goal -> Syn.mk_derivation_subgoals goal (RlNewNum rc) [n_goal]
  | None ->
    let n_exp = rc.rnn_num in
    let var = rc.rnn_var in
    let all_vars = var::goal.Syn.gl_vars in
    let var_e = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_e n_exp no_pos in
    let n_pre = CF.add_pure_formula_to_formula pf goal.gl_pre_cond in
    let n_goal = {goal with gl_vars = all_vars;
                            gl_pre_cond = n_pre;
                            gl_trace = (RlNewNum rc)::goal.Syn.gl_trace} in
    Syn.mk_derivation_subgoals goal (RlNewNum rc) [n_goal]

let process_rule_allocate goal rc =
  if rc.Syn.ra_end then
    Syn.mk_derivation_success goal (Syn.RlAllocate rc)
  else
    match rc.Syn.ra_lookahead with
    | Some n_goal -> Syn.mk_derivation_subgoals goal (RlAllocate rc) [n_goal]
    | None ->
      let data = rc.ra_data in
      let params = rc.ra_params in
      let var = rc.ra_var in
      let hf = CF.mkDataNode var data params no_pos in
      let n_pre = Syn.add_h_formula_to_formula hf goal.Syn.gl_pre_cond in
      let n_goal = {goal with gl_vars = var::goal.gl_vars;
                              gl_pre_cond = n_pre;
                              gl_trace = (RlAllocate rc)::goal.gl_trace} in
      Syn.mk_derivation_subgoals goal (RlAllocate rc) [n_goal]

(*********************************************************************
 * The search procedure
 *********************************************************************)

let rec synthesize_one_goal goal : Syn.synthesis_tree =
  (* let goal = simplify_goal goal in *)
  let trace = goal.Syn.gl_trace in
  if (Syn.num_of_code_rules trace > 2) ||
     (Syn.stop_mk_null trace) ||
     (Syn.length_of_trace trace > 3) ||
     (List.length trace > 8)
  then
    let () = x_tinfo_pp "MORE THAN NUMBER OF RULES ALLOWED" no_pos in
    Syn.mk_synthesis_tree_fail goal [] "more than number of rules allowed"
  else
    let cur_time = get_time () in
    let duration = cur_time -. goal.gl_start_time in
    if duration > !synthesis_timeout && not(!enable_i) then
      Syn.mk_synthesis_tree_fail goal [] "TIMEOUT"
    else
      let () = x_tinfo_hp (add_str "goal" Syn.pr_goal) goal no_pos in
      let rules = choose_synthesis_rules goal in
      process_all_rules goal rules

and process_all_rules goal rules : Syn.synthesis_tree =
  let rec process atrees rules =
    let rules = if !enable_i then choose_rule_interact goal rules
      else rules in
    match rules with
    | rule::other_rules ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      let atrees = atrees @ [stree] in
      if Syn.is_synthesis_tree_success stree then
        let pts = Syn.get_synthesis_tree_status stree in
        Syn.mk_synthesis_tree_search goal atrees pts
      else process atrees other_rules
    | [] ->
      let () = Syn.fail_branch_num := !Syn.fail_branch_num + 1 in
      let () = x_tinfo_hp (add_str "LEAVE NODE: " pr_id) "BACKTRACK" no_pos in
      Syn.mk_synthesis_tree_fail goal atrees "no rule can be applied" in
  process [] rules

and process_one_rule goal rule : Syn.derivation =
  let () = x_tinfo_hp (add_str "processing rule" Syn.pr_rule) rule no_pos in
  let cur_time = get_time () in
  let duration = cur_time -. goal.gl_start_time in
  let () = x_tinfo_pp "marking" no_pos in
  if duration > !synthesis_timeout && not(!enable_i) then
    Syn.mk_derivation_fail goal rule
  else
    match rule with
    | RlFuncCall rc -> process_rule_func_call goal rc
    | RlAllocate rc -> process_rule_allocate goal rc
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
    | RlFree rc -> process_rule_free goal rc

and process_conjunctive_subgoals goal rule (sub_goals: Syn.goal list)
  : Syn.synthesis_tree =
  let rec helper goals subtrees st_cores =
    match goals with
    | sub_goal::other_goals ->
      let syn_tree = synthesize_one_goal sub_goal in
      let status = Syn.get_synthesis_tree_status syn_tree in
      begin
        match status with
        | StUnkn _ -> Syn.mk_synthesis_tree_fail goal [] "one of subgoals failed"
        | StValid st_core ->
          helper other_goals (subtrees@[syn_tree]) (st_cores@[st_core])
      end
    | [] ->
      let st_core = Syn.mk_synthesis_tree_core goal rule st_cores in
      Syn.mk_synthesis_tree_derive goal rule subtrees (StValid st_core)
  in helper sub_goals [] []

and process_one_derivation drv : Syn.synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> Syn.mk_synthesis_tree_fail goal [] "unknown"
  | DrvStatus true -> Syn.mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs

(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)
let synthesize_program goal =
  let goal = Syn.simplify_goal goal in
  let rec simplify goal =
    let unfold_post_rules = choose_rule_unfold_post goal in
    if List.length unfold_post_rules = 1 then
      let rule = List.hd unfold_post_rules in
      match rule with
      | Syn.RlUnfoldPost rc ->
        let n_goal =
          {goal with Syn.gl_post_cond = rc.Syn.rp_case_formula} in
        simplify n_goal
      | _ -> goal
    else goal in
  let goal = simplify goal in
  (* TODO: to print info *)
  let () = x_binfo_hp (add_str "goal" Syn.pr_goal) goal no_pos in
  let st = synthesize_one_goal goal in
  let st_status = Syn.get_synthesis_tree_status st in
  (* TODO: to print info *)
  let () = x_binfo_hp (add_str "synthesis tree " Syn.pr_st) st no_pos in
  match st_status with
  | StValid st_core ->
    let () = x_tinfo_hp (add_str "tree_core " Syn.pr_st_core) st_core no_pos in
    let i_exp = Syn.synthesize_st_core st_core in
    let () = x_tinfo_hp (add_str "iast exp" Syn.pr_i_exp_opt) i_exp no_pos in
    i_exp
  | StUnkn _ -> let () = x_tinfo_pp "SYNTHESIS PROCESS FAILED" no_pos in
    let () = x_tinfo_hp (add_str "fail branches" Syn.pr_int) (!Syn.fail_branch_num) no_pos in
    None

let synthesize_wrapper iprog prog proc pre_cond post_cond vars called_procs num =
  let goal = Syn.mk_goal prog called_procs pre_cond post_cond vars in
  let () = x_tinfo_hp (add_str "goal" Syn.pr_goal) goal no_pos in
  let start_time = get_time () in
  let iast_exp = synthesize_program goal in
  let duration = get_time () -. start_time in
  let () = Syn.synthesis_time := (!Syn.synthesis_time) +. duration in
  let pname, i_procs = proc.CA.proc_name, iprog.IA.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.IA.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, None)
    | Some exp0 -> (Syn.replace_exp_proc exp0 i_proc num, iast_exp) in
  let n_iprocs = List.map (fun x -> if contains pname x.IA.proc_name
                            then n_proc else x) i_procs in
  ({iprog with IA.prog_proc_decls = n_iprocs}, res)

let get_spec_from_hps prog num hps =
  let num_str = string_of_int num in
  let pre_hp = List.find (fun x -> x.CA.hp_name = ("N_P" ^ num_str)) hps in
  let post_hp = List.find (fun x -> x.CA.hp_name = ("N_Q" ^ num_str)) hps in
  let post = post_hp.CA.hp_formula in
  let pre = pre_hp.CA.hp_formula |> Syn.remove_exists in
  let () = x_tinfo_hp (add_str "pre" Syn.pr_f) pre no_pos in
  let () = x_tinfo_hp (add_str "post" Syn.pr_f) post no_pos in
  (pre,post)

let compare_spec (pre1, _) (pre2, _) =
  let hf1 = Syn.get_hf pre1 in
  let hf2 = Syn.get_hf pre2 in
  let hf1_vars = CF.h_fv hf1 in
  let hf2_vars = CF.h_fv hf2 in
  if List.length hf1_vars > List.length hf2_vars then Syn.PriHigh
  else if List.length hf2_vars > List.length hf1_vars then Syn.PriLow
  else PriEqual

let ranking_specs specs =
  let cmp_spec spec1 spec2 =
    let prio = compare_spec spec1 spec2 in
    match prio with
    | Syn.PriEqual -> 0
    | Syn.PriLow -> +1
    | Syn.PriHigh -> -1 in
  List.sort cmp_spec specs

let synthesize_entailments_one (iprog:IA.prog_decl) prog proc proc_names =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  match hps with
  | None -> None
  | Some hps_list ->
    let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
        iprog.IA.prog_proc_decls in
    let decl_vars = match iproc.IA.proc_body with
      | None -> []
      | Some exp -> Syn.get_var_decls (Gen.unsome !Syn.repair_pos) exp in
    let syn_vars = proc.CA.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let helper pre_res (pre, post) =
      if pre_res != None then pre_res
      else
        if Syn.isHFalseOrEmp pre post then
          let () = x_tinfo_hp (add_str "post" Syn.pr_f) post no_pos in
          None
        else
          let all_procs = CA.list_of_procs prog in
          let filter_fun proc =
            let proc_name = proc.CA.proc_name |> CA.unmingle_name in
            List.mem proc_name proc_names in
          let called_procs = List.filter filter_fun all_procs in
          let (n_iprog, res) = synthesize_wrapper iprog prog proc
              pre post syn_vars called_procs 1 in
          if res != None then
            try
              let cprog, _ = Astsimp.trans_prog n_iprog in
              let () = Typechecker.check_prog_wrapper n_iprog cprog in
              let () = Syn.repair_res := Some n_iprog in
              res
            with _ -> None
          else None in
    if hps_list = [] then None
    else
      let spec_list = List.map (get_spec_from_hps prog 1) hps_list in
      let spec_list = ranking_specs spec_list in
      let pr_specs = pr_list (pr_pair Syn.pr_f Syn.pr_f) in
      let () = x_tinfo_hp (add_str "spec" pr_specs) spec_list no_pos in
      (* let spec = List.hd spec_list in *)
      List.fold_left helper None spec_list
      (* helper spec *)

let synthesize_entailments_two (iprog:IA.prog_decl) prog proc proc_names =
  let fst_pos = 1 in
  let snd_pos = 2 in
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_two prog entailments in
  let iproc = List.find (fun x -> contains proc.CA.proc_name x.IA.proc_name)
      iprog.IA.prog_proc_decls in
  let syn_vars = proc.CA.proc_args |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let helper (pre, post) num =
    let decl_vars =
      let proc_body = iproc.IA.proc_body |> Gen.unsome in
      if num = fst_pos then
        Syn.get_var_decls (Gen.unsome !Syn.repair_pos_fst) proc_body
      else if num = snd_pos then
        Syn.get_var_decls (Gen.unsome !Syn.repair_pos_snd) proc_body
      else [] in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let all_procs = CA.list_of_procs prog in
    let filter_fun proc =
      let proc_name = proc.CA.proc_name |> CA.unmingle_name in
      List.mem proc_name proc_names in
    let called_procs = List.filter filter_fun all_procs in
    let goal = Syn.mk_goal prog called_procs pre post syn_vars in
    synthesize_program goal in
  match hps with
  | None -> None
  | Some (hps1, hps2) ->
    let spec_list1 = List.map (get_spec_from_hps prog fst_pos) hps1 in
    let spec_list1 = ranking_specs spec_list1 in
    let spec1 = List.hd spec_list1 in
    let pr_spec = pr_pair Syn.pr_f Syn.pr_f in
    let () = x_tinfo_hp (add_str "spec1" pr_spec) spec1 no_pos in
    let res1 = helper spec1 fst_pos in
    if res1 != None then
      let spec_list2 = List.map (get_spec_from_hps prog snd_pos) hps2 in
      let spec_list2 = ranking_specs spec_list2 in
      let spec2 = List.hd spec_list2 in
      let () = x_tinfo_hp (add_str "spec2" pr_spec) spec2 no_pos in
      let res2 = helper spec2 snd_pos in
      if res2 != None then Some (unsome res1, unsome res2)
      (* To Validate *)
      else None
    else None
