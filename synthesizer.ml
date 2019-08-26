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
 * Processing rules
 *********************************************************************)
let process_rule_assign goal rc =
  if rc.ra_numeric then mk_derivation_success goal (RlAssign rc)
  else
    let pre, post = goal.gl_pre_cond, goal.gl_post_cond in
    let lhs, rhs = rc.ra_lhs, rc.ra_rhs in
    let n_pf = CP.mkEqExp (CP.mkVar lhs no_pos) rhs no_pos in
    let n_pre = CF.add_pure_formula_to_formula n_pf pre in
    let post_vars = CF.fv post in
    let sub_goal = {goal with gl_pre_cond = n_pre;
                              gl_trace = (RlAssign rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlAssign rc) [sub_goal]

let process_rule_return goal rc =
  let checked = rc.r_checked in
  if checked then
    mk_derivation_success goal (RlReturn rc)
  else
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

let process_rule_fwrite goal rc =
  let aux_fun formula var field new_val data_decls =
    match (formula:CF.formula) with
    | CF.Base bf -> let hf = bf.CF.formula_base_heap in
      let () = x_tinfo_hp (add_str "hf" pr_hf) hf no_pos in
      let rec helper (hf:CF.h_formula) = match hf with
        | CF.DataNode dnode ->
          let data_var = dnode.h_formula_data_node in
          if CP.eq_spec_var data_var var then
            let n_dnode = set_field dnode field new_val data_decls in
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
  let pre, var = goal.gl_pre_cond, rc.rfw_bound_var in
  let field, prog = rc.rfw_field, goal.gl_prog in
  let rhs, data_decls = rc.rfw_value, prog.prog_data_decls in
  let n_pre = aux_fun pre var field rhs data_decls in
  let n_goal = {goal with gl_pre_cond = n_pre;
                          gl_trace = (RlFWrite rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlFWrite rc) [n_goal]

let process_rule_fread goal rc =
  match rc.rfr_lookahead with
  | Some n_goal -> mk_derivation_subgoals goal (RlFRead rc) [n_goal]
  | None ->
    let vars = [rc.rfr_value] @ goal.gl_vars |> CP.remove_dups_svl in
    let n_goal = {goal with gl_vars = vars;
                            gl_trace = (RlFRead rc)::goal.gl_trace} in
    mk_derivation_subgoals goal (RlFRead rc) [n_goal]

let process_rule_func_call goal rc : derivation =
  let n_pre = rc.rfc_new_pre in
  (* if check_entail_exact_wrapper goal.gl_prog n_pre goal.gl_post_cond then
   *   mk_derivation_success goal (RlFuncCall rc)
   * else *)
  let n_vars = match rc.rfc_return with
    | None -> goal.gl_vars
    | Some var -> var::goal.gl_vars in
  let n_goal = {goal with gl_trace = (RlFuncCall rc)::goal.gl_trace;
                          gl_lookahead = [];
                          gl_vars = n_vars;
                          gl_pre_cond = n_pre} in
  mk_derivation_subgoals goal (RlFuncCall rc) [n_goal]

let process_rule_unfold_pre goal rc =
  let n_pres = rc.n_pre in
  let n_goal = {goal with gl_pre_cond = rc.n_pre;
                          gl_lookahead = [];
                          gl_trace = (RlUnfoldPre rc)::goal.gl_trace} in
  mk_derivation_subgoals goal (RlUnfoldPre rc) [n_goal]

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
  let subgoal = {goal with gl_post_cond = rc.rfp_post;
                           gl_trace = (RlFramePred rc)::goal.gl_trace;
                           gl_pre_cond = rc.rfp_pre} in
  mk_derivation_subgoals goal (RlFramePred rc) [subgoal]

let process_rule_frame_data goal rc =
  let substs = rc.rfd_pairs in
  let eq_pairs = List.map (fun (x, y) -> CP.mkEqVar x y no_pos) substs in
  let eq_pf = mkAndList eq_pairs in
  let post = rc.rfd_post in
  let substs = substs |> List.map (fun (x,y) -> (y,x)) in
  let e_vars = substs |> List.map fst in
  let exists_vars = CF.get_exists post in
  let n_post = remove_exists_vars post exists_vars in
  let n_post = CF.subst substs n_post in
  let e_vars = CP.diff_svl exists_vars e_vars in
  let n_post = add_exists_vars n_post e_vars in
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
    let n_post = remove_exists_vars goal.gl_post_cond [var] in
    let n_goal = {goal with gl_vars = all_vars;
                            gl_pre_cond = n_pre;
                            gl_post_cond = n_post;
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
  if num_of_code_rules trace > 3 || length_of_trace trace > 3
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
  let pname, i_procs = proc.CA.proc_name, iprog.IA.prog_proc_decls in
  let i_proc = List.find (fun x -> contains pname x.IA.proc_name) i_procs in
  let n_proc, res = match iast_exp with
    | None -> (i_proc, false)
    | Some exp0 -> (replace_exp_proc exp0 i_proc num, true) in
  let n_iprocs = List.map (fun x -> if contains pname x.IA.proc_name
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

let get_spec_from_hps prog num hps =
  let num_str = string_of_int num in
  let pre_hp = List.find (fun x -> x.CA.hp_name = ("N_P" ^ num_str)) hps in
  let post_hp = List.find (fun x -> x.CA.hp_name = ("N_Q" ^ num_str)) hps in
  let post = post_hp.CA.hp_formula in
  let pre = pre_hp.CA.hp_formula |> remove_exists in
  let () = x_tinfo_hp (add_str "pre" pr_f) pre no_pos in
  let () = x_tinfo_hp (add_str "post" pr_f) post no_pos in
  (pre,post)

let compare_spec (pre1, _) (pre2, _) =
  let hf1 = get_hf pre1 in
  let hf2 = get_hf pre2 in
  let hf1_vars = CF.h_fv hf1 in
  let hf2_vars = CF.h_fv hf2 in
  if List.length hf1_vars > List.length hf2_vars then PriHigh
  else if List.length hf2_vars > List.length hf1_vars then PriLow
  else PriEqual

let ranking_specs specs =
  let cmp_spec spec1 spec2 =
    let prio = compare_spec spec1 spec2 in
    match prio with
    | PriEqual -> 0
    | PriLow -> +1
    | PriHigh -> -1 in
  List.sort cmp_spec specs

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
    let syn_vars = proc.CA.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let stop = ref false in
    let helper (pre, post) =
      if !stop then ()
      else
        if isHFalse post then
          let () = x_binfo_hp (add_str "post" pr_f) post no_pos in
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
      let spec_list = List.map (get_spec_from_hps prog 1) hps_list in
      let spec_list = ranking_specs spec_list in
      let spec = List.hd spec_list in
      (* List.iter helper spec_list *)
      helper spec

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
        get_var_decls (Gen.unsome !repair_pos_fst) proc_body
      else if num = snd_pos then
        get_var_decls (Gen.unsome !repair_pos_snd) proc_body
      else [] in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
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
    let spec_list1 = List.map (get_spec_from_hps prog fst_pos) hps1 in
    let spec_list1 = ranking_specs spec_list1 in
    let spec1 = List.hd spec_list1 in
    let pr_spec = pr_pair pr_f pr_f in
    let () = x_binfo_hp (add_str "spec1" pr_spec) spec1 no_pos in
    let (n_iprog, res1) = helper spec1 fst_pos in
    if res1 then
      let spec_list2 = List.map (get_spec_from_hps prog snd_pos) hps2 in
      let spec_list2 = ranking_specs spec_list2 in
      let spec2 = List.hd spec_list2 in
      let () = x_binfo_hp (add_str "spec2" pr_spec) spec2 no_pos in
      let (n_iprog, res2) = helper spec2 snd_pos in
      if res2 then Some n_iprog
      (* To Validate *)
      else None
    else None

let synthesize_block_statements iprog prog orig_proc proc decl_vars =
  let entailments = !Synthesis.entailments |> List.rev in
  let hps = SB.solve_entailments_one prog entailments in
  let syn_vars = proc.CA.proc_args
                 |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
  let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
  let helper cur_res hps =
    if cur_res != None then cur_res
    else
      let post_hp = List.find (fun x -> x.CA.hp_name = "QQ") hps in
      let pre_hp = List.find (fun x -> x.CA.hp_name = "PP") hps in
      let post = post_hp.CA.hp_formula in
      let pre = pre_hp.CA.hp_formula |> remove_exists in
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
    let syn_vars = proc.CA.proc_args
                   |> List.map (fun (x,y) -> CP.mk_typed_sv x y) in
    let syn_vars = syn_vars @ decl_vars |> CP.remove_dups_svl in
    let helper hps =
      let post_hp = List.find (fun x -> x.CA.hp_name = "QQ") hps in
      let pre_hp = List.find (fun x -> x.CA.hp_name = "PP") hps in
      let post = post_hp.CA.hp_formula in
      let pre = pre_hp.CA.hp_formula |> remove_exists in
      (pre, post) in
    let specs = hps_list |> List.map helper in
    Some specs

