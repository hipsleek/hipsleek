open SBGlobals
open SBCast
open SBProof
open SBLib
open SBUnify

module DB = SBDebug
module PP = SBPuretp
module NO = SBNormalize
module PT = SBPuretp
module EList = ExtList.List

let time_unify = ref 0.

(** analyze failure when unifying f1 and f2 *)
let rec analyze_fail_unf mode prog (f1: formula) (f2: formula) unf =
  SBDebug.trace_3 "analyze_fail_unf" (pr_f, pr_f, pr_unf, pr_opt pr_pf) f1 f2 unf
    (fun () -> analyze_fail_unf_x mode prog f1 f2 unf)

and analyze_fail_unf_x mode prog (f1: formula) (f2: formula) unf =
  let nf1 = subst unf.unf_correct_ssts f1 in
  let vs1, vs2 = fv nf1, fv f2 in
  match nf1, f2 with
  | FBase (_, p1, _), FBase (_, p2, _) ->
    let np1 = p1 |> mk_pexists (diff_vs vs1 vs2) |>
              NO.push_qvars_inward_pf in
    let conjuncts = collect_pure_conjuncts_pf np1 in
    let fail_cond =
      conjuncts |>
      List.filter (fun x -> PP.check_imply_slice_lhs p2 x != MvlTrue) |>
      mk_pconj |> NO.simplify_all_pf in
    let res =
      if (PT.check_sat fail_cond = MvlFalse) then None
      else Some fail_cond in
    DB.nsprint ["@@Analyze failure: \n";
               "     f1: "; (pr_f f1); "\n";
               "     f2: "; (pr_f f2); "\n";
               "     res: "; (pr_opt pr_pf res)];
    res
  | FExists _, _ | FForall _, _ -> None
  | _, FExists _ | _, FForall _ -> None


let check_well_founded_hypo goal hypo unf : bool =
  let check_decrease_size_unify unf =
    List.exists is_hatom_df unf.unf_residue in
  let check_decrease_size_trace trace =
    let rules = List.map (fun x -> x.tri_rule) trace in
    let rs = List.fold_left (fun acc r -> match acc with
      | [] -> [r]
      | (RlInduction _)::_ -> acc
      | _ -> r::acc) [] rules in
    List.exists is_rule_star_data rs in
  let check_decrease_structure () =
    let gvs = goal.gl_lstats.fst_views in
    let hvs = hypo.hp_lstats.fst_views in
    gvs |> List.exists (fun gv -> hvs |> List.exists (fun hv ->
      mem_ints hv.viewf_id gv.viewf_ancestor_ids)) in
  match !mutual_induction with
  | true ->
    (check_decrease_size_unify unf) ||
    (check_decrease_size_trace goal.gl_trace)
  | false -> check_decrease_structure ()

let check_potential_hypothesis pstate goal : bool =
  try
    match goal.gl_lhs with
    | FForall _ | FExists _ -> false
    | FBase _ ->
      let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
      if (collect_view_form lhs) = [] then raise_bool false;
      if (has_emp_f lhs) then raise_bool false;
      (* data *)
      let ldatas, rdatas = collect_data_form lhs, collect_data_form rhs in
      if List.exists_pair (fun x y ->
        eq_exp x.dataf_root y.dataf_root) ldatas rdatas then
        raise_bool false;
      (* equality *)
      if (NO.collect_substs_var_var_from_equal lhs != []) then
        raise_bool false;
      (* default *)
      true
  with
  | EBool res -> res
  | _ -> false

let check_potential_mutual_hypothesis pstate goal : bool =
  try
    match goal.gl_lhs with
    | FForall _ | FExists _ -> false
    | FBase _ ->
      let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
      let lst, rst = goal.gl_lstats, goal.gl_rstats in
      if (collect_view_form lhs) = [] then raise_bool false;
      if (has_emp_f lhs) || (has_emp_f rhs) then raise_bool false;
      if (lst.fst_num_hatoms < rst.fst_num_hatoms) then raise_bool false;
      if (check_syntax_equiv lhs rhs) then raise_bool false;
      (* default *)
      true
  with
  | EBool res -> res
  | _ -> false

let check_potential_mutual_lemma pstate lemma ptree : bool =
  let check () =
    try
      let mutual_lemmas = pstate.prs_theorems |> List.filter (fun th ->
        th.th_origin = LorgMutual) in
      if List.length mutual_lemmas >= !thd_max_mutual_lemma then
        raise_bool false;
      let lhs, rhs = lemma.lm_lhs, lemma.lm_rhs in
      if is_qform lhs then raise_bool false;
      if (is_false_f lhs) then raise_bool false;
      if (collect_view_form lhs) = [] then raise_bool false;
      let lhs_subset_view =
        let lvnames, rvnames = Pair.fold (fun f ->
          f |> collect_view_form |>
          List.map (fun vf -> vf.viewf_name) |> dedup_ss) lhs rhs in
        subset_ss lvnames rvnames in
      let trivial_next_rule =
        let next_used_rule = match ptree with
          | PtSearch pts ->
            let ptds = List.map (fun pt -> match pt with
              | PtDerive ptd -> [ptd]
              | _ -> []) pts.pts_sub_trees |> List.concat in
            if ptds = [] then None
            else Some ((List.hd ptds).ptd_rule)
          | PtDerive ptd -> Some ptd.ptd_rule in
        match next_used_rule with
        | None -> false
        | Some rule ->
          if is_rule_axiom rule then true
          else if is_rule_normalization rule then true
          else match rule with
            | RlStarData _ | RlStarView _ | RlViewRight _ -> true
            | _ -> false in
      if trivial_next_rule && lhs_subset_view then raise_bool false;
      if (NO.collect_substs_var_var_from_equal lhs != []) then
        raise_bool false;
      if (has_emp_f lhs) || (has_emp_f rhs) then raise_bool false;
      let _ =
        let ldatas, rdatas = collect_data_form lhs, collect_data_form rhs in
        let has_data_same_root = List.exists_pair (fun x y ->
          eq_exp x.dataf_root y.dataf_root) ldatas rdatas in
        if (has_data_same_root) then raise_bool false
        else () in
      if pstate.prs_theorems |> List.exists (fun th ->
        (eq_s th.th_lhs_name (create_formula_name lhs)) &&
        (eq_s th.th_rhs_name (create_formula_name rhs))) then
        raise_bool false;
      if lhs_subset_view &&
         not (check_good_inductive_ptree ptree) then raise_bool false;
      (* default *)
      true
    with EBool res -> res in
  let res = check () in
  DB.nsprint ["Check potential mutual lemma:\n"; (pr_lm lemma); "\n";
              "   Result: "; pr_bool res; "\n"];
  res

let check_potential_counter_theorem cth  : bool =
  try
    let lhs, rhs = cth.cth_lhs, cth.cth_rhs in
    let _ = match lhs with
      | FExists _ | FForall _ -> raise_bool false
      | _ -> () in
    if (is_false_f lhs) then raise_bool false;
    if (collect_view_form lhs) = [] then raise_bool false;
    if (NO.collect_substs_var_var_from_equal lhs != []) then
      raise_bool false;
    if (has_emp_f lhs) || (has_emp_f rhs) then raise_bool false;
    let _ =
      let ldatas, rdatas = collect_data_form lhs, collect_data_form rhs in
      let has_data_same_root = List.exists (fun x ->
        List.exists (fun y -> eq_exp x.dataf_root y.dataf_root) ldatas
      ) rdatas in
      if (has_data_same_root) then raise_bool false
      else () in
    (* default *)
    true
  with EBool res -> res
