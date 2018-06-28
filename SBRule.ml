open SBGlobals
open SBCast
open SBLib
open SBLib.Func
open SBProof
open SBUnify

module NO = SBNormalize
module DB = SBDebug
module ID = SBInduction
module PT = SBPuretp
module PL = SBPlanner

(***************************************************************************)
(********************            Axiom Rules            ********************)

let prepare_new_goal goal =
  let new_goal =
    { goal with
      gl_ent_id = new_entail_id ();
      gl_hooked_rules = []; } in
  new_goal

let finalize_new_goal_common prog old_goal new_goal rule =
  let trace_item = mk_trace_item old_goal rule in
  let trace = trace_item::new_goal.gl_trace in
  let trace_stats = mk_trace_stats prog trace in
  let has_unplanned_excl_mid = List.exists (fun tri ->
    match tri.tri_rule with
    | RlExclMid rem -> List.exists is_unplanned_excl_mid_case rem.rem_cases
    | _ -> false) trace in
  let precise_unifying_plans = PL.find_precise_unifying_plan prog new_goal in
  let matching_plans = PL.find_matching_plan prog new_goal in
  { new_goal with
    gl_cache_rule = None;
    gl_has_unplanned_excl_mid = has_unplanned_excl_mid;
    gl_precise_unifying_plans = precise_unifying_plans;
    gl_matching_plans = matching_plans;
    gl_trace = trace;
    gl_tstats = trace_stats }

let finalize_new_goal_update_lhs prog old_goal new_goal rule =
  let prog, lhs, hconsumed = prog, new_goal.gl_lhs, new_goal.gl_hconsumed in
  let lstats = mk_formula_stats prog lhs in
  let gstats = mk_goal_stats prog lstats new_goal.gl_rstats in
  let new_goal = {
    new_goal with
    gl_lhs_encoded = NO.encode_formula_hconsumed prog lhs hconsumed;
    gl_lstats = lstats;
    gl_gstats = gstats } in
  finalize_new_goal_common prog old_goal new_goal rule

let finalize_new_goal_update_rhs prog old_goal new_goal rule =
  let lhs, rhs = new_goal.gl_lhs, new_goal.gl_rhs in
  let rstats = mk_formula_stats prog rhs in
  let gstats = mk_goal_stats prog new_goal.gl_lstats rstats in
  let unproved_rpatoms =
    if (is_pmode_infer new_goal) then []
    else find_unproved_conjuncts prog lhs rhs in
  let new_goal = {
    new_goal with
    gl_rstats = rstats;
    gl_gstats = gstats;
    gl_rhs_unproved_patoms = unproved_rpatoms; } in
  finalize_new_goal_common prog old_goal new_goal rule

let finalize_new_goal_update_all prog old_goal new_goal rule =
  let lhs, rhs = new_goal.gl_lhs, new_goal.gl_rhs in
  let lstats = mk_formula_stats prog lhs in
  let rstats = mk_formula_stats prog rhs in
  let unproved_rpatoms = find_unproved_conjuncts prog lhs rhs in
  let new_goal = {
    new_goal with
    gl_lstats = lstats;
    gl_rstats = rstats;
    gl_rhs_unproved_patoms = unproved_rpatoms;} in
  finalize_new_goal_common prog old_goal new_goal rule


(***************************************************************************)
(********************            Axiom Rules            ********************)

let choose_rule_pure_entail pstate goal : rule list =
  let vds = pstate.prs_prog.prog_views in
  let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
  let hconsumed, trace = goal.gl_hconsumed, goal.gl_trace in
  let lsts, rsts = goal.gl_lstats, goal.gl_rstats in
  if lsts.fst_is_pure && (not lsts.fst_has_known_rform) &&
     rsts.fst_is_pure && (not rsts.fst_has_known_rform) then
    let lhsp =
      let invs = (goal.gl_hconsumed @ goal.gl_hreplaced) |>
                 List.map (fun ha -> match ha with
                   | HView vf -> [NO.encode_view_inv_vf vds vf]
                   | _ -> []) |> List.concat in
      mk_pconj (goal.gl_lhs_encoded::invs) in
    let rhsp = extract_pf goal.gl_rhs in
    let status = SBPuretp.check_imply_slice_lhs lhsp rhsp in
    if (status = MvlTrue) then
      [mk_rule_pure_entail goal.gl_lhs goal.gl_rhs status]
    else if (is_pmode_infer goal) &&
            (lsts.fst_has_unk_rform || rsts.fst_has_unk_rform) then
      let asms = mk_assum lhs rhs hconsumed trace in
      [mk_rule_infer_relation lhs rhs hconsumed asms]
    else [mk_rule_pure_entail goal.gl_lhs goal.gl_rhs status]
  else []


let choose_rule_false_left pstate goal : rule list =
  (* simple check for false *)
  let vds = pstate.prs_prog.prog_views in
  let plhs = goal.gl_lhs_encoded in
  let invs = (goal.gl_hconsumed @ goal.gl_hreplaced) |>
             List.map (fun ha -> match ha with
               | HView vf -> [NO.encode_view_inv_vf vds vf]
               | _ -> []) |> List.concat in
  let nplhs = mk_pconj (plhs::invs) in
  if (PT.check_sat nplhs = MvlFalse) then
    [mk_rule_false_left goal.gl_lhs]
  else []

(*****************************************************************************)
(********************         Normalization Rules         ********************)

let choose_rule_equal_left pstate goal : rule list =
  let lhf = extract_hf goal.gl_lhs in
  let hvs = fv_hf lhf in
  let ssts =
    NO.collect_substs_var_var_from_equal goal.gl_lhs |>
    List.filter (fun (v, _) -> mem_vs v hvs) |>
    List.filter (fun (_, e) -> match e with
      | Var _ -> true
      | _ -> false) in
  match ssts with
  | [] -> []
  | _ -> [mk_rule_equal_left goal.gl_lhs]

let choose_rule_exists_left pstate goal : rule list =
  let rec can_remove_pf = function
    | BConst _ | BinRel _ | PRel _ -> false
    | PNeg _ -> false
    | PConj (gs, p) -> List.exists can_remove_pf gs
    | PDisj (gs, p) -> List.exists can_remove_pf gs
    | PForall _ -> false
    | PExists (_, g, _) -> true in
  match goal.gl_lhs with
  | FExists _ -> [mk_rule_exists_left goal.gl_lhs]
  | FBase (_, pf, _) ->
    if (can_remove_pf pf) then
      [mk_rule_exists_left goal.gl_lhs]
    else []
  | _ -> []

let choose_rule_exists_right pstate goal : rule list =
  let ssts = NO.collect_substs_from_equal goal.gl_rhs in
  let rec need_norm_exists g = match g with
    | FBase _ | FForall _ -> false
    | FExists (vs, g0, _) ->
      if (List.exists (fun (x, y) -> mem_vs x vs) ssts) then true
      else need_norm_exists g0 in
  if (need_norm_exists goal.gl_rhs) then
    [mk_rule_exists_right goal.gl_rhs]
  else []

let choose_rule_emp_left pstate goal : rule list =
  if (has_emp_f goal.gl_lhs) && not (is_pure_f goal.gl_lhs) then
    [mk_rule_emp_left goal.gl_lhs]
  else []

let choose_rule_emp_right pstate goal : rule list =
  if (has_emp_f goal.gl_rhs) && not (is_pure_f goal.gl_rhs) then
    [mk_rule_emp_right goal.gl_rhs]
  else []

let choose_rule_drop_left pstate goal : rule list =
  if (goal.gl_tstats.tst_drop_left >= !thd_max_drop_left) then []
  else if (is_pmode_infer_basic goal) then []
  (* else if (is_pmode_unsat goal) then [] *)
  else match goal.gl_lhs with
    | FExists _ | FForall _ -> []
    | FBase (hf, pf, p) ->
      let lhvs = fv_hf hf in
      let rvs = goal.gl_rstats.fst_fvs in
      let hatoms = (collect_hatom_hf hf) @ (goal.gl_hconsumed) in
      let phs = NO.encode_hatoms pstate.prs_prog hatoms in
      let pfs = collect_pure_conjuncts_pf pf in
      let nlhs = FBase (hf, mk_true no_pos, p) in
      let nlhs, drop_pfs, _ = List.fold_left (fun acc pf ->
        match pf with
        | BConst (true, _) -> acc
        | _ ->
          let pvs = fv_pf pf in
          let anlhs, adrop_pfs, afull_pfs = acc in
          if (is_pmode_infer goal) && (is_rform_pf pf) then
            let anlhs = mk_hstar_f_pf anlhs pf in
            let afull_pfs = mk_pconj [afull_pfs; pf] in
            (anlhs, adrop_pfs, afull_pfs)
          else if (disjoint_vs pvs rvs) && (disjoint_vs pvs lhvs) &&
                  List.for_all (fun g ->
                    (eq_patom g pf)  || disjoint_vs pvs (fv_pf g)) pfs then
            (anlhs, adrop_pfs @ [pf], afull_pfs)
          else if (PT.check_imply_slice_lhs afull_pfs pf = MvlTrue) then
            (anlhs, adrop_pfs @ [pf], afull_pfs)
          else
            let anlhs = mk_hstar_f_pf anlhs pf in
            let afull_pfs = mk_pconj [afull_pfs; pf] in
            (anlhs, adrop_pfs, afull_pfs)
      ) (nlhs, [], phs) pfs in
      if (drop_pfs = []) then []
      else [mk_rule_drop_left nlhs (mk_pconj drop_pfs)]

let choose_rule_drop_right pstate goal : rule list =
  let prog, lhs, rhs = pstate.prs_prog, goal.gl_lhs, goal.gl_rhs in
  let nrhs, drop_pfs = match rhs with
    | FBase (rhf, rpf, _) ->
      let plr = mk_pconj [goal.gl_lhs_encoded; (NO.encode_hformula prog rhf)] in
      let keep_pfs, drop_pfs =
        rpf |> collect_pure_conjuncts_pf |>
        List.partition (fun g -> PT.check_imply_slice_lhs plr g != MvlTrue) in
      let nrhs = mk_fbase rhf (mk_pconj keep_pfs) in
      (nrhs, drop_pfs)
    | FExists (vs, FBase (rhf, rpf, _), _) ->
      let prhf = NO.encode_hformula prog rhf in
      let keep_pfs, drop_pfs =
        rpf |> collect_pure_conjuncts_pf |>
        List.partition (fun g -> PT.check_imply_slice_lhs prhf g != MvlTrue) in
      let nrhs = mk_fexists vs (mk_fbase rhf (mk_pconj keep_pfs)) in
      (nrhs, drop_pfs)
    | _ -> (rhs, []) in
  let drop_pfs = List.filter (fun pf -> not (is_true_pf pf)) drop_pfs in
  if (drop_pfs = []) then []
  else [mk_rule_drop_right nrhs (mk_pconj drop_pfs)]

let choose_rule_unfold_relation pstate goal : rule list =
  let rdefns = pstate.prs_prog.prog_rels in
  let lrels = collect_rform goal.gl_lhs |>
              List.filter (fun x ->
                List.exists (fun y ->
                  (is_rf_instance x y) && (not (is_unk_rdefn y))) rdefns) in
  let rrels = collect_rform goal.gl_rhs |>
              List.filter (fun x ->
                List.exists (fun y ->
                  (is_rf_instance x y) && (not (is_unk_rdefn y))) rdefns) in
  if (lrels = []) && (rrels = []) then []
  else [mk_rule_unfold_relation lrels rrels]


(*****************************************************************************)
(********************            Spatial Rules            ********************)

let rec choose_rule_star_data ?(all=false) pstate goal : rule list =
  DB.trace_1 "choose_rule_star_data" (pr_g, pr_rules) goal
    (fun () -> choose_rule_star_data_x ~all:all pstate goal)

and choose_rule_star_data_x ?(all=false) pstate goal : rule list =
  try
    let _ = if (has_qhvars_f goal.gl_lhs) then raise_rules [] in
    match goal.gl_cache_rule, all with
    | None, _ | _, true ->
      let lhs_dsps = goal.gl_lstats.fst_data_split in
      let rhs_dsps = goal.gl_rstats.fst_data_split in
      List.fold_left (fun acc1 x ->
        let rs = List.fold_left (fun acc2 y ->
          if (eq_s x.dsp_head.dataf_name y.dsp_head.dataf_name) then
            let rule, rsd = mk_rule_star_data_all goal x y in
            let _ = if rsd.rsd_trivial && (not all) then raise_rules [rule] in
            acc2@[rule]
          else acc2
        ) [] rhs_dsps in
        acc1@rs) [] lhs_dsps
    | Some rc, false -> rc.crl_star_data
  with ERules rs -> rs

let choose_all_rule_star_data pstate goal =
  choose_rule_star_data ~all:true pstate goal |>
  List.map (function
    | RlStarData r -> [r]
    | _ -> []) |>
  List.concat

let rec choose_rule_star_view ?(all=false) pstate goal : rule list =
  DB.trace_1 "choose_rule_star_view" (pr_g, pr_rules) goal
    (fun () -> choose_rule_star_view_x ~all:all pstate goal)

and choose_rule_star_view_x ?(all=false) pstate goal : rule list =
  try
    let _ = if (has_qhvars_f goal.gl_lhs) then raise_rules [] in
    match goal.gl_cache_rule, all with
    | None, _ | _, true ->
      let lhs_vsps = goal.gl_lstats.fst_view_split in
      let rhs_vsps = goal.gl_rstats.fst_view_split in
      List.fold_left (fun acc1 x ->
        let rs = List.fold_left (fun acc2 y ->
          match (eq_s x.vsp_head.viewf_name y.vsp_head.viewf_name) with
          | true ->
            let rule, rsv = mk_rule_star_view_all goal x y in
            if rsv.rsv_trivial && (is_pmode_infer_rhs goal) then
              raise_rules [rule];
            if rsv.rsv_trivial && (not all) then
              raise_rules [rule];
            acc2@[rule]
          | false ->  acc2
        ) [] rhs_vsps in
        acc1@rs) [] lhs_vsps
    | Some rc, false -> rc.crl_star_view
  with ERules rs -> rs

let choose_all_rule_star_view pstate goal =
  choose_rule_star_view ~all:true pstate goal |>
  List.map (function
    | RlStarView r -> [r]
    | _ -> []) |>
  List.concat

let rec choose_rule_view_left pstate goal : rule list =
  DB.trace_1 "choose_rule_view_left" (pr_g, pr_rules) goal
    (fun () -> choose_rule_view_left_x pstate goal)

and choose_rule_view_left_x pstate goal : rule list =
  try
    let prog, lhs = pstate.prs_prog, goal.gl_lhs in
    if not (is_qfree lhs) then raise_rules [];
    prog.prog_views |> List.map (fun vdef ->
      let vdcs =
        vdef.view_defn_cases |> List.map (fun vdc ->
          if not vdc.vdc_base_case &&
             vdc.vdc_form |> collect_hatom |> List.length |> (<) 1 then
            [{vdc with vdc_form = NO.remove_all_exists_vars vdc.vdc_form}]
          else []) |> List.concat in
      let vdc_unfs =
        vdcs |> List.map (fun vdc ->
          let unfs =
            lhs |> unify_heap prog vdc.vdc_form |> get_unf_success |>
            List.exclude (fun unf ->
              let ghs = unf.unf_hatom_pairs |> List.split |> snd in
              List.exists_pair (fun h1 h2 ->
                let as1, as2 = get_ancestor_ids h1, get_ancestor_ids h2 in
                not (eq_hatom h1 h2) && (intersected_ints as1 as2)) ghs ghs) in
          List.map (fun unf -> (vdc, unf)) unfs) |>
        List.concat in
      vdc_unfs |> List.map (fun (vdc, unf) ->
        let lview = vdef.view_params |> List.map mk_exp_var |>
                    mk_view_form vdef.view_name |>
                    subst_vf unf.unf_correct_ssts in
        let rest = (mk_hstar_hatoms unf.unf_residue), (extract_pf lhs) in
        let vfc = mk_view_fold_case prog lhs lview vdc rest in
        mk_rule_view_left goal lview vfc)) |> List.concat
  with ERules rs -> rs

let rec choose_rule_view_right pstate goal : rule list =
  DB.trace_1 "choose_rule_view_right" (pr_g, pr_rules) goal
    (fun () -> choose_rule_view_right_x pstate goal)

and choose_rule_view_right_x pstate goal : rule list =
  try
    let prog = pstate.prs_prog in
    let plhs = NO.encode_formula prog goal.gl_lhs in
    goal.gl_rstats.fst_view_split |> List.map (fun vsp ->
      let vf = vsp.vsp_head in
      let vargs = vf.viewf_args in
      let old_ufcs = vsp.vsp_unfold_cases in
      let new_ufcs = List.filter (fun ufc ->
        let puc = NO.encode_formula prog ufc.vuc_new_form in
        DB.nhprint "FSC NEW FORM: " pr_f ufc.vuc_new_form;
        DB.nhprint "PUC: " pr_pf puc;
        (PT.check_sat puc != MvlFalse)) vsp.vsp_unfold_cases in
      let rvrs =
        new_ufcs |> List.map (mk_rule_view_right_core goal vsp.vsp_head) |>
        (* refinement *)
        (function
          | [r] ->
            if (List.exists (fun e -> typ_of_exp e = TInt) vargs) then [r]
            else if (is_recur_direct_vf prog.prog_views vf) &&
                    (List.length old_ufcs = List.length new_ufcs) then [r]
            else [{r with rvr_trivial = true}]
          | rs -> rs) |>
        List.map (fun r -> RlViewRight r) in
      let rems = match is_pmode_infer goal with
        | true ->
          vsp.vsp_head |> get_excl_mid_cases prog.prog_views |>
          List.filter (fun f ->
            let fvs = fv_pf f in
            (fvs != []) && (subset_vs fvs goal.gl_rstats.fst_fvs)) |>
          List.filter (fun f ->
            (PT.check_imply plhs f != MvlTrue) &&
            (PT.check_sat (mk_pconj [plhs; f]) != MvlFalse)) |>
          List.map (fun f -> mk_rule_excl_mid f ~plan_rules:rvrs)
        | false -> [] in
      rvrs @ rems) |>
    List.concat
  with ERules rs -> rs

let rec choose_rule_induction pstate goal : rule list =
  DB.trace_1 "choose_rule_induction" (pr_g, pr_rules) goal
    (fun () -> choose_rule_induction_x pstate goal)

and choose_rule_induction_x pstate goal : rule list =
  try
    if (has_qhvars_f goal.gl_lhs) then raise_rules [];
    let prog, pth = pstate.prs_prog, pstate.prs_threshold in
    let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    goal.gl_lstats.fst_view_split |>
    List.map (fun vsp ->
      let ufcases = List.map (fun ufc ->
        let nf = NO.remove_all_heap_exists_vars ufc.vuc_new_form in
        {ufc with vuc_new_form = nf}) vsp.vsp_unfold_cases in
      let record_hypo =
        (is_recur_direct vsp.vsp_view_recur) &&
        (ID.check_potential_hypothesis pstate goal) &&
        (is_false_f rhs || rst.fst_has_view_recur_direct) in
      mk_rule_induction prog goal vsp ufcases record_hypo)
  with (ERules res) -> res

let rec choose_rule_from_hypothesis pstate goal : rule list =
  DB.trace_2 "choose_rule_from_hypothesis"
    (pr_gent, pr_hps, pr_rules) goal goal.gl_hypos
    (fun () -> choose_rule_from_hypothesis_x pstate goal)

and choose_rule_from_hypothesis_x pstate goal : rule list =
  try
    let prog, mode = pstate.prs_prog, goal.gl_proof_mode in
    if (has_qhvars_f goal.gl_lhs) then raise_rules [];
    match goal.gl_cache_rule with
    | None ->
      let lg, plg = goal.gl_lhs, goal.gl_lhs_encoded in
      let hconsumed, trace = goal.gl_hconsumed, goal.gl_trace in
      goal.gl_hypos |> List.fold_left (fun acc hp ->
        DB.nsprint ["CHOOSE HYPO:\n";
                    "   - Goal: "; pr_gc goal; "\n";
                    "   - Hypo: "; pr_hp hp];
        let lhp, lhp_vs = hp.hp_lhs, fv hp.hp_lhs in
        let unfs = unify_heap prog lhp lg in
        let unfs_hsucc, unfs_hfail = split_unf_success_failure unfs in
        let unfs_hsucc =
          unfs_hsucc |> List.filter (ID.check_well_founded_hypo goal hp) |>
          List.map (fun unf ->
            let vs_unf, _ = List.split unf.unf_correct_ssts in
            if (diff_vs lhp_vs vs_unf = []) then [unf]
            else extend_heap_unification prog unf hp.hp_rhs goal.gl_rhs) |>
          List.concat in
        let _ = DB.nhprint "UNFS HEAP SUCCESS: " pr_unfs unfs_hsucc in
        let unfs_psucc, unfs_pfail =
          List.partition (unify_pure mode prog lhp lg) unfs_hsucc in
        let rule_unfs_ok = List.map (mk_rule_hypothesis hp) unfs_psucc in
        let _ = DB.nhprint "UNFS PURE FAIL: " pr_unfs unfs_pfail in
        let rule_unfs_fail = unfs_pfail |> List.fold_left (fun acc unf ->
          match (ID.analyze_fail_unf mode prog lhp lg unf) with
          | None -> acc
          | Some fr ->
            let _ = DB.nhprint "UNFS PURE FAIL REASON: " pr_pf fr in
            match goal.gl_proof_mode with
            | PrfInferLhs | PrfInferRhs ->
              let prels, other_pfs = fr |> collect_pure_conjuncts_pf |>
                                     List.partition is_rform_pf in
              let assums, fail_reasons = match prels, other_pfs with
                | [], [] ->  error "choose_rule_from_hypothesis: empty failure"
                | [], _ -> [], [fr]
                | _, [] ->
                  let ilhs = match goal.gl_proof_mode with
                    | PrfInferLhs -> extract_rform lg
                    | _ -> lg in
                  let irhs = prels |> mk_pconj |> mk_fpure in
                  let iah = mk_assum ilhs irhs [] trace in
                  ([iah], [])
                | _, _ ->
                  let ilhs = match goal.gl_proof_mode with
                    | PrfInferLhs -> extract_rform lg
                    | _ -> lg in
                  let irhs = prels |> mk_pconj |> mk_fpure in
                  let iah = mk_assum ilhs irhs [] trace in
                  ([iah], [mk_pconj other_pfs]) in
              let rules =
                let rhp = mk_rule_hypothesis hp unf ~assums:assums in
                match fail_reasons with
                | [] -> [rhp]
                | pf::_ -> [(mk_rule_excl_mid pf  ~plan_rules:[rhp])] in
              acc @ rules
            | _ ->
              let remids =
                let rhp = mk_rule_hypothesis hp unf in
                if not !proof_use_rule_excl_mid then []
                else if SBPuretp.check_consistency plg fr = MvlFalse then []
                else if List.exists (is_rule_hypothesis) acc then []
                else [(mk_rule_excl_mid fr ~plan_rules:[rhp])] in
              let nlhs, wpf =
                let rnms = List.map (fun (x,y) -> (y,x)) hp.hp_renaming in
                let qvs, hf, pf = extract_components_f hp.hp_lhs in
                let fail_pfs = collect_pure_conjuncts_pf fr in
                let keep_pfs, wpfs =
                  pf |> collect_pure_conjuncts_pf |> List.partition (fun x ->
                    let nx = subst_pf unf.unf_correct_ssts x in
                    not (List.exists (eq_patom nx) fail_pfs)) in
                let new_lhs = keep_pfs |>  mk_pconj |> mk_fbase hf |>
                              mk_qform qvs |> rename_var_f rnms in
                let wpf = wpfs |> mk_pconj |> rename_var_pf rnms in
                (new_lhs, wpf) in
              let rgenls =
                if not !proof_use_backjump || is_true_pf wpf then []
                else [mk_rule_weaken_left ~base:(Some (hp, unf)) nlhs wpf goal] in
              acc @ remids @ rgenls) [] in
        let rule_gen_lefts =
          let _ = DB.nhprint "UNFS HEAP FAILURE: " pr_unfs unfs_hfail in
          let rnms = hp.hp_renaming |> List.map Pair.reverse in
          let qvs, hf, pf = extract_components_f goal.gl_lhs in
          unfs_hfail |> List.fold_left (fun acc_rules unf ->
            let tbl_conflict_vars = Hashtbl.create 2 in
            let tbl_ununified_exps = Hashtbl.create 2 in
            let gen_exps = ref [] in
            let fresh_conflict_var v e =
              try Hashtbl.find tbl_conflict_vars e
              with _ ->
                let nv = fresh_var v in
                let gen_exp = v |> rename_var rnms |> mk_exp_var in
                let _ = gen_exps := !gen_exps @ [gen_exp] in
                Hashtbl.add tbl_conflict_vars e nv; nv in
            let fresh_ununified_exp e =
              try Hashtbl.find tbl_ununified_exps e
              with _ ->
                let nv = e |> typ_of_exp |> fresh_var_of_typ in
                let _ = gen_exps := !gen_exps @ [e] in
                Hashtbl.add tbl_ununified_exps e nv; nv in
            let nhf = unf.unf_hatom_pairs |> List.map (fun (sha, tha) ->
              let args1, args2  = get_hatom_args sha, get_hatom_args tha in
              let nargs1 = List.map2 (fun a1 a2 ->
                match a1 with
                | Var (v, p) ->
                  if List.exists (eq_sst (v, a2)) unf.unf_conflict_ssts then
                    Var (fresh_conflict_var v a2, p)
                  else rename_var_exp rnms a1
                | IConst (_, p) | Null p ->
                  if List.exists (
                    eq_exp_pair (a1, a2)) unf.unf_ununifed_exps then
                    Var (fresh_ununified_exp a1, p)
                  else a1
                | _ -> rename_var_exp rnms a1) args1 args2 in
              update_hatom_args sha nargs1) |> mk_hform_has in
            (* remove useless uninst by generalization *)
            DB.nhprint "GEN_EXPS Length: " pr_int (List.length !gen_exps);
            if List.length !gen_exps > 1 then acc_rules
            else
              let nlhs = mk_fbase nhf pf |> mk_qform qvs in
              let rgl = mk_rule_gen_left ~base:(Some (hp, unf)) nlhs
                          !gen_exps prog goal in
              rgl :: acc_rules) [] in
        acc @ rule_unfs_ok @ rule_unfs_fail @ rule_gen_lefts) []
    | Some rc -> rc.crl_hypothesis
  with (ERules res) -> res

let rec choose_rule_from_theorem pstate goal : rule list =
  DB.trace_1 "choose_rule_from_theorem"
    (pr_g, pr_rules) goal
    (fun () -> choose_rule_from_theorem_x pstate goal)

and choose_rule_from_theorem_x pstate goal : rule list =
  try
    let prog, mode = pstate.prs_prog, goal.gl_proof_mode in
    let vdefns = pstate.prs_prog.prog_views in
    let gl_lvds = collect_view_defn vdefns goal.gl_lhs in
    let gl_rvds = collect_view_defn vdefns goal.gl_rhs in
    let gl_vds = gl_lvds @ gl_rvds in
    if (has_qhvars_f goal.gl_lhs) then raise_rules [];
    if not !proof_use_rule_theorem then raise_rules [];
    DB.nhprint "ALL THEOREMS: " pr_ths pstate.prs_theorems;
    match goal.gl_cache_rule with
    | None ->
      let lg, plg = goal.gl_lhs, goal.gl_lhs_encoded in
      let rhs_goal = goal.gl_rhs in
      let uths_left, uths_right = List.fold_left (fun (accl, accr) tri ->
        match tri.tri_rule with
        | RlTheorem rth ->
          let name = rth.rth_th.th_name in
          if (mem_ss name accl) then (accl, accr)
          else if rth.rth_left then (accl @ [name], accr)
          else (accl, accr @ [name])
        | _ -> (accl, accr)) ([], []) goal.gl_trace in
      let ths_left, ths_right = List.fold_left (fun (lths, rths) th ->
        let rl_lvds = collect_view_defn vdefns th.th_lhs in
        let rl_rvds = collect_view_defn vdefns th.th_rhs in
        let left =
          not (mem_ss th.th_name uths_right) &&
          List.exists_pair check_recur_vdefn gl_vds rl_rvds in
        let right =
          (not !mutual_induction) &&
          not (mem_ss th.th_name uths_left) &&
          List.exists_pair check_recur_vdefn gl_lvds rl_lvds in
        if left && right then (lths @ [th], rths @ [th])
        else if left then (lths @ [th], rths)
        else if right then (lths, rths @ [th])
        else (lths, rths)) ([],[]) pstate.prs_theorems in
      DB.nhprint "THS_LEFT: " pr_ths ths_left;
      DB.nhprint "THS_RIGHT: " pr_ths ths_right;
      let rthleft = ths_left |> List.fold_left (fun acc th ->
        if !mutual_induction && List.length acc >= 3 then
          raise_rules acc;
        let lhs_th, lvs_th = th.th_lhs, fv th.th_lhs in
        let unfs = unify_heap prog lhs_th lg |> get_unf_success in
        (* let unfs = List.first_nth !thd_max_num_unify unfs in *)
        let unfs =
          unfs |> List.map (fun unf ->
            let vs_unf, _ = List.split unf.unf_correct_ssts in
            match (diff_vs lvs_th vs_unf) with
            | [] -> [unf]
            | _ ->
              let nrhs_th = NO.remove_all_qvars
                              (subst unf.unf_correct_ssts th.th_rhs) in
              let nrhs_goal = NO.remove_all_qvars goal.gl_rhs in
              let rvs = dedup_vs ((fv th.th_rhs) @ (fv goal.gl_rhs)) in
              unify_heap prog nrhs_th nrhs_goal |> get_unf_success |>
              List.map (fun unf ->
                List.filter (fun (v, e) ->
                  let uvs = v :: (fv_exp e) in
                  (diff_vs uvs rvs = [])) unf.unf_correct_ssts) |>
              List.filter (fun ssts -> ssts != []) |>
              dedup_sstss |> (fun sstss -> []::sstss) |> List.map (fun ss ->
                {unf with unf_correct_ssts = unf.unf_correct_ssts @ ss})) |>
          List.concat in
        let unfs_ok, unfs_fail =
          unfs |> List.partition (unify_pure mode prog lhs_th lg) in
        let rule_ths = List.map (fun unf ->
          mk_rule_theorem th unf true) unfs_ok in
        let rule_ems = List.fold_left (fun acc unf ->
          let fail_reason = ID.analyze_fail_unf mode prog lhs_th lg unf in
          match fail_reason with
          | None -> acc
          | Some fr ->
            (* ignore unproductive failure *)
            DB.nhprint "choose_hypo: failure reason: " pr_pf fr;
            if (SBPuretp.check_consistency plg fr = MvlFalse) then acc
            else if (has_unprocessed_unplanned_excl_mid goal) then acc
            else
              let rth = mk_rule_theorem th unf true in
              let rem = mk_rule_excl_mid fr ~plan_rules:[rth] in
              acc @ [rem]) [] unfs_fail in
        acc @ rule_ths @ rule_ems) [] in
      let rthright = ths_right |> List.fold_left (fun acc th ->
        (* let rhs_th, rvs_th = th.th_rhs, fv th.th_rhs in *)
        let rqvs_th, hf_th, pf_th = extract_components_f th.th_rhs in
        let rqvs_gl, hf_gl, pf_gl = extract_components_f rhs_goal in
        let nrhs_th = mk_fbase hf_th pf_th in
        let nrhs_gl = mk_fbase hf_gl pf_gl in
        let unfs = unify_heap prog nrhs_th nrhs_gl |> get_unf_success |>
                   List.filter (fun unf ->
                     let nrqvs_th = rqvs_gl |> vars_of_qvars |>
                                    subst_vars unf.unf_correct_ssts |>
                                    fv_exps in
                     (subset_vs nrqvs_th (vars_of_qvars rqvs_gl))) in
        let rs = List.map (fun unf -> mk_rule_theorem th unf false) unfs in
        acc @ rs) [] in
      rthleft @ rthright
    | Some rc -> rc.crl_theorem
  with ERules res -> res

let rec choose_rule_infer_relation pstate goal : rule list =
  DB.trace_1 "choose_rule_infer_relation"
    (pr_gent, pr_rules) goal
    (fun () -> choose_rule_infer_relation_x pstate goal)

and choose_rule_infer_relation_x pstate goal : rule list =
  let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
  let hconsumed, trace = goal.gl_hconsumed, goal.gl_trace in
  try
    let lsts, rsts, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    let lemp, remp = lsts.fst_is_pure, rsts.fst_is_pure in
    let ldata, rdata = lsts.fst_has_data, rsts.fst_has_data in
    let lunkrel, runkrel = lsts.fst_has_unk_rform, rsts.fst_has_unk_rform in
    let gunkrel = lunkrel && runkrel in
    (* let has_view_right = tst.tst_view_right > 0 in *)
    let tsts = goal.gl_tstats in
    if not (is_pmode_infer goal) then
      raise (EAssums []);
    if (lsts.fst_num_prels = 0 && rsts.fst_num_prels = 0) then
      raise (EAssums []);
    if lemp && remp && gunkrel then
      raise (EAssums [(mk_assum lhs rhs hconsumed trace)]);
    if lemp && rdata && lunkrel then
      raise (EAssums [(mk_assum_false lhs hconsumed trace)]);
    (* TRUNG: ldata vs remp is not so reasonable to decide FALSE *)
    if ldata && remp && lunkrel then
      raise (EAssums [(mk_assum_false lhs hconsumed trace)]);
    if tsts.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then (
      DB.npprint "MAKE RHS FALSE by UNKREL";
      raise (EAssums [(mk_assum_false lhs hconsumed trace)]));
    (* default *)
    []
  with EAssums asms -> match asms with
    | [] -> []
    | asms::_ -> [mk_rule_infer_relation lhs rhs hconsumed asms]



(***************************************************************************)
(*************              Process spatial Rules              *************)

(** rule star data *)
let rec process_rule_star_data pstate goal rsd : derivation =
  DB.trace_2 "process_rule_star_data"
    (pr_g, pr_rsd, pr_drv) goal rsd
    (fun () -> process_rule_star_data_x pstate goal rsd)

and process_rule_star_data_x pstate goal rsd : derivation =
  let prog, ldata, rdata = pstate.prs_prog, rsd.rsd_lg_data, rsd.rsd_rg_data in
  if not (is_same_type_df ldata rdata) then (
    error ("rule star data: unmatched data type: "
      ^ (pr_df ldata) ^ " -- " ^ (pr_df rdata)));
  let ld_root, ld_args = ldata.dataf_root, ldata.dataf_args in
  let rd_root, rd_args = rdata.dataf_root, rdata.dataf_args in
  let eq_conds =
    let eq_args = mk_eq_el ld_args rd_args in
    if (eq_exp ld_root rd_root) then eq_args
    else mk_pconj [(mk_eq_exp ld_root rd_root); eq_args] in
  let nlhs =
    let f = mk_fbase (fst rsd.rsd_lg_rest) (snd rsd.rsd_lg_rest) in
    mk_qform rsd.rsd_lg_qvars f in
  let nrhs =
    let f = mk_fbase (fst rsd.rsd_rg_rest) (snd rsd.rsd_rg_rest) in
    let f = mk_hstar_f_pf f eq_conds in
    let nrhs = mk_qform rsd.rsd_rg_qvars f in
    NO.simplify_all ~infer:(is_pmode_infer goal) nrhs in
  let nldrgs, nrdrgs =
    let ldrgs, rdrgs = goal.gl_lhs_derived_groups, goal.gl_rhs_derived_groups in
    let nl = remove_derived_groups ldrgs (HData rsd.rsd_lg_data) in
    let nr = remove_derived_groups rdrgs (HData rsd.rsd_rg_data) in
    (nl, nr) in
  let rule = RlStarData rsd in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs;
            gl_rhs = nrhs;
            gl_hconsumed = goal.gl_hconsumed @ [(HData ldata)];
            gl_lhs_derived_groups = nldrgs;
            gl_rhs_derived_groups = nrdrgs; } in
  let ng = finalize_new_goal_update_all prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule star view *)
let rec process_rule_star_view pstate goal rsv : derivation =
  DB.trace_2 "process_rule_star_view"
    (pr_g, pr_rsv, pr_drv) goal rsv
    (fun () -> process_rule_star_view_x pstate goal rsv)

and process_rule_star_view_x pstate goal rsv : derivation =
  let prog, lview, rview = pstate.prs_prog, rsv.rsv_lg_view, rsv.rsv_rg_view in
  if not (is_same_type_vf lview rview) then (
    error ("rule star view: unmatched view type: "
      ^ (pr_vf lview) ^ " -- " ^ (pr_vf rview)));
  let ld_args, rd_args = lview.viewf_args, rview.viewf_args in
  let eq_conds = mk_eq_el ld_args rd_args in
  let nlhs =
    let f = mk_fbase (fst rsv.rsv_lg_rest) (snd rsv.rsv_lg_rest) in
    mk_qform rsv.rsv_lg_qvars f in
  let nrhs =
    let f = mk_fbase (fst rsv.rsv_rg_rest) (snd rsv.rsv_rg_rest) in
    let f = mk_hstar_f_pf f eq_conds in
    let nrhs = mk_qform rsv.rsv_rg_qvars f in
    NO.simplify_all ~infer:(is_pmode_infer goal) nrhs in
  let nldrgs, nrdrgs =
    let ldrgs, rdrgs = goal.gl_lhs_derived_groups, goal.gl_rhs_derived_groups in
    let nl = remove_derived_groups ldrgs (HView rsv.rsv_lg_view) in
    let nr = remove_derived_groups rdrgs (HView rsv.rsv_rg_view) in
    (nl, nr) in
  let rule = RlStarView rsv in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs;
            gl_rhs = nrhs;
            gl_hconsumed = goal.gl_hconsumed @ [(HView lview)];
            gl_lhs_derived_groups = nldrgs;
            gl_rhs_derived_groups = nrdrgs; } in
  let ng = finalize_new_goal_update_all prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule view left *)
let rec process_rule_view_left pstate goal rvl : derivation =
  DB.trace_2 "process_rule_view_left"
    (pr_g, pr_rvl, pr_drv) goal rvl
    (fun () -> process_rule_view_left_x pstate goal rvl)

and process_rule_view_left_x pstate goal rvl : derivation =
  (* DB.sprint ["PROCESS VIEW-LEFT: "; "\n -- ";  pr_gc goal;
   *            "\n -- "; pr_rvl rvl]; *)
  let prog = pstate.prs_prog in
  let rule = RlViewLeft rvl in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = rvl.rvl_fold_case.vfc_new_form} in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule view right *)
let rec process_rule_view_right pstate goal rvr : derivation =
  DB.trace_2 "process_rule_view_right"
    (pr_g, pr_rvr, pr_drv) goal rvr
    (fun () -> process_rule_view_right_x pstate goal rvr)

and process_rule_view_right_x pstate goal rvr : derivation =
  let prog = pstate.prs_prog in
  let ufh = (HView rvr.rvr_rg_view) in
  let nhs = collect_hatom rvr.rvr_unfold_case.vuc_view_case_form in
  let rdrgs = update_derived_groups goal.gl_rhs_derived_groups [ufh] nhs in
  let rule = RlViewRight rvr in
  let ng = {(prepare_new_goal goal) with
            gl_rhs = rvr.rvr_unfold_case.vuc_new_form;
            gl_rhs_derived_groups = rdrgs; } in
  let ng = finalize_new_goal_update_rhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(*************************************************************************)
(**********        Process induction and theorems rules        *************)

(** rule induction on formula *)
and process_rule_induction pstate goal rid : derivation =
  DB.trace_2 "process_rule_induction"
    (pr_g, pr_rid, pr_drv) goal rid
    (fun () -> process_rule_induction_x pstate goal rid)

and process_rule_induction_x pstate goal rid : derivation =
  (* record the hypothesis *)
  let prog = pstate.prs_prog in
  let hypos =
    if not rid.rid_record_hypo then goal.gl_hypos
    else goal.gl_hypos @ [(mk_hypothesis prog goal)] in
  let ngs =
    rid.rid_unfold_cases |>
    List.map (fun vc ->
      let nlhs = NO.simplify_all vc.vuc_new_form in
      let rule = RlInduction {rid with rid_unfold_cases = [vc]} in
      let ufh = HView rid.rid_lg_view in
      let nhs = collect_hatom vc.vuc_view_case_form in
      let ldrgs = update_derived_groups goal.gl_lhs_derived_groups [ufh] nhs in
      let ng = {(prepare_new_goal goal) with
                gl_lhs = nlhs;
                gl_lhs_derived_groups = ldrgs;
                gl_hypos = hypos;} in
      finalize_new_goal_update_lhs prog goal ng rule) in
  mk_derivation_goals (RlInduction rid) goal ngs

(** rule apply hypothesis *)
and process_rule_hypothesis pstate goal rhp : derivation =
  DB.trace_2 "process_rule_hypothesis"
    (pr_g, pr_rhp, pr_drv) goal rhp
    (fun () -> process_rule_hypothesis_x pstate goal rhp)

and process_rule_hypothesis_x pstate goal rhp : derivation =
  let prog = pstate.prs_prog in
  let hp_lhs, hp_rhs = rhp.rhp_hp.hp_lhs, rhp.rhp_hp.hp_rhs in
  let nhp_lhs = subst rhp.rhp_unf_ssts hp_lhs in
  let nhp_rhs = hp_rhs |> rename_all_qvars |>
                subst rhp.rhp_unf_ssts |>
                change_origin HorgHypo in
  let nlhs =
    let plhs_g = extract_pf goal.gl_lhs in
    let plhs_hp = extract_pf nhp_lhs in
    let nlhs = mk_hstar_f_hf nhp_rhs rhp.rhp_unf_residue in
    (* NOTE: encode the whole lhs of goal is costly *)
    (* let plhs = encode_lhs_goal pstate.prs_prog goal in *)
    nlhs |>
    mk_hstar_pf_f plhs_g |>
    mk_hstar_pf_f plhs_hp |>
    NO.remove_all_heap_exists_vars |>
    NO.simplify_all in
  let nhatoms = collect_hatom nhp_rhs in
  let ldrgs = goal.gl_lhs_derived_groups in
  let nldrgs = update_derived_groups ldrgs [] nhatoms in
  let rule = RlHypothesis rhp in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs;
            gl_lhs_derived_groups = nldrgs;
            gl_assums =
              goal.gl_assums @ rhp.rhp_assums; } in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule apply theorem *)
and process_rule_theorem pstate goal rth : derivation =
  DB.trace_2 "process_rule_theorem"
    (pr_g, pr_rth, pr_drv) goal rth
    (fun () -> process_rule_theorem_x pstate goal rth)

and process_rule_theorem_x pstate goal rth : derivation =
  let prog = pstate.prs_prog in
  let th_lhs, th_rhs = rth.rth_th.th_lhs, rth.rth_th.th_rhs in
  let rule = RlTheorem rth in
  let ng = match rth.rth_left with
    | true ->
      let nth_rhs = th_rhs |> rename_all_qvars |>
                    subst rth.rth_unf_ssts |>
                    change_origin HorgTheorem in
      let nlhs =
        let nlhs = mk_hstar_f_hf nth_rhs rth.rth_unf_residue in
        extract_pf goal.gl_lhs |>
        mk_hstar_f_pf nlhs |>
        NO.remove_all_heap_exists_vars |>
        NO.simplify_all in
      let hreplaced = rth.rth_th.th_lhs |> subst rth.rth_unf_ssts |>
                      collect_hatom in
      let nhatoms = collect_hatom nth_rhs in
      let ldrgs = goal.gl_lhs_derived_groups in
      let nldrgs = update_derived_groups ldrgs [] nhatoms in
      let ng = {(prepare_new_goal goal) with
                gl_lhs = nlhs;
                gl_hreplaced = hreplaced;
                gl_lhs_derived_groups = nldrgs; } in
      finalize_new_goal_update_lhs prog goal ng rule
    | false ->
      let nth_lhs = th_lhs |> rename_all_qvars |>
                    subst rth.rth_unf_ssts |>
                    change_origin HorgTheorem in
      (* let nthvs = diff_vs (fv nth_lhs) goal.gl_gstats.gst_fvs in *)
      let nrhs =
        let rqvs, _, rpf = extract_components_f goal.gl_rhs in
        rth.rth_unf_residue |> mk_hstar_f_hf nth_lhs |>
        mk_hstar_pf_f rpf |> mk_qform rqvs |>
        (* mk_fexists nthvs |> *)
        NO.simplify_all in
      let ng = {(prepare_new_goal goal) with
                gl_rhs = nrhs; } in
      finalize_new_goal_update_rhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule excluded middle *)
and process_rule_excluded_middle pstate goal rem : derivation =
  DB.trace_2 "process_rule_excluded_middle"
    (pr_g, pr_rem, pr_drv) goal rem
    (fun () -> process_rule_excluded_middle_x pstate goal rem)

and process_rule_excluded_middle_x pstate goal rem : derivation =
  let subgoals = List.map (fun emc ->
    let prog = pstate.prs_prog in
    let emc_cond =
      if (has_unk_rform_pf prog.prog_rels emc.emc_pure_cond) then
        NO.remove_all_qvars_pf emc.emc_pure_cond
      else emc.emc_pure_cond in
    let nlhs = mk_hstar_f_pf goal.gl_lhs emc_cond in
    let rule = RlExclMid {rem with rem_cases = [emc] } in
    let ng = {(prepare_new_goal goal) with
              gl_lhs = nlhs;
              gl_hooked_rules = emc.emc_rule_planned} in
    finalize_new_goal_update_lhs prog goal ng rule) rem.rem_cases in
  mk_derivation_goals (RlExclMid rem) goal subgoals

(** rule infer relation *)
and process_rule_infer_relation pstate goal rir : derivation =
  DB.trace_2 "process_rule_infer_relation"
    (pr_g, pr_rir, pr_drv) goal rir
    (fun () -> process_rule_infer_relation_x pstate goal rir)

and process_rule_infer_relation_x pstate goal rir : derivation =
  let prog = pstate.prs_prog in
  let asms = [rir.rir_assumption] in
  pstate.prs_assums <- pstate.prs_assums @ asms;
  let ng = {goal with gl_assums = goal.gl_assums @ asms} in
  let rule = RlInferRel rir in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_infer rule ng

(** rule generalize left *)
and process_rule_gen_left pstate goal rgl : derivation =
  DB.trace_2 "process_rule_gen_left"
    (pr_g, pr_rgl, pr_drv) goal rgl
    (fun () -> process_rule_gen_left_x pstate goal rgl)

and process_rule_gen_left_x pstate goal rgl : derivation =
  let rule = RlGenLeft rgl in
  let prog = pstate.prs_prog in
  let backjump = match rgl.rgl_base_hypo_unf with
    | None -> None
    | Some (hp, unf) when hp.hp_ent_id = goal.gl_ent_id -> None
    | Some (hp, un) -> Some hp.hp_ent_id in
  let ng = {(prepare_new_goal goal) with gl_lhs = rgl.rgl_new_lg} in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  match backjump with
  | None -> mk_derivation_goals rule goal [ng]
  | Some ent_id -> mk_derivation_backjump ent_id rule goal [ng]

(** rule weaken left *)
and process_rule_weaken_left pstate goal rwl : derivation =
  DB.trace_2 "process_rule_weaken_left"
    (pr_g, pr_rwl, pr_drv) goal rwl
    (fun () -> process_rule_weaken_left_x pstate goal rwl)

and process_rule_weaken_left_x pstate goal rwl : derivation =
  let rule = RlWeakenLeft rwl in
  let prog = pstate.prs_prog in
  let backjump = match rwl.rwl_base_hypo_unf with
    | None -> None
    | Some (hp, unf) when hp.hp_ent_id = goal.gl_ent_id -> None
    | Some (hp, unf) -> Some hp.hp_ent_id in
  let ng = {(prepare_new_goal goal) with gl_lhs = rwl.rwl_new_lg} in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  match backjump with
  | None -> mk_derivation_goals rule goal [ng]
  | Some ent_id -> mk_derivation_backjump ent_id rule goal [ng]


(******************************************************************)
(**********        Process normalization rules        *************)

(** rule equal left *)
let rec process_rule_equal_left pstate goal reql : derivation =
  DB.trace_1 "process_rule_equal_left" (pr_g, pr_drv)
    goal (fun () -> process_rule_equal_left_x pstate goal reql)

and process_rule_equal_left_x pstate goal reql : derivation =
  let prog = pstate.prs_prog in
  let nlhs, nrhs = NO.simplify_equal_lhs_rhs goal.gl_lhs goal.gl_rhs in
  let rule = RlEqualLeft reql in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs;
            gl_rhs = nrhs; } in
  let ng = finalize_new_goal_update_all prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule remove emp left *)
let rec process_rule_emp_left pstate goal reml : derivation =
  DB.trace_2 "process_rule_emp_left"
    (pr_g, pr_reml, pr_drv) goal reml
    (fun () -> process_rule_emp_left_x pstate goal reml)

and process_rule_emp_left_x pstate goal reml : derivation =
  let prog = pstate.prs_prog in
  let nlhs = NO.simplify_emp goal.gl_lhs in
  let rule = RlEmpLeft reml in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs; } in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule remove emp right *)
let rec process_rule_emp_right pstate goal remr : derivation =
  DB.trace_2 "process_rule_emp_right"
    (pr_g, pr_remr, pr_drv) goal remr
    (fun () -> process_rule_emp_right_x pstate goal remr)

and process_rule_emp_right_x pstate goal remr : derivation =
  let prog = pstate.prs_prog in
  let nrhs = NO.simplify_emp goal.gl_rhs in
  let rule = RlEmpRight remr in
  let ng = {(prepare_new_goal goal) with
            gl_rhs = nrhs; } in
  let ng = finalize_new_goal_update_rhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule remove exists left *)
let rec process_rule_exists_left pstate goal rexl : derivation =
  DB.trace_2 "process_rule_exists_left"
    (pr_g, pr_rexl, pr_drv) goal rexl
    (fun () -> process_rule_exists_left_x pstate goal rexl)

and process_rule_exists_left_x pstate goal rexl : derivation =
  let prog = pstate.prs_prog in
  let nlhs = NO.remove_all_exists_vars goal.gl_lhs in
  let rule = RlExistsLeft rexl in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs; } in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule remove exists right *)
let rec process_rule_exists_right pstate goal rexr : derivation =
  DB.trace_2 "process_rule_exists_right"
    (pr_g, pr_rexr, pr_drv) goal rexr
    (fun () -> process_rule_exists_right_x pstate goal rexr)

and process_rule_exists_right_x pstate goal rexr : derivation =
  let prog = pstate.prs_prog in
  let nrhs = NO.simplify_exists_var_by_equal goal.gl_rhs in
  let rule = RlExistsRight rexr in
  let ng = {(prepare_new_goal goal) with
            gl_rhs = nrhs; } in
  let ng = finalize_new_goal_update_rhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule drop left *)
let rec process_rule_drop_left pstate goal rdr : derivation =
  DB.trace_2 "process_rule_drop_left"
    (pr_g, pr_rdl, pr_drv) goal rdr
    (fun () -> process_rule_drop_left_x pstate goal rdr)

and process_rule_drop_left_x pstate goal rdl : derivation =
  let prog = pstate.prs_prog in
  let nlhs = rdl.rdl_lg in
  let rule = RlDropLeft rdl in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs; } in
  let ng = finalize_new_goal_update_lhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule drop right *)
let rec process_rule_drop_right pstate goal rdr : derivation =
  DB.trace_2 "process_rule_drop_right"
    (pr_g, pr_rdr, pr_drv) goal rdr
    (fun () -> process_rule_drop_right_x pstate goal rdr)

and process_rule_drop_right_x pstate goal rdr : derivation =
  let prog = pstate.prs_prog in
  let nrhs = rdr.rdr_rg in
  let rule = RlDropRight rdr in
  let ng = {(prepare_new_goal goal) with
            gl_rhs = nrhs; } in
  let ng = finalize_new_goal_update_rhs prog goal ng rule in
  mk_derivation_goals rule goal [ng]

(** rule unfold relation *)
let rec process_rule_unfold_relation pstate goal rur : derivation =
  DB.trace_2 "process_rule_unfold_relation"
    (pr_g, pr_rur, pr_drv) goal rur
    (fun () -> process_rule_unfold_relation_x pstate goal rur)

and process_rule_unfold_relation_x pstate goal rur : derivation =
  let prog = pstate.prs_prog in
  let rdefns = pstate.prs_prog.prog_rels in
  let nlhs =
    if rur.rur_lg_rels = [] then goal.gl_lhs
    else unfold_rform rdefns goal.gl_lhs in
  let nrhs =
    if rur.rur_rg_rels = [] then goal.gl_rhs
    else unfold_rform rdefns goal.gl_rhs in
  let rule = RlUnfoldRel rur in
  let ng = {(prepare_new_goal goal) with
            gl_lhs = nlhs;
            gl_rhs = nrhs; } in
  let ng =
    if (rur.rur_lg_rels != []) && (rur.rur_rg_rels != []) then
      finalize_new_goal_update_all prog goal ng rule
    else if (rur.rur_lg_rels != []) then
      finalize_new_goal_update_lhs prog goal ng rule
    else if (rur.rur_rg_rels != []) then
      finalize_new_goal_update_rhs prog goal ng rule
    else ng in
  mk_derivation_goals rule goal [ng]


(******************************************************************)
(**************        Process axioms Rules        ****************)

(** rule false left *)
let rec process_rule_false_left pstate goal rfl : derivation =
  DB.trace_2 "process_rule_false_left"
    (pr_g, pr_rfl, pr_drv) goal rfl
    (fun () -> process_rule_false_left_x pstate goal rfl)

and process_rule_false_left_x pstate goal rfl : derivation =
  mk_derivation_valid (RlFalseLeft rfl) goal

(** rule pure entailment *)
let rec process_rule_pure_entail pstate goal rpe : derivation =
  DB.trace_2 "process_rule_pure_entail"
    (pr_g, pr_rpe, pr_drv) goal rpe
    (fun () -> process_rule_pure_entail_x pstate goal rpe)

and process_rule_pure_entail_x pstate goal rpe : derivation =
  let status = rpe.rpe_status in
  if (status = MvlTrue) then mk_derivation_valid (RlPureEntail rpe) goal
  else if (status = MvlFalse) then mk_derivation_invalid (RlPureEntail rpe) goal
  else mk_derivation_unknown (RlPureEntail rpe) goal

(*****************************************************************************)
(******************        COMPARE INFERENCE RULES        ********************)

let compare_hypothesis hp1 hp2 : priority =
  try
    let lsts1, rsts1 = hp1.hp_lstats, hp1.hp_rstats in
    let lsts2, rsts2 = hp2.hp_lstats, hp2.hp_rstats in
    let dsize1 = lsts1.fst_num_hatoms - rsts1.fst_num_hatoms in
    let dsize2 = lsts2.fst_num_hatoms - rsts2.fst_num_hatoms in
    if (dsize1 > dsize2) then raise_prio PrioHigh ~msg:"compare #ldatas";
    if (dsize1 < dsize2) then raise_prio PrioLow ~msg:"compare #ldatas";
    let dview1 = lsts1.fst_num_views - rsts1.fst_num_views in
    let dview2 = lsts2.fst_num_views - rsts2.fst_num_views in
    if (dview1 > dview2) then raise_prio PrioHigh ~msg:"compare #lviews";
    if (dview1 < dview2) then raise_prio PrioLow ~msg:"compare #lviews";
    PrioEqual
  with EPrio (res, msg) -> res

(*******************************************)
(***********      star data      ***********)
let compare_star_data_vs_star_data pstate goal r1 r2  : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if r2.rsd_trivial then raise_prio PrioLow;
    if (not r1.rsd_can_match_all_args) && r2.rsd_can_match_all_args then
      raise_prio PrioLow;
    if r1.rsd_can_match_all_args && (not r2.rsd_can_match_all_args) then
      raise_prio PrioHigh;
    if r1.rsd_has_common_arg && (not r2.rsd_has_common_arg) then
      raise_prio PrioHigh;
    if r2.rsd_has_common_arg && (not r1.rsd_has_common_arg) then
      raise_prio PrioLow;
    if (is_pmode_infer goal) then (
      let ldorg1 = r1.rsd_lg_data.dataf_origin in
      let rdorg1 = r1.rsd_rg_data.dataf_origin in
      let ldorg2 = r2.rsd_lg_data.dataf_origin in
      let rdorg2 = r2.rsd_rg_data.dataf_origin in
      if (ldorg1 = HorgUnfold) && (rdorg1= HorgUnfold) &&
         not ((ldorg2 = HorgUnfold) && (rdorg2 = HorgUnfold)) then
        raise_prio PrioHigh;
      if (ldorg2 = HorgUnfold) && (rdorg2 = HorgUnfold) &&
         not ((ldorg1 = HorgUnfold) && (rdorg1 = HorgUnfold)) then
        raise_prio PrioLow;
      let d1_derived = (is_derived_df r1.rsd_lg_data) &&
                       not (is_derived_df r1.rsd_rg_data) in
      let d2_derived = (is_derived_df r2.rsd_lg_data) &&
                       not (is_derived_df r2.rsd_rg_data) in
      if d1_derived && (not d2_derived) then raise_prio PrioHigh;
      if (not d1_derived) && d2_derived then raise_prio PrioLow;
      if (goal.gl_tstats.tst_star_data = 0) &&
         ((r1.rsd_lg_data.dataf_origin = HorgInput) ||
          (r1.rsd_rg_data.dataf_origin = HorgInput)) then
        raise_prio PrioLow ;
      if (goal.gl_tstats.tst_star_data = 0) &&
         ((r2.rsd_lg_data.dataf_origin = HorgInput) ||
          (r2.rsd_rg_data.dataf_origin = HorgInput)) then
        raise_prio PrioHigh);
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_star_view pstate goal r1 r2 : priority =
  try
    if (r1.rsd_trivial) then raise_prio PrioHigh;
    if (r2.rsv_trivial) then raise_prio PrioLow;
    if (not r1.rsd_can_match_all_args) && r2.rsv_can_match_all_args then
      raise_prio PrioLow;
    if r1.rsd_can_match_all_args && (not r2.rsv_can_match_all_args) then
      raise_prio PrioHigh;
    (* if (r2.rsv_can_match_all_args) then *)
    (*   raise_prio PrioLow; *)
    if r2.rsv_can_match_all_args && (goal.gl_precise_unifying_plans != []) then
      raise_prio PrioLow;
    if r1.rsd_has_common_arg && (not r2.rsv_has_common_arg) then
      raise_prio PrioHigh;
    if (not r1.rsd_has_common_arg) && r2.rsv_has_common_arg then
      raise_prio PrioLow;
    if (not r1.rsd_has_common_arg) then raise_prio PrioLow;
    if (is_pmode_infer goal) &&
       (is_derived_df r1.rsd_lg_data) && (is_derived_df r1.rsd_rg_data) then
      raise_prio PrioHigh;
    if (is_pmode_infer goal) && (goal.gl_tstats.tst_star_data = 0) &&
       ((r1.rsd_lg_data.dataf_origin = HorgInput) ||
        (r1.rsd_rg_data.dataf_origin = HorgInput)) then
      raise_prio PrioLow ;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_view_left pstate goal r1 r2 : priority =
  try
    PrioHigh
  with EPrio (res, msg) -> res

let compare_star_data_vs_view_right pstate goal r1 r2 : priority =
  try
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    if r1.rsd_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if r1.rsd_has_common_arg &&
       (subset_vs (fv_vf r2.rvr_rg_view) (rst.fst_qvs)) then
      raise_prio PrioHigh;
    if not r1.rsd_has_common_arg &&
       r2.rvr_has_data_same_root &&
       (r2.rvr_num_ldatas >= r2.rvr_num_rdatas) then
      raise_prio PrioLow;
    if r1.rsd_has_common_arg &&
       not r2.rvr_has_data_same_root then
      raise_prio PrioHigh;
    if (is_pmode_infer goal) then (
      if (not r1.rsd_has_common_arg) then
        raise_prio PrioLow;
      if (not r1.rsd_has_common_arg) &&
         (r2.rvr_has_data_same_root || r2.rvr_has_data_same_args) then
        raise_prio PrioLow;
      if (is_derived_df r1.rsd_lg_data) && (is_derived_df r1.rsd_rg_data) then
        raise_prio PrioHigh;
      if (goal.gl_tstats.tst_induction > 0) && (not r1.rsd_has_common_arg) then
        raise_prio PrioLow;
      if (goal.gl_tstats.tst_induction > 0) &&
         (is_pmode_infer_basic goal) &&
         (not r1.rsd_rdata_has_fvars) then
        raise_prio PrioHigh;
      if (goal.gl_tstats.tst_star_data = 0) &&
         ((r1.rsd_lg_data.dataf_origin = HorgInput) ||
          (r1.rsd_rg_data.dataf_origin = HorgInput)) then
        raise_prio PrioLow);
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_induction pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if (is_latest_spatial_rule_hypothesis goal) then raise_prio PrioHigh;
    if (not r1.rsd_has_common_arg) then raise_prio PrioLow;
    let _ = match is_pmode_infer goal with
      | true ->
        if (is_derived_df r1.rsd_lg_data) &&
           (is_derived_df r1.rsd_rg_data) then
          raise_prio PrioHigh;
        if (goal.gl_tstats.tst_star_data = 0) &&
           ((is_origin_input_df r1.rsd_lg_data) ||
            (is_origin_input_df r1.rsd_rg_data)) then
          raise_prio PrioLow
      | false -> () in
    if not r2.rid_has_data_common_arg_indt_case then raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_hypothesis pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    let _ = match is_pmode_infer goal with
      | true ->
        if is_latest_spatial_rule_view_right goal then
          raise_prio PrioHigh;
      | false ->
        if not r1.rsd_has_common_arg then
          raise_prio PrioLow; in
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_theorem pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if (not r1.rsd_has_common_arg) then raise_prio PrioLow;
    (* if is_latest_spatial_rule_theorem goal then raise_prio PrioHigh; *)
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_excl_mid pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if (is_recent_rule_induction_without_hypothesis goal) &&
       (is_excl_mid_seed_rule_hypo r2) then
      raise_prio PrioLow;
    if (r1.rsd_has_common_arg) && (is_pmode_infer goal) then
      raise_prio PrioHigh;
    if (not r1.rsd_has_common_arg) then raise_prio PrioLow;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_data_vs_gen_left pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if r1.rsd_has_common_arg then raise_prio PrioHigh;
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_star_data_vs_weaken_left pstate goal r1 r2 : priority =
  try
    if r1.rsd_trivial then raise_prio PrioHigh;
    if r1.rsd_has_common_arg then raise_prio PrioHigh;
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_star_data_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_star_data_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_star_data_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_star_data_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_star_data_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_star_data_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_star_data_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_star_data_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_star_data_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_star_data_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_star_data: not expect rule: " ^ (pr_rule r2))

(*******************************************)
(***********      star view      ***********)

let compare_star_view_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_star_view pstate goal r2 r1)

let compare_star_view_vs_star_view pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if r2.rsv_trivial then raise_prio PrioLow;
    if r1.rsv_can_match_all_args && (not r2.rsv_can_match_all_args) then
      raise_prio PrioHigh;
    if r2.rsv_can_match_all_args && (not r1.rsv_can_match_all_args) then
      raise_prio PrioLow;
    if r1.rsv_has_common_arg && (not r2.rsv_has_common_arg) then
      raise_prio PrioHigh;
    if (not r1.rsv_has_common_arg) && r2.rsv_has_common_arg then
      raise_prio PrioLow;
    if r1.rsv_can_match_all_args && (goal.gl_precise_unifying_plans != []) then
      raise_prio PrioHigh;
    if r2.rsv_can_match_all_args && (goal.gl_precise_unifying_plans != []) then
      raise_prio PrioLow;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_view_left pstate goal r1 r2 : priority =
  try
    PrioHigh
  with EPrio (res, msg) -> res

let compare_star_view_vs_view_right pstate goal r1 r2 : priority =
  try
    let lsts, rsts = goal.gl_lstats, goal.gl_rstats in
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if is_pmode_prove goal &&
       not (is_latest_spatial_rule_induction goal) &&
       r1.rsv_can_match_all_args then
      raise_prio PrioHigh;
    if is_pmode_prove goal && not r1.rsv_can_match_all_args then
      raise_prio PrioLow;
    if r1.rsv_can_match_all_args && goal.gl_precise_unifying_plans != [] then
      raise_prio PrioHigh;
    if r2.rvr_has_data_same_root && r2.rvr_num_ldatas >= r2.rvr_num_rdatas then
      raise_prio PrioLow;
    if lsts.fst_num_datas = 0 && rsts.fst_num_datas = 0
       && (r1.rsv_has_common_arg) then
      raise_prio PrioHigh;
    if is_pmode_infer goal && goal.gl_tstats.tst_induction > 0 &&
       r1.rsv_rview_has_fvars && not r1.rsv_has_common_arg then
      raise_prio PrioLow;
    if (is_pmode_infer_basic goal) && (goal.gl_tstats.tst_induction > 0) &&
       (not r1.rsv_rview_has_fvars) then
      raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_induction pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if is_latest_spatial_rule_theorem goal && r1.rsv_has_common_arg then
      raise_prio PrioHigh;
    if (is_pmode_infer goal) then (
      if goal.gl_tstats.tst_induction > 0 && r1.rsv_has_common_arg then
        raise_prio PrioHigh;
      if goal.gl_tstats.tst_induction = 0 then
        raise_prio PrioLow);
    if r1.rsv_can_match_all_args && goal.gl_precise_unifying_plans != [] then
      raise_prio PrioHigh;
    if r1.rsv_can_match_all_args then
      raise_prio PrioHigh;
    if is_pmode_prove goal && not r1.rsv_can_match_all_args then
      raise_prio PrioLow;
    (* if not r2.rid_has_data_common_arg_indt_case then raise_prio PrioHigh; *)
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_hypothesis pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    let tst = goal.gl_tstats in
    if (r1.rsv_can_match_all_args) then
      raise_prio PrioHigh;
    if (is_pmode_prove goal) && (not r1.rsv_can_match_all_args) then
      raise_prio PrioLow;
    if (is_pmode_infer goal) then (
      if (tst.tst_induction > tst.tst_hypothesis) then
        raise_prio PrioLow;
      if (tst.tst_induction <= tst.tst_hypothesis) then
        raise_prio PrioHigh);
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_theorem pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if r1.rsv_can_match_all_args && (goal.gl_precise_unifying_plans != []) then
      raise_prio PrioHigh;
    if (is_pmode_prove goal) && (not r1.rsv_can_match_all_args) then
      raise_prio PrioLow;
    if r2.rth_th.th_origin = LorgSynth then raise_prio PrioLow;
    (* if is_latest_spatial_rule_theorem goal then raise_prio PrioHigh; *)
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_excl_mid pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if (r1.rsv_can_match_all_args) then
      raise_prio PrioHigh;
    if (is_pmode_prove goal) && (not r1.rsv_can_match_all_args) then
      raise_prio PrioLow;
    if (is_recent_rule_induction_without_hypothesis goal) &&
       (is_excl_mid_seed_rule_hypo r2) then
      raise_prio PrioLow;
    if (r1.rsv_has_common_arg) && (is_pmode_infer goal) then
      raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_star_view_vs_gen_left pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if r1.rsv_has_common_arg then raise_prio PrioHigh;
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_star_view_vs_weaken_left pstate goal r1 r2 : priority =
  try
    if r1.rsv_trivial then raise_prio PrioHigh;
    if goal.gl_precise_unifying_plans != [] then raise_prio PrioHigh;
    if r1.rsv_has_common_arg then raise_prio PrioHigh;
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_star_view_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_star_view_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_star_view_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_star_view_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_star_view_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_star_view_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_star_view_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_star_view_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_star_view_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_star_view_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_star_view: not expect rule: " ^ (pr_rule r2))

(********************************************)
(***********      view left      ***********)

let compare_view_left_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_view_left pstate goal r2 r1)

let compare_view_left_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_view_left pstate goal r2 r1)

let compare_view_left_vs_view_left pstate goal r1 r2 : priority =
  try
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_view_left_vs_view_right pstate goal r1 r2 : priority =
  try
    let common_arg1 = r1.rvl_has_view_common_args in
    let common_arg2 = r2.rvr_has_data_same_root ||
                      r2.rvr_has_data_same_args in
    if common_arg1 && not common_arg2 then raise_prio PrioHigh;
    if not common_arg1 && common_arg2 then raise_prio PrioLow;
    (* default *)
    PrioEqual
  with EPrio (res, msg)-> res

let compare_view_left_vs_induction pstate goal r1 r2 : priority =
  try
    let common_arg1 = r1.rvl_has_view_common_args in
    let common_arg2 = r2.rid_has_data_same_root ||
                      r2.rid_has_data_common_arg_indt_case in
    if common_arg1 && not common_arg2 then raise_prio PrioHigh;
    if not common_arg1 && common_arg2 then raise_prio PrioLow;
    (* default *)
    PrioEqual
  with EPrio (res, msg)-> res

let compare_view_left_vs_hypothesis pstate goal r1 r2 : priority =
  try
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_left_vs_theorem pstate goal r1 r2 : priority =
  try
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_left_vs_excl_mid pstate goal r1 r2 : priority =
  try
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_left_vs_gen_left pstate goal r1 r2 : priority =
  try
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_left_vs_weaken_left pstate goal r1 r2 : priority =
  try
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_left_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_view_left_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_view_left_vs_star_view pstate goal r1 r2
  | RlViewLeft r2 -> compare_view_left_vs_view_left pstate goal r1 r2
  | RlViewRight r2 -> compare_view_left_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_view_left_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_view_left_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_view_left_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_view_left_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_view_left_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_view_left_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_view_left: not expect rule: " ^ (pr_rule r2))

(********************************************)
(***********      view right      ***********)

let compare_view_right_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_view_right pstate goal r2 r1)

let compare_view_right_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_view_right pstate goal r2 r1)

let compare_view_right_vs_view_right pstate goal r1 r2 : priority =
  try
    let lst, rst, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    let ufc1, ufc2 = r1.rvr_unfold_case, r2.rvr_unfold_case in
    let unfold_same_view = eq_vf r1.rvr_rg_view r2.rvr_rg_view in
    let _ = match is_pmode_infer goal, unfold_same_view with
      | false, _ ->
        if r1.rvr_has_data_same_root && (not r2.rvr_has_data_same_root) &&
           (r1.rvr_num_ldatas >= r1.rvr_num_rdatas) then
          raise_prio PrioHigh;
        if r2.rvr_has_data_same_root && (not r1.rvr_has_data_same_root) &&
           (r2.rvr_num_ldatas >= r2.rvr_num_rdatas) then
          raise_prio PrioLow;
        if (subset_vs (fv_vf r1.rvr_rg_view) (rst.fst_qvs)) &&
           not (subset_vs (fv_vf r2.rvr_rg_view) (rst.fst_qvs)) then
          raise_prio PrioLow;
        if not (subset_vs (fv_vf r1.rvr_rg_view) (rst.fst_qvs)) &&
           (subset_vs (fv_vf r2.rvr_rg_view) (rst.fst_qvs)) then
          raise_prio PrioHigh;
        (* check indt case of right view *)
        let rview = r1.rvr_rg_view in
        if not ufc1.vuc_base_case && not ufc2.vuc_base_case then (
          let lufcs_indt_same_view =
            goal.gl_trace |> List.map (fun tri -> match tri.tri_rule with
              | RlInduction rid -> rid.rid_unfold_cases
              | _ -> []) |> List.concat |>
            List.filter (fun lufc ->
              not lufc.vuc_base_case &&
              eq_s lufc.vuc_view.viewf_name rview.viewf_name &&
              is_common_args_vf lufc.vuc_view rview) in
          let lufcs_case1 =
            lufcs_indt_same_view |> List.filter (fun lufc ->
              lufc.vuc_view_case_id = ufc1.vuc_view_case_id) in
          let lufcs_case2 =
            lufcs_indt_same_view |> List.filter (fun lufc ->
              lufc.vuc_view_case_id = ufc2.vuc_view_case_id) in
          if lufcs_case1 != [] && lufcs_case2 = [] then raise_prio PrioHigh;
          if lufcs_case1 = [] && lufcs_case2 != [] then raise_prio PrioLow;);
      | true, true ->
        if (tst.tst_view_right = 0 && tst.tst_induction > 0 &&
            lst.fst_num_datas > rst.fst_num_datas) then (
          if ufc1.vuc_base_case && not ufc2.vuc_base_case then
            raise_prio PrioLow;
          if not ufc1.vuc_base_case && ufc2.vuc_base_case then
            raise_prio PrioHigh;);
        (* check number of hatoms *)
        if (lst.fst_hatoms = []) &&
           (is_pure_f r1.rvr_unfold_case.vuc_new_form) then
          raise_prio PrioHigh;
        if (lst.fst_hatoms = []) &&
           (is_pure_f r2.rvr_unfold_case.vuc_new_form) then
          raise_prio PrioLow;
        let same_num_hatom1 = r1.rvr_num_ldatas = r1.rvr_num_rdatas &&
                              r1.rvr_num_lviews = r1.rvr_num_rviews in
        let same_num_hatom2 = r2.rvr_num_ldatas = r2.rvr_num_rdatas &&
                              r2.rvr_num_lviews = r2.rvr_num_rviews in
        if same_num_hatom1 && (not same_num_hatom2) then
          raise_prio PrioHigh;
        if (not same_num_hatom1) && same_num_hatom2 then
          raise_prio PrioLow;
      | true, false ->
        if (r1.rvr_has_data_same_root || r1.rvr_has_data_same_args) &&
           not (r2.rvr_has_data_same_root || r2.rvr_has_data_same_args) then
          raise_prio PrioHigh;
        if (r2.rvr_has_data_same_root || r2.rvr_has_data_same_args) &&
           not (r1.rvr_has_data_same_root || r1.rvr_has_data_same_args) then
          raise_prio PrioLow; in
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_view_right_vs_induction pstate goal r1 r2 : priority =
  try
    let lst, rst, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    if r2.rid_trivial && not (is_pmode_infer goal) then
      raise_prio PrioLow;
    DB.npprint "CMP VR IDF: data same root";
    if r1.rvr_has_data_same_root &&
       (not r1.rvr_unfold_case.vuc_base_case) &&
       (r1.rvr_num_ldatas >= r1.rvr_num_rdatas) then
      raise_prio PrioHigh;
    DB.npprint "CMP VR IDF: unfold base case";
    let _ = match is_pmode_infer goal with
      | true ->
        if tst.tst_induction = 0 then
          raise_prio PrioLow;
        if (r1.rvr_unfold_case.vuc_base_case) &&
           (goal.gl_has_unplanned_excl_mid) then
          raise_prio PrioHigh;
      | false ->
        if (tst.tst_induction = 0) then raise_prio PrioLow;
        if (lst.fst_num_datas <= rst.fst_num_datas) then raise_prio PrioLow;
        if (is_recent_rule_induction_without_view_right goal) then
          raise_prio PrioHigh in
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_view_right_vs_hypothesis pstate goal r1 r2 : priority =
  try
    let vdefns = pstate.prs_prog.prog_views in
    if r1.rvr_has_data_same_root &&
       (r1.rvr_num_ldatas >= r1.rvr_num_rdatas) &&
       (is_latest_spatial_rule_hypothesis goal) then
      raise_prio PrioHigh;
    let _ = match is_pmode_infer goal with
      | true ->
        if is_latest_spatial_rule_induction goal then
          raise_prio PrioHigh;
      | false ->
        let srules = get_latest_spatial_rules goal 1 in
        let _ = match srules with
          | (RlInduction rid)::_ ->
            let r1vd = get_view_recur_direction vdefns r1.rvr_rg_view in
            let r2vd = get_view_recur_direction vdefns rid.rid_lg_view in
            if (r1vd != r2vd) then raise_prio PrioLow
          | _ -> () in
        if List.length r1.rvr_rg_view.viewf_args <= 3 &&
           is_latest_spatial_rule_induction goal then
          raise_prio PrioHigh in
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_right_vs_theorem pstate goal r1 r2 : priority =
  try
    if r2.rth_th.th_origin = LorgSynth then raise_prio PrioLow;
    if r1.rvr_has_data_same_root &&
       (r1.rvr_num_ldatas >= r1.rvr_num_rdatas) then
      raise_prio PrioHigh;
    if (is_theorem_applied_earlier ~left:r2.rth_left goal r2.rth_th) then
      raise_prio PrioLow;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_view_right_vs_excl_mid pstate goal r1 r2 : priority =
  try
    if (is_latest_spatial_rule_excl_middle goal) then
      raise_prio PrioHigh;
    if (is_latest_spatial_rule_hypothesis goal) then
      raise_prio PrioHigh;
    if (r1.rvr_unfold_case.vuc_base_case) &&
       (goal.gl_has_unplanned_excl_mid) &&
       (is_pmode_infer goal) then
      raise_prio PrioHigh;
    let _ = match goal.gl_proof_mode with
      | PrfInferLhs | PrfInferRhs ->
        if (not r1.rvr_has_data_same_root) &&
           (not r1.rvr_has_data_same_args) then
          raise_prio PrioLow
      | PrfInferBasic | PrfInferAll -> raise_prio PrioHigh;
      | _ ->
        if (is_recent_rule_induction_without_hypothesis goal) &&
           (is_excl_mid_seed_rule_hypo r2) then
          raise_prio PrioLow;
        if (List.for_all is_int_typ (collect_typ_pf r2.rem_seed_cond)) then
          raise_prio PrioLow;
        if r2.rem_seed_rule.ems_view_right |> List.exists (fun x ->
          eq_vf r1.rvr_rg_view x.rvr_rg_view) then
          raise_prio PrioHigh in
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_view_right_vs_gen_left pstate goal r1 r2 : priority =
  try
    if r1.rvr_trivial then raise_prio PrioHigh;
    if r2.rgl_base_hypo_unf = None then raise_prio PrioHigh;
    if not r1.rvr_has_data_same_root &&
       not r1.rvr_has_data_same_args then raise_prio PrioLow;
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_view_right_vs_weaken_left pstate goal r1 r2 : priority =
  try
    if r1.rvr_trivial then raise_prio PrioHigh;
    if r2.rwl_base_hypo_unf = None then raise_prio PrioHigh;
    if r1.rvr_has_data_same_root then raise_prio PrioHigh;
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_view_right_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_view_right_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_view_right_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_view_right_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_view_right_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_view_right_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_view_right_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_view_right_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_view_right_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_view_right_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_view_right: not expect rule: " ^ (pr_rule r2))


(******************************************************)
(***********      induction on formula      ***********)

let compare_induction_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_induction pstate goal r2 r1)

let compare_induction_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_induction pstate goal r2 r1)

let compare_induction_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_induction pstate goal r2 r1)

let compare_induction_vs_induction pstate goal r1 r2 : priority =
  try
    let vdefns = pstate.prs_prog.prog_views in
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    let v1_recurd = get_view_recur_direction vdefns r1.rid_lg_view in
    let v2_recurd = get_view_recur_direction vdefns r2.rid_lg_view in
    (* trivial *)
    if (r1.rid_trivial && (not r2.rid_trivial)) then raise_prio PrioHigh;
    if (r2.rid_trivial && (not r1.rid_trivial)) then raise_prio PrioLow;
    (* check unfold of same root *)
    let has_same_root1 = r1.rid_has_data_same_root && v1_recurd = VrdHead in
    let has_same_root2 = r2.rid_has_data_same_root && v2_recurd = VrdHead in
    if has_same_root1 && not has_same_root2 then raise_prio PrioHigh;
    if not has_same_root1 && has_same_root2 then raise_prio PrioLow;
    (* check unfold of common args *)
    let has_common_arg1 = r1.rid_has_data_common_arg_indt_case &&
                          v1_recurd = VrdTail in
    let has_common_arg2 = r2.rid_has_data_common_arg_indt_case &&
                          v2_recurd = VrdTail in
    if has_common_arg1 && not has_common_arg2 then raise_prio PrioHigh;
    if not has_common_arg1 && has_common_arg2 then raise_prio PrioLow;
    (* view common roots *)
    if r1.rid_has_view_common_root && v1_recurd = VrdHead &&
       not r2.rid_has_view_common_root then
      raise_prio PrioHigh;
    if r2.rid_has_view_common_root && v2_recurd = VrdHead &&
       not r1.rid_has_view_common_root then
      raise_prio PrioLow;
    (* view common args *)
    if r1.rid_has_data_common_arg_indt_case && v1_recurd = VrdTail &&
       not (r2.rid_has_data_common_arg_indt_case && v2_recurd = VrdTail) then
      raise_prio PrioHigh;
    if r2.rid_has_data_common_arg_indt_case && v2_recurd = VrdTail &&
       not (r1.rid_has_data_common_arg_indt_case && v1_recurd = VrdTail) then
      raise_prio PrioLow;
    let _ = match (is_pmode_infer goal) with
      | true ->
        if (intersected_vs r1.rid_lg_view_vars rst.fst_fvs) &&
           not (intersected_vs r2.rid_lg_view_vars rst.fst_fvs) then
          raise_prio PrioHigh;
        if (intersected_vs r2.rid_lg_view_vars rst.fst_fvs) &&
           not (intersected_vs r1.rid_lg_view_vars rst.fst_fvs) then
          raise_prio PrioLow;
        if not (mem_ss r1.rid_lg_view.viewf_name rst.fst_view_names) &&
           (mem_ss r2.rid_lg_view.viewf_name rst.fst_view_names) then
          raise_prio PrioHigh;
        if not (mem_ss r2.rid_lg_view.viewf_name rst.fst_view_names) &&
           (mem_ss r1.rid_lg_view.viewf_name rst.fst_view_names) then
          raise_prio PrioLow;
      | false ->
        (* view position *)
        let r1_indt_pos =
          (r1.rid_lg_view_pos = HpHead && v1_recurd = VrdHead) ||
          (r1.rid_lg_view_pos = HpTail && v1_recurd = VrdTail) in
        let r2_indt_pos =
          (r2.rid_lg_view_pos = HpHead && v2_recurd = VrdHead) ||
          (r2.rid_lg_view_pos = HpTail && v2_recurd = VrdTail) in
        if r1_indt_pos && not r2_indt_pos then raise_prio PrioHigh;
        if not r1_indt_pos && r2_indt_pos then raise_prio PrioLow;
        if not r1_indt_pos && not r2_indt_pos then (
          if r1.rid_record_hypo && not r2.rid_record_hypo then
            raise_prio PrioLow;
          if not r1.rid_record_hypo && r2.rid_record_hypo then
            raise_prio PrioHigh;);
        (* inductive vars *)
        let common_vs = intersect_vs r1.rid_lg_view_vars r2.rid_lg_view_vars in
        let rvs = rst.fst_fvs in
        let indt_vs1 = get_view_inductive_vars vdefns r1.rid_lg_view in
        let indt_vs2 = get_view_inductive_vars vdefns r2.rid_lg_view in
        let common_indt_vs1 = intersected_vs indt_vs1 common_vs in
        let common_indt_vs2 = intersected_vs indt_vs2 common_vs in
        if common_indt_vs1 && not common_indt_vs2 then raise_prio PrioHigh;
        if not common_indt_vs1 && common_indt_vs2 then raise_prio PrioLow;
        let rvs_indt_vs1 = intersected_vs indt_vs1 rvs in
        let rvs_indt_vs2 = intersected_vs indt_vs2 rvs in
        if not rvs_indt_vs1 && rvs_indt_vs2 then raise_prio PrioHigh;
        if rvs_indt_vs1 && not rvs_indt_vs2 then raise_prio PrioLow in
    let _ = if is_pmode_unsat goal then (
      if r1.rid_has_related_emid_cond && not r2.rid_has_related_emid_cond then
        raise_prio PrioHigh;
      if not r1.rid_has_related_emid_cond && r2.rid_has_related_emid_cond then
        raise_prio PrioLow;) in
    (* default *)
    PrioEqual
  with EPrio (res, msg)-> res

let compare_induction_vs_hypothesis pstate goal r1 r2 : priority =
  try
    if (r1.rid_trivial) then raise_prio PrioHigh;
    if not r1.rid_has_data_common_arg_indt_case then raise_prio PrioLow;
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_induction_vs_theorem pstate goal r1 r2 : priority =
  try
    (* if is_latest_spatial_rule_theorem goal then *)
    (*   raise_prio PrioHigh; *)
    if (is_theorem_applied_earlier ~left:r2.rth_left goal r2.rth_th) then
      raise_prio PrioLow;
    if (r2.rth_th.th_origin = LorgUser) &&
       ((goal.gl_lstats.fst_num_hatoms < goal.gl_rstats.fst_num_hatoms) ||
        (r2.rth_th.th_lstats > r2.rth_th.th_rstats)) then
      raise_prio PrioLow;
    if r2.rth_th.th_origin = LorgSynth then raise_prio PrioLow;
    if not r1.rid_has_data_common_arg_indt_case then raise_prio PrioLow;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_induction_vs_excl_mid pstate goal r1 r2 : priority =
  try
    if (r1.rid_has_data_same_root) then raise_prio PrioHigh;
    if (is_recent_rule_induction_without_hypothesis goal) &&
       (is_excl_mid_seed_rule_hypo r2) then raise_prio PrioLow;
    if (r1.rid_trivial) && not (is_pmode_infer goal) then
      raise_prio PrioHigh;
    if not (is_excl_mid_seed_rule_hypo r2) then raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_induction_vs_gen_left pstate goal r1 r2 : priority =
  try
    let lst = goal.gl_lstats in
    if r1.rid_trivial then raise_prio PrioHigh;
    let _ = if is_pmode_unsat goal then (
      if r1.rid_has_related_emid_cond then raise_prio PrioHigh;
      if intersected_vs lst.fst_fpvs r1.rid_lg_view_vars &&
         r1.rid_lg_view.viewf_ancestor_ids = [] then raise_prio PrioHigh;
      if not r1.rid_has_related_emid_cond &&
         r2.rgl_has_gen_emid_vars then raise_prio PrioLow;
      if r2.rgl_has_gen_unfolded_exps then raise_prio PrioLow;
    ) in
    if r1.rid_lg_view.viewf_origin = HorgInput &&
       r2.rgl_base_hypo_unf != None then raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_induction_vs_weaken_left pstate goal r1 r2 : priority =
  try
    if r1.rid_trivial then raise_prio PrioHigh;
    let _ = if is_pmode_unsat goal then (
      if r1.rid_has_related_emid_cond then raise_prio PrioHigh;
      if not r1.rid_has_related_emid_cond && r2.rwl_has_gen_emid_vars then
        raise_prio PrioLow) in
    if r1.rid_lg_view.viewf_origin = HorgInput &&
       r2.rwl_base_hypo_unf != None then raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_induction_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_induction_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_induction_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_induction_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_induction_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_induction_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_induction_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_induction_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_induction_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_induction_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_induction: not expect rule: " ^ (pr_rule r2))

(****************************************************)
(***********          hypothesis          ***********)

let compare_hypothesis_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_hypothesis pstate goal r2 r1)

let compare_hypothesis_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_hypothesis pstate goal r2 r1)

let compare_hypothesis_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_hypothesis pstate goal r2 r1)

let compare_hypothesis_vs_induction pstate goal r1 r2 : priority =
  neg_prio (compare_induction_vs_hypothesis pstate goal r2 r1)

let compare_hypothesis_vs_hypothesis pstate goal r1 r2 : priority =
  try
    let prio = compare_hypothesis r1.rhp_hp r2.rhp_hp in
    if (prio != PrioEqual) then raise_prio prio;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_hypothesis_vs_theorem pstate goal r1 r2 : priority =
  try
    if r2.rth_th.th_origin = LorgSynth then raise_prio PrioLow;
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_hypothesis_vs_excl_mid pstate goal r1 r2 : priority =
  try
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_hypothesis_vs_gen_left pstate goal r1 r2 : priority =
  try
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_hypothesis_vs_weaken_left pstate goal r1 r2 : priority =
  try
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_hypothesis_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_hypothesis_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_hypothesis_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_hypothesis_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_hypothesis_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_hypothesis_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_hypothesis_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_hypothesis_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_hypothesis_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_hypothesis_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_hypothesis: not expect rule: " ^ (pr_rule r2))


(******************************************************)
(***********            theorem             ***********)

let compare_theorem_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_theorem pstate goal r2 r1)

let compare_theorem_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_theorem pstate goal r2 r1)

let compare_theorem_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_theorem pstate goal r2 r1)

let compare_theorem_vs_induction pstate goal r1 r2 : priority =
  neg_prio (compare_induction_vs_theorem pstate goal r2 r1)

let compare_theorem_vs_hypothesis pstate goal r1 r2 : priority =
  neg_prio (compare_hypothesis_vs_theorem pstate goal r2 r1)

let compare_theorem_vs_theorem pstate goal r1 r2 : priority =
  try
    let vdefns = pstate.prs_prog.prog_views in
    if r1.rth_left = r2.rth_left then (
      if r1.rth_unf_ssts_len > r2.rth_unf_ssts_len then
        raise_prio PrioHigh;
      if r1.rth_unf_ssts_len < r2.rth_unf_ssts_len then
        raise_prio PrioLow);
    let th1, th2 = r1.rth_th, r2.rth_th in
    if (eq_s th1.th_name th2.th_name) &&
       (th1.th_lstats.fst_num_datas < th1.th_rstats.fst_num_datas) then (
      if r1.rth_left && not r2.rth_left then raise_prio PrioLow;
      if not r1.rth_left && r2.rth_left then raise_prio PrioHigh;
    );
    let lst1, lst2 = th1.th_lstats, th2.th_lstats in
    let rst1, rst2 = th1.th_rstats, th2.th_rstats in
    let added_size1 =
      if r1.rth_left then rst1.fst_num_hatoms - lst1.fst_num_hatoms
      else lst1.fst_num_hatoms - rst1.fst_num_hatoms in
    let added_size2 =
      if r2.rth_left then rst2.fst_num_hatoms - lst2.fst_num_hatoms
      else lst2.fst_num_hatoms - rst2.fst_num_hatoms in
    if (added_size1 < added_size2) then raise_prio PrioHigh;
    if (added_size1 > added_size2) then raise_prio PrioLow;
    let nvfs1 = match r1.rth_left with
      | true -> (collect_view_form r1.rth_th.th_rhs) @
                (collect_view_form_hf r1.rth_unf_residue) @
                (collect_view_form goal.gl_rhs)
      | false -> (collect_view_form r1.rth_th.th_lhs) @
                 (collect_view_form_hf r1.rth_unf_residue) @
                 (collect_view_form goal.gl_lhs) in
    let nvfs2 = match r2.rth_left with
      | true -> (collect_view_form r2.rth_th.th_rhs) @
                (collect_view_form_hf r2.rth_unf_residue) @
                (collect_view_form goal.gl_rhs)
      | false -> (collect_view_form r2.rth_th.th_lhs) @
                 (collect_view_form_hf r2.rth_unf_residue) @
                 (collect_view_form goal.gl_lhs) in
    let nvnames1 = nvfs1 |> List.map (fun vf -> vf.viewf_name) |>
                   dedup_ss |> List.length in
    let nvnames2 = nvfs2 |> List.map (fun vf -> vf.viewf_name) |>
                   dedup_ss |> List.length in
    let nrecurd_head1 = nvfs1 |> List.map (get_view_recur_direction vdefns) |>
                        List.filter (fun rc -> rc = VrdHead) |> List.length in
    let nrecurd_head2 = nvfs2 |> List.map (get_view_recur_direction vdefns) |>
                        List.filter (fun rc -> rc = VrdHead) |> List.length in

    if lst1.fst_num_hatoms = 1 && rst1.fst_num_hatoms = 1 &&
       lst1.fst_num_hatoms = 1 && rst1.fst_num_hatoms = 1 then (
      if List.length lst1.fst_fvs > List.length rst1.fst_fvs && r1.rth_left then
        raise_prio PrioHigh;
      if List.length lst2.fst_fvs > List.length rst2.fst_fvs && r2.rth_left then
        raise_prio PrioLow;
      if nvnames1 < nvnames2 then raise_prio PrioHigh;
      if nvnames1 > nvnames2 then raise_prio PrioLow;
      if nrecurd_head1 < nrecurd_head2 then raise_prio PrioLow;
      if nrecurd_head1 > nrecurd_head2 then raise_prio PrioHigh;
      if r1.rth_left && not r2.rth_left then raise_prio PrioHigh;
      if r2.rth_left && not r1.rth_left then raise_prio PrioLow;);
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_theorem_vs_excl_mid pstate goal r1 r2 : priority =
  try
    if (is_recent_rule_induction_without_hypothesis goal) &&
       (is_excl_mid_seed_rule_hypo r2) then
      raise_prio PrioLow;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_theorem_vs_gen_left pstate goal r1 r2 : priority =
  try
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_theorem_vs_weaken_left pstate goal r1 r2 : priority =
  try
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_theorem_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_theorem_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_theorem_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_theorem_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_theorem_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_theorem_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_theorem_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_theorem_vs_excl_mid  pstate goal r1 r2
  | RlGenLeft r2 -> compare_theorem_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_theorem_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_theorem: not expect rule: " ^ (pr_rule r2))

(****************************************************)
(***********          excl_mid          ***********)

let compare_excl_mid_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_induction pstate goal r1 r2 : priority =
  neg_prio (compare_induction_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_hypothesis pstate goal r1 r2 : priority =
  neg_prio (compare_hypothesis_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_theorem pstate goal r1 r2 : priority =
  neg_prio (compare_theorem_vs_excl_mid pstate goal r2 r1)

let compare_excl_mid_vs_excl_mid pstate goal r1 r2 : priority =
  try
    let nr1, nr2 = r1.rem_seed_rule, r2.rem_seed_rule in
    let prio = match nr1.ems_hypothesis, nr2.ems_hypothesis with
      | rhp1::_, rhp2::_ ->
        compare_hypothesis rhp1.rhp_hp rhp2.rhp_hp
      | rhp1::_, _ -> raise_prio PrioHigh;
      | _, rhp2::_ -> raise_prio PrioLow;
      | _ -> PrioEqual in
    if (prio != PrioEqual) then raise_prio prio;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_excl_mid_vs_gen_left pstate goal r1 r2 : priority =
  try
    if r2.rgl_base_hypo_unf != None then raise_prio PrioHigh;
    (* default *)
    PrioHigh;
  with EPrio (res, msg)-> res

let compare_excl_mid_vs_weaken_left pstate goal r1 r2 : priority =
  try
    if r2.rwl_base_hypo_unf != None then raise_prio PrioHigh;
    (* default *)
    PrioLow;
  with EPrio (res, msg)-> res

let compare_excl_mid_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_excl_mid_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_excl_mid_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_excl_mid_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_excl_mid_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_excl_mid_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_excl_mid_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_excl_mid_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_excl_mid_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_excl_mid_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_excl_mid: not expect rule: " ^ (pr_rule r2))

(****************************************************)
(***********           gen_left           ***********)

let compare_gen_left_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_induction pstate goal r1 r2 : priority =
  neg_prio (compare_induction_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_hypothesis pstate goal r1 r2 : priority =
  neg_prio (compare_hypothesis_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_theorem pstate goal r1 r2 : priority =
  neg_prio (compare_theorem_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_excl_mid pstate goal r1 r2 : priority =
  neg_prio (compare_excl_mid_vs_gen_left pstate goal r2 r1)

let compare_gen_left_vs_gen_left pstate goal r1 r2 : priority =
  try
    let _ = match r1.rgl_base_hypo_unf, r2.rgl_base_hypo_unf with
      | None, None -> ()
      | None, Some _ -> raise_prio PrioLow
      | Some _, None -> raise_prio PrioHigh
      | Some (hp1, unf1), Some (hp2, unf2) ->
        if (hp1.hp_ent_id > hp2.hp_ent_id) then raise_prio PrioHigh
        else if (hp1.hp_ent_id < hp2.hp_ent_id) then raise_prio PrioLow
        else () in
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_gen_left_vs_weaken_left pstate goal r1 r2 : priority =
  try
    (* default *)
    let _ = match r1.rgl_base_hypo_unf, r2.rwl_base_hypo_unf with
      | None, None -> ()
      | None, Some _ -> raise_prio PrioLow
      | Some _, None -> raise_prio PrioHigh
      | Some (hp1, unf1), Some (hp2, unf2) ->
        if (hp1.hp_ent_id > hp2.hp_ent_id) then raise_prio PrioHigh
        else if (hp1.hp_ent_id < hp2.hp_ent_id) then raise_prio PrioLow
        else () in
    PrioLow;
  with EPrio (res, msg)-> res

let compare_gen_left_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_gen_left_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_gen_left_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_gen_left_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_gen_left_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_gen_left_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_gen_left_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_gen_left_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_gen_left_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_gen_left_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_gen_left: not expect rule: " ^ (pr_rule r2))

(****************************************************)
(***********           weaken_left           ***********)

let compare_weaken_left_vs_star_data pstate goal r1 r2 : priority =
  neg_prio (compare_star_data_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_star_view pstate goal r1 r2 : priority =
  neg_prio (compare_star_view_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_view_right pstate goal r1 r2 : priority =
  neg_prio (compare_view_right_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_induction pstate goal r1 r2 : priority =
  neg_prio (compare_induction_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_hypothesis pstate goal r1 r2 : priority =
  neg_prio (compare_hypothesis_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_theorem pstate goal r1 r2 : priority =
  neg_prio (compare_theorem_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_excl_mid pstate goal r1 r2 : priority =
  neg_prio (compare_excl_mid_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_gen_left pstate goal r1 r2 : priority =
  neg_prio (compare_gen_left_vs_weaken_left pstate goal r2 r1)

let compare_weaken_left_vs_weaken_left pstate goal r1 r2 : priority =
  try
    let _ = match r1.rwl_base_hypo_unf, r2.rwl_base_hypo_unf with
      | None, None -> ()
      | None, Some _ -> raise_prio PrioLow
      | Some _, None -> raise_prio PrioHigh
      | Some (hp1, unf1), Some (hp2, unf2) ->
        if (hp1.hp_ent_id > hp2.hp_ent_id) then raise_prio PrioHigh
        else if (hp1.hp_ent_id < hp2.hp_ent_id) then raise_prio PrioLow
        else () in
    let lhs1_size = r1.rwl_new_lg |> collect_hatom |> List.length in
    let lhs2_size = r2.rwl_new_lg |> collect_hatom |> List.length in
    if lhs1_size > lhs2_size then raise_prio PrioLow;
    if lhs1_size < lhs2_size then raise_prio PrioHigh;
    (* default *)
    PrioEqual;
  with EPrio (res, msg)-> res

let compare_weaken_left_vs_other_rule pstate goal r1 r2 : priority =
  match r2 with
  | RlStarData r2 -> compare_weaken_left_vs_star_data pstate goal r1 r2
  | RlStarView r2 -> compare_weaken_left_vs_star_view pstate goal r1 r2
  | RlViewRight r2 -> compare_weaken_left_vs_view_right pstate goal r1 r2
  | RlInduction r2 -> compare_weaken_left_vs_induction pstate goal r1 r2
  | RlHypothesis r2 -> compare_weaken_left_vs_hypothesis pstate goal r1 r2
  | RlTheorem r2 -> compare_weaken_left_vs_theorem pstate goal r1 r2
  | RlExclMid r2 -> compare_weaken_left_vs_excl_mid pstate goal r1 r2
  | RlGenLeft r2 -> compare_weaken_left_vs_gen_left pstate goal r1 r2
  | RlWeakenLeft r2 -> compare_weaken_left_vs_weaken_left pstate goal r1 r2
  | _ -> error ("compare_weaken_left: not expect rule: " ^ (pr_rule r2))

(**************************************************)
(***********     compare all rules      ***********)

let rec compare_rule pstate goal (r1: rule) (r2: rule) : priority =
  SBDebug.trace_2 "compare_rule" (pr_rule, pr_rule, pr_prio) r1 r2
    (fun () -> compare_rule_x pstate goal r1 r2)

and compare_rule_x pstate goal (r1: rule) (r2: rule) : priority =
  match r1 with
  | RlStarData r1 -> compare_star_data_vs_other_rule pstate goal r1 r2
  | RlStarView r1 -> compare_star_view_vs_other_rule pstate goal r1 r2
  | RlViewLeft r1 -> compare_view_left_vs_other_rule pstate goal r1 r2
  | RlViewRight r1 -> compare_view_right_vs_other_rule pstate goal r1 r2
  | RlInduction r1 -> compare_induction_vs_other_rule pstate goal r1 r2
  | RlHypothesis r1 -> compare_hypothesis_vs_other_rule pstate goal r1 r2
  | RlTheorem r1 -> compare_theorem_vs_other_rule pstate goal r1 r2
  | RlExclMid r1 -> compare_excl_mid_vs_other_rule pstate goal r1 r2
  | RlGenLeft r1 -> compare_gen_left_vs_other_rule pstate goal r1 r2
  | RlWeakenLeft r1 -> compare_weaken_left_vs_other_rule pstate goal r1 r2
  | _ -> error ("compare_rule: not expect rule: " ^ (pr_rule r1))


(*************************************************************************)
(******************        CHECK USELESS RULES        ********************)

let is_rule_star_data_useless pstate goal rules rsd =
  try
    (* datas of different type *)
    let ldata, rdata = rsd.rsd_lg_data, rsd.rsd_rg_data in
    if not (eq_s ldata.dataf_name rdata.dataf_name) then
      raise_bool true;
    (* hatoms in the rest of lhs, rhs *)
    let lhf, rhf = fst rsd.rsd_lg_rest, fst rsd.rsd_rg_rest in
    let lhatoms, rhatoms = Pair.fold collect_hatom_hf lhf rhf in
    let ldatas, rdatas = Pair.fold collect_data_form_hf lhf rhf in
    (* inference mode *)
    let tsts = goal.gl_tstats in
    let _ = match goal.gl_proof_mode with
      | PrfInferBasic  ->
        if tsts.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
        if rsd.rsd_rdata_has_fvars && (not rsd.rsd_has_common_arg) then
          raise_bool true;
      | PrfInferAll | PrfInferLhs | PrfInferRhs ->
        if tsts.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
      | _ ->
        (* check num of datas *)
        if lhatoms = [] && rdatas != [] then raise_bool true;
        if rhatoms = [] && ldatas != [] then raise_bool true;
        (* check common datas *)
        if not rsd.rsd_has_common_arg && not rsd.rsd_rdata_has_qvars then
          raise_bool true in
    (* default *)
    false
  with EBool res -> res

let is_rule_star_view_useless pstate goal rules rsv =
  try
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    (* views of difference predicates *)
    let lview, rview = rsv.rsv_lg_view, rsv.rsv_rg_view in
    if not (eq_s lview.viewf_name rview.viewf_name) then raise_bool true;
    (* hatoms in the rest of lhs, rhs *)
    let lhf, rhf = fst rsv.rsv_lg_rest, fst rsv.rsv_rg_rest in
    let lhatoms, rhatoms = Pair.fold collect_hatom_hf lhf rhf in
    (* inference mode *)
    let tsts = goal.gl_tstats in
    let _ = match goal.gl_proof_mode with
      | PrfInferBasic ->
        if tsts.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
        if rsv.rsv_rview_has_fvars && (not rsv.rsv_has_common_arg) then
          raise_bool true;
      | PrfInferLhs | PrfInferRhs ->
        if tsts.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
        if not rsv.rsv_has_common_arg then raise_bool true;
      | PrfVerifyIndtLemma ->
        if is_latest_spatial_rule_induction goal then
          raise_bool true;
      | _ ->
        (* check num of datas *)
        if (lhatoms = [] && rhatoms != []) then raise_bool true;
        if (rhatoms = [] && lhatoms != []) then raise_bool true;
        if rst.fst_num_views = 1 &&
           lst.fst_num_datas > rst.fst_num_datas then
          raise_bool true;
        if not rsv.rsv_has_common_arg && not rsv.rsv_rview_has_qvars then
          raise_bool true in
    (* default *)
    false
  with EBool res -> res

let is_rule_view_left_useless pstate goal rules rvl =
  try
    if goal.gl_tstats.tst_induction = 0 then raise_bool true;
    if List.exists is_rule_hypothesis rules then raise_bool true;
    (* default *)
    false
  with EBool res -> res

let is_rule_view_right_useless pstate goal rules rvr =
  try
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    let tst, pth = goal.gl_tstats, pstate.prs_threshold in
    let rview = rvr.rvr_rg_view in
    let ufc = rvr.rvr_unfold_case in
    (* check derived groups *)
    let lvnames_common_args =
      lst.fst_views |>
      List.filter (fun vf -> intersected_vs (fv_vf vf) (fv_vf rview)) |>
      List.map (fun vf -> vf.viewf_name) |> dedup_ss in
    let rhf, drgs = (HView rview), goal.gl_rhs_derived_groups in
    if (has_derived_group_contain_hatom pstate drgs rhf) then
      raise_bool true;
    if (tst.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan) then
      raise_bool true;
    (* check latest spatial rule is unplanned excluded middle *)
    let _ = match get_latest_spatial_rules goal 1 with
      | [RlExclMid rem] -> (match rem.rem_cases with
        | [emc] -> if emc.emc_type = EmctUnplanned then raise_bool true;
        | _ -> ())
      | [RlViewRight rvr] ->
        if (is_pmode_infer goal) &&
           (not rvr.rvr_unfold_case.vuc_base_case) then
          raise_bool true;
      | _ -> () in
    (* proof mode *)
    let _ = match goal.gl_proof_mode  with
      | PrfInferRhs | PrfInferLhs | PrfInferBasic | PrfInferAll ->
        if lst.fst_has_data && rst.fst_is_pure then raise_bool true;
        if tst.tst_size = 0 && lst.fst_num_hatoms < rst.fst_num_hatoms then
          raise_bool true;
      | _ ->
        (* check emp heap in lhs *)
        if lst.fst_hatoms = [] && rst.fst_datas != [] then raise_bool true;
        (* check inconsistency *)
        if tst.tst_size >= pth.pth_trace_min_length_inconsist then (
          let vcf = ufc.vuc_view_case_form in
          let pvcf = NO.encode_view_inv_f pstate.prs_prog.prog_views vcf in
          if (PT.check_imply goal.gl_lhs_encoded pvcf = MvlFalse) then
            raise_bool true;);
        (* view-right with no progress in the next step *)
        if (not rvr.rvr_has_data_same_root) &&
           (not rvr.rvr_has_data_same_args) &&
           (eq_ss lvnames_common_args [rview.viewf_name]) then
          raise_bool true;
        let srules = get_latest_spatial_rules goal 3 in
        if (List.length srules = 3) &&
           (List.for_all (is_rule_view_right_inductive_case) srules) then
          raise_bool true in
    (* default *)
    false
  with EBool res -> res

let is_rule_induction_useless pstate goal rules rid =
  try
    let prog, tst = pstate.prs_prog, goal.gl_tstats in
    let lview, lst, rst = rid.rid_lg_view, goal.gl_lstats, goal.gl_rstats in
    (* check derived groups *)
    let drgs = goal.gl_lhs_derived_groups in
    if (has_derived_group_contain_hatom pstate drgs (HView lview)) then
      raise_bool true;
    if List.exists (fun tri -> match tri.tri_rule with
      | RlViewLeft rvl -> lview.viewf_id = rvl.rvl_lg_view.viewf_id
      | _ -> false) goal.gl_trace then raise_bool true;
    (* proof mode *)
    let _ = match goal.gl_proof_mode with
      | PrfInferBasic | PrfInferLhs | PrfInferRhs | PrfInferAll ->
        if tst.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
        let srules = collect_used_spatial_rules goal in
        if (List.exists is_rule_induction srules) &&
           (List.exists is_rule_view_right srules) &&
           not (List.exists is_rule_star_data srules) then
          raise_bool true;
        if (is_recent_rule_induction_without_hypothesis goal) then
          raise_bool true;
      | PrfVerifyLemma | PrfVerifyIndtLemma ->
        if is_latest_spatial_rule_induction goal then
          raise_bool true;
      | PrfUnsat ->
        let ancestor_ids = lview.viewf_ancestor_ids in
        if is_recur_self_vf prog.prog_views lview &&
           List.length ancestor_ids > 2 then raise_bool true;
        let unrelated_hatoms = lst.fst_hatoms |> List.exclude (fun ha ->
          intersected_ints (get_ancestor_ids ha) ancestor_ids) in
        let unrelated_vars = unrelated_hatoms |> fv_has in
        if intersected_vs (fv_vf lview) unrelated_vars then raise_bool false
        else raise_bool true;
      | _ ->
        (* check emp heap in rhs *)
        if lst.fst_datas != [] && rst.fst_hatoms = [] then
          raise_bool true;
        (* check latest spatial rules *)
        let srules = get_latest_spatial_rules goal 3 in
        if (List.length srules = 3) &&
           (List.for_all (fun r ->
              (is_rule_induction_inductive_case r) ||
              (is_rule_hypothesis r)) srules) then
          raise_bool true in
    false
  with EBool res -> res

let is_rule_hypothesis_useless pstate goal rules rhp =
  try
    let lst, rst, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    if rhp.rhp_unf_ssts = [] then raise_bool true;
    (* inference mode *)
    let _ = match is_pmode_infer goal with
      | true ->
        if tst.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan then
          raise_bool true;
        if is_latest_spatial_rule_hypothesis goal then
          raise_bool true;
      | false -> () in
    let _ = match is_pmode_verify goal with
      | true ->
        if is_latest_spatial_rule_hypothesis goal then
          raise_bool true;
      | false -> () in
    if (goal.gl_proof_mode = PrfInferLhs) &&
       not (is_emp_hf rhp.rhp_unf_residue) then
      raise_bool true;
    (* default *)
    false
  with EBool res -> res

let is_rule_theorem_useless pstate goal rules rth =
  try
    let lst, rst, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    let th = rth.rth_th in
    let thlst, thrst = th.th_lstats, th.th_rstats in
    let used_rths =
      goal |> collect_used_spatial_rules |> List.map (function
        | RlTheorem rth -> [rth]
        | _ -> []) |> List.concat in
    if rth.rth_left &&
       not (intersected_ss thrst.fst_view_names rst.fst_view_names) then
      raise_bool true;
    if not rth.rth_left &&
       not (intersected_ss thlst.fst_view_names lst.fst_view_names) then
      raise_bool true;
    let num_used_same_th =
      used_rths |>
      List.filter (fun rth -> eq_s rth.rth_th.th_name th.th_name) |>
      List.length in
    if List.exists (fun urth ->
      (rth.rth_left = urth.rth_left) &&
      is_reverse_theorem rth.rth_th urth.rth_th) used_rths then
      raise_bool true;
    if rth.rth_left && (num_used_same_th > 3) && th.th_origin = LorgMutual &&
       thlst.fst_num_hatoms < thrst.fst_num_hatoms then
      raise_bool true;
    if not rth.rth_left && (num_used_same_th > 3) && th.th_origin = LorgMutual &&
       thlst.fst_num_hatoms > thrst.fst_num_hatoms then
      raise_bool true;
    if rth.rth_left && (tst.tst_theorem > 2) &&
       (lst.fst_num_hatoms > rst.fst_num_hatoms) &&
       (thlst.fst_num_hatoms < thrst.fst_num_hatoms) then
      raise_bool true;
    if not rth.rth_left && (tst.tst_theorem > 2) &&
       (lst.fst_num_hatoms < rst.fst_num_hatoms) &&
       (thlst.fst_num_hatoms > thrst.fst_num_hatoms) then
      raise_bool true;
    if rth.rth_unf_ssts = [] then raise_bool true;
    (* default *)
    false
  with EBool res -> res

let is_rule_gen_left_useless pstate goal rules rgl =
  try
    let pth, tst = pstate.prs_threshold, goal.gl_tstats in
    if not !proof_use_rule_gen_left then raise_bool true;
    if goal.gl_need_infer_lemma then raise_bool true;
    if is_pmode_infer goal || is_pmode_verify goal then raise_bool true;
    if is_pmode_unsat goal && tst.tst_gen_left > 1 then raise_bool true;
    if goal.gl_tstats.tst_size > pth.pth_trace_max_length_uninst_var then
      raise_bool true;
    (* default *)
    false
  with EBool res -> res

let is_rule_weaken_left_useless pstate goal rules rwl =
  try
    let pth, tst = pstate.prs_threshold, goal.gl_tstats in
    if not !proof_use_rule_gen_left then raise_bool true;
    if goal.gl_need_infer_lemma then raise_bool true;
    if is_pmode_infer goal || is_pmode_verify goal then raise_bool true;
    if is_pmode_unsat goal && tst.tst_weaken_left > 1 then
      raise_bool true;
    (* default *)
    false
  with EBool res -> res

let is_rule_excl_mid_useless pstate goal rules rem =
  try
    let prog = pstate.prs_prog in
    let lst, rst, tst = goal.gl_lstats, goal.gl_rstats, goal.gl_tstats in
    let rvrs = rem.rem_seed_rule.ems_view_right in
    let rhps = rem.rem_seed_rule.ems_hypothesis in
    let srules = collect_used_spatial_rules goal in
    let has_indt_rule_indt_case = List.exists (function
      | RlInduction rid when rid.rid_unfold_cases != [] ->
        let ufcase = List.hd rid.rid_unfold_cases in
        not ufcase.vuc_base_case
      | _ -> false) srules in
    if not has_indt_rule_indt_case then raise_bool true;
    (* consider proof mode *)
    let _ = match is_pmode_infer goal with
      | true ->
        if lst.fst_is_pure || rst.fst_is_pure || rvrs != [] then
          raise_bool true;
        DB.nhprint "REM SEED COND: " pr_pf rem.rem_seed_cond;
        if (has_qvars_pf rem.rem_seed_cond) &&
           (List.exists is_ptr_typ (collect_typ_pf rem.rem_seed_cond)) then
          raise_bool true;
        let has_large_vf = List.exists (fun vf ->
          List.length vf.viewf_args >= 4) (lst.fst_views @ lst.fst_views) in
        let has_unconnected_ha =
          List.exists (fun ha ->
            not (intersected_vs (fv_ha ha) rst.fst_fvs)) lst.fst_hatoms ||
          List.exists (fun ha ->
            not (intersected_vs (fv_ha ha) lst.fst_fvs)) rst.fst_hatoms in
        if has_unconnected_ha && has_large_vf then
          raise_bool true;
        if goal.gl_depth_infer = 0 && has_large_vf then
          raise_bool true;
        let inferred_vs = goal |> collect_rform_goal |> fv_rfs in
        if (is_pmode_infer_lhs goal) &&
           not (intersected_vs inferred_vs (fv_pf rem.rem_seed_cond)) then
          raise_bool true;
        if (is_pmode_infer_lhs goal) &&
           not goal.gl_gstats.gst_has_common_hvars then
          raise_bool true;
      | false ->
        (* ignore if seed rule is HP and the last spatial rule isn't INDT *)
        if is_pmode_unsat goal && tst.tst_excmid_unkrel_plan > 1 then
          raise_bool true;
        if not (is_pmode_unsat goal) &&
           not (intersected_vs lst.fst_fvs rst.fst_fvs) then
          raise_bool true;
        if rhps != [] && not (is_latest_spatial_rule_induction goal) then
          raise_bool true;
        if is_latest_spatial_rule_gen_left goal then
          raise_bool true;
        let pfs = collect_pure_conjuncts_pf rem.rem_seed_cond in
        if (List.length pfs > 1) then raise_bool true;
    in
    let _ = match rvrs, rhps with
      | [], [] -> ()
      | rvr::_, [] ->
        if (tst.tst_excmid_view_right >= 1) then
          raise_bool true;
        let rvname = rvr.rvr_rg_view.viewf_name in
        let vdefn = find_view_defn prog.prog_views rvname in
        if not vdefn.view_empty_base_case then
          raise_bool true;
        let lvnames_common_args =
          lst.fst_views |> List.filter (fun vf ->
            intersected_vs (fv_vf vf) (fv_vf rvr.rvr_rg_view)) |>
          List.map (fun vf -> vf.viewf_name) |> dedup_ss in
        if (List.exists (fun rvr ->
          (eq_ss lvnames_common_args [rvname]) &&
          (not rvr.rvr_unfold_case.vuc_base_case) &&
          (not rvr.rvr_has_data_same_args) &&
          (not rvr.rvr_has_data_same_root)) rvrs) then
          raise_bool true
      | [], _ ->
        let rhp = List.hd rhps in
        if (mem_ints rhp.rhp_hp.hp_ent_id tst.tst_used_hypo_id_excmid) then
          raise_bool true;
        DB.nhprint "RHP.RHP_UNF_RESIDUE: " pr_hf rhp.rhp_unf_residue;
        if (is_pmode_infer_lhs goal) &&
           not (is_emp_hf rhp.rhp_unf_residue) then
          raise_bool true;
      | _, _ -> error "is_rule_emid_useless: expect 1 kind of seed rule" in
    (* default *)
    false
  with EBool res -> res

let rec is_rule_useless pstate goal rules rule =
  DB.trace_2 "is_rule_useless" (pr_g, pr_rule, pr_b) goal rule
    (fun () -> is_rule_useless_x pstate goal rules rule)

and is_rule_useless_x pstate goal rules rule = match rule with
  | RlStarData rsd -> is_rule_star_data_useless pstate goal rules rsd
  | RlStarView rsv -> is_rule_star_view_useless pstate goal rules rsv
  | RlViewLeft rvl -> is_rule_view_left_useless pstate goal rules rvl
  | RlViewRight rvr -> is_rule_view_right_useless pstate goal rules rvr
  | RlInduction rid -> is_rule_induction_useless pstate goal rules rid
  | RlHypothesis rhp -> is_rule_hypothesis_useless pstate goal rules rhp
  | RlTheorem rth -> is_rule_theorem_useless pstate goal rules rth
  | RlGenLeft rgl -> is_rule_gen_left_useless pstate goal rules rgl
  | RlExclMid rem -> is_rule_excl_mid_useless pstate goal rules rem
  | _ -> false

let has_rule_view_right_data_same_root pstate goal =
  let rules = choose_rule_view_right pstate goal in
  List.exists (function
    | RlViewRight rvr -> rvr.rvr_has_data_same_root
    | _ -> false) rules
