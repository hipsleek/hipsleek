open Printf
open SBGlobals
open SBLib
open SBLib.Basic
open SBCast
open SBProof
open SBRule

module EList = ExtList.List
module EString = ExtString.String
module NO = SBNormalize
module ID = SBInduction
module PL = SBPlanner
module PT = SBPuretp
module FK = SBFarkas
module FF = SBFarkasfix
module TL = SBTemplate
module LN = SBLearner
module IP = SBIprover
module DB = SBDebug

let get_max_var_index prog =
  let vs = av_prog prog in
  let index = ref 0 in
  let _ = vs |> List.iter (fun v ->
    let name = name_of_var v in
    let _, suffix = extract_var_name_prefix_suffix name in
    if suffix > !index then index := suffix) in
  !index

let reset_index_vars prog =
  index_var := get_max_var_index prog;
  index_var_infer := 0;
  index_farkas_var := 0

let save_index_vars () : int list =
  [!index_var; !index_var_infer; !index_farkas_var]

let save_and_reset_index_vars prog : int list =
  let indices = save_index_vars () in
  let _ = reset_index_vars prog in
  indices

let restore_index_vars vars =
  match vars with
  | [x; y; z] ->
    index_var := x;
    index_var_infer := y;
    index_farkas_var := z
  | _ -> error "incorrect index vars state"

(***************************************************************************)
(********************         process all rules         ********************)

let rec choose_axiom_rules pstate goal =
  DB.trace_1 "choose_axiom_rules" (pr_g, pr_opt pr_rule) goal
    (fun () -> choose_axiom_rules_x pstate goal)

and choose_axiom_rules_x pstate goal =
  try
    let _ = choose_rule_false_left pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_pure_entail pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_infer_relation pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    (* default result *)
    None
  with ERules rs -> Some (List.hd rs)

let rec choose_normalize_rules pstate goal : rule list =
  DB.trace_1 "choose_normalize_rules" (pr_g, pr_rules) goal
    (fun () -> choose_normalize_rules_x pstate goal)

and choose_normalize_rules_x pstate goal : rule list =
  try
    let _ = choose_rule_unfold_relation pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_emp_left pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_emp_right pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_exists_left pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_exists_right pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_equal_left pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_drop_left pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    let _ = choose_rule_drop_right pstate goal |>
            fun rs -> if rs != [] then raise (ERules rs) in
    (* default result *)
    []
  with ERules rs -> rs

let rec refine_spatial_rules goal rules =
  DB.trace_2 "refine_spatial_rules" (pr_g, pr_rules, pr_rules) goal rules
    (fun () -> refine_spatial_rules_x goal rules)

and refine_spatial_rules_x goal rules =
  try
    let _ = List.iter (fun r -> match r with
      | RlStarData rsd ->
        let ld, rd = rsd.rsd_lg_data, rsd.rsd_rg_data in
        if (eq_exp ld.dataf_root rd.dataf_root) then
          (* immediately select a star-data rule of same root data node *)
          raise (ERules [r])
      | _ -> ()) rules in
    (* default *)
    rules
  with ERules res -> res

let rec choose_spatial_rules pstate goal : rule list =
  DB.trace_1 "choose_spatial_rules" (pr_g, pr_rules) goal
    (fun () -> choose_spatial_rules_x pstate goal)

and choose_spatial_rules_x pstate goal : rule list =
  try
    let lst, rst, pth = goal.gl_lstats, goal.gl_rstats, pstate.prs_threshold in
    let used_srules = collect_used_spatial_rules goal in
    let rules = [] in
    let rules =
      let rs = choose_rule_star_data pstate goal in
      try raise_rules [List.find is_rule_trivial rs]
      with Not_found -> rules @ rs in
    let rules =
      let rs = choose_rule_star_view pstate goal in
      try raise_rules [List.find is_rule_trivial rs]
      with Not_found -> rules @ rs in
    let _ = if is_pmode_prove goal && goal.gl_matching_plans != []  then
      raise_rules rules in
    let rules =
      let rs = choose_rule_from_theorem pstate goal in
      if (rs != []) &&
         (lst.fst_num_hatoms >= !thd_min_size_choose_only_theorem) &&
         (rst.fst_num_hatoms >= !thd_min_size_choose_only_theorem) then
        raise_rules rs
      else rules @ rs  in
    let rules =
      let rs = choose_rule_view_right pstate goal in
      let srs = match pth.pth_goal_unfold_right_intensive with
        | true -> List.filter (fun r -> match r with
          | RlViewRight rvr -> rvr.rvr_has_data_same_root
          | _ -> false) rs
        | false -> [] in
      if srs != [] then raise (ERules srs)
      else rules @ rs in
    let rules =
      let rs = choose_rule_induction pstate goal in
      if rs != [] && (goal.gl_proof_mode = PrfVerifyIndtLemma) &&
         not (List.exists is_rule_induction used_srules) then
        raise (ERules rs)
      else rules @ rs in
    let rules =
      let rs = choose_rule_from_hypothesis pstate goal in
      if List.length rs = 1 && (goal.gl_proof_mode = PrfVerifyIndtLemma) &&
         not (List.exists is_rule_hypothesis used_srules) then
        raise (ERules rs)
      else rules @ rs in
    (* let rules = rules @ (choose_rule_gen_left pstate goal) in *)
    let rules = rules @ (choose_rule_view_left pstate goal) in
    refine_spatial_rules goal rules
  with ERules rs -> rs

and choose_rule_important pstate goal rules : rule list =
  DB.trace_2 "choose_rule_important"
    (pr_g, pr_rules, pr_rules) goal rules
    (fun () -> choose_rule_important_x pstate goal rules)

and choose_rule_important_x pstate goal rules : rule list =
  try
    (* try other heuristics *)
    if List.exists (function
      | RlStarData rsd -> rsd.rsd_same_data_name && rsd.rsd_has_common_arg
      | RlStarView rsv -> rsv.rsv_same_view_name && rsv.rsv_has_common_arg
      | _ -> false ) rules then
      raise_rules rules;
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    let rths = List.filter (function
      | RlTheorem rth ->
        let thlst, thrst = rth.rth_th.th_lstats, rth.rth_th.th_rstats in
        if rth.rth_th.th_origin != LorgSynth then false
        else if rth.rth_left &&
                (lst.fst_num_hatoms >= rst.fst_num_hatoms) &&
                (thlst.fst_num_hatoms < thrst.fst_num_hatoms) then
          false
        else if not rth.rth_left &&
                (lst.fst_num_hatoms <= rst.fst_num_hatoms) &&
                (thlst.fst_num_hatoms > thrst.fst_num_hatoms) then
          false
        else if rth.rth_left &&
                not (intersected_ss thrst.fst_view_names rst.fst_view_names) then
          false
        else if not rth.rth_left &&
                not (intersected_ss thlst.fst_view_names lst.fst_view_names) then
          false
        else true
      | _ -> false) rules in
    if rths != [] then rths
    else rules
  with ERules res -> res

and remove_useless_rules pstate goal rules : rule list =
  DB.trace_2 "remove_useless_rules"
    (pr_g, pr_rules, pr_rules) goal rules
    (fun () -> remove_useless_rules_x pstate goal rules)

and remove_useless_rules_x pstate goal rules : rule list =
  let rules = rules |> List.exclude (is_rule_useless pstate goal rules) in
  let rs_hpths = List.filter (fun r ->
    (is_rule_theorem r) || (is_rule_hypothesis r)) rules in
  if List.length rs_hpths > 3 then rs_hpths
  else rules

and remove_redundant_rules pstate goal rules : rule list =
  DB.trace_2 "remove_redundant_rules"
    (pr_g, pr_rules, pr_rules) goal rules
    (fun () -> remove_redundant_rules_x pstate goal rules)

and remove_redundant_rules_x pstate goal rules : rule list =
  List.fold_left (fun acc r1 ->
    match r1 with
    | RlWeakenLeft rwl1 ->
      let has_duplicate_rwl = acc |> List.exists (fun r2 -> match r2 with
        | RlWeakenLeft rwl2 ->
          let same_hypo =
            match rwl1.rwl_base_hypo_unf, rwl2.rwl_base_hypo_unf with
            | Some (hp1, unf1), Some (hp2, unf2) ->
              hp1.hp_ent_id = hp2.hp_ent_id
            | _ -> false in
          same_hypo &&
          (check_syntax_equiv_pf rwl1.rwl_dropped_pf rwl2.rwl_dropped_pf)
        | _ -> false) in
      if has_duplicate_rwl then acc else acc @ [r1]

    | _ -> acc @ [r1]) [] rules

and reorder_cluster_rules pstate goal rules : rule list list =
  DB.trace_2 "reorder_cluster_rules"
    (pr_g, pr_rules, pr_items pr_rules) goal rules
    (fun () -> reorder_cluster_rules_x pstate goal rules)

and reorder_cluster_rules_x pstate goal rules : rule list list =
  let rec insert r rss = match rss with
    | [] -> [[r]]
    | xs::xss -> match xs with
      | [] -> error "reorder_cluster_rules: not expect empty cluster"
      | x::_ ->
        let prio = compare_rule pstate goal r x in
        if (prio = PrioEqual) then (r::xs)::xss
        else if (prio = PrioHigh) then [r]::rss
        else xs::(insert r xss) in
  let rec reorder rs acc = match rs with
    | [] -> acc
    | r::rs -> reorder rs (insert r acc) in
  reorder rules []

and is_goal_useless pstate goal : bool =
  DB.trace_1 "is_goal_useless" (pr_g, pr_b) goal
    (fun () -> is_goal_useless_x pstate goal)

(* TRUNG TODO: need better improvement of this checking useless *)
and is_goal_useless_x pstate goal =
  try
    let _ = match goal.gl_lhs with
      | FForall _ -> raise_bool true
      | _ -> () in
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    let lhsp, rhsp = goal.gl_lhs_encoded, (extract_pf goal.gl_rhs) in
    let _ = match is_pmode_infer goal with
      | true ->
        if lst.fst_has_data && rst.fst_is_pure then raise_bool true;
        if (is_latest_spatial_rule_view_right goal) &&
           (PT.check_sat (mk_pconj [lhsp; rhsp]) = MvlFalse) then
          raise_bool true;
      | false ->
        (* check heap vars *)
        if rst.fst_fhvs != [] && rst.fst_qhvs = [] && lst.fst_fhvs != []
           && (is_latest_spatial_rule_star_data goal
               || is_latest_spatial_rule_star_view goal)
           && not (intersected_vs lst.fst_fhvs rst.fst_fhvs) then
          raise_bool true;
        (* check goal repetition *)
        if List.exists (fun tri ->
          (check_syntax_equiv goal.gl_lhs tri.tri_lhs) &&
          (check_syntax_equiv goal.gl_rhs tri.tri_rhs)) goal.gl_trace then
          raise_bool true;
        (* check latest rule *)
        if (is_latest_spatial_rule_view_right goal) &&
           not (is_latest_spatial_rule_trivial goal) &&
           not rst.fst_has_view &&
           (lst.fst_num_hatoms > rst.fst_num_hatoms) then
          raise_bool true in
    (* default *)
    false
  with EBool res -> res


and is_unproductive_goal pstate goal : bool =
  DB.trace_1 "is_unproductive_goal" (pr_g, pr_b) goal
    (fun () -> is_unproductive_goal_x pstate goal)

and is_unproductive_goal_x pstate goal : bool =
  let decide msg =
    if (pstate.prs_interact) then (
      let _ = DB.pprint ("Unproductive goal detected: " ^ (pr_g goal)) in
      let _ = DB.pprint ("Unproductive reason: " ^ msg) in
      let answer = DB.ask_decision "Do you want to continue processing \
                                    this goal?" ["y"; "n"] in
      let answer = String.uppercase_ascii answer in
      if (String.equal answer "N") then raise_bool true)
    else raise_bool true in
  try
    let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
    let tst, pth = goal.gl_tstats, pstate.prs_threshold in
    let _ = match lhs with
      | FExists _ | FForall _ -> raise_bool false
      | _ -> () in
    let _ = if (has_unk_rform pstate.prs_prog.prog_rels lhs) then (
      if (is_pmode_infer goal) &&
         (tst.tst_excmid_unkrel_unplan > !thd_max_excmid_unkrel_unplan) then
        decide "detect unproductive goal by unplanned unknown excl-mid") in
    let plhs = goal.gl_lhs_encoded in
    let prhs = NO.encode_formula pstate.prs_prog goal.gl_rhs in
    (* check for number of rules used *)
    if (tst.tst_size > pth.pth_trace_max_length) then
      decide "detect unproductive goal by max-trace-length";
    if (tst.tst_induction > pth.pth_trace_max_induction) then
      decide "detect unproductive goal by max-num-induction";
    if (tst.tst_view_right > pth.pth_trace_max_view_right) then
      decide "detect unproductive goal by max-num-view-right";
    if (tst.tst_hypothesis > pth.pth_trace_max_hypothesis) then
      decide "detect unproductive goal by max-num-hypothesis";
    (* (\* using counter-theorems *\) *)
    (* if !proof_use_counter_theorem then ( *)
    (*   List.iter (fun cth -> *)
    (*     let unfs = ID.unify_heap cth.cth_lhs lhs in *)
    (*     List.iter (fun unf -> *)
    (*       if (ID.unify_pure cth.cth_lhs lhs unf) then *)
    (*         let cth_rhs = subst unf.unfs_ssts cth.cth_rhs in *)
    (*         let cth_rhs = mk_hstar_f_hf cth_rhs unf.unfs_residue in *)
    (*         let tmp_gl = mk_goal pstate.prs_prog rhs cth_rhs in *)
    (*         let ptree = prove_using_direct_matching pstate tmp_gl in *)
    (*         let ptstatus = get_ptree_status ptree in *)
    (*         match ptstatus with *)
    (*         | PtValid _ -> *)
    (*           decide "detect unproductive goal by cth" *)
    (*         | _ -> () *)
    (*     ) unfs) pstate.prs_counter_theorems); *)
    (* check if pure LHS is inconsistent with pure RHS *)
    if not (is_pmode_infer goal) &&
       goal.gl_tstats.tst_size >= pth.pth_trace_min_length_inconsist &&
       Puretp.check_consistency plhs prhs = MvlFalse then
      decide "detect unproductive goal by inconsitent LHS, RHS";
    (* check size *)
    let trace = List.filter (fun x ->
      is_rule_handle_heap_atom x.tri_rule) goal.gl_trace in
    let sizes = List.map (fun x -> x.tri_ent_size) trace in
    let _ = match sizes with
      | s1::s2::s3::s4::s5::s6::s7::s8::_ ->
        if (s1 >= s2) && (s2 >= s3) && (s3 >= s4) && (s4 >= s5)
           && (s5 >= s6) && (s6 >= s7) && (s7 >= s8) then
          decide "detect unproductive goal by size increase consecutively";
      | _ -> () in
    (* default *)
    false
  with EBool res -> res

and detect_unproductive_goal_early pstate goal : proof_tree option =
  DB.trace_1 "detect_unproductive_goal_early" (pr_g, pr_opt pr_ptree) goal
    (fun () -> detect_unproductive_goal_early_x pstate goal)

and detect_unproductive_goal_early_x pstate goal : proof_tree option =
  try (
    if (is_pmode_infer goal) &&
       (List.length pstate.prs_assums > !thd_max_infer_assumpts) then
      raise_ptree (mk_ptree_search_unkn goal [] "Unproductive-Goal");
    match (is_unproductive_goal pstate goal) with
    | false -> None
    | true -> Some (mk_ptree_search_unkn goal [] "Unproductive-Goal")
  )
  with EPtree res -> Some res


and check_unsat_lhs ?(interact=false) prog goal : proof_tree option =
  DB.trace_1 "check_unsat_lhs" (pr_g, pr_opt pr_ptree) goal
    (fun () -> check_unsat_lhs_x ~interact:interact prog goal)

and check_unsat_lhs_x ?(interact=false) prog goal : proof_tree option =
  DB.nhprint "CHECK UNSAT LHS: " pr_g goal;
  let pstate = mk_prover_state ~interact:interact prog goal in
  let lst, tst, pth = goal.gl_lstats, goal.gl_tstats, pstate.prs_threshold in
  let lhs, interact = goal.gl_lhs, pstate.prs_interact in
  let has_const_hargs () =
    (List.exists has_const_arg_vf lst.fst_views) ||
    (List.exists has_const_arg_df lst.fst_datas) in
  if !proof_check_lhs_unsat && (not goal.gl_need_infer_lemma) &&
     (goal.gl_proof_mode = PrfEntail) &&
     (lst.fst_num_views <= 1) &&
     (has_const_hargs ()) &&
     not (List.exists has_int_const_arg_vf lst.fst_views) &&
     (lst.fst_num_hatoms <= 5) &&
     (tst.tst_size <= pth.pth_trace_max_length_check_unsat) &&
     (check_unsat_indt ~interact:interact prog lhs = MvlFalse) then
    let rfl = mk_rule_false_left goal.gl_lhs in
    let ptc = mk_proof_tree_core goal rfl [] in
    Some (mk_proof_tree_derive goal rfl [] (PtValid ptc))
  else None

and detect_trivial_rules pstate goal rules : rule option =
  DB.trace_1 "detect_trivial_rules" (pr_rules, pr_opt pr_rule) rules
    (fun () -> detect_trivial_rules_x pstate goal rules)

and detect_trivial_rules_x pstate goal rules : rule option =
  let trirules = List.filter is_rule_trivial rules in
  if (trirules = []) then None
  else Some (List.hd trirules)

and remove_useless_derivations pstate goal derivations : derivation list =
  DB.trace_2 "remove_useless_derivations"
    (pr_g, pr_drvs, pr_drvs) goal derivations
    (fun () -> remove_useless_derivations_x pstate goal derivations)

and remove_useless_derivations_x pstate goal derivations : derivation list =
  (* filter by early proving pure *)
  List.filter (fun x -> match x.drv_kind with
    | DrvStatus MvlTrue -> true
    | DrvStatus MvlInfer -> true
    | DrvStatus MvlUnkn -> false
    | DrvStatus MvlFalse -> false
    | DrvBackjump _ -> true
    | DrvSubgoals gs -> not (List.exists (is_goal_useless pstate) gs)
  ) derivations

and compare_conjunctive_goals pstate goals1 goals2 : priority =
  let rec compare gs1 gs2 = match gs1, gs2 with
    | [], [] -> PrioEqual
    | [], _ -> PrioHigh
    | _, [] -> PrioLow
    | g1::gs1, g2::gs2 ->
      let prio = compare_goal pstate g1 g2 in
      if (prio != PrioEqual) then prio
      else compare gs1 gs2 in
  compare goals1 goals2

and compare_goal pstate g1 g2 : priority =
  DB.trace_2 "compare_goal" (pr_g, pr_g, pr_prio) g1 g2
    (fun () -> compare_goal_x pstate g1 g2)

and compare_goal_x pstate g1 g2 : priority =
  try
    let gst1, gst2 = g1.gl_gstats, g2.gl_gstats in
    let prog = pstate.prs_prog in
    (* number of data in lhs and rhs *)
    let ldatas1, rdatas1 = g1.gl_lstats.fst_datas, g1.gl_rstats.fst_datas in
    let ldatas2, rdatas2 = g2.gl_lstats.fst_datas, g2.gl_rstats.fst_datas in
    let n1 = (List.length ldatas1) - (List.length rdatas1) in
    let n2 = (List.length ldatas2) - (List.length rdatas2) in
    if n1 >= 0 && n2 < 0 then raise_prio_high "compare #datas in lhs, rhs";
    if n1 < 0 && n2 >= 0 then raise_prio_low "compare #datas in lhs, rhs";
    (* find all view-right rules *)
    let rsvs1 = g1 |> choose_all_rule_star_view pstate in
    let rsvs2 = g2 |> choose_all_rule_star_view pstate in
    (* rule StarView trivial *)
    let n1 = rsvs1 |> List.filter (fun r -> r.rsv_trivial) |> List.length in
    let n2 = rsvs2 |> List.filter (fun r -> r.rsv_trivial) |> List.length in
    if n1 > n2 then raise_prio_high "compare #rule-star-view trivial";
    if n1 < n2 then raise_prio_low "compare #rule-star-view trivial";
    (* number of view defn *)
    let n1, n2 = gst1.gst_num_view_names, gst2.gst_num_view_names in
    if n1 > n2 then raise_prio_low "compare #view names";
    if n1 < n2 then raise_prio_high "compare #view names";
    (* unproved pure conjunct in lhs and rhs *)
    let n1 = List.length g1.gl_rhs_unproved_patoms in
    let n2 = List.length g2.gl_rhs_unproved_patoms in
    if n1 > n2 then raise_prio_low "compare #conjuncts unproved";
    if n1 < n2 then raise_prio_high "compare #conjuncts unproved";
    (* rule StarData trivial *)
    let rsds1 = g1 |> choose_all_rule_star_data pstate in
    let rsds2 = g2 |> choose_all_rule_star_data pstate in
    let n1 = rsds1 |> List.filter (fun r -> r.rsd_trivial) |> List.length in
    let n2 = rsds2 |> List.filter (fun r -> r.rsd_trivial) |> List.length in
    if n1 > n2 then raise_prio_high "compare #rule-star-data trivial";
    if n1 < n2 then raise_prio_low "compare #rule-star-data trivial";
    (* rule StarView of matching all args *)
    let n1 = rsvs1 |> List.filter (fun r ->
      r.rsv_can_match_all_args && r.rsv_rview_has_fvars) |> List.length in
    let n2 = rsvs2 |> List.filter (fun r ->
      r.rsv_can_match_all_args && r.rsv_rview_has_fvars) |> List.length in
    if n1 > n2 then raise_prio_high "compare #rule-star-view match args";
    if n1 < n2 then raise_prio_low "compare #rule-star-view match args";
    (* consider possibilities in applying hypothesis and theorems *)
    let rhts1 = (choose_rule_from_hypothesis pstate g1) @
                (choose_rule_from_theorem pstate g1) in
    let rhts2 = (choose_rule_from_hypothesis pstate g2) @
                (choose_rule_from_theorem pstate g2) in
    let rhps1, rhps2 = Pair.fold (List.filter is_rule_hypothesis) rhts1 rhts2 in
    let rths1, rths2 = Pair.fold (List.filter is_rule_theorem) rhts1 rhts2 in
    let n1 = (List.length rhps1) + (List.length rths1) in
    let n2 = (List.length rhps2) + (List.length rths2) in
    if n1 > n2 then raise_prio_high "compare #rules hypos & theorems";
    if n1 < n2 then raise_prio_low "compare #rules hypos & theorems";
    let rwls1, rwls2 = Pair.fold (List.filter is_rule_weaken_left) rhts1 rhts2 in
    let rgls1, rgls2 = Pair.fold (List.filter is_rule_gen_left) rhts1 rhts2 in
    let rems1, rems2 = Pair.fold (List.filter is_rule_excl_mid) rhts1 rhts2 in
    let n1 = (List.length rwls1) + (List.length rgls1) + (List.length rems1) in
    let n2 = (List.length rwls2) + (List.length rgls2) + (List.length rems2) in
    if n1 > n2 then raise_prio_high "compare #rules weaken, gen-left & emid";
    if n1 < n2 then raise_prio_low "compare #rules weaken, gen-left & emid";
    (* special for infer mode  *)
    if (is_pmode_infer g1) && (is_pmode_infer g2) then (
      let n1 = (List.length rsds1) + (List.length rsvs1) in
      let n2 = (List.length rsds2) + (List.length rsvs2) in
      if n1 > n2 then raise_prio_high "icompare #rules-star-view-data";
      if n1 < n2 then raise_prio_low "icompare #rules-star-view-data";
    );
    (* views and datas component *)
    let lst1, rst1 = g1.gl_lstats, g1.gl_rstats in
    let lst2, rst2 = g2.gl_lstats, g2.gl_rstats in
    let ldv1 = lst1.fst_num_datas + lst1.fst_num_views in
    let ldv2 = lst2.fst_num_datas + lst2.fst_num_views in
    let rdv1 = rst1.fst_num_datas + rst1.fst_num_views in
    let rdv2 = rst2.fst_num_datas + rst2.fst_num_views in
    if rdv1 < rdv2 then raise_prio_high "compare #right-datas-views";
    if rdv1 > rdv2 then raise_prio_low "compare #right-datas-views";
    if ldv1 < ldv2 then raise_prio_high "compare #left-datas-views";
    if ldv1 > ldv2 then raise_prio_low "compare #left-datas-views";
    (* view types *)
    let nvn1 = g1.gl_gstats.gst_view_names |> List.length in
    let nvn2 = g2.gl_gstats.gst_view_names |> List.length in
    if nvn1 > nvn2 then raise_prio_low "compare #view-names";
    if nvn1 < nvn2 then raise_prio_high "compare #view-names";
    (* compare hooked rules *)
    let _ = match g1.gl_hooked_rules, g2.gl_hooked_rules with
      | [], [] -> ()
      | _, [] -> raise_prio_high "compare hooked rule"
      | [], _ -> raise_prio_low "compare hooked rule"
      | [r1], [r2] ->
        let drv1 = process_one_rule pstate g1 r1 in
        let drv2 = process_one_rule pstate g2 r2 in
        let prio = compare_derivation pstate drv1 drv2 in
        if (prio != PrioEqual) then
          raise_prio prio ~msg:"compare hooked rule"
      | [r], _ -> raise_prio_high "compare hooked rule"
      | _, [r] -> raise_prio_low "compare hooked rule"
      | _ -> () in
    (* number of common args *)
    let cargs1 =
      let rsds_args = List.map (fun r -> r.rsd_num_common_args) rsds1 in
      let rsvs_args = List.map (fun r -> r.rsv_num_common_args) rsvs1 in
      List.sort (fun x y -> y - x) (rsds_args @ rsvs_args) in
    let cargs2 =
      let rsds_args = List.map (fun r -> r.rsd_num_common_args) rsds2 in
      let rsvs_args = List.map (fun r -> r.rsv_num_common_args) rsvs2 in
      List.sort (fun x y -> y - x) (rsds_args @ rsvs_args) in
    let cmp_cargs = List.compare compare_int cargs1 cargs2 in
    if cmp_cargs > 0 then raise_prio_high "compare #args common";
    if cmp_cargs < 0 then raise_prio_low "compare #args common";
    (* unifying plan *)
    (* TRUNG NOTE: this computation of unifying plan can be SLOW *)
    let n1 = g1 |> PL.find_unifying_plan prog |> List.length in
    let n2 = g2 |> PL.find_unifying_plan prog |> List.length in
    if n1 > n2 then raise_prio_high "compare unifying plan";
    if n1 < n2 then raise_prio_low "compare unifying plan";
    (* default *)
    PrioEqual
  with EPrio (res, msg) ->
    DB.nsprint ["compare_goal:";
                "\n ++ goal 1: "; pr_g g1; "\n ++ goal 2: "; pr_g g2;
               "\n ++ result: "; pr_prio res; "\n ++ reason: "; msg];
    res

and reorder_goals pstate goals : goal list =
  DB.trace_1 "reorder_goals"
    (pr_gs, pr_gs) goals
    (fun () -> reorder_goals_x pstate goals)

and reorder_goals_x pstate goals : goal list =
  (* sort derivations by a decreasing order of their weights *)
  let cmp_goal g1 g2 =
    let prio = compare_goal pstate g1 g2 in
    match prio with
    | PrioEqual -> 0
    | PrioLow -> -1
    | PrioHigh -> +1 in
  List.sort cmp_goal goals

and preprocess_derivation pstate drv : derivation =
  match drv.drv_kind with
  | DrvStatus _ -> drv
  | DrvBackjump _ -> drv
  | DrvSubgoals gs ->
    let gs = reorder_goals pstate gs in
    let gs = List.map (fun g ->
      (* DB.sprint ["Preprocess goal: "; pr_gc g]; *)
      let cache_rule = {
        crl_star_data = choose_rule_star_data pstate g;
        crl_star_view = choose_rule_star_view pstate g;
        crl_hypothesis = choose_rule_from_hypothesis pstate g;
        crl_theorem = choose_rule_from_theorem pstate g; } in
      {g with gl_cache_rule = Some cache_rule}) gs in
    {drv with drv_kind = DrvSubgoals gs}

and compare_derivation pstate drv1 drv2 : priority =
  DB.trace_2 "compare_derivation" (pr_drv, pr_drv, pr_prio) drv1 drv2
    (fun () -> compare_derivation_x pstate drv1 drv2)

and compare_derivation_x pstate drv1 drv2 : priority =
  try
    let rule1, rule2 = drv1.drv_rule, drv2.drv_rule in
    let kind1, kind2 = drv1.drv_kind, drv2.drv_kind in
    match kind1, kind2 with
    | DrvStatus MvlTrue, _ -> raise_prio PrioHigh;
    | _, DrvStatus MvlTrue -> raise_prio PrioLow;
    | DrvStatus MvlInfer, _ -> raise_prio PrioHigh;
    | _, DrvStatus MvlInfer -> raise_prio PrioLow;
    | DrvStatus MvlFalse, _ ->
      if (is_rule_trivial rule1) then raise_prio PrioHigh
      else raise_prio PrioLow
    | _, DrvStatus MvlFalse ->
      if (is_rule_trivial rule2) then raise_prio PrioLow
      else raise_prio PrioHigh
    | DrvStatus MvlUnkn, DrvStatus MvlUnkn -> raise_prio PrioEqual
    | DrvStatus MvlUnkn, _ -> raise_prio PrioLow
    | _, DrvStatus MvlUnkn -> raise_prio PrioHigh
    | DrvBackjump _, DrvBackjump _ -> raise_prio PrioEqual
    | DrvBackjump _, _ -> raise_prio PrioHigh
    | _, DrvBackjump _ -> raise_prio PrioLow
    | DrvSubgoals gs1, DrvSubgoals gs2 ->
      compare_conjunctive_goals pstate gs1 gs2
  (* default *)
  with EPrio (res, _) -> res

and reorder_derivations pstate goal drvs : derivation list =
  DB.trace_2 "reorder_derivations" (pr_g, pr_drvs, pr_drvs) goal drvs
    (fun () -> reorder_derivations_x pstate goal drvs)

and reorder_derivations_x pstate goal drvs : derivation list =
  (* sort derivations by a decreasing order of their weights *)
  let cmp_derivation drv1 drv2 =
    let prio = compare_derivation pstate drv1 drv2 in
    match prio with
    | PrioEqual -> 0
    | PrioLow -> 1
    | PrioHigh -> -1 in
  List.sort cmp_derivation drvs

and remove_low_priority_rules pstate goal rules : rule list =
  DB.trace_2 "remove_low_priority_rules"
    (pr_g, pr_rules, pr_rules) goal rules
    (fun () -> remove_low_priority_rules_x pstate goal rules)

and remove_low_priority_rules_x pstate goal rules : rule list =
  (* suppose that the list of rules is reordered *)
  let pth = pstate.prs_threshold in
  match rules with
  | [] -> rules
  | rule::_ ->
    let rules = match rule with
      | RlStarData rsd -> if (rsd.rsd_trivial) then [rule] else rules
      | RlStarView rsv -> if (rsv.rsv_trivial) then [rule] else rules
      | _ -> rules in
    if (pstate.prs_interact) then rules
    else if (List.length rules < pth.pth_tree_max_width) then rules
    else fst (EList.split_nth pth.pth_tree_max_width rules)

and remove_low_priority_derivations pstate goal drvs : derivation list =
  DB.trace_2 "remove_low_priority_derivations"
    (pr_g, pr_drvs, pr_drvs) goal drvs
    (fun () -> remove_low_priority_derivations_x pstate goal drvs)

and remove_low_priority_derivations_x pstate goal drvs : derivation list =
  (* suppose that the list of derivations is reordered *)
  let pth = pstate.prs_threshold in
  match drvs with
  | [] -> drvs
  | drv::_ ->
    let ndrvs = match drv.drv_rule with
      | RlStarData rsd -> if (rsd.rsd_trivial) then [drv] else drvs
      | RlStarView rsv -> if (rsv.rsv_trivial) then [drv] else drvs
      | _ -> drvs in
    if (pstate.prs_interact) then ndrvs
    else if (List.length ndrvs < pth.pth_tree_max_width) then ndrvs
    else fst (EList.split_nth pth.pth_tree_max_width ndrvs)

and process_axiom_goal pstate goal rule status : proof_tree =
  DB.trace_3 "process_axiom_goal"
    (pr_g, pr_rule, pr_mvl, pr_ptree) goal rule status
    (fun () -> process_axiom_goal_x pstate goal rule status)

and process_axiom_goal_x pstate goal rule status : proof_tree =
  let assumptions = goal.gl_assums in
  let ptc = mk_proof_tree_core ~assums:assumptions goal rule [] in
  let ptree = match status with
    | MvlTrue -> PtValid ptc
    | MvlInfer -> PtInfer ptc
    | _ -> herror "process_axiom_goal: not expect status: " pr_mvl status in
  mk_proof_tree_derive goal rule [] ptree

and process_conjunctive_subgoals pstate goal rule subgoals =
  DB.trace_3 "process_conjunctive_subgoals"
    (pr_g, pr_rule, pr_gs, pr_ptree) goal rule subgoals
    (fun () -> process_conjunctive_subgoals_x pstate goal rule subgoals)

and process_conjunctive_subgoals_x pstate goal rule subgoals =
  let collect_mutual_hps goal ptcs =
    if !mutual_induction && goal.gl_proof_mode = PrfEntail then
      ptcs |> List.map (fun ptc -> ptc.ptc_mutual_hypos) |>
      List.concat |> dedup_hypos
    else [] in
  let rec combine_status_conjuct (asts, apt, aptc, aasm, abkj) sgs =
    match sgs with
    | [] -> (asts, apt, aptc, aasm, abkj)
    | g::gs ->
      let g = {g with gl_assums = (g.gl_assums @ aasm) |> dedup_assums;
                      gl_hypos = g.gl_hypos @ (collect_mutual_hps goal aptc)} in
      let pt = prove_one_goal pstate g in
      let apt = apt @ [pt] in
      let ptstatus = get_ptree_status pt in
      match ptstatus with
      | PtValid ptc when ptc.ptc_backjump != None ->
        (MvlTrue, [pt], [ptc], [], ptc.ptc_backjump)
      | PtValid ptc ->
        let naasm = (aasm @ ptc.ptc_assums) |> dedup_assums in
        let status = if naasm = [] then asts else MvlInfer in
        combine_status_conjuct (status, apt, aptc @ [ptc], naasm, None) gs
      | PtInfer ptc ->
        let naasm = (aasm @ ptc.ptc_assums) |> dedup_assums in
        combine_status_conjuct (MvlInfer, apt, aptc @ [ptc], naasm, None) gs
      | PtInvalid ->
        if not !disprove_entail then (MvlUnkn, apt, [], [], None)
        else if is_rule_bidirection rule || List.length subgoals = 1 then
          (MvlFalse, apt, [], [], None)
        else (MvlUnkn, apt, [], [], None)
      | PtUnkn _ -> (MvlUnkn, apt, [], [], None) in
  let status, pts, ptcs, asm, backjump =
    subgoals |>
    List.sort (fun g1 g2 -> compare_f_by_heap_size g1.gl_lhs g2.gl_lhs) |>
    combine_status_conjuct (MvlTrue, [], [], [], None) in
  match backjump with
  | Some bkj when bkj.bkj_ent_id = goal.gl_ent_id -> List.hd pts
  | _ ->
    let heur = get_rule_heur rule in
    let heur = combine_heurs (heur::(List.map get_ptree_heur pts)) in
    let ptstatus = match status with
      | MvlTrue ->
        let _ = if (asm != []) then error "process_conjunctive_subgoals: \
                                           expect empty assumptions" in
        let nhps =
          if !mutual_induction && (is_rule_induction rule) &&
             (ID.check_potential_mutual_hypothesis pstate goal) then
            [mk_hypothesis pstate.prs_prog goal]
          else [] in
        let hps = nhps @ (collect_mutual_hps goal ptcs) in
        PtValid (mk_proof_tree_core goal rule ptcs ~mutualhp:hps)
      | MvlInfer ->
        PtInfer (mk_proof_tree_core ~assums:asm goal rule ptcs)
      | MvlFalse -> PtInvalid
      | MvlUnkn -> PtUnkn "ConjunctSubgoals" in
    mk_proof_tree_derive ~heur:heur goal rule pts ptstatus

and process_candidate_derivations pstate goal drvs =
  DB.trace_2 "process_candidate_derivations"
    (pr_g, pr_drvs, pr_ptree_detail) goal drvs
    (fun () -> process_candidate_derivations_x pstate goal drvs)

and process_candidate_derivations_x pstate goal drvs =
  let heur = combine_heurs (List.map (fun drv -> drv.drv_heur) drvs) in
  let actions = drvs |> List.map (fun r -> PraDrv r) in
  process_candidate_actions pstate goal heur actions

and process_candidate_rules pstate goal rules =
  DB.trace_2 "process_candidate_rules"
    (pr_g, pr_rules, pr_ptree_detail) goal rules
    (fun () -> process_candidate_rules_x pstate goal rules)

and process_candidate_rules_x pstate goal rules =
  let heur = get_rules_heur rules in
  let actions = rules |> List.map (fun r -> PraRule r) in
  process_candidate_actions pstate goal heur actions

and process_candidate_actions pstate goal heur actions =
  let prog = pstate.prs_prog in
  let rec try_action aptrees acts =
    let act = select_candidate_action pstate goal acts in
    let stored_interact = pstate.prs_interact in
    let selection = match act with
      | DB.UacQuit -> None
      | DB.UacRunAll [] -> None
      | DB.UacRunAll (x::xs) -> pstate.prs_interact <- false; Some (x, xs)
      | DB.UacRunStep (x, xs) -> Some (x, xs) in
    match selection, act, actions with
    | _, DB.UacQuit, _ ->
      DB.pprint "Quit";
      mk_ptree_search_unkn goal aptrees ~heur:heur "Quit"
    | None, _, [] ->
      mk_ptree_search_invalid goal [] ~heur:heur
    | None, _, _ ->
      List.iter (fun pt ->
        let status = pt |> get_ptree_status |> pr_ptree_status in
        DB.nsprint ["Entail: "; pt |> get_ptree_goal |> pr_gc; "; ";
                   "Status: "; status]) aptrees;
      disprove_one_goal pstate goal aptrees
    | Some (act, acts), _, _ ->
      let ptree, rule = match act with
        | PraDrv drv -> (process_one_derivation pstate drv, drv.drv_rule)
        | PraRule rule ->
          let drv = process_one_rule pstate goal rule in
          (process_one_derivation pstate drv, rule) in
      let acc = aptrees @ [ptree] in
      let status = get_ptree_status ptree in
      if !dump_ptree_profile && is_valid_status status then
        Xml.export_negative_goal_rule prog goal rule;
      let ptree = match status with
        | PtValid _ | PtInfer _ ->
          mk_proof_tree_search ~heur:heur goal acc status
        | PtInvalid ->
          if is_rule_bidirection rule then ptree
          else try_action acc acts
        | PtUnkn _ -> try_action acc acts in
      let _ = pstate.prs_interact <- stored_interact in
      ptree in
  try_action [] actions

and update_mutual_hypotheses pstate goal ptree =
  match !mutual_induction with
  | false -> ()
  | true ->
    let ptstatus = get_ptree_status ptree in
    (* update theorems and counter theorems *)
    let lhs, rhs, id = goal.gl_lhs, goal.gl_rhs, goal.gl_ent_id in
    match ptstatus with
    | PtValid _ ->
      (* TODO FIXME: check status of theorems later *)
      let lm_name = "ent_" ^ (string_of_int id) in
      let lm = mk_lemma lm_name lhs rhs LmsValid LorgMutual in
      if (ID.check_potential_mutual_lemma pstate lm ptree) then
        let lhs, rhs, origin = lm.lm_lhs, lm.lm_rhs, lm.lm_origin in
        let th = mk_theorem pstate.prs_prog lm.lm_name lhs rhs origin in
        pstate.prs_theorems <- pstate.prs_theorems @ [th];
    | PtInfer _ -> ()     (* no need to update lemmas in infer-tree *)
    | PtInvalid ->
      (* TODO: consider *)
      let cth_name = "Goal(" ^ (pr_int id) ^ ")" in
      let cth = mk_counter_theorem pstate.prs_prog cth_name lhs rhs MvlFalse in
      if (ID.check_potential_counter_theorem cth) then
        pstate.prs_counter_theorems <- pstate.prs_counter_theorems @ [cth];
    | PtUnkn _ ->
      let cth_name = "Goal(" ^ (pr_int id) ^ ")" in
      let cth = mk_counter_theorem pstate.prs_prog cth_name lhs rhs MvlUnkn in
      if (ID.check_potential_counter_theorem cth) then
        pstate.prs_counter_theorems <- pstate.prs_counter_theorems @ [cth]

and need_infer_lemma_early goal =
  try
    if !proof_lemma_synthesis_early then raise_bool true;
    let lst, rst, gst = goal.gl_lstats, goal.gl_rstats, goal.gl_gstats in
    let vfs = lst.fst_views @ rst.fst_views in
    if List.exists has_int_const_arg_vf vfs then raise_bool true;
    if gst.gst_num_view_names > 1 &&
       lst.fst_num_hatoms >= !thd_min_size_choose_only_theorem &&
       rst.fst_num_hatoms >= !thd_min_size_choose_only_theorem then
      raise_bool true;
    (* default *)
    false
  with EBool res -> res

and noneed_infer_lemma prog goal =
  try
    let lst, rst, gst = goal.gl_lstats, goal.gl_rstats, goal.gl_gstats in
    let vdefns = prog.prog_views in
    (* if lst.fst_num_hatoms = 1 && *)
    (*    rst.fst_num_hatoms = 1 && *)
    (*    List.for_all (is_recur_direct_vf vdefns) lst.fst_views && *)
    (*    not (List.exists has_const_arg_vf lst.fst_views) then *)
    (*   raise_bool true; *)
    (* no need lemma when then entailment is simple *)
    if goal.gl_matching_plans = [] &&
       lst.fst_num_views > 0 && rst.fst_num_views > 0 &&
       rst.fst_fhvs = [] then
      raise_bool false;
    let _, _, pf = extract_components_f goal.gl_lhs in
    if List.for_all (is_recur_direct_vf vdefns) lst.fst_views &&
       not (List.exists has_const_arg_vf lst.fst_views) &&
       (is_true_pf pf) && gst.gst_num_view_names <= 1 &&
       gst.gst_num_hatoms <= 10 then
      raise_bool true;
    (* find unifying pland *)
    let unfs = PL.find_unifying_plan prog goal in
    if unfs != [] then raise_bool true;
    (* default *)
    raise_bool false
  with EBool res ->
    DB.npprint ("NONEED infer lemma?\n" ^
               "   GOAL: " ^ (pr_g goal) ^ "\n" ^
               "   NONEED: " ^ (pr_bool res));
    res

and need_infer_lemma pstate goal rules : bool =
  try
    let vdefns = pstate.prs_prog.prog_views in
    if not (is_pmode_entail goal) || not (goal.gl_need_infer_lemma) then
      raise_bool false;
    let has_useful_rule_theorem = rules |> List.exists (fun r ->
      (is_rule_theorem r) && not (is_rule_useless pstate goal rules r)) in
    if has_useful_rule_theorem then
      raise_bool false;
    if goal.gl_matching_plans != [] then
      raise_bool false;
    let can_use_current_rule =
      List.exists (fun r -> match r with
        | RlInduction rid ->
          (rid.rid_has_data_common_arg_indt_case &&
           get_view_recur_direction vdefns rid.rid_lg_view = VrdTail) ||
          (rid.rid_has_data_same_root &&
           get_view_recur_direction vdefns rid.rid_lg_view = VrdHead)
        | RlStarData rsd -> rsd.rsd_same_root
        | _ -> false) rules in
    if can_use_current_rule then raise_bool false;
    (* default *)
    true
  with EBool res -> res

and choose_lemma_template_important prog goal lmts =
  let lmt_converts = List.filter (fun lmt ->
    match lmt.lmt_typ with
    | LmtConvert -> true
    | _ -> false) lmts in
  if (List.length lmts > 5) && (List.length lmt_converts <=2) then
    lmt_converts
  else lmts

and compare_lemma_template prog goal lmt1 lmt2 =
  let vdefns = prog.prog_views in
  let rec compare_lmt lmt1_data lmt2_data =
    let lhs1, rhs1, lst1, rst1, typ1 = lmt1_data in
    let lhs2, rhs2, lst2, rst2, typ2 = lmt2_data in
    let lvfs1, rvfs1 = Pair.fold collect_view_form lhs1 rhs1 in
    let lvfs2, rvfs2 = Pair.fold collect_view_form lhs2 rhs2 in
    let vrds1 =
      (lvfs1 @ rvfs1) |> List.map (get_view_recur_direction vdefns) |>
      List.dedup (=) in
    let vrds2 =
      (lvfs2 @ rvfs2) |> List.map (get_view_recur_direction vdefns) |>
      List.dedup (=) in
    let num_lvs1 = lhs1 |> av |> List.length in
    let num_rvs1 = rhs1 |> av |> List.length in
    let num_lvs2 = lhs2 |> av |> List.length in
    let num_rvs2 = rhs2 |> av |> List.length in
    let num_vs1 = num_lvs1 + num_rvs1 in
    let num_vs2 = num_lvs2 + num_rvs2 in
    try match typ1, typ2 with
      | LmtConvert, LmtConvert ->
        if (List.length vrds1 < List.length vrds2) then
          raise_prio PrioHigh;
        if (List.length vrds1 > List.length vrds2) then
          raise_prio PrioLow;
        if (num_lvs1 < num_lvs2) && (num_rvs1 < num_rvs2) then
          raise_prio PrioHigh;
        if (num_lvs1 > num_lvs2) && (num_rvs1 > num_rvs2) then
          raise_prio PrioLow;
        if (num_vs1 < num_vs2) then raise_prio PrioHigh;
        if (num_vs1 > num_vs2) then raise_prio PrioLow;
        (* default *)
        PrioEqual
      | LmtConvert, LmtCombine ->
        let _ = match lst1.fst_views, rst1.fst_views with
          | [lvf], [rvf] ->
            if List.length lvf.viewf_args = List.length rvf.viewf_args then
              raise_prio PrioHigh;
          | _ -> () in
        (* if (List.length vrds1 < List.length vrds2) then *)
        (*   raise_prio PrioHigh; *)
        (* if (List.length vrds1 > List.length vrds2) then *)
        (*   raise_prio PrioLow; *)
        (* default *)
        PrioHigh
      | LmtConvert, LmtSplit ->
        let _ = match lst1.fst_views, rst1.fst_views with
          | [lvf], [rvf] ->
            if List.length lvf.viewf_args = List.length rvf.viewf_args then
              raise_prio PrioHigh;
          | _ -> () in
        (* if (List.length vrds1 < List.length vrds2) then *)
        (*   raise_prio PrioHigh; *)
        (* if (List.length vrds1 > List.length vrds2) then *)
        (*   raise_prio PrioLow; *)
        (* default *)
        PrioHigh
      | LmtCombine, LmtConvert ->
        neg_prio (compare_lmt lmt2_data lmt1_data)
      | LmtCombine, LmtCombine ->
        if (List.length vrds1 < List.length vrds2) then
          raise_prio PrioHigh;
        if (List.length vrds1 > List.length vrds2) then
          raise_prio PrioLow;
        (* default *)
        PrioEqual
      | LmtCombine, LmtSplit ->
        (* default *)
        PrioEqual
        (* PrioHigh *)
      | LmtSplit, LmtConvert ->
        neg_prio (compare_lmt lmt2_data lmt1_data)
      | LmtSplit, LmtCombine ->
        neg_prio (compare_lmt lmt2_data lmt1_data)
      | LmtSplit, LmtSplit ->
        if (List.length vrds1 < List.length vrds2) then
          raise_prio PrioHigh;
        if (List.length vrds1 > List.length vrds2) then
          raise_prio PrioLow;
        if rst1.fst_num_datas > rst2.fst_num_datas then
          raise_prio PrioHigh;
        if rst1.fst_num_datas < rst2.fst_num_datas then
          raise_prio PrioLow;
        (* default *)
        PrioEqual
    with EPrio (res, _) -> res in
  let typ1, typ2 = lmt1.lmt_typ, lmt2.lmt_typ in
  let lhs1, lhs2 = lmt1.lmt_lhs, lmt2.lmt_lhs in
  let rhs1, rhs2 = lmt1.lmt_rhs, lmt2.lmt_rhs in
  let lst1, lst2 = mk_formula_stats prog lhs1, mk_formula_stats prog lhs2 in
  let rst1, rst2 = mk_formula_stats prog rhs1, mk_formula_stats prog rhs2 in
  let lmt1_data = (lhs1, rhs1, lst1, rst1, typ1) in
  let lmt2_data = (lhs2, rhs2, lst2, rst2, typ2) in
  match compare_lmt lmt1_data lmt2_data with
  | PrioEqual -> 0
  | PrioLow -> -1
  | PrioHigh -> 1

and infer_lemma_by_need pstate goal rules =
  let old_interact = pstate.prs_interact in
  let prog = pstate.prs_prog in
  try
    let _ = if goal.gl_proof_mode = PrfEntail then (
      let needed = need_infer_lemma pstate goal rules in
      DB.nhprint "CHECK NEED INFER LEMMA: GOAL: " pr_g goal;
      DB.nhprint "INFER LEMMA ATTEMPTED: " pr_ss pstate.prs_infer_lemma_attempted;
      DB.nhprint "RULES: " pr_rules rules;
      DB.nhprint "NEED_INFER_LEMMA: " pr_bool needed) in
    if not (need_infer_lemma pstate goal rules) then raise_lemmas [];
    pstate.prs_interact <- false;
    let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
    (* create all templates *)
    let lm_tmpls =
      (create_lemma_template_convert pstate lhs rhs) @
      (create_lemma_template_combine pstate lhs rhs) @
      (create_lemma_template_split pstate lhs rhs) in
    DB.nhprint "LEMMA TEMPLATES: " pr_lmts lm_tmpls;
    if lm_tmpls = [] then raise_lemmas [];
    (* remove useless, reorder, and cluster *)
    DB.pprint "===> START INFER LEMMA BY NEED!";
    DB.hprint "GOAL ENTAILMENT: " pr_g goal;
    DB.hprint "ALL LEMMA TEMPLATES:\n" pr_lmts lm_tmpls;
    let lm_tmpls = choose_lemma_template_important pstate goal lm_tmpls in
    DB.hprint "LEMMA TEMPLATES AFTER CHOOSING IMPORTANT:\n" pr_lmts lm_tmpls;
    let lm_tmpls =
      List.sortd (compare_lemma_template prog goal) lm_tmpls in
    DB.hprint "LEMMA TEMPLATES AFTER REORDERING:\n" pr_lmts lm_tmpls;
    let lm_tmplss =
      List.cluster (compare_lemma_template prog goal) lm_tmpls in
    DB.hprint "LEMMA TEMPLATES AFTER CLUSTERING:\n" pr_lmtss lm_tmplss;
    (* synthesize *)
    let num_tmpls = lm_tmplss |> List.map List.length |> List.fold_left (+) 0 in
    let lms = List.fold_left (fun acc lmts ->
      let lms =
        lmts |> List.map (infer_one_lemma_template pstate goal) |>
        List.concat in
      if lms = [] then acc
      else if num_tmpls > 2 then raise_lemmas (acc @ lms)
      else if lms |> List.exists (fun lm ->
        let num_lvs = List.length (av lm.lm_lhs) in
        let num_rvs = List.length (av lm.lm_rhs) in
        String.exists lm.lm_name "convert" &&
        (num_lvs != num_rvs)) then acc @ lms
      else raise_lemmas (acc @ lms)) [] lm_tmplss in
    (* default *)
    raise_lemmas lms ;
  with ELemmas lms ->
    pstate.prs_interact <- old_interact;
    if (lms != []) then
      DB.hprint "LEMMAS INFERRED BY NEED: \n" pr_lms lms;
    lms

and check_goal_timeout pstate goal : unit =
  if !timeout_check_enabled &&
     (get_time () -. pstate.prs_start_time) > pstate.prs_timeout then
    raise_ptree (mk_ptree_search_unkn goal [] "TimeOut")
  else ()

and prove_one_goal pstate goal : proof_tree =
  DB.trace_1 "prove_one_goal" (pr_g, pr_ptree) goal
    (fun () -> prove_one_goal_x pstate goal)

and prove_one_goal_x pstate goal : proof_tree =
  let pr_msg msg f x = DB.fhprintln pstate.prs_interact (msg ^ "\n") f x in
  try
    let _ = check_goal_timeout pstate goal in
    let _ = goal |> choose_axiom_rules pstate |>
            Opt.iter ((process_axiom_rule pstate goal) >> raise_ptree) in
    let _ = goal |> detect_unproductive_goal_early pstate |>
            Opt.iter raise_ptree in
    let rules = match goal.gl_hooked_rules with
      | [] ->
        let rule_norms = choose_normalize_rules pstate goal in
        if (rule_norms != []) then rule_norms
        else choose_spatial_rules pstate goal
      | rs -> rs in
    pr_msg "GOAL ENTAILMENT: " pr_g goal;
    pr_msg "ALL POSSIBLE RULES: " pr_rules rules;
    let trirule = detect_trivial_rules pstate goal rules in
    let ptree = match trirule with
      | Some r ->
        pr_msg "FOUND A TRIVIAL RULE: " pr_rules [r];
        process_candidate_rules pstate goal [r]
      | None ->
        (* infer lemmas *)
        DB.nhprint "NONEED_INFER_LEMMA: " pr_bool
          (noneed_infer_lemma pstate.prs_prog goal);
        let lms =
          if noneed_infer_lemma pstate.prs_prog goal then []
          else infer_lemma_by_need pstate goal rules in
        match lms with
        | [] -> process_spatial_rules pstate goal rules
        | _ ->
          goal |> update_inferred_lemmas_mode_need pstate lms |>
          prove_one_goal pstate in
    raise_ptree ptree
  with EPtree ptree ->
    let _ = update_mutual_hypotheses pstate goal ptree in
    (* return *)
    ptree

and update_inferred_lemmas_mode_need pstate lemmas goal : goal =
  let prog = pstate.prs_prog in
  DB.hprint "LEMMAS: " pr_lms lemmas;
  let ths = List.map (mk_theorem_from_lemma prog) lemmas in
  DB.hprint "THEOREMS: " pr_ths ths;
  let _ = pstate.prs_theorems <- pstate.prs_theorems @ ths in
  {goal with gl_cache_rule = None}

and process_one_derivation pstate (drv: derivation) : proof_tree =
  DB.trace_1 "process_one_derivation" (pr_drv, pr_ptree_detail) drv
    (fun () -> process_one_derivation_x pstate drv)

and process_one_derivation_x pstate (drv: derivation) : proof_tree =
  let r, g = drv.drv_rule, drv.drv_goal in
  let mk_ptd = mk_proof_tree_derive ~heur:drv.drv_heur in
  match drv.drv_kind with
  | DrvStatus MvlFalse -> mk_ptd g r [] PtInvalid
  | DrvStatus MvlTrue -> process_axiom_goal pstate g r MvlTrue
  | DrvStatus MvlInfer -> process_axiom_goal pstate g r MvlInfer
  | DrvStatus MvlUnkn -> mk_ptd g r [] (PtUnkn "ProcessOneDerivation")
  | DrvSubgoals sgs -> process_conjunctive_subgoals pstate g r sgs
  | DrvBackjump (sgs, ent_id) ->
    let ptree = process_conjunctive_subgoals pstate g r sgs in
    let bkj = mk_backjump ent_id drv.drv_rule in
    update_ptree_backjump ptree bkj

and select_candidate_action pstate goal actions =
  let pr_msg msg f x = DB.fhprintln pstate.prs_interact (msg ^ "\n") f x in
  let action_typ =
    if List.exists (fun act -> match act with
      | PraRule _ -> true | _ -> false) actions then "rule"
    else "derivation" in
  if pstate.prs_interact then
    let rec select_one_action action =
      let num_drvs = List.length actions in
      let derivation_enum =
        if (num_drvs = 0) then "[a/q]"
        else if (num_drvs = 1) then "[1/a/q]"
        else "[1.." ^ (pr_int num_drvs) ^ "/a/q]" in
      DB.print ("$$$ Choose a " ^ action_typ ^ " " ^ derivation_enum ^ ": ");
      try
        (* TODO: make type for choice *)
        let choice = String.uppercase_ascii (String.trim (read_line ())) in
        if (String.equal choice "Q") then DB.UacQuit
        else if (String.equal choice "A") then DB.UacRunAll actions
        else
          let derivation_id = int_of_string (choice) in
          let _, chosen_drvs, other_drvs = List.fold_left (fun (id, cs, os) r ->
            if (id = derivation_id) then (id + 1, cs @ [r], os)
            else (id + 1, cs, os @ [r])) (1, [], []) actions in
          if chosen_drvs = [] then raise Not_found
          else DB.UacRunStep (List.hd chosen_drvs, other_drvs)
      with _ ->
        DB.pprint "Invalid derivation id. Please try again!";
        select_one_action actions in
    let action_msg = match actions with
      | [] -> "[no " ^ action_typ ^"]"
      | _ ->
        actions |> List.mapi (fun id act -> match act with
          | PraRule rule -> " [" ^ (pr_int (id + 1)) ^ "] " ^ (pr_rule rule)
          | PraDrv drv -> " [" ^ (pr_int (id + 1)) ^ "] " ^ (pr_drv drv)) |>
        String.concat "\n" in
    pr_msg "PROVING ENTAILMENT GOAL: " pr_g goal;
    pr_msg ("CANDIDATE " ^ (String.uppercase_ascii action_typ) ^ " : ")
      pr_id action_msg;
    select_one_action actions
  else match actions with
    | [] -> DB.UacRunAll []
    | act::acts -> DB.UacRunStep (act, acts)

and select_candidate_derivation pstate goal drvs  =
  let pr_msg msg f x = DB.fhprintln pstate.prs_interact (msg ^ "\n") f x in
  if pstate.prs_interact then
    let rec select_one_derivation drvs =
      let num_drvs = List.length drvs in
      let derivation_enum =
        if (num_drvs = 0) then "[a/q]"
        else if (num_drvs = 1) then "[1/a/q]"
        else "[1.." ^ (pr_int num_drvs) ^ "/a/q]" in
      DB.print ("$$$ Choose a derivation " ^ derivation_enum ^ ": ");
      try
        (* TODO: make type for choice *)
        let choice = String.uppercase_ascii (String.trim (read_line ())) in
        if (String.equal choice "Q") then DB.UacQuit
        else if (String.equal choice "A") then DB.UacRunAll drvs
        else
          let derivation_id = int_of_string (choice) in
          let _, chosen_drvs, other_drvs = List.fold_left (fun (id, cs, os) r ->
            if (id = derivation_id) then (id + 1, cs @ [r], os)
            else (id + 1, cs, os @ [r])) (1, [], []) drvs in
          if chosen_drvs = [] then raise Not_found
          else DB.UacRunStep (List.hd chosen_drvs, other_drvs)
      with _ ->
        DB.pprint "Invalid derivation id. Please try again!";
        select_one_derivation drvs in
    let drvs_msg = match drvs with
      | [] -> "[no sub goal]"
      | _ ->
        let msg, _ = List.fold_left (fun (msg, id) drv ->
          let nmsg = msg ^ (" [" ^ (pr_int id) ^ "] " ^ (pr_drv drv)) ^ "\n" in
          let nid = id + 1 in
          (nmsg, nid)) ("", 1) drvs in
        msg in
    pr_msg "PROVING ENTAILMENT GOAL: " pr_g goal;
    pr_msg "CANDIDATE DERIVATIONS: " pr_id drvs_msg;
    select_one_derivation drvs
  else match drvs with
    | [] -> DB.UacRunAll []
    | drv::drvs -> DB.UacRunStep (drv, drvs)

and select_candidate_rule ?(interact=false) pstate goal rules  =
  let pr_msg msg f x = DB.fhprintln pstate.prs_interact (msg ^ "\n") f x in
  if interact then
    let rec select_one_rule rules =
      let num_rules = List.length rules in
      let rule_enum =
        if (num_rules = 0) then "[a/q]"
        else if (num_rules = 1) then "[1/a/q]"
        else "[1.." ^ (pr_int num_rules) ^ "/a/q]" in
      DB.print ("$$$ Choose a rule " ^ rule_enum ^ ": ");
      try
        (* TODO: make type for choice *)
        let choice = String.uppercase_ascii (String.trim (read_line ())) in
        if (String.equal choice "Q") then DB.UacQuit
        else if (String.equal choice "A") then DB.UacRunAll rules
        else
          let rule_id = int_of_string (choice) in
          let _, chosen_rules, other_rules = List.fold_left (fun (id, cs, os) r ->
            if (id = rule_id) then (id + 1, cs @ [r], os)
            else (id + 1, cs, os @ [r])) (1, [], []) rules in
          if chosen_rules = [] then raise Not_found
          else DB.UacRunStep (List.hd chosen_rules, other_rules)
      with _ ->
        DB.pprint "Invalid rule id. Please try again!";
        select_one_rule rules in
    let rules_msg = match rules with
      | [] -> "[no sub goal]"
      | _ ->
        let msg, _ = List.fold_left (fun (msg, id) rule ->
          let nmsg = msg ^ (" [" ^ (pr_int id) ^ "] " ^ (pr_rule rule)) ^ "\n" in
          let nid = id + 1 in
          (nmsg, nid)) ("", 1) rules in
        msg in
    pr_msg "PROVING ENTAILMENT GOAL: " pr_g goal;
    pr_msg "CANDIDATE RULES: " pr_id rules_msg;
    select_one_rule rules
  else match rules with
    | [] -> DB.UacRunAll rules
    | rule::rules -> DB.UacRunStep (rule, rules)

and process_one_rule pstate goal rule : derivation =
  DB.trace_2 "process_one_rule" (pr_g, pr_rule, pr_drv) goal rule
    (fun () -> process_one_rule_x pstate goal rule)

and process_one_rule_x pstate goal rule : derivation =
  let drv = match rule with
    | RlStarData rsd -> process_rule_star_data pstate goal rsd
    | RlStarView rsv -> process_rule_star_view pstate goal rsv
    | RlViewLeft rvl -> process_rule_view_left pstate goal rvl
    | RlViewRight rvr -> process_rule_view_right pstate goal rvr
    | RlInduction rid -> process_rule_induction pstate goal rid
    | RlHypothesis rhp -> process_rule_hypothesis pstate goal rhp
    | RlTheorem rth -> process_rule_theorem pstate goal rth
    | RlPureEntail rpe -> process_rule_pure_entail pstate goal rpe
    | RlEqualLeft reql -> process_rule_equal_left pstate goal reql
    | RlExistsLeft rexl -> process_rule_exists_left pstate goal rexl
    | RlExistsRight rexr -> process_rule_exists_right  pstate goal rexr
    | RlEmpLeft reml -> process_rule_emp_left pstate goal reml
    | RlEmpRight remr -> process_rule_emp_right pstate goal remr
    | RlDropLeft rdl -> process_rule_drop_left pstate goal rdl
    | RlDropRight rdr -> process_rule_drop_right pstate goal rdr
    | RlUnfoldRel rur -> process_rule_unfold_relation pstate goal rur
    | RlFalseLeft rfl -> process_rule_false_left pstate goal rfl
    | RlExclMid rem -> process_rule_excluded_middle pstate goal rem
    | RlInferRel rir -> process_rule_infer_relation pstate goal rir
    | RlGenLeft rgl -> process_rule_gen_left pstate goal rgl
    | RlWeakenLeft rwl -> process_rule_weaken_left pstate goal rwl
    | _ -> herror "process_one_rule: not expect: " pr_rule rule in
  let heur = get_rule_heur rule in
  {drv with drv_heur = heur}

and process_axiom_rule pstate goal rule =
  DB.trace_2 "process_axiom_rule" (pr_g, pr_rule, pr_ptree) goal rule
    (fun () -> process_axiom_rule_x pstate goal rule)

and process_axiom_rule_x pstate goal rule =
  let pr_msg f x = DB.fhprintln pstate.prs_interact f x in
  pr_msg "AXIOM RULE:\n" pr_rule rule;
  let drv = process_one_rule pstate goal rule in
  process_candidate_derivations pstate goal [drv]

and process_spatial_rules pstate goal rules =
  try
    let pr_msg msg f x = DB.fhprintln pstate.prs_interact msg f x in
    pr_msg "PROCESS SPATIAL RULES: " pr_rules rules;
    let prog = pstate.prs_prog in
    let mrules, rules =
      match !machine_learning, !machine_learning_hybrid with
      | true, false when (List.length rules > 1) ->
        let mrs = goal |> LN.query_rule prog |> List.split |> fst in
        let rs = List.filter (fun r ->
          List.exists (fun mr -> mr = get_meta_rule r) mrs) rules in
        pr_msg "RULES AFTER LEARNING CLASS: " pr_rules rs;
        let rs = List.map (update_rule_heur PhML) rs in
        (mrs, rs)
      | true, true when (List.length rules > 1) ->
        let mrs = goal |> LN.query_rule prog in
        let max_cfd = mrs |> List.split |> snd |> List.max in
        let mrs = List.fold_left (fun acc (mr, c) ->
          if c >= !machine_learning_hybrid_confidence then acc @ [mr]
          else acc) [] mrs in
        let msg = "Hybrid mode: max confident: " ^ (pr_float max_cfd) in
        if (mrs != []) then (
          DB.pprint (msg ^ ":  ---> use ML");
          let rs = List.filter (fun r ->
            List.exists (fun mr -> mr = get_meta_rule r) mrs) rules in
          let rs = List.map (update_rule_heur PhML) rs in
          let _ = pr_msg "RULES AFTER LEARNING CLASS (ML HYBRID MODE): "
                    pr_rules rs in
          (mrs, rs))
        else (
          DB.pprint (msg ^ ":  ---> use HM");
          let rs = choose_rule_important pstate goal rules in
          pr_msg "RULES AFTER CHOOSING IMPORTANT (ML HYBRID MODE): "
            pr_rules rs;
          ([], rs))
      | _ ->
        let rs = choose_rule_important pstate goal rules in
        pr_msg "RULES AFTER CHOOSING IMPORTANT: " pr_rules rs;
        ([], rs) in
    DB.ddhprint "Process spatial rules: " pr_rules rules;
    match mrules, !machine_learning_all with
    | [], _ -> process_spatial_rules_heuristics pstate goal rules
    | _, false -> process_spatial_rules_heuristics pstate goal rules
    | _, true -> process_spatial_rules_learning pstate goal rules mrules
  with EPtree pt -> pt

and process_spatial_rules_learning pstate goal rules mrules =
  let pr_msg msg f x = DB.fhprintln pstate.prs_interact msg f x in
  let heap_pos = List.map (LN.query_heap_pos pstate.prs_prog goal) mrules in
  let rules = rules |> List.filter (fun rule ->
    let lpos, rpos = get_rule_heap_pos goal rule in
    heap_pos |> List.exists (fun (x, y)-> x = lpos && y = rpos)) in
  pr_msg "RULES AFTER LEARNING PREDICATE: " pr_rules rules;
  process_candidate_rules pstate goal rules

  (* TODO: rename proc *)
and process_spatial_rules_heuristics pstate goal rules =
  let pr_msg msg = DB.fprintln pstate.prs_interact msg in
  let pr_hmsg msg f x = DB.fhprintln pstate.prs_interact msg f x in
  let rules, ruless =
    let rules = remove_useless_rules pstate goal rules in
    pr_hmsg "RULES AFTER REMOVING USELESS: " pr_rules rules;
    let rules = remove_redundant_rules pstate goal rules in
    pr_hmsg "RULES AFTER REMOVING REDUNDANT: " pr_rules rules;
    let ruless = reorder_cluster_rules pstate goal rules in
    pr_hmsg "REORDER CLUSTER RULES: " pr_ruless ruless;
    let rules = List.concat ruless in
    rules, ruless in
  DB.ddhprint "Process spatial rules (2): " pr_rules rules;
  let need_preprocess_drv =
    try
      if (is_pmode_infer goal) then raise_bool true;
      let used_theorem_names = rules |> List.map (function
        | RlTheorem rth -> [rth.rth_th.th_name]
        | _ -> []) |> List.concat |> dedup_ss in
      if (List.for_all (is_rule_theorem) rules) &&
         (List.length used_theorem_names = 1) then raise_bool false;
      if (List.length rules <=1 ) then raise_bool false;
      if (List.length rules > !thd_max_num_rules_preprocess) &&
         not (List.exists is_rule_theorem rules) then
        raise_bool false;
      (* default *)
      true
    with EBool res -> res in
  match need_preprocess_drv with
  | true ->
    pr_msg "START PRE-PROCESSING RULES";
    let drvss = List.map (fun rs ->
      rs |> List.map (process_one_rule pstate goal)) ruless in
    pr_hmsg "RULES AFTER PROCESS ONE RULES: " pr_rule_drvss drvss;
    let drvss = List.map (remove_useless_derivations pstate goal) drvss in
    pr_hmsg "RULES AFTER REMOVING USELESS DERIVATIONS: " pr_rule_drvss drvss;
    let drvss = List.map (List.map (preprocess_derivation pstate)) drvss in
    pr_hmsg "RULES AFTER PREPROCESS DERIVATIONS: " pr_rule_drvss drvss;
    let drvss = List.map (reorder_derivations pstate goal) drvss in
    pr_hmsg "RULES AFTER REORDERING DERIVATIONS: " pr_rule_drvss drvss;
    let drvs = List.concat drvss in
    let drvs = remove_low_priority_derivations pstate goal drvs in
    pr_hmsg "RULES AFTER REMOVING LOW-PRIORITY DERIVATIONS: " pr_rule_drvs drvs;
    process_candidate_derivations pstate goal drvs
  | false ->
    pr_msg "SKIP PRE-PROCESSING RULES";
    let rules = remove_low_priority_rules pstate goal rules in
    process_candidate_rules pstate goal rules

and disprove_one_goal pstate (goal: goal) strees : proof_tree =
  DB.trace_1 "disprove_one_goal" (pr_g, pr_ptree) goal
    (fun () -> disprove_one_goal_x pstate goal strees)

and disprove_one_goal_x pstate goal strees =
  let heur = strees |> List.map get_ptree_heur |> combine_heurs in
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let lhs, hconsumed, trace = goal.gl_lhs, goal.gl_hconsumed, goal.gl_trace in
  let mk_pts = mk_proof_tree_search ~heur:heur in
  if is_pmode_infer goal && goal.gl_has_unplanned_excl_mid then
    let ias = (mk_assum_false lhs hconsumed trace) in
    let asm = goal.gl_assums @ [ias] in
    let goal = {goal with gl_assums = asm} in
    let rule = mk_rule_infer_relation_false lhs hconsumed ias in
    let ptcore = mk_proof_tree_core ~assums:asm goal rule [] in
    mk_pts goal strees (PtInfer ptcore)
  else if lst.fst_is_pure && not rst.fst_is_pure then
    mk_pts goal strees PtInvalid
  else if not lst.fst_has_view && List.for_all is_invalid_ptree strees then
    mk_pts goal strees PtInvalid
  else if not lst.fst_is_pure && not lst.fst_has_view && rst.fst_is_pure then
    mk_pts goal strees PtInvalid
  else
    mk_pts goal strees (PtUnkn "DisproveOneGoal")

and infer_lemma_constr_basic constr prog lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_constr_basic" (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_constr_basic_x constr prog lhs rhs)

and infer_lemma_constr_basic_x constr prog lhs rhs : lemmas =
  try
    DB.dprint "++++++++++ INFER BASIC ++++++++++";
    let lhvs = lhs |> fhv |> List.filter (check_ict_var constr) in
    let prog, nlhs, rforms =
      let rparams = lhvs in
      let rforms, rdefns =
        let rparamss = match constr with
          | IctAll ->
            let rparams1 = List.filter (check_ict_var IctArith) rparams in
            let rparams2 = List.filter (check_ict_var IctPointer) rparams in
            DB.nhprint "RPARAMS1: " pr_vs rparams1;
            DB.nhprint "RPARAMS2: " pr_vs rparams2;
            [rparams1; rparams2] |> List.filter List.not_empty
          | _ -> [rparams] in
        List.map (fun args ->
          let rname = fresh_rel_name () in
          let rform = mk_rform rname (List.map mk_exp_var args) in
          let rdefn = mk_rel_defn_unknown rname args in
          (rform, rdefn)) rparamss |>
        List.split in
      let nprog = insert_prog_rdefns prog rdefns in
      let nlhs = mk_hstar_f_pf lhs (mk_pconj_rfs rforms) in
      (nprog, nlhs, rforms) in
    DB.dhprint "INFER BASIC: nlhs: " pr_f nlhs;
    DB.dhprint "INFER BASIC: rhs: " pr_f rhs;
    let istate = mk_infer_state PrfInferBasic constr prog lhvs [] in
    let goal = mk_goal ~mode:PrfInferBasic prog nlhs rhs in
    let ifes = infer_one_goal istate prog goal in
    let lms = ifes |> List.map (fun ife ->
      let ptstatus = match ife.ife_ptree with
        | None -> PtUnkn "InferBasic"
        | Some pt -> get_ptree_status pt in
      DB.dhprint "INFER BASIC: ptstatus: " pr_ptree_status ptstatus;
      DB.dhprint "INFER BASIC: rds: " pr_rds ife.ife_rdefns;
      match ptstatus, ife.ife_rdefns with
      | PtValid _, [] ->
        [mk_lemma "infer_basic" lhs rhs LmsValid LorgSynth]
      | PtInfer _, [] -> []
      | PtValid _, _ | PtInfer _, _ ->
        [mk_lemma_ent "infer_basic" ife.ife_entail_inferred LmsValid LorgSynth]
      | _ -> []) |> List.concat in
    DB.dhprint "INFER-BASIC: LMS: " pr_lms lms;
    lms
  with e ->
    DB.dhprint "infer_lemma_constr_basic: exception: " pr_exn e;
    []

and infer_lemma_constr_lhs constr prog lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_constr_lhs" (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_constr_lhs_x constr prog lhs rhs)

and infer_lemma_constr_lhs_x constr prog lhs rhs : lemmas =
  try
    DB.dprint "++++++++++ INFER LHS ++++++++++";
    let lhvs = lhs |> fhv |> List.filter (check_ict_var constr) in
    let rhvs = rhs |> ahv |> List.filter (check_ict_var constr) in
    let prog, nlhs, nrhs, rforms =
      let rparams = (lhvs @ rhvs) |> dedup_vs in
      let rforms, rdefns =
        let rparamss = match constr with
          | IctAll ->
            let rparams1 = List.filter (check_ict_var IctArith) rparams in
            let rparams2 = List.filter (check_ict_var IctPointer) rparams in
            DB.nhprint "RPARAMS1: " pr_vs rparams1;
            DB.nhprint "RPARAMS2: " pr_vs rparams2;
            [rparams1; rparams2] |> List.filter List.not_empty
          | _ -> [rparams] in
        List.map (fun args ->
          let rname = fresh_rel_name () in
          let rform = mk_rform rname (List.map mk_exp_var args) in
          let rdefn = mk_rel_defn_unknown rname args in
          (rform, rdefn)) rparamss |>
        List.split in
      let nprog = insert_prog_rdefns prog rdefns in
      let nrhs = NO.remove_heap_exists_vars rhs rhvs in
      let nlhs = mk_hstar_f_pf lhs (mk_pconj_rfs rforms) in
      (nprog, nlhs, nrhs, rforms) in
    DB.dhprint "INFER LHS: nlhs: " pr_f nlhs;
    DB.dhprint "INFER LHS: nrhs: " pr_f nrhs;
    let istate = mk_infer_state PrfInferLhs constr prog lhvs rhvs in
    let goal = mk_goal ~mode:PrfInferLhs prog nlhs nrhs in
    let ifes = infer_one_goal istate prog goal in
    let lms = ifes |> List.map (fun ife ->
      let ptstatus = match ife.ife_ptree with
        | None -> PtUnkn "InferLhs"
        | Some pt -> get_ptree_status pt in
      DB.dhprint "INFER LHS: ptstatus: " pr_ptree_status ptstatus;
      DB.dhprint "INFER LHS: nrdefns: " pr_rds ife.ife_rdefns;
      DB.dhprint "INFER LHS: goal: " pr_g ife.ife_goal_origin;
      DB.dhprint "INFER LHS: entail: " pr_ent ife.ife_entail_inferred;
      match ptstatus, ife.ife_rdefns with
      | PtValid _, [] ->
        let name = "infer_lhs: " ^ (create_lemma_name lhs nrhs) in
        [mk_lemma name lhs nrhs LmsValid LorgSynth]
      | PtInfer _, [] -> []
      | PtValid _, _ | PtInfer _, _ ->
        let ent = ife.ife_entail_inferred in
        let name = "infer_lhs: " ^ (create_lemma_name ent.ent_lhs ent.ent_rhs) in
        [mk_lemma_ent name ent LmsValid LorgSynth]
      | _ -> []) |> List.concat in
    DB.dhprint "INFER-LHS: LMS: " pr_lms lms;
    lms
  with e ->
    DB.dhprint "infer_lemma_constr_lhs: exception: " pr_exn e;
    []

and infer_lemma_constr_rhs constr prog lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_constr_rhs" (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_constr_rhs_x constr prog lhs rhs)

and infer_lemma_constr_rhs_x constr prog lhs rhs : lemmas =
  try
    DB.dprint "++++++++++ INFER RHS ++++++++++";
    let lhvs = lhs |> fhv |> List.filter (check_ict_var constr) in
    let rqvs, rhf, rpf = extract_components_f rhs in
    let rhvs = rhf |> fv_hf |> List.filter (check_ict_var constr) in
    let prog, nrhs, rforms =
      let rparams = (lhvs @ rhvs) |> dedup_vs in
      let rforms, rdefns =
        let rparamss = match constr with
          | IctAll ->
            let rparams1 = List.filter (check_ict_var IctArith) rparams in
            let rparams2 = List.filter (check_ict_var IctPointer) rparams in
            [rparams1; rparams2] |> List.filter List.not_empty
          | _ -> [rparams] in
        List.map (fun args ->
          let rname = fresh_rel_name () in
          let rform = mk_rform rname (List.map mk_exp_var args) in
          let rdefn = mk_rel_defn_unknown rname args in
          (rform, rdefn)) rparamss |>
        List.split in
      let _ = DB.dhprint "Rparams: " pr_vs rparams in
      let nprog = insert_prog_rdefns prog rdefns in
      let nrhs =
        let npfs = rforms |> List.map mk_prel in
        mk_qform rqvs (mk_fbase rhf (mk_pconj (rpf::npfs))) in
      (nprog, nrhs, rforms) in
    DB.dhprint "INFER RHS: lhs: " pr_f lhs;
    DB.dhprint "INFER RHS: nrhs: " pr_f nrhs;
    let istate = mk_infer_state PrfInferRhs constr prog lhvs rhvs in
    let goal = mk_goal ~mode:PrfInferRhs prog lhs nrhs in
    let ifes = infer_one_goal istate prog goal in
    let lms = ifes |> List.map (fun ife ->
      let ptstatus = match ife.ife_ptree with
        | None -> PtUnkn "InferRhs"
        | Some pt -> get_ptree_status pt in
      DB.dhprint "INFER RHS: ptstatus: " pr_ptree_status ptstatus;
      DB.dhprint "INFER RHS: nrdefns: " pr_rds ife.ife_rdefns;
      match ptstatus, ife.ife_rdefns with
      | PtValid _, [] ->
        [mk_lemma "infer_rhs" lhs rhs LmsValid LorgSynth]
      | PtInfer _, [] -> []
      | PtValid _, _ |  PtInfer _, _ ->
        let lm1 =
          let ent = ife.ife_entail_inferred in
          let name = "infer_rhs_1: " ^
                     (create_lemma_name ent.ent_lhs ent.ent_rhs) in
          mk_lemma_ent name ent LmsValid LorgSynth in
        let lms2 =
          let npf = rforms |> List.map (unfold_rform_rf ife.ife_rdefns) |>
                    mk_pconj in
          let nrhs = NO.remove_heap_exists_vars rhs (fv_pf npf) in
          let nrhs_inv = NO.encode_formula ~constr:constr prog nrhs in
          let nlhs = mk_hstar_f_pf lhs (mk_pconj [npf; nrhs_inv]) in
          DB.nhprint "NLHS: " pr_f nlhs;
          let nlhs, nrhs = NO.simplify_all_lhs_rhs prog nlhs nrhs in
          DB.nhprint "NLHS 2: " pr_f nlhs;
          DB.nhprint "NRHS: " pr_f nrhs;
          if (constr = IctArith) &&
             (check_entail_direct prog nlhs nrhs = MvlTrue) then
            let name = "infer_rhs_2: " ^ (create_lemma_name nlhs nrhs) in
            [mk_lemma name nlhs nrhs LmsValid LorgSynth]
          else [] in
        let lms = match lms2 with
          | [] -> [lm1]
          | _ -> lms2 in
        lms
      | _ -> []) |> List.concat in
    DB.dhprint "INFER-RHS: LMS: " pr_lms lms;
    lms
  with e -> DB.dhprint "infer_lemma_constr_rhs: exception: " pr_exn e; []

and infer_lemma_constr mode constr prog lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_constr" (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_constr_x mode constr prog lhs rhs)

and infer_lemma_constr_x mode constr prog lhs rhs : lemmas =
  DB.dhprint "Infer lemma constr: " pr_entp (lhs, rhs);
  try
    let lhas, rhas = Pair.fold collect_hatom lhs rhs in
    if (List.length lhas > !thd_max_size_infer_lemma_constr) &&
       (List.length rhas > !thd_max_size_infer_lemma_constr) then
      raise_lemmas [];
    let lhs =
      lhs |> NO.currify_f |> NO.remove_all_heap_exists_vars |>
      extract_hf |> mk_fheap in
    let rhs =
      let rqvs, rhf, _ = rhs |> NO.currify_f |> extract_components_f in
      mk_qform rqvs (mk_fheap rhf) in
    match mode with
    | PrfInferBasic -> infer_lemma_constr_basic constr prog lhs rhs
    | PrfInferLhs -> infer_lemma_constr_lhs constr prog lhs rhs
    | PrfInferRhs -> infer_lemma_constr_rhs constr prog lhs rhs
    | PrfInferAll ->
      (infer_lemma_constr_lhs constr prog lhs rhs)
      @ (infer_lemma_constr_rhs constr prog lhs rhs)
    | _ -> herror "infer_lemma_constr: not expect mode: " pr_prm mode
  with
  | ELemmas lms -> lms
  | e -> DB.dhprint "infer_lemma_constr_all: exception: " pr_exn e; []

and infer_lemma_constr_actions prog lm_init actions : lemmas =
  DB.trace_1 "infer_lemma_constr_actions" (pr_lm, pr_lms) lm_init
    (fun () -> infer_lemma_constr_actions_x prog lm_init actions)

and infer_lemma_constr_actions_x prog lm_init actions : lemmas =
  DB.dhprint "Infer lemma constr actions: lemma_init: " pr_lm lm_init;
  DB.dhprint "=====>>> NEW ACTION SEQUENCE: "
    (pr_list (pr_pair pr_prm pr_ict)) actions;
  actions |> List.fold_left (fun lms (mode, constr) ->
    DB.dhprint "CURRENT LMS: " pr_lms lms;
    DB.dhprint ">>> ACTION ITEM: " (pr_pair pr_prm pr_ict) (mode, constr);
    match lms with
    | [] -> []
    | [lm] ->
      let lhs, rhs = lm.lm_lhs, lm.lm_rhs in
      let lvs, rvs = av lhs, av rhs in
      if List.exists (check_ict_var constr) lvs &&
         List.exists (check_ict_var constr) rvs then
        match mode with
        | PrfInferLhs -> infer_lemma_constr_lhs constr prog lhs rhs
        | PrfInferRhs -> infer_lemma_constr_rhs constr prog lhs rhs
        | _ -> herror "infer_lemma_constr: not expect mode: " pr_prm mode
      else [lm]
    | _ -> error "infer_lemma_constr: expect 1 lemma at a time"
  ) [lm_init]

and prepare_create_lemma_template () =
  index_var_infer := 0

and create_lemma_template_convert ?(history=[]) pstate lhs rhs =
  DB.trace_2 "create_lemma_template_convert"
    (pr_f, pr_f, pr_lmts) lhs rhs
    (fun () -> create_lemma_template_convert_x ~history:history pstate lhs rhs)

and create_lemma_template_convert_x ?(history=[]) pstate lhs rhs =
  try
    let gl_lhs, gl_rhs = lhs, rhs in
    let prog = pstate.prs_prog in
    let lvdefns =
      gl_lhs |> collect_view_form |>
      List.filter (fun vf -> vf.viewf_origin != HorgHypo) |>
      List.map (fun vf -> vf.viewf_name) |> dedup_ss |>
      List.map (find_view_defn prog.prog_views) |>
      List.filter (fun vd -> match vd.view_recurt with
        | VrtMutual _ | VrtSelf -> true
        | VrtIndirect vs | VrtMix vs -> List.length vs <= 3
        | _ -> false) |>
      List.filter (fun vd -> match vd.view_recurt with
        | VrtIndirect _ -> List.for_all (fun vdc ->
          vdc.vdc_form |> collect_view_form |>
          List.map (fun vf -> vf.viewf_name) |> dedup_ss |>
          List.length < 2) vd.view_defn_cases
        | _ -> true) in
    let rvdefns =
      gl_rhs |> collect_view_form |>
      List.map (fun vf -> vf.viewf_name) |> dedup_ss |>
      List.map (find_view_defn prog.prog_views) |>
      List.filter is_recur_direct_vd in
    DB.nhprint "LVDS: " pr_vdfs lvdefns;
    DB.nhprint "RVDS: " pr_vdfs rvdefns;
    let need_infer lvd rvd =
      if (eq_s lvd.view_name rvd.view_name) then false
      else if (lvd.view_min_size < rvd.view_min_size) &&
              List.for_all is_int_var lvd.view_params then false
      else (check_same_data_vdefn lvd rvd) in
    let vpairs = List.fold_left (fun acc1 lvd ->
      List.fold_left (fun acc2 rvd ->
        if (eq_s lvd.view_name rvd.view_name) ||
           not (need_infer lvd rvd) then acc2
        else acc2 @ [(lvd, rvd)]) acc1 rvdefns) [] lvdefns in
    vpairs |> List.dedup (fun (lvd1, rvd1) (lvd2, rvd2) ->
      (eq_s lvd1.view_name lvd2.view_name) &&
      (eq_s rvd1.view_name rvd2.view_name)) |>
    List.map (fun (lvd, rvd) ->
      (* prepare_create_lemma_template (); *)
      let lvf = fresh_vform_infer lvd in
      let rvf = fresh_vform_infer rvd in
      let lhs = lvf |> mk_hform_vf |> mk_fheap in
      let rhs = rvf |> mk_hform_vf |> mk_fheap |> mk_fexists (fv_vf rvf) in
      match check_attempt_inferring_lemma pstate lhs rhs with
      | true -> []
      | false -> [mk_lemma_template lhs rhs LmtConvert]) |>
    List.concat
  with ELemmaTemplates res -> res

and create_lemma_template_combine ?(all=false) pstate lhs rhs =
  DB.trace_2 "create_lemma_template_combine"
    (pr_f, pr_f, pr_lmts) lhs rhs
    (fun () -> create_lemma_template_combine_x ~all:all pstate lhs rhs)

and create_lemma_template_combine_x ?(all=false) pstate lhs rhs =
  try
    let lhatoms, rhatoms = Pair.fold collect_hatom lhs rhs in
    if (List.length lhatoms <= 1) then raise_lemma_templates [];
    let check_same_name ha1 ha2 =
      eq_s (get_hatom_name ha1) (get_hatom_name ha2) in
    let lhatoms =
      let all_lhatoms = collect_hatom lhs in
      let unique_lhatoms = List.dedup check_same_name all_lhatoms in
      List.fold_left (fun acc ha -> match ha with
        | HData _ -> acc
        | HView _ ->
          if List.count (check_same_name ha) all_lhatoms > 1 then acc @ [ha]
          else acc) unique_lhatoms unique_lhatoms in
    let rhatoms = rhs |> collect_view_form |> List.map mk_hatom_vf |>
                  List.dedup check_same_name in
    let lhass =
      lhatoms |> Comb.gen_combinations 2 |>
      List.filter (fun has -> match has with
        | [ha1; ha2] ->
          if (is_hatom_df ha1) && (is_hatom_df ha2) then false
          else if all then true
          else if (get_hatom_origin ha1) = HorgUnfold then false
          else if (get_hatom_origin ha2) = HorgUnfold then false
          else if not (intersected_vs (fv_ha ha1) (fv_ha ha2)) then false
          else true
        | _ -> false) in
    lhass |> List.map (fun lhas ->
      rhatoms |> List.filter (fun rha ->
        let rvs = fv_ha rha in
        all || not (intersected_vs rvs (fv rhs)) ||
        intersected_vs (fv_ha rha) (fv_has lhas)) |>
      List.map (fun rha ->
        match check_attempt_inferring_lemma_hatoms pstate lhas [rha] with
        | true -> []
        | false -> [lhas, [rha]])) |> List.concat |> List.concat |>
    List.dedup check_equiv_lemma_template_hatoms |>
    List.map (fun (lhas, rhas) ->
      prepare_create_lemma_template ();
      let nlhs = fresh_forms_infer lhas in
      let nrhs = rhas |> fresh_forms_infer |> mk_fexists_all in
      mk_lemma_template nlhs nrhs LmtCombine)
  with ELemmaTemplates lms -> lms

and create_lemma_template_split ?(all=false) pstate lhs rhs =
  DB.trace_2 "infer_lemma_split"
    (pr_f, pr_f, pr_lmts) lhs rhs
    (fun () -> create_lemma_template_split_x ~all:all pstate lhs rhs)

and create_lemma_template_split_x ?(all=false) pstate lhs rhs =
  try
    prepare_create_lemma_template ();
    let check_same_name ha1 ha2 =
      eq_s (get_hatom_name ha1) (get_hatom_name ha2) in
    let lhas = lhs |> collect_view_form |> List.map mk_hatom_vf |>
               List.dedup check_same_name in
    let rhass =
      rhs |> collect_hatom |> Comb.gen_combinations 2 |>
      List.filter (fun has -> match has with
        | [ha1; ha2] ->
          if (is_hatom_df ha1) && (is_hatom_df ha2) then false
          else if all then true
          else if (get_hatom_origin ha1) = HorgUnfold then false
          else if (get_hatom_origin ha2) = HorgUnfold then false
          (* else if not (intersected_vs (fv_ha ha1) (fv_ha ha2)) then false *)
          else true
        | _ -> false) in
    rhass |> List.map (fun rhas ->
      let rvs = rhas |> List.map fv_ha |> List.concat |> dedup_vs in
      lhas |> List.filter (fun ha ->
        all || not (intersected_vs rvs (fv rhs)) ||
        intersected_vs (fv_has rhas) (fv_ha ha)) |>
      List.map (fun lha ->
        match check_attempt_inferring_lemma_hatoms pstate [lha] rhas with
        | true -> []
        | false -> [[lha], rhas])) |> List.concat |> List.concat |>
    List.dedup check_equiv_lemma_template_hatoms |>
    List.map (fun (lhas, rhas) ->
      prepare_create_lemma_template ();
      let nlhs = fresh_forms_infer lhas in
      let nrhs = rhas |> fresh_forms_infer |> mk_fexists_all in
      mk_lemma_template nlhs nrhs LmtSplit)
  with ELemmaTemplates lms -> lms

and infer_one_lemma_convert pstate lhs rhs : lemmas =
  DB.trace_2 "infer_one_lemma_convert"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_one_lemma_convert_x pstate lhs rhs)

and infer_one_lemma_convert_x pstate lhs rhs =
  let prog = pstate.prs_prog in
  let vds = prog.prog_views in
  let lvfs, rvfs = collect_view_form lhs, collect_view_form rhs in
  match lvfs, rvfs with
  | [lvf], [rvf] ->
    DB.hprint "LEMMA CONVERT TEMPLATE: " pr_entp (lhs, rhs);
    let lm_init = mk_lemma "lemma_init" lhs rhs LmsUnknown LorgSynth in
    let actionss =
      if not (List.exists has_int_operator_vd vds) then
        [[(PrfInferLhs, IctAll)]; [(PrfInferRhs, IctAll)]]
      else if List.length lvf.viewf_args >= List.length rvf.viewf_args then
        [[(PrfInferLhs, IctPointer); (PrfInferLhs, IctArith)];
         [(PrfInferLhs, IctPointer); (PrfInferRhs, IctArith)];
         [(PrfInferRhs, IctPointer); (PrfInferRhs, IctArith)];
         [(PrfInferRhs, IctPointer); (PrfInferLhs, IctArith)];]
      else
        [[(PrfInferRhs, IctPointer); (PrfInferLhs, IctArith)];
         [(PrfInferRhs, IctPointer); (PrfInferRhs, IctArith)]] in
    let lms = List.fold_left (fun acc actions ->
      if acc != [] then acc
      else infer_lemma_constr_actions prog lm_init actions) [] actionss in
    (* remove unnecessary pure in lhs *)
    let lms1 = List.map (fun lm ->
      let nlhs = lm.lm_lhs |> extract_components_f |> snd3 |> mk_fheap in
      if check_entail_direct prog nlhs lm.lm_rhs != MvlTrue then lm
      else {lm with lm_lhs = nlhs}) lms in
    (* reverse lemma convert *)
    let lms2 = lms1 |> List.map (fun lm ->
      let nlhs = lm.lm_rhs |> NO.remove_all_qvars in
      let nrhs =
        let qvs = diff_vs (fv lm.lm_lhs) (fv nlhs) |> mk_qexists in
        lm.lm_lhs |> mk_qform [qvs] in
      DB.hprint "NLHS: " pr_f nlhs;
      DB.hprint "NRHS: " pr_f nrhs;
      if check_entail_direct prog nlhs nrhs = MvlTrue then
        let _ = update_attempt_inferring_lemma pstate nlhs nrhs in
        let name = "infer_convert (reverse): " ^ (create_lemma_name nlhs nrhs) in
        [mk_lemma name nlhs nrhs LmsValid LorgSynth]
      else []) |> List.concat in
    (* rename *)
    let lms = (lms1 @ lms2) |> List.map (fun lm ->
      let lmname = fresh_lemma_name ("lm_convert: " ^ lm.lm_name) in
      {lm with lm_name = lmname}) in
    lms
  | _ -> []

and infer_one_lemma_combine pstate lhs rhs : lemmas =
  DB.trace_2 "infer_one_lemma_combine"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_one_lemma_combine_x pstate lhs rhs)

and infer_one_lemma_combine_x pstate lhs rhs =
  DB.hprint "+++ LEMMA COMBINE TEMPLATE: " pr_entp (lhs, rhs);
  let prog = pstate.prs_prog in
  let lvds = collect_view_defn prog.prog_views lhs in
  let rvds = collect_view_defn prog.prog_views rhs in
  let need_infer = List.exists_pair (fun vd1 vd2 ->
    (eq_s vd1.view_name vd2.view_name) ||
    (check_recur_vdefn vd1 vd2) ||
    (check_same_data_vdefn vd1 vd2)) lvds rvds in
  let lms = match need_infer with
    | true ->
    let actionss = match (List.exists has_int_operator_vd lvds) with
        | false -> [[(PrfInferLhs, IctAll)]]
        | true ->
          [[(PrfInferLhs, IctPointer); (PrfInferLhs, IctArith)];
           [(PrfInferLhs, IctPointer); (PrfInferRhs, IctArith)]] in
      let lm_init = mk_lemma "lemma_init" lhs rhs LmsUnknown LorgSynth in
     List.fold_left (fun acc actions ->
      if acc != [] then acc
      else infer_lemma_constr_actions prog lm_init actions) [] actionss
      (* infer_lemma_constr_actions prog lm_init actions *)
    | false -> [] in
  (* remove unnecessary pure in lhs *)
  let lms = List.map (fun lm ->
    let lqvs, lhf, lpf = lm.lm_lhs |> extract_components_f in
    let lhatoms = lm.lm_lhs |> collect_hatom in
    let nlpf =
      lpf |> collect_pure_conjuncts_pf |> List.filter (fun pf ->
        let pvs = fv_pf pf in
        List.for_all (fun ha -> not (subset_vs pvs (fv_ha ha))) lhatoms) |>
      mk_pconj in
    let nlhs1 = mk_fheap lhf in
    let nlhs2 = nlpf |> mk_fbase lhf |> mk_qform lqvs in
    if check_entail_direct prog nlhs1 lm.lm_rhs = MvlTrue then
      {lm with lm_lhs = nlhs1}
    else if check_entail_direct prog nlhs2 lm.lm_rhs = MvlTrue then
      {lm with lm_lhs = nlhs2}
    else lm) lms in
  (* rename *)
  let lms = List.map (fun lm ->
    let name = fresh_lemma_name ("lm_combine: " ^ lm.lm_name) in
    {lm with lm_name = name }) lms in
  lms

and infer_one_lemma_split pstate lhs rhs : lemmas =
  DB.trace_2 "infer_one_lemma_split"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_one_lemma_split_x pstate lhs rhs)

and infer_one_lemma_split_x pstate lhs rhs =
  DB.hprint "+++ LEMMA SPLIT TEMPLATE: " pr_entp (lhs, rhs);
  let prog = pstate.prs_prog in
  let lvds = collect_view_defn prog.prog_views lhs in
  let rvds = collect_view_defn prog.prog_views rhs in
  let rdatas = collect_data_form rhs in
  let need_infer = List.exists_pair (fun vd1 vd2 ->
    (eq_s vd1.view_name vd2.view_name) ||
    (check_recur_vdefn vd1 vd2) ||
    (check_same_data_vdefn vd1 vd2) ||
    (List.length vd1.view_params = List.length vd2.view_params)
  ) lvds rvds in
  let actions = match rdatas with
    | [] -> [[(PrfInferRhs, IctPointer); (PrfInferRhs, IctArith)]]
    | _ -> [[(PrfInferRhs, IctPointer); (PrfInferLhs, IctArith)]] in
  let lms = match need_infer with
    | false -> []
    | true ->
      let lms_init =
        match choose_ict_f lhs with
        | IctAll | IctArith ->
          let lms = infer_lemma_constr PrfInferBasic IctArith prog lhs rhs in
          if lms != [] then lms
          else
          (* else if check_entail_direct prog lhs rhs = MvlTrue then *)
            [mk_lemma "lemma_init" lhs rhs LmsUnknown LorgSynth]
          (* else [] *)
        | _ -> [mk_lemma "lemma_init" lhs rhs LmsUnknown LorgSynth] in
      match lms_init with
      | [] -> []
      | [lm] -> actions |> List.map (infer_lemma_constr_actions prog lm) |>
                List.concat
      | _ -> error "infer_lemma_split: expect only 1 lemma" in
  (* rename *)
  List.map (fun lm ->
    let name = fresh_lemma_name ("lm_split: " ^ lm.lm_name) in
    {lm with lm_name = name}) lms

and infer_one_lemma_template pstate goal lmt : lemmas =
  DB.trace_2 "infer_one_lemma_template"
    (pr_gent, pr_lmt, pr_lms) goal lmt
    (fun () -> infer_one_lemma_template_x pstate goal lmt)

and infer_one_lemma_template_x pstate goal lmt : lemmas =
  let styp = String.uppercase_ascii (pr_lemma_typ lmt.lmt_typ) in
  let var_indices = save_and_reset_index_vars pstate.prs_prog in
  try
    let infer_one_lemma lmt =
      let lhs, rhs, lmt_typ = lmt.lmt_lhs, lmt.lmt_rhs, lmt.lmt_typ in
      if (check_attempt_inferring_lemma pstate lhs rhs) then
        raise_lemmas [];
      update_attempt_inferring_lemma pstate lhs rhs;
      DB.pprint ("========== INFER ONE LEMMA [" ^ styp ^ "] ==========");
      DB.hprint "+++ CURRENT GOAL: " pr_g goal;
      let timeout = match lmt_typ with
        | LmtCombine | LmtSplit -> !timeout_infer_lemma
        | _ -> 60 in
      let lms = Func.timeout_default timeout (fun () ->
        Z3bin.restart_prover ();
        let time_begin = get_time () in
        let res = match lmt_typ with
          | LmtCombine -> infer_one_lemma_combine pstate lhs rhs
          | LmtSplit -> infer_one_lemma_split pstate lhs rhs
          | LmtConvert -> infer_one_lemma_convert pstate lhs rhs in
        let time = (get_time ()) -. time_begin in
        let _ = match lmt_typ with
          | LmtCombine -> time_lm_cb := !time_lm_cb +. time
          | LmtSplit -> time_lm_sp := !time_lm_sp +. time
          | LmtConvert -> time_lm_cv := !time_lm_cv +. time in
        res) [] in
      raise_lemmas lms in
    infer_one_lemma lmt
  with ELemmas lms ->
    let _ = restore_index_vars var_indices in
    DB.hprint (">>>>> RESULT LEMMA [" ^ styp ^ "]: \n") pr_lms lms;
    lms

and infer_lemma_convert pstate lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_convert"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_convert_x pstate lhs rhs)

and infer_lemma_convert_x pstate lhs rhs : lemmas =
  let lmts = create_lemma_template_convert pstate lhs rhs in
  let goal = mk_goal pstate.prs_prog lhs rhs in
  lmts |> List.map (infer_one_lemma_template pstate goal) |>
  List.concat

and infer_lemma_split pstate lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_split"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_split_x pstate lhs rhs)

and infer_lemma_split_x pstate lhs rhs : lemmas =
  let lmts = create_lemma_template_split ~all:true pstate lhs rhs in
  let goal = mk_goal pstate.prs_prog lhs rhs in
  lmts |> List.map (infer_one_lemma_template pstate goal) |>
  List.concat

and infer_lemma_combine pstate lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_combine"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_combine_x pstate lhs rhs)

and infer_lemma_combine_x pstate lhs rhs : lemmas =
  let lmts = create_lemma_template_combine ~all:true pstate lhs rhs in
  let goal = mk_goal pstate.prs_prog lhs rhs in
  lmts |> List.map (infer_one_lemma_template pstate goal) |>
  List.concat

and infer_lemma_self_split pstate lhs rhs : lemmas =
  DB.trace_2 "infer_lemma_self_split"
    (pr_f, pr_f, pr_lms) lhs rhs
    (fun () -> infer_lemma_self_split_x pstate lhs rhs)

and infer_lemma_self_split_x pstate lhs rhs : lemmas =
  try
    let prog = pstate.prs_prog in
    let lvdefns = collect_view_defn_direct_recur prog.prog_views lhs in
    let lhss = lvdefns |> List.map (fun vd ->
      vd |> fresh_vform_infer |> mk_hform_vf |> mk_fheap) in
    let rhss = List.concat @@ List.map (fun vd ->
      let ddefns =
        vd.view_defn_cases |> List.map (fun vdc ->
          vdc.vdc_form |> collect_data_form) |> List.concat |>
        List.map (fun df -> df.dataf_name) |> dedup_ss |>
        List.map (find_data_defn prog.prog_datas) in
      ddefns |> List.map (fun dd ->
        let ha1 = HView (fresh_vform_infer vd) in
        let ha2 = HData (fresh_dform_infer dd) in
        [ha1; ha2] |> mk_hstar_hatoms |> mk_fheap |> mk_fexists_all)) @@
      lvdefns in
    let lms = List.fold_left (fun acc1 lhs ->
      acc1 @ (rhss |> List.fold_left (fun acc2 rhs ->
        match check_attempt_inferring_lemma pstate lhs rhs with
        | true -> acc2
        | false ->
          DB.pprint "========== INFER LEMMA SELF-SPLIT ==========";
          DB.hprint "+++ CURRENT GOAL: " pr_entp (lhs, rhs);
          let lms = infer_one_lemma_split pstate lhs rhs in
          DB.hprint "+++ INFERRED LEMMA SELF-SPLIT: " pr_lms lms;
          acc2 @ lms) [])) [] lhss in
    List.map (fun lm ->
      {lm with lm_name = fresh_lemma_name ("lm_split: " ^ lm.lm_name)}) lms
  with ELemmas lms -> lms

and synthesize_lemmas lmts prog lhs rhs =
  let goal = mk_goal prog lhs rhs in
  let pstate = mk_prover_state prog goal in
  List.fold_left (fun acc lmt ->
    let lms =
      try match lmt with
        | LmtSplit -> infer_lemma_split pstate lhs rhs
        | LmtCombine -> infer_lemma_combine pstate lhs rhs
        | LmtConvert -> infer_lemma_convert pstate lhs rhs
      with ELemmas res -> res in
    let ths = List.map (mk_theorem_from_lemma prog) lms in
    pstate.prs_theorems <- pstate.prs_theorems @ ths;
    acc @ lms) [] lmts

and infer_unknown_relations typ prog pents : infer_rdefns =
  DB.trace_2 "infer_unknown_relations"
    (pr_ifr, pr_pents, pr_irds) typ pents
    (fun () -> infer_unknown_relations_x typ prog pents)

and infer_unknown_relations_x typ prog pents : infer_rdefns =
  (* DB.hprint "program.rel_defn: " (pr_list pr_rel_defn) prog.prog_rels;
   * DB.hprint "program.command list: " (pr_list pr_cmd) prog.prog_rels; *)
  PT.reset_cache ();
  let unk_rnames =
    pents |> List.map collect_rform_pent |> List.concat |>
    List.map (fun r -> r.prel_name) |> dedup_ss in
  let unk_rdefns = prog.prog_rels |> List.filter (fun rd ->
    (is_unk_rdefn rd) && (mem_ss rd.rel_name unk_rnames)) in
  let ird_farkas =
    let strong = match typ with
      | IfrStrong -> true
      | IfrWeak -> false in
    let nrdefns = List.map (fun rd ->
      TL.mk_rdefn_dummy rd.rel_name rd.rel_params) unk_rdefns in
    DB.nhprint "nrdefns: " (pr_list pr_rel_defn) nrdefns;
    DB.nhprint "program: " (pr_program) prog;
    let nprog = replace_prog_rdefns prog nrdefns in
    (* let () = DB.hprint "prog_rels prover: " FK.pr_rels nprog.prog_rels in *)
    DB.nhprint "program: " (pr_program) nprog;
    let rds =
      try
        if List.length unk_rnames > 1 then []
        else if !use_farkas_incr then
          FK.solve_pentails_precise nprog strong pents
        else FF.solve_pentails_precise nprog strong pents
      with _ -> [] in
    let rds =
      if List.for_all (fun rd -> not (is_unk_rdefn rd)) rds then rds
      else [] in
    DB.nhprint "RESULT OF SOLVE ENTAIL BY FARKAS: " pr_rds rds;
    mk_infer_rdefn IsvFarkas rds in
  (* infer unknown constraints using iprover *)
  let irds_iprover = match pents with
    | [pent] ->
      let rdss = IP.solve_one_pure_entail prog pent in
      DB.nhprint "RESULT OF SOLVE 1 ENTAIL BY IPROVER: " pr_rdss rdss;
      List.map (mk_infer_rdefn IsvIprover) rdss
    | _ -> [] in
  let irds = ird_farkas::irds_iprover |>
             List.map (fun ird ->
               let rds = ird.ird_rdefns |> List.filter (fun rd ->
                 match rd.rel_body with
                 | RbForm pf -> not (is_false_pf pf)
                 | _ -> false) in
               if rds = [] then []
               else [mk_infer_rdefn ird.ird_solver rds]) |> List.concat in
  irds

and infer_unknown_functions typ prog pents (* : infer_rdefns *) =
  PT.reset_cache ();
  let unk_fdefns =
    pents |> List.map collect_fform_pent |> List.concat in
  let unk_fnames = List.map (fun (a, _, _) -> a) unk_fdefns in
  let unk_fdefns = prog.prog_funcs |> List.filter (fun fd ->
    (is_unk_fdefn fd) && (mem_ss fd.func_name unk_fnames)) in
  let strong = match typ with
    | IfrStrong -> true
    | IfrWeak -> false in
  DB.nhprint "program: " (pr_program) prog;
  let nfdefns = List.map (fun fd ->
    TL.mk_fdefn_dummy fd.func_name fd.func_params) unk_fdefns in
  let nprog = replace_prog_fdefns prog nfdefns in
  let fds = FK.solve_fentails_incr nprog strong pents in
  let fds =
    if List.for_all (fun rd -> not (is_unk_fdefn rd)) fds then fds
    else [] in
  DB.nhprint "RESULT OF SOLVE ENTAIL BY FARKAS: " pr_fds fds;
  [mk_infer_fdefn IsvFarkas fds]

and decompose_rdefn goal rdefn : rel_defn list =
  DB.trace_1 "decompose_rdefn" (pr_rd, pr_rds) rdefn
    (fun () -> decompose_rdefn_x goal rdefn)

and decompose_rdefn_x goal rdefn : rel_defn list =
  DB.dhprint "DECOMPOSE RDEFN: " pr_rd rdefn;
  match rdefn.rel_body with
  | RbForm f ->
    let pfs = f |> collect_pure_conjuncts_pf in
    let npfs_nontrivial = pfs |> List.filter (fun pf -> match pf with
      | PExists _ | PForall _ | PNeg _ -> false
      | _ -> not (PT.unsat_or_has_unique_model_all_vars pf)) in
    DB.dhprint "DECOMPOSED: npfs_nontrivial: " pr_pfs npfs_nontrivial;
    let npfs =
      npfs_nontrivial |> List.filter (fun pf ->
        let vs = fv_pf pf in
        List.for_all (fun v -> List.for_all (fun gf ->
          (eq_patom pf gf) || not (mem_vs v (fv_pf gf))) pfs) vs) |>
      List.dedup eq_patom in
    DB.dhprint "DECOMPOSED: npfs1: " pr_pfs npfs;
    (* TRUNG: BELOW MAY NOT BE EFFICIENT *)
    let need_decompose_pfs_nontrivial () =
      if (List.length (collect_rform_goal goal) > 1) then true
      else ((goal.gl_depth_infer <= 5) && (List.length npfs_nontrivial <= 5)) in
    let npfs =
      if npfs != [] then npfs
      else if need_decompose_pfs_nontrivial () then
        let nnpfs, eq_pairs = npfs_nontrivial |> List.fold_left (fun acc pf ->
          let acc_pf, acc_pair = acc in
          match pf with
          | BinRel (Eq, Var (v1, _), Var (v2, _), _) ->
            (acc_pf, acc_pair @ [v1, v2])
          | _ -> acc_pf @ [pf], acc_pair) ([], []) in
        let eq_groups = eq_pairs |> List.fold_left (fun acc (u, v) ->
          let grps, ngrps = acc |> List.partition (fun xs ->
            (mem_vs u xs) || (mem_vs v xs)) in
          match grps with
          | [] -> [u;v]::ngrps
          | grp::_ -> (dedup_vs (u::v::grp))::ngrps) [] in
        let eq_npfs = eq_groups |> List.map (fun grp ->
          grp |> Comb.gen_combinations 2 |>
          List.map (fun vs -> match vs with
            | u::v::_ ->[ mk_eq_var u v]
            | _ -> []) |> List.concat) |> List.concat in
        let npfs = nnpfs @ eq_npfs in
        npfs
      else [(mk_pconj npfs_nontrivial)] in
    let npfs = npfs |> List.dedup eq_patom in
    DB.dhprint "DECOMPOSED: npfs: " pr_pfs npfs;
    let nbodies =
      if (List.length npfs = List.length pfs) then
        if (List.length npfs <= 1) then []
        else npfs
      else if (List.length npfs <= 1) then npfs
      else (mk_pconj npfs)::npfs in
    let rds = List.map (fun pf -> {rdefn with rel_body = RbForm pf}) nbodies in
    DB.dhprint "RDEFNS DECOMPOSED: " pr_rds rds;
    rds
  | _ -> []

and solve_relation_constraints istate prog goal ipents : infer_rdefns =
  DB.trace_3 "solve_relation_constraints"
    (pr_ist, pr_g, pr_pents, pr_irds) istate goal ipents
    (fun () -> solve_relation_constraints_x istate prog goal ipents)

and solve_relation_constraints_x istate prog goal ipents : infer_rdefns =
  DB.dhprint "SOLVE-PURE-ENTAILMENTS: " pr_pents ipents;
  let mode, constr = istate.ist_mode, istate.ist_constr in
  let ifr_typ = get_infer_rels_type mode in
  let rforms = [goal.gl_lhs; goal.gl_rhs] |> collect_rform_fs in
  let irds =
    ipents |> infer_unknown_relations ifr_typ prog |>
    dedup_infer_rdefns |> List.map (fun ird ->
      let rds =
        let nrds = ird.ird_rdefns |>
                   List.filter (fun rd -> match rd.rel_body with
                     | RbForm f -> not (is_true_pf f)
                     | _ -> false) in
        if (nrds = []) then nrds
        else ird.ird_rdefns in
      if (rds = []) then []
      else [mk_infer_rdefn ird.ird_solver rds]) |> List.concat in
  DB.dhprint "INFERRED RELATION: " pr_irds irds;
  let irds =
    irds |> List.map (fun ird ->
      let irds_decomposed =
        let rdss = ird.ird_rdefns |> List.map (decompose_rdefn goal) in
        let nrdss = match rdss with
          | [] -> []
          | [rds] -> rds |> List.map (fun rd -> [rd])
          | _ ->
            let rdss1 = rdss |> Comb.gen_cartesian in
            let rdss2 = rdss |> List.concat |> List.map (fun rd -> [rd]) in
            rdss1 @ rdss2 in
        nrdss |> List.map (mk_infer_rdefn (IsvDecompose ird.ird_solver)) in
      DB.nhprint "NEW IRDS ALL: " pr_irds irds;
      DB.nhprint "NEW IRDS DECOMPOSED: " pr_irds irds_decomposed;
      if irds_decomposed = [] then
        [ird]
      else if not (is_feasible_relations mode ird.ird_rdefns) then
        irds_decomposed
      else if ird.ird_solver = IsvFarkas then
        (* ird :: irds_decomposed *)
        match constr with
        | IctArith -> irds_decomposed @ [ird]
        | _ -> ird :: irds_decomposed
      else if (ird.ird_solver = IsvIprover) &&
              (goal.gl_depth_infer <= 0) &&
              (List.length ird.ird_rdefns <= 1) then
        irds_decomposed
      else ird :: irds_decomposed) |> List.concat in
  DB.nhprint "DECOMPOSED RELATIONS: " pr_irds irds;
  let diffconstrs =
    let livs = goal.gl_lhs |> collect_hatom |> List.map fv_ha |>
               List.filter (intersected_vs istate.ist_lhs_vars) in
    let rivs = goal.gl_rhs |> collect_hatom |> List.map fv_ha |>
               List.filter (intersected_vs istate.ist_rhs_vars) in
    let lpairs = livs |> List.map (Comb.gen_combinations 2) |> List.concat in
    let rpairs = rivs |> List.map (Comb.gen_combinations 2) |> List.concat in
    (lpairs @ rpairs) |>
    List.map (fun vs -> match vs with
      | v1::v2::[] -> [(mk_neq_var v1 v2)]
      | _ -> []) |> List.concat in
  let irds = irds |> List.filter (fun ird ->
    let prog = replace_prog_rdefns prog ird.ird_rdefns in
    let rds_body = rforms |> List.map mk_prel |> mk_pconj |>
                   NO.simplify_all_pf ~prog:(Some prog) in
    let rds_body_distinct = (rds_body::diffconstrs) |> mk_pconj in
    if (PT.check_sat rds_body_distinct != MvlTrue) then false
    else match mode with
      | PrfInferLhs | PrfInferRhs -> not (is_true_pf rds_body)
      | _ -> true) in
  DB.nhprint "FILTERED INFERRED RELATION: " pr_irds irds;
  let irds = match irds, mode with
    | [], _ -> irds
    | _, PrfInferBasic | _, PrfInferAll ->
      irds |> List.map (fun ird ->
        let prog = replace_prog_rdefns prog ird.ird_rdefns in
        let plhs = NO.encode_formula ~constr:constr prog goal.gl_lhs in
        if (PT.check_sat plhs = MvlFalse) then []
        else [ird]) |> List.concat
    | _, PrfInferLhs ->
      irds |> List.map (fun ird ->
        let prog = replace_prog_rdefns prog ird.ird_rdefns in
        let plhs = NO.encode_formula ~constr:constr prog goal.gl_lhs in
        if (PT.check_sat plhs = MvlFalse) then []
        else [ird]) |> List.concat
    | _ -> irds in
  irds

and need_infer_more_entail istate goal : bool =
  List.length istate.ist_inferred_ents < !thd_max_num_inferred_ents

and need_infer_one_goal_incr istate goal =
  try
    if not (need_infer_more_entail istate goal) then
      raise_bool false;
    if goal.gl_proof_mode = PrfInferRhs && (goal.gl_depth_infer > 6) then
      raise_bool false;
    if goal.gl_proof_mode = PrfInferLhs && (goal.gl_depth_infer > 5) then
      raise_bool false;
    if (goal.gl_depth_infer > 3) then
      raise_bool false;
    true
  with EBool res -> res

and is_feasible_relations mode rdefns : bool =
  DB.trace_1 "is_feasible_relations"
    (pr_rds, pr_bool) rdefns
    (fun () -> is_feasible_relations_x mode rdefns)

and is_feasible_relations_x mode rdefns : bool =
  DB.dhprint "check feasible relation: " pr_rdsl rdefns;
  let res = try (
    if (mode = PrfInferRhs) && not (List.for_all is_equality_rdefn rdefns) then
      raise_bool false;
    if List.exists (fun rd -> match rd.rel_body with
      | RbForm pf -> PT.unsat_or_has_unique_model_one_var ~constr:IctArith pf
      | _ -> false) rdefns then
      raise_bool false;
    true
  ) with EBool res -> res in
  DB.dhprint "check feasible relation: result: " pr_bool res;
  res

and check_potential_infer_lemma prog lhs rhs : bool  =
  DB.trace_2 "check_potential_infer_lemma"
    (pr_f, pr_f, pr_b)  lhs rhs
    (fun () -> check_potential_infer_lemma_x prog lhs rhs)

and check_potential_infer_lemma_x prog lhs rhs : bool  =
  let lhss = lhs |> unfold_all_vform prog.prog_views 2 |>
             (* List.filter has_view_f |> *)
             List.exclude has_view_f |>
             List.map NO.remove_all_heap_exists_vars |>
             List.map (NO.simplify_all) in
  let rhss = rhs |> mk_fexists (diff_vs (fv rhs) (fv lhs)) |>
             unfold_all_vform prog.prog_views 2 |>
             (* List.filter has_view_f |> *)
             List.exclude has_view_f |>
             List.map (NO.simplify_all) in
  DB.dhprint "CHECK POTENTIAL: LHSS: " pr_fs lhss;
  DB.dhprint "CHECK POTENTIAL: RHSS: " pr_fs rhss;
  (* let ldfs = lhss |> List.map collect_data_form |> List.concat in *)
  let has_unmatch_data_rhs = rhss |> List.for_all (fun rhs ->
    lhss |> List.for_all (fun lhs ->
      let lhs, rhs = NO.simplify_all_lhs_rhs prog lhs rhs in
      let ldfs, rdfs = Pair.fold collect_data_form lhs rhs in
      (List.length ldfs > List.length rdfs) ||
      rdfs |> List.exists (fun rdf ->
        let unmatch_rhs = ldfs |> List.for_all (fun ldf ->
          let rfvs = fv rhs in
          (* DB.hprint "RFVS: " pr_vs rfvs; *)
          let largs = ldf.dataf_root :: ldf.dataf_args in
          let rargs = rdf.dataf_root :: rdf.dataf_args in
          (* DB.hprint "LDF, RDF: " (pr_pair pr_df pr_df) (ldf, rdf); *)
          match (eq_s ldf.dataf_name rdf.dataf_name) with
          | false -> true
          | true -> List.exists2 (fun e1 e2 ->
            not (is_const_exp e1) && not (is_const_exp e2) &&
            (not (eq_exp e1 e2)) && (subset_vs (fv_exp e2) rfvs)
          ) largs rargs) in
        let _ = if unmatch_rhs then
            DB.dhprint "UNMATCH DATA RHS: " pr_df rdf in
        unmatch_rhs))) in
  DB.nhprint "HAS_UNMATCH DATA RHS: " pr_bool has_unmatch_data_rhs;
  if has_unmatch_data_rhs then false
  else true


and verify_valid_lemma pstate goal =
  let _ = enable_mode_check_entail_normal () in
  let prog = pstate.prs_prog in
  (* reset timeout in pstate *)
  let pstate = mk_prover_state ~interact:false prog goal in
  (* timeout_check_enabled := false; *)
  (* let pstate = {pstate with prs_interact = true} in *)
  let ptree = prove_one_goal pstate goal in
  let _ = enable_mode_lemma_synthesis () in
  ptree

and verify_relations istate prog goal rdefns : verify_ifent  =
  DB.trace_3 "verify_relations"
    (pr_ist, pr_g, pr_rds, pr_vif) istate goal rdefns
    (fun () -> verify_relations_x istate prog goal rdefns)

and verify_relations_x istate prog goal rdefns : verify_ifent =
  let constr, mode = istate.ist_constr, goal.gl_proof_mode in
  DB.dhprint " +++ VERIFY RELATIONS: " pr_rds rdefns;
  let prog = replace_prog_rdefns ~norm_unk:true prog rdefns in
  let ient = goal |> mk_entail_of_goal |> NO.simplify_all_ent prog in
  DB.dhprint " ==> entail inferred: " pr_ent ient;
  let raise_vifent ?(record_fail=true) ifents continue msg =
    let vif = mk_verify_ifent ifents continue msg in
    let _ = if ifents = [] && continue = false && record_fail = true then
        istate.ist_failed_ents <- ient :: istate.ist_failed_ents in
    raise_vifent vif in
  try
    if not (need_infer_more_entail istate goal) then
      raise_vifent [] false "no need more lemma";
    if not (is_feasible_relations mode rdefns) then
      raise_vifent [] false "infeasible relation";
    PT.reset_cache ();
    if List.exists (check_syntax_equiv_ent ient) istate.ist_failed_ents then
      raise_vifent [] false ~record_fail:false
        "failed entailment encountered before";
    let ng = mk_goal_of_entail prog ~mode:PrfVerifyLemma ient in
    let ng_verify = {ng with gl_proof_mode = PrfVerifyIndtLemma} in
    let pstate = mk_prover_state ~interact:false prog ng in
    let lst, rst, gst = ng.gl_lstats, ng.gl_rstats, ng.gl_gstats in
    DB.dhprint " ==> verify new goal: " pr_g ng;
    if (mode = PrfInferLhs || mode = PrfInferRhs) then (
      let rvrs = choose_rule_view_right pstate ng |> List.map (function
        | RlViewRight rvr -> [rvr] | _ -> []) |> List.concat in
      let rvls = choose_rule_induction pstate ng |> List.map (function
        | RlInduction rid -> [rid] | _ -> []) |> List.concat in
      if List.exists (fun r -> not r.rvr_unfold_case.vuc_base_case &&
                               r.rvr_has_data_same_root) rvrs then
        raise_vifent [] false "infer lhs/rhs: indt view-right has data same root";
      if List.exists (fun r -> r.rvr_trivial) rvrs then
        raise_vifent [] false "infer lhs/rhs: rule view-right trivial";
      if List.exists (fun r -> r.rid_has_data_same_root) rvls then
        raise_vifent [] false "infer lhs/rhs: view-left has data same root";
    );
    let all_fvs = (lst.fst_fvs @ rst.fst_fvs) |> dedup_vs in
    let all_hatoms = lst.fst_hatoms @ rst.fst_hatoms in
    if (lst.fst_num_datas = 0 && rst.fst_num_datas = 0) &&
       (lst.fst_num_hatoms + rst.fst_num_hatoms > 2) &&
       List.exists (fun v -> List.for_all (fun ha ->
         mem_vs v (fv_ha ha)) all_hatoms ) all_fvs then
      raise_vifent [] false "infer lhs/rhs: var appear in all non-data hatoms";
    let lviews, rviews = ng.gl_lstats.fst_views, ng.gl_rstats.fst_views in
    let views = lviews @ rviews in
    let max_num_args = if views = [] then 0 else
        views |> List.map (fun hf ->
          hf.viewf_args |> List.filter (check_ict_exp constr) |>
          List.length) |> max_ints in
    let min_num_args = if views = [] then 0 else
        views |> List.map (fun hf ->
          hf.viewf_args |> List.filter (check_ict_exp constr) |>
          List.length) |> min_ints in
    if List.exists_pair (fun lv rv ->
      (eq_s lv.viewf_name rv.viewf_name) &&
      (List.for_all2 (fun x y ->
         not (check_ict_exp constr x) ||
         (eq_exp x y )) lv.viewf_args rv.viewf_args)) lviews rviews then
      raise_vifent [] false "view has same args of inferred constr";
    if (goal |> collect_rform_goal |> List.length <= 1) &&
       not (check_potential_infer_lemma prog ng.gl_lhs ng.gl_rhs) then
      raise_vifent [] false "check potential lemma by base case unfolding";
    let is_connected_lhs =
      if lst.fst_num_hatoms <= 1 then true
      else
        lst.fst_hatoms |> Comb.gen_combinations 2 |>
        List.exists (function
          | [ha1; ha2] -> intersected_vs (fv_ha ha1) (fv_ha ha2)
          | _ -> false) in
    DB.dhprint " --> new goal: " pr_g ng;
    if lviews |> Comb.gen_combinations 2 |> List.exists (function
      | vf1::vf2::[] -> equiv_vs (fv_vf vf1) (fv_vf vf2)
      | _ -> false) then
      raise_vifent [] false "lviews of same vars";
    if rviews |> Comb.gen_combinations 2 |> List.exists (function
      | vf1::vf2::[] -> equiv_vs (fv_vf vf1) (fv_vf vf2)
      | _ -> false) then
      raise_vifent [] false "rviews of same vars";
    let ifent = mk_infer_entail None rdefns goal ient in
    let _ = match mode with
      | PrfInferBasic | PrfInferAll ->
        if not (subset_vs rst.fst_fhvs lst.fst_fhvs) then
          raise_vifent [] true "infer basic/all: uncommon hvars lhs/rhs";
      | PrfInferLhs ->
        if rst.fst_views |> List.exists (fun vf ->
          vf.viewf_args |> Comb.gen_combinations 2 |>
          List.exists (function | e1::e2::[] -> eq_exp e1 e2
                                | _ -> false)) then
          raise_vifent [] false "infer lhs: duplicated var rhs";
        if not (subset_vs rst.fst_fhvs lst.fst_fhvs) &&
           (lst.fst_num_datas = 0 && rst.fst_num_datas = 0) then
          raise_vifent [] true "infer lhs: non-data lhs && \
                                uncommon heap vars lhs, rhs";
      | PrfInferRhs ->
        if not (subset_vs rst.fst_fhvs lst.fst_fhvs) then
          raise_vifent [] false "infer rhs: uncommon heap vars lhs, rhs";
        let has_uninstantiated_rvs = List.exists (fun ha ->
          not (intersected_vs (fv_ha ha) lst.fst_fvs)) rst.fst_hatoms in
        if has_uninstantiated_rvs && max_num_args <= 3 && min_num_args > 1 then
          raise_vifent [ifent] true "infer rhs: uninstantiated hvars rhs";
      | _ -> () in
    let ptree = verify_valid_lemma pstate ng in
    let ifent = mk_infer_entail (Some ptree) rdefns goal ient in
    let ifent = if check_good_inductive_ptree ptree then
        {ifent with ife_good_lemma_ptree = true}
      else ifent in
    DB.dhprint " --> ptree: " pr_ptree ptree;
    DB.dhprint " --> IFENT: " pr_ife ifent;
    match mode with
    | PrfInferBasic ->
      if not (is_valid_ptree ptree) then
        raise_vifent [] true "infer basic: invalid ptree";
      raise_vifent [ifent] false "infer basic: GOOD!";
    | PrfInferAll ->
      if not (check_good_inductive_ptree ptree) then
        raise_vifent [] true "infer all: invalid induction ptree";
      raise_vifent [ifent] false "infer all: GOOD!";
    | PrfInferLhs ->
      if not (check_good_inductive_ptree ptree) then (
        if lst.fst_num_datas = 0 then
          raise_vifent [] true "infer lhs: non-data lhs && \
                                invalid induction ptree"
        else if not is_connected_lhs then
          raise_vifent [] true  "infer lhs: has-data && unconnected lhs && \
                                 invalid induction ptree"
        else if ng.gl_depth_infer <= 0 then
          raise_vifent [] true "infer lhs: has-data && unconnected lhs && \
                                invalid induction ptree && \
                                but too early to stop"
        else
          raise_vifent [] true "infer lhs: has-data && unconnected lhs && \
                                invalid induction ptree");
      let pf = NO.encode_formula ~constr:IctArith prog ng.gl_lhs in
      if (PT.unsat_or_has_unique_model_one_var ~constr:IctArith pf) then
        raise_vifent [] true "infer lhs: unsat or has unique arith model";
      raise_vifent [ifent] false "infer lhs: GOOD!";
    | PrfInferRhs ->
      let rqvsr = ng.gl_rhs |> extract_components_f |> fst3 |>
                  vars_of_qvars |> List.filter (check_ict_var constr) in
      if not (is_valid_ptree ptree) && (rqvsr = []) then
        raise_vifent [] false "infer rhs: invalid ptree";
      if goal.gl_depth_infer <= 1 &&
         not (check_good_inductive_ptree ptree) then (
        match constr with
        | IctArith ->
          if (is_valid_ptree ptree) &&
             (ng_verify |> verify_valid_lemma pstate |>
              check_good_inductive_ptree ) then
            let ifent = {ifent with ife_good_lemma_ptree = true} in
            raise_vifent [ifent] true "infer rhs: valid induction ptree \
                                       with arithmetic constr"
          else
            raise_vifent [] false "infer rhs: invalid induction ptree \
                                       with arithmetic constr"
        | _ ->
          raise_vifent [ifent] true "infer rhs: invalid induction ptree \
                                       but too early to stop");
      if not (check_good_inductive_ptree ptree) && rst.fst_has_data then
        raise_vifent [] false "infer rhs: invalid induction ptree \
                               with data in rhs";
      if not (List.for_all is_equality_rdefn rdefns) then
        raise_vifent [] false "infer rhs: not an induction ptree: \
                               non equality rdefn";
      let has_uninstantiated_lvs =
        let lvs = List.filter (check_ict_var constr) ng.gl_lstats.fst_fvs in
        let rvs = List.filter (check_ict_var constr) ng.gl_rstats.fst_fvs in
        (diff_vs lvs rvs) != [] in
      if not (check_good_inductive_ptree ptree) &&
         (ng.gl_gstats.gst_num_view_names <= 1) then (
        if has_uninstantiated_lvs then
          raise_vifent [ifent] true
            "infer rhs: invalid induction ptree: uninstantiated lvars");
      let has = lst.fst_hatoms @ rst.fst_hatoms in
      let hvs = has |> fv_has |> List.filter (check_ict_var constr) in
      let has_duplicated_rha = rst.fst_hatoms |> List.exists (fun ha ->
        let rhvs = ha |> fv_ha |> intersect_vs hvs in
        subset_vs rhvs lst.fst_fvs) in
      if not (check_good_inductive_ptree ptree) && has_duplicated_rha then
        raise_vifent [] false
          "infer rhs: not an induction ptree: duplicated rha";
      let has_isolated_vs = List.exists (fun v ->
        let ha_involved = List.filter (fun ha -> mem_vs v (fv_ha ha)) has in
        List.length ha_involved = 1) hvs in
      let has_isolated_rha = rst.fst_hatoms |> List.exists (fun ha ->
        let rhvs = ha |> fv_ha |> intersect_vs hvs in
        not (intersected_vs rhvs lst.fst_fvs)) in
      if not (check_good_inductive_ptree ptree) &&
         (lst.fst_num_hatoms > 1 || rst.fst_num_hatoms > 1) &&
         has_isolated_vs && (not has_isolated_rha) && (rqvsr = []) then
        raise_vifent [] false
          "infer rhs: not an induction tree: isolated vs or rha";
      if (check_good_inductive_ptree ptree) &&
         (lst.fst_num_hatoms > 1 || rst.fst_num_hatoms > 1) &&
         has_isolated_vs then
        (* (List.length rst.fst_hatoms > 1) then *)
        raise_vifent [ifent] true
          "infer rhs: induction tree: isolated vs";
      let has_view_contain_same_arg_index =
        rst.fst_views |> Comb.gen_combinations 2 |>
        List.exists (function
          | [vf1; vf2] ->
            (eq_s vf1.viewf_name vf2.viewf_name) &&
            List.exists2 eq_exp vf1.viewf_args vf2.viewf_args
          | _ -> false) in
      if has_view_contain_same_arg_index then
        raise_vifent [] false
          "infer rhs: has view containing the same arg at the same index";
      let pstate = mk_prover_state ~interact:false prog ng_verify in
      let ptree_verify = verify_valid_lemma pstate ng_verify in
      if check_good_inductive_ptree ptree_verify ||
        (gst.gst_num_data_names = 0 && gst.gst_num_hatoms > 2) then
        let ifent = {ifent with ife_good_lemma_ptree = true} in
        raise_vifent [ifent] true "infer rhs: GOOD (induction ptree_verify)"
      else
        let ifent = {ifent with ife_good_lemma_ptree = false} in
        raise_vifent [ifent] true "infer rhs: GOOD (not induction ptree)!";
    | _ -> herror "verify_relation: incorrect mode: " pr_prm mode
  with EVifent vif ->
    let msg =
      if vif.vif_continue then "=====> CONTINUE INFER: " ^ vif.vif_msg
      else "~~~~~> STOP INFER: " ^ vif.vif_msg in
    DB.dprint (" ==> Verify relation: " ^ msg);
    vif

and infer_one_goal_incr istate prog goal ird ifents : infer_entails =
  DB.trace_4 "infer_one_goal_incr"
    (pr_g, pr_ist, pr_ird, pr_ifes, pr_ifes) goal istate ird ifents
    (fun () -> infer_one_goal_incr_x istate prog goal ird ifents)

and infer_one_goal_incr_x istate prog goal ird ifents : infer_entails =
  try
    DB.dhprint "+++ INFER STATE: " pr_ist istate;
    DB.dhprint "+++ INFER INCREMENTAL: PREVIOUS IFENTS: " pr_ifes ifents;
    DB.dhprint "+++ INFER INCREMENTAL: GOAL: " pr_g goal;
    DB.dhprint "+++ INFER INCREMENTAL: IFENTS: " pr_ifes ifents;
    let mode, constr = goal.gl_proof_mode, istate.ist_constr in
    let _ = match mode, ifents with
      | PrfInferBasic, _::_
      | PrfInferLhs, _::_ -> raise_ifents ifents;
      | PrfInferAll, _::_ -> raise_ifents ifents;
      | PrfInferRhs, [] -> raise_ifents ifents
      | _ -> () in
    if not (need_infer_one_goal_incr istate goal) then
      raise_ifents ifents;
    let goal = {goal with gl_depth_infer = goal.gl_depth_infer + 1} in
    DB.dhprint "+++ CURRENT INFER LEVEL : " pr_int goal.gl_depth_infer;
    DB.dhprint "+++ CONSTR : " pr_ict istate.ist_constr ;
    let rforms = [goal.gl_lhs; goal.gl_rhs] |> collect_rform_fs in
    let rfvs = rforms |> fv_rfs |> List.filter (check_ict_var constr) in
    let ifes =
      let prog = replace_prog_rdefns ~norm_unk:true prog ird.ird_rdefns in
      let ent = goal |> mk_entail_of_goal |> NO.simplify_all_ent prog in
      let lhs, rhs = ent.ent_lhs, ent.ent_rhs in
      match mode with
      | PrfInferLhs ->
        let prog, lhs, rform =
          let rparams = intersect_vs rfvs (fhv_ent ent) in
          let rforms, rdefns =
            let rparamss = match constr with
              | IctAll ->
                let ps1 = List.filter (check_ict_var IctArith) rparams in
                let ps2 = List.filter (check_ict_var IctPointer) rparams in
                [ps1; ps2] |> List.filter List.not_empty
              | _ -> [rparams] in
            List.map (fun args ->
              let rname = fresh_rel_name () in
              let rform = mk_rform rname (List.map mk_exp_var args) in
              let rdefn = mk_rel_defn_unknown rname args in
              (rform, rdefn)) rparamss |>
            List.split in
          let prog = insert_prog_rdefns prog rdefns in
          let lhs = mk_hstar_f_pf lhs (mk_pconj_rfs rforms) in
          (prog, lhs, rforms) in
        let rule = mk_rule_infer_entail goal ird.ird_rdefns ent in
        let ng = {goal with gl_lhs = lhs; gl_rhs = rhs;} in
        let ng = finalize_new_goal_update_all prog goal ng rule in
        let nifents = infer_one_goal istate prog ng in
        List.filter (fun ife -> ife.ife_good_lemma_ptree) nifents
      | PrfInferRhs ->
        let prog, rhs, rform =
          let rparams = intersect_vs rfvs (ahv_ent ent) in
          if (diff_vs rparams (fv lhs)) = [] then raise_ifents ifents;
          let rforms, rdefns =
            let rparamss = match constr with
              | IctAll ->
                let ps1 = List.filter (check_ict_var IctArith) rparams in
                let ps2 = List.filter (check_ict_var IctPointer) rparams in
                [ps1; ps2] |> List.filter List.not_empty
              | _ -> [rparams] in
            List.map (fun args ->
              let rname = fresh_rel_name () in
              let rform = mk_rform rname (List.map mk_exp_var args) in
              let rdefn = mk_rel_defn_unknown rname args in
              (rform, rdefn)) rparamss |>
            List.split in
          let prog = insert_prog_rdefns prog rdefns in
          let rhs = mk_hstar_inject_pf rhs (mk_pconj_rfs rforms) in
          (prog, rhs, rforms) in
        let rule = mk_rule_infer_entail goal ird.ird_rdefns ent in
        let ng = {goal with gl_rhs = rhs;} in
        let ng = finalize_new_goal_update_all prog goal ng rule in
        let nifents =
          let ifs = infer_one_goal istate prog ng in
          if ifs != [] then ifs else ifents in
        List.filter (fun ife -> ife.ife_good_lemma_ptree) nifents
      | _ -> [] in
    let ifes = ifes |> List.map (fun ife ->
      match rforms, ird.ird_rdefns with
      | [rf], [rd] when eq_s rf.prel_name rd.rel_name ->
        let stss = List.map2 (fun e v -> match e with
          | Var (u, _) -> [(u, mk_exp_var v)]
          | _ -> []) rf.prel_args rd.rel_params |> List.concat in
        let nbody =
          let nfs1 = rforms |> List.map (unfold_rform_rf ird.ird_rdefns) in
          let nfs2 = ife.ife_goal_origin |> collect_rform_goal |>
                     List.map (unfold_rform_rf ife.ife_rdefns) in
          (nfs1 @ nfs2) |> mk_pconj |> NO.simplify_all_pf |> subst_pf stss in
        let nrds = [{rd with rel_body = RbForm nbody}] in
        DB.dhprint "NRDS: " pr_rds nrds;
        if (is_feasible_relations mode nrds) then
          let prog = replace_prog_rdefns prog nrds in
          let ent = goal |> mk_entail_of_goal |> NO.simplify_all_ent prog in
          {ife with ife_goal_origin = goal;
                    ife_rdefns = nrds;
                    ife_entail_inferred = ent}
        else ife
      | _ -> ife) in
    let ients = ifes |> List.map (fun ife -> ife.ife_entail_inferred) in
    DB.dhprint "##### UPDATING INFERRED: ENTAILS " pr_ents ients;
    (* TODO: check duplicated inferred entail *)
    if ifes = [] then (
      let ient = goal |> mk_entail_of_goal |> NO.simplify_all_ent prog in
      if not (List.exists (check_syntax_equiv_ent ient)
                istate.ist_failed_ents) then
        istate.ist_failed_ents <- ient :: istate.ist_failed_ents);
    istate.ist_inferred_ents <- istate.ist_inferred_ents @ ients;
    ifes
  with EIfents res -> res

and infer_one_goal istate prog goal : infer_entails =
  DB.trace_2 "infer_one_goal" (pr_g, pr_ist, pr_ifes) goal istate
    (fun () -> infer_one_goal_x istate prog goal)

and infer_one_goal_x istate prog goal : infer_entails =
  DB.dhprint "+++ INFER ONE GOAL: " pr_g goal;
  DB.dhprint "INFER LEVEL: " pr_int goal.gl_depth_infer;
  let lhs, rhs, constr = goal.gl_lhs, goal.gl_rhs, istate.ist_constr in
  let pstate = mk_prover_state ~interact:istate.ist_interact prog goal in
  let ptree = prove_one_goal pstate goal in
  istate.ist_interact <- false;
  let ptree_status = get_ptree_status ptree in
  DB.dhprint "ALL ASSUMPTIONS: " pr_asms pstate.prs_assums;
  let ifes, ipents =
    match ptree_status with
    | PtInfer ptc ->
      DB.dprint "################### SOLVE FUL RELATIONS";
      DB.dhprint "INFER-ASSUMPTION: " pr_asms ptc.ptc_assums;
      let ipents = ptc.ptc_assums |> List.map (mk_assume_pent istate prog) in
      DB.dhprint "CONSTR: " pr_ict constr;
      let ipents = ipents |> List.map (fun pent ->
        let rhs = NO.remove_rform_exists_vars_pf pent.pent_rhs in
        if has_qvars_pf rhs then []
        else [{pent with pent_rhs = rhs}]) |> List.concat in
      DB.dhprint "IPENTS AFTER REMOVE RFORM QVARS & DISJ: " pr_pents ipents;
      let ipents = ipents |> List.map (fun ip ->
        let lhs = ip.pent_lhs |> collect_pure_conjuncts_pf |>
                  List.filter (check_ict_pf constr) |> mk_pconj in
        let rhs = ip.pent_rhs |> collect_pure_conjuncts_pf |>
                  List.filter (check_ict_pf constr) |> mk_pconj in
        {ip with pent_lhs = lhs; pent_rhs = rhs}) in
      DB.dhprint ("IPENTS: FILTER BY CONSTR (" ^ (pr_ict constr) ^ "): ")
        pr_pents ipents;
      let ipents = ipents |> List.map (fun ip ->
        let lhs, rhs = ip.pent_lhs, ip.pent_rhs in
        let lrfs, rrfs = collect_rform_pf lhs, collect_rform_pf rhs in
        if (lrfs != [] && rrfs != [] && constr = IctArith) then
          let lhs, rhs = mk_pconj_rfs lrfs, mk_pconj_rfs rrfs in
          {ip with pent_lhs = lhs; pent_rhs = rhs}
        else ip) in
      DB.dhprint ("IPENTS: REFINE FOR ARITH: ") pr_pents ipents;
      let ipents_core = ipents |> List.filter (fun ip ->
        let lrfs = collect_rform_pf ip.pent_lhs in
        let rrfs = collect_rform_pf ip.pent_rhs in
        not (is_false_pf ip.pent_rhs) &&
        (List.length lrfs <= 2) && (List.length rrfs <= 1)) in
      DB.dhprint "IPENTS CORE: " pr_pents ipents_core;
      let ipents =
        let plhs = NO.encode_formula prog ~constr:constr lhs in
        let ipents_inv = match goal.gl_proof_mode, constr with
          | PrfInferBasic, _ -> [mk_pure_entail plhs (mk_true no_pos)]
          | PrfInferLhs, IctArith ->
            let prhs =
              let pf = NO.encode_formula prog ~constr:istate.ist_constr rhs in
              if (has_qvars_pf pf) then (mk_true no_pos) else pf in
            [mk_pure_entail plhs prhs]
          | _ -> [] in
        ipents @ ipents_inv in  (* keep invariant at the end *)
      DB.dhprint "IPENTS WITH INV: " pr_pents ipents;
      let ipentss =
        if (List.length ipents = List.length ipents_core) then [ipents]
        else if (List.length ipents <= 8) then [ipents; ipents_core]
        else [ipents_core; ipents] in
      let irds = ipentss |> List.fold_left (fun acc pents ->
        if acc != [] then acc
        else if List.length ipents > !thd_max_num_farkas_pents then []
        else solve_relation_constraints istate prog goal pents) [] in
      DB.dhprint "INFERRED RELATION: " pr_irds irds;
      let ifes = irds |> List.fold_left (fun acc ird ->
        if acc != [] then acc
        else
          let vif = ird.ird_rdefns |> verify_relations istate prog goal in
          if not vif.vif_continue then vif.vif_ifents
          else infer_one_goal_incr istate prog goal ird vif.vif_ifents) [] in
      (ifes, ipents)
    | _ -> ([], List.map (mk_assume_pent istate prog) pstate.prs_assums) in
  let solved_rdefnss = ref [] in
  match ifes, istate.ist_partial with
  | [], true ->
    DB.dprint ">>>>>>>>>>>>>>>>>> START SOLVING PARTIAL RELATIONS";
    DB.dhprint "PARTIAL: ALL PURE ENTAILS TO BE INFERRED: " pr_pents ipents;
    let ipents = ipents |> List.map (fun pent ->
      if (has_pdisj_pf pent.pent_lhs) then []
      else if (has_pdisj_pf pent.pent_rhs) then []
      else if (has_qvars_pf pent.pent_rhs) then
        [{pent with pent_rhs = NO.remove_all_exists_vars_pf pent.pent_rhs}]
      else [pent]) |> List.concat in
    DB.dhprint "IPENTS: FILTER BY VARS AND CONSTR: " pr_pents ipents;
    let ipents =
      if List.length ipents <= !thd_max_num_pents_solving_partial then ipents
      else
        let ipents_not_false = ipents |> List.filter (fun p ->
          PT.check_sat p.pent_rhs != MvlFalse) in
        if ipents_not_false != [] then ipents_not_false else ipents in
    DB.dhprint "IPENTS: FILTER FALSE RHS: " pr_pents ipents;
    let ipents = ipents |> List.sortd compare_pent_by_unk_rform |> dedup_pents |>
                 List.first_nth !thd_max_num_pents_solving_partial in
    DB.dhprint "IPENTS: REORDER AND SELECT HIGH PRIORITY: " pr_pents ipents;
    ipents |>
    List.fold_left (fun acc pent ->
      match acc, need_infer_more_entail istate goal with
      | [], true ->
        DB.dhprint " # SOLVE 1 PURE ENTAIL: " pr_pent pent;
        let irds = solve_relation_constraints istate prog goal [pent] in
        DB.dhprint "INFERRED RELATION (OF 1 PENT): " pr_irds irds;
        let irds = irds |> List.filter (fun ird ->
          ird.ird_rdefns |> List.for_all (fun rd -> match rd.rel_body with
            | RbForm f -> not (has_neq_pf f)
            | _ -> true)) in
        DB.dhprint "PARTIAL SOLVING: INFERRED RELATION FILTERED: " pr_irds irds;
        let ifes = irds |> List.fold_left (fun acc ird ->
          if acc != [] ||
             List.exists (check_equiv_infer_rdefn ird) !solved_rdefnss then
            acc
          else
            let _ = solved_rdefnss := !solved_rdefnss @ [ird] in
            let vif = ird.ird_rdefns |> verify_relations istate prog goal in
            if not vif.vif_continue then vif.vif_ifents
            else infer_one_goal_incr istate prog goal ird vif.vif_ifents) [] in
        acc @ ifes
      | _ -> acc) [] |>
    List.fold_left (fun acc ife ->
      let rdss = acc |> List.map (fun ife -> ife.ife_rdefns) in
      if List.exists (check_equiv_rdefns ife.ife_rdefns) rdss then acc
      else acc @ [ife]) []
  | _ -> ifes

and infer_entailment istate prog ent : infer_entails =
  DB.trace_2 "infer_entailment" (pr_ent, pr_ist, pr_ifes) ent istate
    (fun () -> infer_entailment_x istate prog ent)

and infer_entailment_x istate prog ent : infer_entails =
  let ent = NO.simplify_all_ent prog ent in
  let goal = mk_goal_of_entail ~mode:istate.ist_mode prog ent in
  let lms = match !proof_lemma_synthesis with
    | true ->
      let lst, rst = goal.gl_lstats, goal.gl_rstats in
      let lhs, rhs = goal.gl_lhs, goal.gl_rhs in
      if lst.fst_num_hatoms <= 1 && rst.fst_num_hatoms <= 1 then []
      else infer_lemma_convert (mk_prover_state prog goal) lhs rhs
    | _ -> [] in
  let prog = {prog with prog_lemmas = prog.prog_lemmas @ lms} in
  let ifes = infer_one_goal istate prog goal in
  let ents = List.map (fun ife -> ife.ife_entail_inferred) ifes in
  DB.dhprint "+++++++ INFERRED ENTAILS: " pr_ents ents;
  ifes

and check_entail_direct ?(interact=false) prog lhs rhs : mvlogic =
  let goal = mk_goal prog lhs rhs in
  let pstate = mk_prover_state ~interact:interact prog goal in
  let ptree = prove_one_goal pstate goal in
  get_ptree_validity ptree

and check_entailment ?(interact=false) prog ent : mvlogic =
  reset_index_vars prog;
  let ent = NO.simplify_all_ent prog ent in
  let lhs, rhs = ent.ent_lhs, ent.ent_rhs in
  let pmode = if is_false_f rhs then PrfUnsat else PrfEntail in
  let goal = mk_goal ~mode:pmode prog lhs rhs in
  let lst, rst, gst = goal.gl_lstats, goal.gl_rstats, goal.gl_gstats in
  let pstate = mk_prover_state ~interact:interact prog goal in
  let ptree =
    if (!mutual_induction && lst.fst_num_indirect_recur_views > 1) ||
       (!mutual_induction && not !failure_learning) then
      let _ = enable_mode_mutual_induction () in
      prove_one_goal pstate goal
    else if (build_release = RlsFailureAnalysis) ||
            (!failure_learning && lst.fst_num_indirect_recur_views < 2) ||
            (!failure_learning && not !mutual_induction) ||
            (!failure_learning && lst.fst_num_views <= 3) then
      let _ = enable_mode_failure_learning () in
      prove_one_goal pstate goal
    else if !failure_learning && !mutual_induction then
      let _ = enable_mode_mutual_induction_with_failure_analysis () in
      prove_one_goal pstate goal
    else if !proof_lemma_synthesis && (need_infer_lemma_early goal) then
      let _ = enable_mode_lemma_synthesis () in
      prove_one_goal pstate {goal with gl_need_infer_lemma = true}
    else if !proof_lemma_synthesis then (
      (* prove entailment normally first *)
      let _ = DB.hprint "CHECK ENTAILMENT NORMALLY" pr_g goal in
      let ptree =
        let _ = enable_mode_check_entail_normal () in
        match pstate.prs_interact with
        | true -> prove_one_goal pstate goal
        | false ->
          let vsize = lst.fst_num_views + rst.fst_num_views in
          let timeout = if vsize < 10 then 15
            else if vsize < 20 then 20 else 30 in
          let _ = reset_pstate_timeout pstate timeout in
          prove_one_goal pstate goal in
      (* check unsat lhs if possible *)
      let ptree =
        let _ = enable_mode_check_unsat () in
        if is_valid_ptree ptree then ptree else
          let goal = mk_unsat_goal prog goal.gl_lhs in
          let _ = DB.hprint "CHECK UNSAT LHS: " pr_g goal in
          let _ = if not pstate.prs_interact then
              reset_pstate_timeout pstate 5 in
          prove_one_goal pstate goal in
      (* finally synthesize lemmas *)
      match is_valid_ptree ptree with
      | true -> ptree
      | false ->
        let _ = enable_mode_lemma_synthesis () in
        DB.pprint "Timeout when checking entailment. Start to infer lemma";
        reset_index_vars prog;
        let goal = {goal with gl_need_infer_lemma = true} in
        let _ = reset_pstate_timeout pstate !timeout_check_entail in
        prove_one_goal pstate goal)
    else
      let _ = enable_mode_check_entail_normal () in
      prove_one_goal pstate goal in
  dump_proof_info pstate ptree;
  get_ptree_validity ptree

and dump_proof_info pstate ptree =
  let prog = pstate.prs_prog in
  if !dump_ptree_latex then Latex.export_ptree ptree;
  if !dump_ptcore_latex then Latex.export_ptcore ptree;
  if !dump_ptree_xml then Xml.export_ptree ptree;
  if !dump_ptree_profile then Xml.export_ptree_profile prog ptree;
  let ptstatus = get_ptree_status ptree in
  match ptstatus with
  | PtValid ptc ->
    if !print_lemma_stats then (
      let lms_all = pstate.prs_theorems |> List.map mk_lemma_from_theorem in
      (* number of lemmas *)
      if lms_all != [] then
        DB.rhprint " ==> ALL LEMMAS SYNTHESIZED:\n" pr_lms lms_all;
      let naconvert, nasplit, nacombine = ref 0, ref 0, ref 0 in
      let _ = lms_all |> List.iter (fun lm ->
        let s = lm.lm_name in
        if String.exists s "convert" then naconvert := !naconvert + 1
        else if String.exists s "split" then nasplit := !nasplit + 1
        else if String.exists s "combine" then nacombine := !nacombine + 1) in
      (* number of used lemmas *)
      let lms_used = ptree |> collect_used_theorems |>
                     List.map mk_lemma_from_theorem in
      if lms_used != [] then
        DB.rhprint " ==> LEMMAS USED IN THE VALID PROOF:\n" pr_lms lms_used;
      let nuconvert, nusplit, nucombine = ref 0, ref 0, ref 0 in
      let _ = lms_used |> List.iter (fun lm ->
        let s = lm.lm_name in
        if String.exists s "convert" then nuconvert := !nuconvert + 1
        else if String.exists s "split" then nusplit := !nusplit + 1
        else if String.exists s "combine" then nucombine := !nucombine + 1) in
      (* time used lemmas *)
      let tuconvert, tusplit, tucombine = ref 0, ref 0, ref 0 in
      let _ =
        let fg, fp = (fun x -> ()), (fun y -> None) in
        let fr r = match r with
          | RlTheorem rth ->
            let s = rth.rth_th.th_name in
            if String.exists s "convert" then tuconvert := !tuconvert + 1
            else if String.exists s "split" then tusplit := !tusplit + 1
            else if String.exists s "combine" then tucombine := !tucombine + 1
          | _ -> () in
        iter_ptcore (fp, fg, fr) ptc in
      let nlms_all = List.length lms_all in
      let nlms_used = List.length lms_used in
      let tlms = !tuconvert + !tusplit + !tucombine in
      let time_lm = !time_lm_cv +. !time_lm_sp +. !time_lm_cb in
      DB.rpprint (
        " ==> LEMMA SYNTHESIS STATS:\n" ^
        "   - Number of lemmas inferred: " ^ (pr_int nlms_all) ^ "\n" ^
        "       + Lemma-convert inferred: " ^ (pr_int !naconvert) ^ "\n" ^
        "       + Lemma-split inferred: " ^ (pr_int !nasplit) ^ "\n" ^
        "       + Lemma-combine inferred: " ^ (pr_int !nacombine) ^ "\n" ^
        "   - Number of lemmas used: " ^ (pr_int nlms_used) ^ "\n" ^
        "       + Lemma-convert used: " ^ (pr_int !nuconvert) ^ "\n" ^
        "       + Lemma-split used: " ^ (pr_int !nusplit) ^ "\n" ^
        "       + Lemma-combine used: " ^ (pr_int !nucombine) ^ "\n" ^
        "   - Number of times using lemmas: " ^ (pr_int tlms) ^ "\n" ^
        "       + Lemma-convert using times: " ^ (pr_int !tuconvert) ^ "\n" ^
        "       + Lemma-split using times: " ^ (pr_int !tusplit) ^ "\n" ^
        "       + Lemma-combine using times: " ^ (pr_int !tucombine) ^ "\n" ^
        "   - Runtime inferring lemmas : \n" ^
        "       + All lemmas runtime: " ^ (pr_float time_lm) ^ "\n" ^
        "       + Lemma-convert runtime: " ^ (pr_float !time_lm_cv) ^ "\n" ^
        "       + Lemma-split runtime: " ^ (pr_float !time_lm_sp) ^ "\n" ^
        "       + Lemma-combine runtime: " ^ (pr_float !time_lm_cb) ^ "\n"));
    let _ = print_endline (string_of_bool !print_failure_stats) in
    if !print_failure_stats then (
      let nemid, nweaken, ngenvar, ngenconst =
        let fg acc goal = None in
        let fp acc ptc = None in
        let fr acc rule =
          let (nemid, nweaken, ngenvar, ngenconst) = acc in
          let nacc = match rule with
            | RlExclMid _ -> (nemid + 1, nweaken, ngenvar, ngenconst)
            | RlGenLeft rg ->
              let vs = fv_exps rg.rgl_gen_exps in
              if vs != [] then (nemid, nweaken, ngenvar + 1, ngenconst)
              else (nemid, nweaken, ngenvar, ngenconst + 1)
            | RlWeakenLeft _-> (nemid, nweaken + 1, ngenvar, ngenconst)
            | _ -> (nemid, nweaken, ngenvar, ngenconst) in
          Some nacc in
        fold_ptcore (fp, fg, fr) (0, 0, 0, 0) ptc in
      let stats =
        " ==> LEARNING FROM FAILURE STATS:\n" ^
        "  - Num of Rule Case Analysis: " ^ (pr_int nemid) ^ "\n" ^
        "  - Num of Rule Weakening: " ^ (pr_int nweaken) ^ "\n" ^
        "  - Num of Rule Generalizing Variable: " ^ (pr_int ngenvar) ^ "\n" ^
        "  - Num of Rule Generalizing Constant: " ^ (pr_int ngenconst) in
      DB.rpprint stats);
  | _ -> ()

and check_unsat_approx prog (f: formula) : mvlogic =
  DB.trace_1 "check_unsat_approx" (pr_f, pr_mvl) f
    (fun () -> check_unsat_approx_x prog f)

and check_unsat_approx_x prog (f: formula) : mvlogic =
  let pf = f |> NO.encode_formula prog |>
           NO.simplify_all_pf ~prog:(Some prog) in
  Puretp.check_sat pf

and check_unsat_indt ?(interact=false) prog (f: formula) : mvlogic =
  DB.trace_1 "check_unsat_indt" (pr_f, pr_mvl) f
    (fun () -> check_unsat_indt_x ~interact:interact prog f)

and check_unsat_indt_x ?(interact=false) prog (f: formula) : mvlogic =
  let lhs = NO.simplify_all ~prog:(Some prog) f in
  let rhs = mk_ffalse no_pos in
  let goal = mk_goal prog lhs rhs ~mode:PrfUnsat in
  let pstate = mk_prover_state ~interact:interact prog goal in
  let ptree = prove_one_goal pstate goal in
  let _ = if !dump_ptree_latex then Latex.export_ptree ptree in
  let _ = if !dump_ptcore_latex then Latex.export_ptcore ptree in
  let _ = if !dump_ptree_xml then Xml.export_ptree ptree in
  let _ = if !dump_ptree_profile then Xml.export_ptree_profile prog ptree in
  match get_ptree_status ptree with
  | PtValid _ -> MvlFalse
  | PtInvalid -> MvlTrue
  | PtUnkn _ -> MvlUnkn
  | PtInfer _ -> MvlInfer
