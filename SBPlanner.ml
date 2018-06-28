open SBGlobals
open SBLib
open SBCast
open SBProof
open SBUnify

module NO = SBNormalize
module ID = SBInduction

exception EInstantiations of substs list

(* TODO:
try the following proof planners:
  - matching proof
  - unfold proof
  - induction proof
*)


let rec find_unifying_plan prog goal : unification list =
  Debug.trace_1 "find_unifying_plan" (pr_g, pr_unfs) goal
    (fun () -> find_unifying_plan_x prog goal)

and find_unifying_plan_x prog goal : unification list =
  (* exception A; *)
  try
    let lstats, rstats = goal.gl_lstats, goal.gl_rstats in
    if (lstats.fst_num_hatoms > !thd_max_lhs_size_unifying_plan) then
      raise (EUnfs []);
    if (lstats.fst_num_datas > rstats.fst_num_datas) then
      raise (EUnfs []);
    if (lstats.fst_num_views > rstats.fst_num_views) then
      raise (EUnfs []);
    if not (subset_ss lstats.fst_data_names rstats.fst_data_names) then
      raise (EUnfs []);
    if not (subset_ss lstats.fst_view_names rstats.fst_view_names) then
      raise (EUnfs []);
    let vars = lstats.fst_fvs in
    let hfs1 =
      (List.map mk_hatom_vf lstats.fst_views)
      @ (List.map mk_hatom_df lstats.fst_datas) in
    let hfs2 =
      (List.map mk_hatom_vf rstats.fst_views)
      @ (List.map mk_hatom_df rstats.fst_datas) in
    let init_unf = mk_unification [] [] [] [] [] in
    let unfs = unify_hatoms prog hfs1 hfs2 [] vars init_unf in
    List.filter (fun unf ->
      unf.unf_conflict_ssts = [] &&
      unf.unf_residue = []) unfs
  with EUnfs res -> res

let rec find_precise_unifying_plan prog goal : unification list =
  let pr_out x = match x with
    | [] -> "[]"
    | _ -> pr_items ~bullet:"  # " pr_unf x in
  Debug.trace_1 "find_precise_unifying_plan" (pr_g, pr_out) goal
    (fun () -> find_precise_unifying_plan_x prog goal)

and find_precise_unifying_plan_x prog goal : unification list =
  (* exception A; *)
  try
    let lstats, rstats = goal.gl_lstats, goal.gl_rstats in
    if (lstats.fst_num_hatoms > !thd_max_lhs_size_unifying_plan) then
      raise (EUnfs []);
    if (lstats.fst_num_datas != rstats.fst_num_datas) then
      raise (EUnfs []);
    if (lstats.fst_num_views != rstats.fst_num_views) then
      raise (EUnfs []);
    let hfs1 =
      (List.map mk_hatom_vf lstats.fst_views)
      @ (List.map mk_hatom_df lstats.fst_datas) in
    let hfs2 =
      (List.map mk_hatom_vf rstats.fst_views)
      @ (List.map mk_hatom_df rstats.fst_datas) in
    let vars = lstats.fst_hvs in
    let init_unf = mk_unification [] [] [] [] [] in
    let substs = unify_hatoms prog hfs1 hfs2 [] vars init_unf in
    List.filter (fun unf -> unf.unf_conflict_ssts = []) substs
  with EUnfs res -> res

let rec find_matching_plan prog goal : unification list =
  let pr_out x = match x with
    | [] -> "[]"
    | _ -> pr_items ~bullet:"  # " pr_unf x in
  Debug.trace_1 "find_matching_plan" (pr_g, pr_out) goal
    (fun () -> find_matching_plan_x prog goal)

and find_matching_plan_x prog goal : unification list =
  (* exception A; *)
  try
    let lstats, rstats = goal.gl_lstats, goal.gl_rstats in
    if (lstats.fst_num_hatoms > !thd_max_lhs_size_unifying_plan) then
      raise (EUnfs []);
    if (lstats.fst_num_datas != rstats.fst_num_datas) then
      raise (EUnfs []);
    if (lstats.fst_num_views != rstats.fst_num_views) then
      raise (EUnfs []);
    let hfs1 =
      (List.map mk_hatom_vf lstats.fst_views)
      @ (List.map mk_hatom_df lstats.fst_datas) in
    let hfs2 =
      (List.map mk_hatom_vf rstats.fst_views)
      @ (List.map mk_hatom_df rstats.fst_datas) in
    let vars = rstats.fst_hvs in
    let init_unf = mk_unification [] [] [] [] [] in
    let substs =
      init_unf |> unify_hatoms prog hfs2 hfs1 [] vars |>
      List.filter (fun unf ->
        let svs = unf.unf_conflict_ssts |> List.split |> fst in
        unf.unf_conflict_ssts = [] && (subset_vs svs rstats.fst_qvs)) in
    substs
  with EUnfs res -> res
