open SBGlobals
open SBLib
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
module TL = SBTemplate

let rec div_pure_form f1 f2 =
  DB.trace_2 "div_pure_form" (pr_pf, pr_pf, pr_pf) f1 f2
    (fun () -> div_pure_form_x f1 f2)

and div_pure_form_x f1 f2 =
  f1 |> collect_pure_conjuncts_pf |>
  List.filter (fun x -> PT.check_imply f2 x = MvlFalse) |>
  mk_pconj

let subst_rdefn rdefn rfargs rfbody =
  try
    let ssts = List.map2 (fun e v -> match e with
      | Var (u, _) -> (u, mk_exp_var v)
      | _ ->
        let msg = "subst_rdefn: need to currify: " ^ (pr_exp e) in
        let _ = warning msg in
        failwith msg) rfargs rdefn.rel_params in
    let cmp_sst sst1 sst2 = compare_var (fst sst1) (fst sst2) in
    let clustered_sstss = List.cluster cmp_sst ssts in
    DB.nhprint "clustered_ssts: " pr_sstss clustered_sstss;
    let sstss =
      let clustered_sstss = List.filter (fun ssts ->
        List.length ssts <= 2
        (* TRUNG: should consider only single cluster? *)
        (* List.length ssts <= 1 *)
      ) clustered_sstss in
      Comb.gen_cartesian clustered_sstss in
    sstss |>
    List.map (fun ssts ->
      let sstsvs = ssts |> List.split |> fst in
      let nrfbody = rfbody |> collect_pure_conjuncts_pf |>
                    List.filter (fun pf -> subset_vs (fv_pf pf) sstsvs) |>
                    mk_pconj in
      let nbody = subst_pf ssts nrfbody in
      let nrd = {rdefn with rel_body = RbForm nbody} in
      [nrd]) |> dedup_rdefnss
  with _ -> []

let rec solve_one_pure_entail prog pent : rel_defnss =
  DB.trace_1 "solve_one_pure_entail" (pr_pent, pr_rdss) pent
    (fun () -> solve_one_pure_entail_x prog pent)

and solve_one_pure_entail_x prog pent : rel_defnss =
  DB.nhprint "IPROVER: SOLVE ENTAIL: " pr_pent pent;
  let lrfs = pent.pent_lhs |> collect_pure_conjuncts_pf |>
             List.map (function | PRel rf -> [rf] | _ -> []) |> List.concat in
  let rrfs = pent.pent_rhs |> collect_pure_conjuncts_pf |>
             List.map (function | PRel rf -> [rf] | _ -> []) |> List.concat in
  let rfs = lrfs @ rrfs in
  let lpfs = pent.pent_lhs |> remove_all_rform_pf |>
             collect_pure_conjuncts_pf in
  let rpfs = pent.pent_rhs |> remove_all_rform_pf |>
             collect_pure_conjuncts_pf in
  let rdefns =
    rfs |> List.map (fun r -> r.prel_name) |> dedup_ss |>
    List.map (find_rel_defn prog.prog_rels) in
  let rdss1 =
    lrfs |>
    List.map (fun rf ->
      let rfvs = fv_rf rf in
      let lhs = lpfs |> List.filter (fun pf -> subset_vs (fv_pf pf) rfvs) |>
                mk_pconj in
      let rhs = rpfs |> List.filter (fun pf -> subset_vs (fv_pf pf) rfvs) |>
                mk_pconj in
      let body = div_pure_form rhs lhs in
      let rd = find_rel_defn rdefns rf.prel_name in
      subst_rdefn rd rf.prel_args body |> List.concat) |>
    Comb.gen_cartesian in
  let rdss2 =
    rrfs |>
    List.map (fun rf ->
      let rfvs = fv_rf rf in
      let lhs = lpfs |> List.filter (fun pf -> subset_vs (fv_pf pf) rfvs) |>
                mk_pconj in
      let rhs = rpfs |> List.filter (fun pf -> subset_vs (fv_pf pf) rfvs) |>
                mk_pconj in
      let body = div_pure_form lhs rhs in
      let rd = find_rel_defn rdefns rf.prel_name in
      subst_rdefn rd rf.prel_args body |> List.concat) |>
    Comb.gen_cartesian in
  let rdss = rdss1 @ rdss2 in
  DB.nhprint "IPROVER: RESULT: " pr_rdss rdss;
  rdss



(* let solve_pents_ prog pents : rel_defn list = *)
