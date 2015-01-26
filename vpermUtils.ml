module MCP = Mcpure
module MCD = Mcpure_D

open Gen.Basic
open Globals
open Others
open Cprinter
open Cpure
open Cformula

let remove_dups = Gen.BList.remove_dups_eq eq_spec_var
let diff = Gen.BList.difference_eq eq_spec_var

let rec merge_vperm_sets vps_list = 
  match vps_list with
  | [] -> empty_vperm_sets
  | v::vs ->
    let mvs = merge_vperm_sets vs in
    { vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
      vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
      vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
      vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
      vperm_frac_vars = v.vperm_frac_vars @ mvs.vperm_frac_vars; }

let rec merge_vperm_anns ann_list = 
  match ann_list with
  | [] -> empty_vperm_sets
  | (ann, svl, _)::vs ->
    let mvs = merge_vperm_anns vs in
    match ann with
    | VP_Zero -> { mvs with vperm_zero_vars = mvs.vperm_zero_vars @ svl; } 
    | VP_Full -> { mvs with vperm_full_vars = mvs.vperm_full_vars @ svl; } 
    | VP_Value -> { mvs with vperm_value_vars = mvs.vperm_value_vars @ svl; } 
    | VP_Lend -> { mvs with vperm_lend_vars = mvs.vperm_lend_vars @ svl; } 
    | VP_Const frac -> { mvs with vperm_frac_vars = mvs.vperm_frac_vars @ [(frac, svl)]; }

let extract_vperm_b_formula bf = 
  let (pf, _) = bf in
  match pf with
  | VarPerm vp -> Some vp
  | _ -> None

let extract_vperm_formula f = 
  match f with
  | BForm (bf, _) -> extract_vperm_b_formula bf
  | _ -> None

let strip_vperm_pure_only f =
  let mf_ls = split_conjunctions f in
  let (vps, other_p) = List.fold_left (fun (av, ap) f ->
    let vp = extract_vperm_formula f in
    match vp with
    | Some vp -> (av @ [vp], ap)
    | None -> (av, ap @ [f])) ([], []) mf_ls 
  in
  (merge_vperm_anns vps, join_conjunctions other_p)

let def_lbl l = LO.is_common l

let def_lbl l =
  Debug.no_1 "def_lbl" (LO.string_of) string_of_bool def_lbl l

let strip_vperm_list ls =
  let rec aux xs =
    match xs with
    | [] -> ([], [])
    | ((l, f) as ff)::xs ->
      let (l0, r0) = aux xs in
      let (l1, r1) =
        if def_lbl l then
          let (l2, f2) = strip_vperm_pure_only f in
          ([l2], (l, f2))
        else ([], ff)
      in (l1 @ l0, r1::r0)
  in aux ls

let strip_vperm_pure_andlist ls =
  List.fold_left (fun (av, af) f ->
    match f with
    | AndList ls -> 
      let (vps, nls) = strip_vperm_list ls in
      (av @ vps, (AndList nls)::af)
    | _ ->
      let vp, rf = strip_vperm_pure_only f in
      (av @ [vp], af @ [rf])) ([], []) ls

let strip_vperm_pure f =
  let mf_ls = split_conjunctions f in
  let (vps, fs) = strip_vperm_pure_andlist mf_ls in
  (merge_vperm_sets vps, join_conjunctions fs)

let strip_vperm_memo_grp mg =
  let b_vperm, memo_grp_cons = List.fold_left (fun (av, am) mc ->
    let vp = extract_vperm_b_formula mc.MCD.memo_formula in
    match vp with
    | Some vp -> (av @ [vp], am)
    | None -> (av, am @ [mc])) ([], []) mg.MCD.memo_group_cons
  in
  let b_vps = merge_vperm_anns b_vperm in
  let vps, memo_grp_slice = List.split (List.map 
    (fun f -> strip_vperm_pure f) mg.MCD.memo_group_slice) in
  let vps = merge_vperm_sets (b_vps::vps) in
  (vps, { mg with
    MCD.memo_group_cons = memo_grp_cons;
    MCD.memo_group_slice = memo_grp_slice; })

let strip_vperm_mix_formula (mf: MCP.mix_formula) =
  match mf with
  | MCP.OnePF f ->
    let vps, f = strip_vperm_pure f in
    (vps, MCP.OnePF f)
  | MCP.MemoF mp -> 
    let vps_list, mp = List.split (List.map strip_vperm_memo_grp mp) in
    (merge_vperm_sets vps_list, MCP.MemoF mp)

let strip_vperm_mix_formula mf =
  let pr1 = CP.string_of_vperm_sets in
  let pr2 = !MCP.print_mix_formula in
  Debug.no_1 "strip_vperm_mix_formula" pr2 (pr_pair pr1 pr2) 
  strip_vperm_mix_formula mf

let strip_vperm_formula (f: formula) : vperm_sets * formula =
  let _, pure_f, _, _, _ = split_components f in
  let (vps, other_p) = strip_vperm_mix_formula pure_f in
  (* Using transform_formula to update the pure part of f *)
  let f_e_f _ = None in
  let f_f _ = None in
  let f_h_f e = Some e in
  let f_m mp = Some (MCP.memo_of_mix other_p) in
  let f_a _ = None in
  let f_p_f pf = Some (MCP.pure_of_mix other_p) in
  let f_b _ = None in
  let f_e _ = None in
  (vps, transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) f) 

let norm_vperm_sets vps = 
  let zero_vars = remove_dups vps.vperm_zero_vars in
  let lend_vars = remove_dups vps.vperm_lend_vars in
  let full_vars = remove_dups vps.vperm_full_vars in
  { vps with
    vperm_full_vars = full_vars;
    vperm_lend_vars = diff lend_vars full_vars;
    vperm_zero_vars = diff zero_vars (full_vars @ lend_vars); }

let norm_vperm_sets vps = 
  let pr = string_of_vperm_sets in
  Debug.no_1 "norm_vperm_sets" pr pr norm_vperm_sets vps
  