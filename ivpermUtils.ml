#include "xdebug.cppo"
open Gen
open VarGen
open Globals
open Ipure

type spec_var = ident * primed

(* let eq_spec_var (v1, p1) (v2, p2) =       *)
(*   (String.compare v1 v2 = 0) && (p1 = p2) *)

(* let remove_dups = Gen.BList.remove_dups_eq eq_spec_var *)

(* let diff = Gen.BList.difference_eq eq_spec_var *)

(* To store vperm of variables *)
type vperm_sets = {
  vperm_zero_vars: spec_var list;
  vperm_lend_vars: spec_var list;
  vperm_value_vars: spec_var list;
  vperm_full_vars: spec_var list;
  vperm_frac_vars: (Frac.frac * spec_var list) list;
}

let empty_vperm_sets = {
  vperm_zero_vars = [];
  vperm_lend_vars = [];
  vperm_value_vars = [];
  vperm_full_vars = [];
  vperm_frac_vars = [];
}

let is_empty_vperm_sets vps = 
  not (!Globals.ann_vp) ||
      ((is_empty vps.vperm_full_vars) &&
          (is_empty vps.vperm_lend_vars) &&
          (is_empty vps.vperm_value_vars) &&
          (is_empty vps.vperm_zero_vars) &&
          (is_empty vps.vperm_frac_vars))

let create_vperm_sets ann svl =
  let empty_vps = empty_vperm_sets in
  match ann with
  | VP_Full -> { empty_vps with vperm_full_vars = svl; }
  | VP_Lend -> { empty_vps with vperm_lend_vars = svl; }
  | VP_Value -> { empty_vps with vperm_value_vars = svl; }
  | VP_Zero -> { empty_vps with vperm_zero_vars = svl; }
  | VP_Frac frac -> { empty_vps with vperm_frac_vars = [(frac, svl)]; }

(* let norm_vperm_sets vps =                                       *)
(*   let zero_vars = remove_dups vps.vperm_zero_vars in            *)
(*   let lend_vars = remove_dups vps.vperm_lend_vars in            *)
(*   let full_vars = remove_dups vps.vperm_full_vars in            *)
(*   { vps with                                                    *)
(*     vperm_full_vars = full_vars;                                *)
(*     vperm_lend_vars = diff lend_vars full_vars;                 *)
(*     vperm_zero_vars = diff zero_vars (full_vars @ lend_vars); } *)

let rec merge_vperm_sets vps_list = 
  match vps_list with
  | [] -> empty_vperm_sets
  | v::vs ->
    let mvs = merge_vperm_sets vs in
    let mvs = 
      { vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
        vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
        vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
        vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
        vperm_frac_vars = v.vperm_frac_vars @ mvs.vperm_frac_vars; }
    in (* norm_vperm_sets *) mvs

let rec vperm_sets_of_anns ann_list = 
  match ann_list with
  | [] -> empty_vperm_sets
  | (ann, sv)::vs ->
    let mvs = vperm_sets_of_anns vs in
    match ann with
    | VP_Zero -> { mvs with vperm_zero_vars = sv::mvs.vperm_zero_vars; } 
    | VP_Full -> { mvs with vperm_full_vars = sv::mvs.vperm_full_vars; } 
    | VP_Value -> { mvs with vperm_value_vars = sv::mvs.vperm_value_vars; } 
    | VP_Lend -> { mvs with vperm_lend_vars = sv::mvs.vperm_lend_vars; } 
    | VP_Frac frac -> 
      let frac_vps, others = List.partition (fun (fr, _) -> 
        Frac.eq_frac frac fr) mvs.vperm_frac_vars in
      let m_frac_vps = List.concat (List.map snd frac_vps) in
      { mvs with vperm_frac_vars = (frac, sv::m_frac_vps)::others; }

let subst_f f sst vps = 
  let f_list vl = List.map (fun v -> f sst v) vl in
  { vps with
    vperm_zero_vars = f_list vps.vperm_zero_vars;
    vperm_lend_vars = f_list vps.vperm_lend_vars;
    vperm_value_vars = f_list vps.vperm_value_vars;
    vperm_full_vars = f_list vps.vperm_full_vars;
    vperm_frac_vars = List.map (fun (frac, vl) -> (frac, f_list vl)) vps.vperm_frac_vars; } 

let vp_apply_one sst vps = 
  subst_f v_apply_one sst vps
