open Globals
open Ipure

type spec_var = ident * primed

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

let create_vperm_sets ann svl =
  let empty_vps = empty_vperm_sets in
  match ann with
  | VP_Full -> { empty_vps with vperm_full_vars = svl; }
  | VP_Lend -> { empty_vps with vperm_lend_vars = svl; }
  | VP_Value -> { empty_vps with vperm_value_vars = svl; }
  | VP_Zero -> { empty_vps with vperm_zero_vars = svl; }
  | VP_Const frac -> { empty_vps with vperm_frac_vars = [(frac, svl)]; }

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

let v_apply_list s vl = List.map (fun v -> v_apply_one s v) vl

let vp_apply_one s vp = 
  { vp with
    vperm_zero_vars = v_apply_list s vp.vperm_zero_vars;
    vperm_lend_vars = v_apply_list s vp.vperm_lend_vars;
    vperm_value_vars = v_apply_list s vp.vperm_value_vars;
    vperm_full_vars = v_apply_list s vp.vperm_full_vars;
    vperm_frac_vars = List.map (fun (frac, vl) -> 
      (frac, v_apply_list s vl)) vp.vperm_frac_vars; } 
