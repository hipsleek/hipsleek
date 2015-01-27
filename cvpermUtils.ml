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

let is_Zero ann = 
  match ann with
  | VP_Zero -> true
  | _ -> false

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
  