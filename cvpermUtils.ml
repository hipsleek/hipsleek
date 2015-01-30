open Gen
open Globals
open Cpure

(* To store vperm of variables *)
type vperm_sets = {
  vperm_zero_vars: spec_var list;
  vperm_lend_vars: spec_var list;
  vperm_value_vars: spec_var list;
  vperm_full_vars: spec_var list;
  vperm_frac_vars: (Frac.frac * spec_var list) list; }

let print_vperm_sets = ref (fun (vps: vperm_sets) -> "vperm_sets printer has not been initialized") 

let empty_vperm_sets = {
  vperm_zero_vars = [];
  vperm_lend_vars = [];
  vperm_value_vars = [];
  vperm_full_vars = [];
  vperm_frac_vars = []; }

let is_empty_vperm_sets vps = 
  (is_empty vps.vperm_full_vars) &&
  (is_empty vps.vperm_lend_vars) &&
  (is_empty vps.vperm_value_vars) &&
  (is_empty vps.vperm_zero_vars) &&
  (is_empty vps.vperm_frac_vars)

let remove_dups = Gen.BList.remove_dups_eq eq_spec_var
let check_dups = Gen.BList.check_dups_eq eq_spec_var
let diff = Gen.BList.difference_eq eq_spec_var
let intersect = Gen.BList.intersect_eq eq_spec_var
let overlap = Gen.BList.overlap_eq eq_spec_var

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

let is_Zero ann = 
  match ann with
  | VP_Zero -> true
  | _ -> false

let norm_vperm_sets vps = 
  let zero_vars = remove_dups vps.vperm_zero_vars in (* @zero[x] * @zero[x] -> @zero[x] *)
  let lend_vars = remove_dups vps.vperm_lend_vars in (* @lend[x] * @lend[x] -> @lend[x] *)
  let full_vars = (* remove_dups *) vps.vperm_full_vars in (* @full[x] * @full[x] -> false *)
  let group_frac_vars_sets = partition_by_key fst Frac.eq_frac vps.vperm_frac_vars in
  let frac_vars_set = List.map (fun (frac, group) -> 
    let m_group = List.concat (List.map snd group) in
    (frac, m_group)) group_frac_vars_sets in
  { vps with
    vperm_full_vars = full_vars;
    vperm_lend_vars = diff lend_vars full_vars;
    vperm_zero_vars = diff zero_vars (full_vars @ lend_vars); 
    vperm_frac_vars = frac_vars_set; }

let norm_vperm_sets vps = 
  let pr = !print_vperm_sets in
  Debug.no_1 "norm_vperm_sets" pr pr norm_vperm_sets vps

let merge_vperm_sets vps_list = 
  let rec helper vps_list =  
    match vps_list with
    | [] -> empty_vperm_sets
    | v::vs ->
      let mvs = helper vs in
      { vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
        vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
        vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
        vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
        vperm_frac_vars = v.vperm_frac_vars @ mvs.vperm_frac_vars; }
  in norm_vperm_sets (helper vps_list)

(* @full[x] * @full[x] -> ERR                     *)
(* @full[x] * @lend[x] -> ERR                     *)
(* @full[x] * @zero[x] -> @full[x]                *)
(* @lend[x] * @lend[x] -> @lend[x] => remove_dups *)
(* @lend[x] * @zero[x] -> @lend[x]                *)
(* @zero[x] * @zero[x] -> @zero[x] => remove_dups *)
let combine_vperm_sets vps_list = 
  let rec helper vps_list =  
    match vps_list with
    | [] -> empty_vperm_sets
    | v::vs ->
      let mvs = helper vs in
      { vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
        vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
        vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
        vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
        vperm_frac_vars = v.vperm_frac_vars @ mvs.vperm_frac_vars; }
  in
  let comb_vps = helper vps_list in
  let full_vars = comb_vps.vperm_full_vars in
  let lend_vars = comb_vps.vperm_lend_vars in
  let zero_vars = comb_vps.vperm_zero_vars in
  let msg = "Combination of vperm sets causes contradiction" in
  let err = ({ Error.error_loc = proving_loc # get; Error.error_text = msg }) in
  if (check_dups full_vars) (* || (overlap full_vars lend_vars) *)
  then Error.report_error err
  else
    { comb_vps with
      vperm_zero_vars = remove_dups (diff zero_vars (full_vars @ lend_vars));
      vperm_lend_vars = remove_dups lend_vars; }

let vperm_sets_of_anns ann_list =
  let rec helper ann_list =  
    match ann_list with
    | [] -> empty_vperm_sets
    | (ann, svl)::vs ->
      let mvs = helper vs in
      match ann with
      | VP_Zero -> { mvs with vperm_zero_vars = mvs.vperm_zero_vars @ svl; } 
      | VP_Full -> { mvs with vperm_full_vars = mvs.vperm_full_vars @ svl; } 
      | VP_Value -> { mvs with vperm_value_vars = mvs.vperm_value_vars @ svl; } 
      | VP_Lend -> { mvs with vperm_lend_vars = mvs.vperm_lend_vars @ svl; } 
      | VP_Const frac -> { mvs with vperm_frac_vars = mvs.vperm_frac_vars @ [(frac, svl)]; }
  in norm_vperm_sets (helper ann_list)

let clear_vperm_sets ann_list vps =
  let rec helper ann_list =
    match ann_list with
    | [] -> vps
    | (ann, svl)::vs ->
      let cvs = helper vs in
      match ann with
      | VP_Zero -> { cvs with vperm_zero_vars = diff cvs.vperm_zero_vars svl; } 
      | VP_Full -> { cvs with vperm_full_vars = diff cvs.vperm_full_vars svl; } 
      | VP_Value -> { cvs with vperm_value_vars = diff cvs.vperm_value_vars svl; } 
      | VP_Lend -> { cvs with vperm_lend_vars = diff cvs.vperm_lend_vars svl; } 
      | VP_Const frac ->
        let frac_sets, others = List.partition (fun (f, _) -> 
          Frac.eq_frac f frac) cvs.vperm_frac_vars in
        let frac_svl = List.concat (List.map snd frac_sets) in
        let frac_svl = (frac, diff frac_svl svl) in
        { cvs with vperm_frac_vars = (frac, svl)::others; }  
  in helper ann_list

let fv vps =
  remove_dups (vps.vperm_zero_vars @ vps.vperm_full_vars @ vps.vperm_value_vars @
    vps.vperm_lend_vars @ (List.concat (List.map snd vps.vperm_frac_vars)))

let subst_f f sst vps = 
  let f_list vl = List.map (fun v -> f sst v) vl in
  { vps with
    vperm_zero_vars = f_list vps.vperm_zero_vars;
    vperm_lend_vars = f_list vps.vperm_lend_vars;
    vperm_value_vars = f_list vps.vperm_value_vars;
    vperm_full_vars = f_list vps.vperm_full_vars;
    vperm_frac_vars = List.map (fun (frac, vl) -> (frac, f_list vl)) vps.vperm_frac_vars; } 

let subst_par sst vps = 
  subst_f subst_var_par sst vps

let subst_one sst vps = 
  subst_f subst_var sst vps

let subst_avoid_capture f t vps = 
  let sst = List.combine f t in
  subst_f subs_one sst vps

let is_false_vperm_sets vps = 
  let full_vars = vps.vperm_full_vars in
  check_dups full_vars
