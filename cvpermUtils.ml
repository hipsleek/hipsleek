open Gen
open Globals
open Cpure

let remove_dups = Gen.BList.remove_dups_eq eq_spec_var
let check_dups = Gen.BList.check_dups_eq eq_spec_var
let diff = Gen.BList.difference_eq eq_spec_var
let intersect = Gen.BList.intersect_eq eq_spec_var
let overlap = Gen.BList.overlap_eq eq_spec_var
let mem = Gen.BList.mem_eq eq_spec_var

(* To store vperm of variables *)
type vperm_sets = {
  vperm_unprimed_flag: bool;
  vperm_zero_vars: spec_var list;
  vperm_lend_vars: spec_var list;
  vperm_value_vars: spec_var list;
  vperm_full_vars: spec_var list;
  vperm_frac_vars: (Frac.frac * spec_var list) list; 
  (* vperm_frac_vars: (Frac.frac * spec_var) list; (\*simpler*\)  *)
}

let print_vperm_sets = ref (fun (vps: vperm_sets) -> "vperm_sets printer has not been initialized") 

(* unused cos of ivperm? *)
let build_vperm  ?zero:(zero=[])  ?lend:(lend=[])  ?value:(value=[])
 ?frac:(frac=[]) full
=
  let cnt = (List.length zero) + (List.length lend) + (List.length value) + (List.length frac) + (List.length full) in
  {
    vperm_unprimed_flag = if cnt=0 then true else false;
    vperm_zero_vars = List.map sp_rm_prime zero;
    vperm_lend_vars = List.map sp_rm_prime lend;
    vperm_value_vars = List.map sp_rm_prime value;
    vperm_full_vars = List.map sp_rm_prime full;
    vperm_frac_vars = List.map (fun (a,vs) -> (a,List.map sp_rm_prime vs)) frac;
  }

let vperm_unprime vp = { vp with vperm_unprimed_flag = false}

let vperm_rm_prime vp =
  if vp.vperm_unprimed_flag then vp
  else 
    { vperm_unprimed_flag = true;
    vperm_zero_vars = List.map sp_rm_prime vp.vperm_zero_vars;
    vperm_lend_vars = List.map sp_rm_prime vp.vperm_lend_vars;
    vperm_value_vars = List.map sp_rm_prime vp.vperm_value_vars;
    vperm_full_vars = List.map sp_rm_prime vp.vperm_full_vars;
    vperm_frac_vars = List.map (fun (a,vs) -> (a,List.map sp_rm_prime vs)) vp.vperm_frac_vars;
    }

let vperm_rm_prime vps = 
  let pr = !print_vperm_sets in
  Debug.no_1 "vperm_rm_prime" pr pr vperm_rm_prime vps

(* ZH: it is redundant?*)
(* let vperm_rm_prime vp = *)
(*   if vp.vperm_unprimed_flag then vp *)
(*   else vperm_rm_prime vp *)


let empty_vperm_sets = build_vperm []

let is_empty_vperm_sets vps = 
  (is_empty vps.vperm_full_vars) &&
  (is_empty vps.vperm_lend_vars) &&
  (is_empty vps.vperm_value_vars) &&
  (is_empty vps.vperm_zero_vars) &&
  (is_empty vps.vperm_frac_vars)

let is_empty_frac fr =
  let xs = List.filter (fun (f,_) -> not(Frac.is_zero f || Frac.is_value f)) fr in
  is_empty xs

(* WN : need to filter frac list *)
let is_leak_vperm vps = 
  match vps with
    | { vperm_full_vars = full; vperm_frac_vars = frac } ->
          not(is_empty full) || not(is_empty_frac frac)

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
  | VP_Frac f -> Frac.is_zero f
  | _ -> false

let norm_vperm_sets vps = 
  let vps = vperm_rm_prime vps in
  let zero_vars = remove_dups vps.vperm_zero_vars in (* @zero[x] * @zero[x] -> @zero[x] *)
  let lend_vars = remove_dups vps.vperm_lend_vars in (* @lend[x] * @lend[x] -> @lend[x] *)
  let full_vars = (* remove_dups *) vps.vperm_full_vars in (* @full[x] * @full[x] -> false *)
  let group_frac_vars_sets = partition_by_key fst Frac.eq_frac vps.vperm_frac_vars in
  (* WN : need to check if below correct! *)
  let frac_vars_set = List.map (fun (frac, group) -> 
    let m_group = List.concat (List.map snd group) in
    (frac, m_group)) group_frac_vars_sets 
  in
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
            { 
                vperm_unprimed_flag = (v.vperm_unprimed_flag && mvs.vperm_unprimed_flag);
                vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
                vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
                vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
                vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
                vperm_frac_vars = v.vperm_frac_vars @ mvs.vperm_frac_vars; }
  in norm_vperm_sets (helper vps_list)

let merge_vperm_sets vps_list = 
  let vps_list = List.filter (fun x -> not (is_empty_vperm_sets x)) vps_list in
  if (List.length vps_list)<=1 then merge_vperm_sets vps_list
  else 
    let pr = !print_vperm_sets in
    Debug.no_1 "merge_vperm_sets" (pr_list pr) pr merge_vperm_sets vps_list

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
            let v = vperm_rm_prime v in 
            let mvs = helper vs in
            { 
                vperm_unprimed_flag = (v.vperm_unprimed_flag && mvs.vperm_unprimed_flag);
                vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
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
  (* let _ = Debug.binfo_pprint "inside combine_vperm_sets" no_pos in *)
  if (check_dups full_vars) (* || (overlap full_vars lend_vars) *)
  then Error.report_error err
  else
    { comb_vps with
        vperm_zero_vars = remove_dups (diff zero_vars (full_vars @ lend_vars));
        vperm_lend_vars = remove_dups lend_vars; }

let combine_vperm_sets vps_list = 
  let vps_list = List.filter (fun x -> not (is_empty_vperm_sets x)) vps_list in
  if (List.length vps_list)<=1 then combine_vperm_sets vps_list
  else 
    let pr = !print_vperm_sets in
    Debug.no_1 "combine_vperm_sets" (pr_list pr) pr combine_vperm_sets vps_list


(* @full[x] or @full[x] -> @full[x] *)
(* @full[x] or @lend[x] -> @lend[x] *)
(* @full[x] or @zero[x] -> @zero[x] *)
(* @lend[x] or @lend[x] -> @lend[x] *)
(* @lend[x] or @zero[x] -> @zero[x] *)
(* @zero[x] or @zero[x] -> @zero[x] *)
let combine_or_vperm_sets vps1 vps2 =
  let f1, f2 = vps1.vperm_full_vars, vps2.vperm_full_vars in
  let l1, l2 = vps1.vperm_lend_vars, vps2.vperm_lend_vars in
  let z1, z2 = vps1.vperm_zero_vars, vps2.vperm_zero_vars in
  let v1, v2 = f1 @ l1 @ z1, f2 @ l2 @ z2 in
  let alone_vars = diff (v1 @ v2) (intersect v1 v2) in
  let z = remove_dups (z1 @ z2 @ alone_vars) in
  let l = remove_dups (diff (l1 @ l2) z) in
  let f = remove_dups (diff (f1 @ f2) (l @ z)) in
  { 
      vperm_unprimed_flag = (vps1.vperm_unprimed_flag && vps2.vperm_unprimed_flag);
      vperm_zero_vars = z;
      vperm_lend_vars = l;
      vperm_full_vars = f;
      vperm_value_vars = vps1.vperm_value_vars @ vps2.vperm_value_vars; (* TODO *)
      vperm_frac_vars = vps1.vperm_frac_vars @ vps2.vperm_frac_vars; (* TODO *) }

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
      | VP_Frac frac -> { mvs with vperm_frac_vars = mvs.vperm_frac_vars @ [(frac, svl)]; }
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
      | VP_Frac frac ->
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

(* type: (Cpure.spec_var * Cpure.spec_var) list -> vperm_sets -> vperm_sets *)

let subst_par sst vps = 
  let pr = pr_list (pr_pair Cpure.string_of_spec_var Cpure.string_of_spec_var) in
  let pr2 = !print_vperm_sets  in
  Debug.no_2 "subst_par" pr pr2 pr2 subst_par sst vps

let subst_one sst vps = 
  subst_f subst_var sst vps

let subst_one sst vps = 
  let pr = (pr_pair Cpure.string_of_spec_var Cpure.string_of_spec_var) in
  let pr2 = !print_vperm_sets  in
  Debug.no_2 "subst_one" pr pr2 pr2 subst_one sst vps

let subst_avoid_capture f t vps = 
  let sst = List.combine f t in
  subst_f subs_one sst vps

let is_false_vperm_sets vps = 
  let full_vars = vps.vperm_full_vars in
  check_dups full_vars

let get_vperm_spec_var sv vps = 
  if mem sv vps.vperm_full_vars then VP_Full
  else if mem sv vps.vperm_lend_vars then VP_Lend
  else if mem sv vps.vperm_value_vars then VP_Value
  else 
    try
      let frac_perm, _ = List.find (fun (_, svl) -> mem sv svl) vps.vperm_frac_vars in
      VP_Frac frac_perm
    with _ -> VP_Zero
