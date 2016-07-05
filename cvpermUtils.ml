#include "xdebug.cppo"
open VarGen
open Gen
open Globals
open Cpure

let remove_dups = Gen.BList.remove_dups_eq eq_spec_var_ident
let check_dups = Gen.BList.check_dups_eq eq_spec_var_ident
let diff = Gen.BList.difference_eq eq_spec_var_ident
let intersect = Gen.BList.intersect_eq eq_spec_var_ident
let overlap = Gen.BList.overlap_eq eq_spec_var_ident
let mem = Gen.BList.mem_eq eq_spec_var_ident

(* To store vperm of variables *)
type vperm_sets = {
  vperm_unprimed_flag: bool;
  vperm_is_false : bool;
  vperm_zero_vars: spec_var list;
  vperm_lend_vars: spec_var list;
  vperm_value_vars: spec_var list;
  vperm_full_vars: spec_var list;
  (* vperm_frac_vars: (Frac.frac * spec_var list) list;  *)
  vperm_frac_vars: (Frac.frac * spec_var) list; (*simpler*)
}

let print_vperm_sets = ref (fun (vps: vperm_sets) -> "vperm_sets printer has not been initialized") 

(* unused cos of ivperm? *)
let build_vperm  ?zero:(zero=[])  ?lend:(lend=[])  ?value:(value=[])
    ?frac:(frac=[]) full
  =
  let cnt = (List.length zero) + (List.length lend) + (List.length value) + (List.length frac) + (List.length full) in
  {
    vperm_unprimed_flag = if cnt=0 then true else false;
    vperm_is_false = false;
    vperm_zero_vars = List.map sp_rm_prime zero;
    vperm_lend_vars = List.map sp_rm_prime lend;
    vperm_value_vars = List.map sp_rm_prime value;
    vperm_full_vars = List.map sp_rm_prime full;
    vperm_frac_vars = List.map (fun (a,v) -> (a,sp_rm_prime v)) frac;
  }

let vperm_unprime vp = { vp with vperm_unprimed_flag = false}

let vperm_rm_prime vp = vp
(* if vp.vperm_unprimed_flag then vp *)
(* else  *)
(*   { vp with *)
(*       vperm_unprimed_flag = true; *)
(*       vperm_zero_vars = List.map sp_rm_prime vp.vperm_zero_vars; *)
(*       vperm_lend_vars = List.map sp_rm_prime vp.vperm_lend_vars; *)
(*       vperm_value_vars = List.map sp_rm_prime vp.vperm_value_vars; *)
(*       vperm_full_vars = List.map sp_rm_prime vp.vperm_full_vars; *)
(*       vperm_frac_vars = List.map (fun (a,vs) -> (a,sp_rm_prime vs)) vp.vperm_frac_vars; *)
(*   } *)

(* let vperm_rm_prime vps =  *)
(*   let pr = !print_vperm_sets in *)
(*   Debug.no_1 "vperm_rm_prime" pr pr vperm_rm_prime vps *)

(* ZH: it is redundant?*)
(* let vperm_rm_prime vp = *)
(*   if vp.vperm_unprimed_flag then vp *)
(*   else vperm_rm_prime vp *)


let empty_vperm_sets = build_vperm []

let is_empty_frac fr =
  (* let xs = List.filter (fun (f,_) -> not(Frac.is_zero f)) fr in *)
  (* is_empty xs *)
  List.for_all (fun (f,_) -> Frac.is_zero f) fr

let is_empty_vperm_sets vps = 
  not (!Globals.ann_vp) ||
  ((is_empty vps.vperm_full_vars) &&
   (is_empty vps.vperm_lend_vars) &&
   (is_empty vps.vperm_value_vars) &&
   (* (is_empty vps.vperm_zero_vars) && *)
   (is_empty_frac vps.vperm_frac_vars))

let is_empty_frac_leak fr =
  (* let xs = List.filter (fun (f,_) -> not(Frac.is_zero f || Frac.is_value f)) fr in *)
  (* is_empty xs *)
  List.for_all (fun (f,_) -> Frac.is_zero f || Frac.is_value f) fr

(* WN : need to filter frac list *)
let is_leak_vperm vps = 
  match vps with
  | { vperm_full_vars = full; vperm_frac_vars = frac } ->
    not(is_empty full) || not(is_empty_frac_leak frac)

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

let norm_frac_list xs = 
  let rec aux xs fr sv =
    match xs with
    | [] -> [(fr,sv)]
    | (fr2,sv2)::xs -> 
      if eq_spec_var_ident sv sv2 then aux xs (Frac.add fr fr2) sv
      else (fr,sv)::(aux xs fr2 sv2)
  in match xs with
  | [] -> []
  | (fr,sv)::xs -> aux xs fr sv

let norm_frac_list frac_vars =
  let frac_vars = List.sort (fun (_,sv1) (_,sv2) -> 
      String.compare (get_unprime sv1) (get_unprime sv2)) frac_vars in
  let frac_vars2 = norm_frac_list frac_vars in
  frac_vars2

let check_dupl svl =
  let rec aux svl p =
    match svl with
    | [] -> false
    | v::vs -> if eq_spec_var_ident p v then true else aux vs v
  in match svl with
  | [] -> false
  | v::vs -> aux vs v

let norm_list svl  = 
  let svl2 = List.sort (fun v1 v2 -> String.compare (get_unprime v1) (get_unprime v2)) svl in
  (svl2,check_dupl svl2)

let check_dupl_two s1 s2 =
  let rec aux s1 s2 =
    match s1,s2 with
    | [],_ -> false
    | _,[] -> false
    | (v1::t1),(v2::t2) -> 
      let c = String.compare (get_unprime v1) (get_unprime v2) in
      if c=0 then true
      else if c<0 then aux t1 s2
      else aux s1 t2 in
  aux s1 s2

let norm_full_value full value =
  let svl1,f1 = norm_list full in
  let svl2,f2 = norm_list value in
  let f = f1||f2 in
  if f then (svl1,svl2,f)
  else (svl1,svl2,check_dupl_two svl1 svl2)

let is_frac_false xs =
  List.exists (Frac.is_false) (List.map fst xs)

(* let rm_zero frac_vars = *)
(*   List.filter (fun (f,v) -> not(Frac.is_zero f)) frac_vars *)

let is_false_frac_other frac_vars full_vars value_vars =
  let vs = full_vars@value_vars in
  List.exists (fun (f,v) -> not(Frac.is_zero f) && mem v vs) frac_vars 


let norm_vperm_sets vps = 
  let vps = vperm_rm_prime vps in
  let (full_vars,value_vars,flag1) = norm_full_value vps.vperm_full_vars vps.vperm_value_vars in
  let zero_vars = remove_dups vps.vperm_zero_vars in (* @zero[x] * @zero[x] -> @zero[x] *)
  let lend_vars = remove_dups vps.vperm_lend_vars in (* @lend[x] * @lend[x] -> @lend[x] *)
  (* let full_vars = (\* remove_dups *\) vps.vperm_full_vars in (\* @full[x] * @full[x] -> false *\) *)
  let frac_vars2 = norm_frac_list vps.vperm_frac_vars in
  let false_flag = flag1 || (is_frac_false frac_vars2) 
                   || (is_false_frac_other frac_vars2 full_vars value_vars) in
  (* WN : need to check if below correct! *)
  (* let frac_vars_set = List.map (fun (frac, group) ->  *)
  (*   let m_group = List.concat (List.map snd group) in *)
  (*   (frac, m_group)) group_frac_vars_sets  *)
  { vps with
    vperm_full_vars = full_vars;
    vperm_is_false = false_flag;
    vperm_lend_vars = diff lend_vars full_vars; (* TO FIX Value? *)
    vperm_value_vars = value_vars;
    vperm_zero_vars = diff zero_vars (full_vars @ lend_vars); 
    vperm_frac_vars = frac_vars2; }

let norm_vperm_sets vps = 
  if not (!Globals.ann_vp) then vps
  else
    let pr = !print_vperm_sets in
    Debug.no_1 "norm_vperm_sets" pr pr norm_vperm_sets vps

let quick_is_false vps = vps.vperm_is_false 

let merge_vperm_sets vps_list = 
  if not (!Globals.ann_vp) then empty_vperm_sets
  else
    let rec helper vps_list =  
      match vps_list with
      | [] -> empty_vperm_sets
      | v::vs ->
        let mvs = helper vs in
        { 
          vperm_unprimed_flag = (v.vperm_unprimed_flag && mvs.vperm_unprimed_flag);
          vperm_is_false = v.vperm_is_false ||  mvs.vperm_is_false;
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
  if not (!Globals.ann_vp) then empty_vperm_sets
  else
    let rec helper vps_list =  
      match vps_list with
      | [] -> empty_vperm_sets
      | v::vs ->
        let v = vperm_rm_prime v in 
        let mvs = helper vs in
        { 
          vperm_unprimed_flag = (v.vperm_unprimed_flag && mvs.vperm_unprimed_flag);
          vperm_is_false = v.vperm_is_false || mvs.vperm_is_false;
          vperm_zero_vars = v.vperm_zero_vars @ mvs.vperm_zero_vars;
          vperm_lend_vars = v.vperm_lend_vars @ mvs.vperm_lend_vars;
          vperm_value_vars = v.vperm_value_vars @ mvs.vperm_value_vars;
          vperm_full_vars = v.vperm_full_vars @ mvs.vperm_full_vars;
          vperm_frac_vars = norm_frac_list (v.vperm_frac_vars @ mvs.vperm_frac_vars); }
    in
    let comb_vps = helper vps_list in
    let full_vars = comb_vps.vperm_full_vars in
    let lend_vars = comb_vps.vperm_lend_vars in
    let zero_vars = comb_vps.vperm_zero_vars in
    let msg = "Combination of vperm sets causes contradiction" in
    let err = ({ Error.error_loc = proving_loc # get; Error.error_text = msg }) in
    (* let () = x_binfo_pp "inside combine_vperm_sets" no_pos in *)
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
(* this method loses too much information ; it should not be used *)
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
    vperm_is_false = vps1.vperm_is_false && vps2.vperm_is_false;
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
      | VP_Frac frac -> { mvs with vperm_frac_vars = mvs.vperm_frac_vars @ (List.map (fun v -> (frac, v)) svl); }
  in norm_vperm_sets (helper ann_list)

(* This seems to be removing vps of some ids *)
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
      | VP_Frac frac -> { cvs with vperm_frac_vars = 
                                     (List.filter (fun (_,v) -> not(mem v svl)) cvs.vperm_frac_vars) } (* TODO:WN *)
      (*   let frac_sets, others = List.partition (fun (f, _) ->  *)
      (*     Frac.eq_frac f frac) cvs.vperm_frac_vars in *)
      (*   let frac_svl = List.concat (List.map snd frac_sets) in *)
      (*   let frac_svl = (frac, diff frac_svl svl) in *)
      (*   { cvs with vperm_frac_vars = (frac, svl)::others; }   *)
  in helper ann_list

let fv vps =
  remove_dups (vps.vperm_zero_vars @ vps.vperm_full_vars @ vps.vperm_value_vars @
               vps.vperm_lend_vars @ (List.map snd vps.vperm_frac_vars))

let subst_f f sst vps = 
  let f_list vl = List.map (fun v -> f sst v) vl in
  { vps with
    vperm_zero_vars = f_list vps.vperm_zero_vars;
    vperm_lend_vars = f_list vps.vperm_lend_vars;
    vperm_value_vars = f_list vps.vperm_value_vars;
    vperm_full_vars = f_list vps.vperm_full_vars;
    vperm_frac_vars = List.map (fun (frac, v) -> (frac, f sst v)) vps.vperm_frac_vars; } 

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
  vps.vperm_is_false

let norm_is_false_vperm_sets vps = 
  let vps = norm_vperm_sets vps in
  (vps,vps.vperm_is_false)
(* let full_vars = vps.vperm_full_vars in *)
(*   check_dups full_vars *)

let get_vperm_spec_var sv vps = 
  if mem sv vps.vperm_full_vars then VP_Full
  else if mem sv vps.vperm_lend_vars then VP_Lend
  else if mem sv vps.vperm_value_vars then VP_Value
  else 
    try
      let frac_perm, _ = List.find (fun (_, s) -> eq_spec_var_ident sv s) vps.vperm_frac_vars in
      VP_Frac frac_perm
    with _ -> VP_Zero
