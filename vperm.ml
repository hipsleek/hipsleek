open Globals
open Cformula
open Cpure
open Mcpure
open Gen

module CP = Cpure
module MCP = Mcpure
module VPU = VpermUtils

exception Vperm_Entail_Fail of (spec_var * vp_ann * vp_ann)

type vperm_res = 
  | Fail of list_context
  | Succ of entail_state

let ann_set_of_vperm_sets vps = 
  let full_vars = List.map (fun v -> (v, VP_Full)) vps.vperm_full_vars in
  let lend_vars = List.map (fun v -> (v, VP_Lend)) vps.vperm_lend_vars in
  let value_vars = List.map (fun v -> (v, VP_Value)) vps.vperm_value_vars in
  let zero_vars = List.map (fun v -> (v, VP_Zero)) vps.vperm_zero_vars in
  let frac_vars = List.concat (List.map (fun (fperm, svl) -> 
    List.map (fun v -> (v, VP_Const fperm)) svl) vps.vperm_frac_vars) in
  full_vars @ lend_vars @ value_vars @ zero_vars @ frac_vars

let vperm_sets_of_ann_set ans = 
  let rec helper ans = match ans with
    | [] -> empty_vperm_sets
    | (v, ann)::ans ->
      let vps = helper ans in
      begin match ann with
      | VP_Full -> { vps with vperm_full_vars = vps.vperm_full_vars @ [v] }
      | VP_Lend -> { vps with vperm_lend_vars = vps.vperm_lend_vars @ [v] }
      | VP_Value -> { vps with vperm_value_vars = vps.vperm_value_vars @ [v] }
      | VP_Zero -> { vps with vperm_zero_vars = vps.vperm_zero_vars @ [v] }
      | VP_Const fperm ->
        let fperm_svl, others = List.partition (fun (vf, _) -> Frac.eq_frac fperm vf) vps.vperm_frac_vars in
        let fperm_svl = v::(List.concat (List.map snd fperm_svl)) in
        { vps with vperm_frac_vars = others @ [(fperm, fperm_svl)] }
      end
  in VPU.norm_vperm_sets (helper ans)

(* Pair LHS and RHS vp_ann sets        *)
(* Return: pair sets, rem lhs, rem rhs *)
let rec pair_ann_sets lhs_as rhs_as = 
  match lhs_as with
  | [] -> ([], [], rhs_as)
  | (vl, lhs_ann)::lhs_as ->
    let ps, ls, rs = pair_ann_sets lhs_as rhs_as in
    try
      let _, rhs_ann = List.find (fun (vr, _) -> eq_spec_var vl vr) rs in
      let rem_rs = List.filter (fun (vr, _) -> not (eq_spec_var vl vr)) rs in
      (vl, lhs_ann, rhs_ann)::ps, ls, rem_rs
    with Not_found -> (ps, (vl, lhs_ann)::ls, rs)

let vperm_entail_var sv lhs_ann rhs_ann = 
  let err = Vperm_Entail_Fail (sv, lhs_ann, rhs_ann) in
  match lhs_ann with
  | VP_Full ->
    begin match rhs_ann with
    | VP_Full -> VP_Zero
    | VP_Lend -> if Globals.infer_const_obj # is_par then raise err else VP_Full 
    | VP_Value -> VP_Full
    | VP_Zero -> VP_Full
    | _ -> lhs_ann
    end
  | VP_Lend ->
    begin match rhs_ann with
    | VP_Full -> raise err
    | VP_Lend -> VP_Lend
    | VP_Value -> VP_Lend
    | VP_Zero -> VP_Lend
    | _ -> lhs_ann
    end
  | VP_Value ->
    begin match rhs_ann with
    | VP_Full -> VP_Zero
    | VP_Lend -> VP_Value (* TODO: to check *)
    | VP_Value -> VP_Value
    | VP_Zero -> VP_Value
    | _ -> lhs_ann
    end
  | VP_Zero ->
    begin match rhs_ann with
    | VP_Zero -> VP_Zero
    | _ -> raise err
    end
  | _ -> lhs_ann

let mkFailCtx_vp msg estate rhs_p pos = 
  (* let msg = "Error in VPerm entailment: " ^ msg in *)
  let rhs = (formula_of_mix_formula rhs_p pos) in
  let rhs_b = extr_rhs_b rhs in
  let estate = { estate with es_formula = substitute_flow_into_f !Exc.GTable.top_flow_int estate.es_formula } in
  mkFailCtx_in (
    Basic_Reason (mkFailContext msg estate (Base rhs_b) None pos,
    mk_failure_may msg logical_error, estate.es_trace)) (mk_cex true)

let vperm_entail_rhs estate lhs_p rhs_p pos =
  if not (!Globals.ann_vp) then Succ estate
  else
    let pr_vp = pr_pair !print_sv string_of_vp_ann in
    let lhs_vperm_sets = estate.es_vperm_sets in
    let rhs_vperm_sets, _ = VPU.strip_vperm_mix_formula rhs_p in
    let rhs_vperm_sets = VPU.norm_vperm_sets rhs_vperm_sets in

    let las = ann_set_of_vperm_sets lhs_vperm_sets in
    let ras = ann_set_of_vperm_sets rhs_vperm_sets in
    let pas, rem_las, rem_ras = pair_ann_sets las ras in

    let non_zero_vps = List.find_all (fun (_, ann) -> not (VPU.is_Zero ann)) rem_ras in
    if (non_zero_vps != []) then
      let msg = 
        "Mismatch non-zero variable permission in consequent " ^
        (pr_list pr_vp non_zero_vps) in 
      let fctx = mkFailCtx_vp msg estate rhs_p pos in
      Fail fctx
    else
      try
        let res_vps = List.map (fun (v, la, ra) -> (v, vperm_entail_var v la ra)) pas in
        let estate = { estate with es_vperm_sets = vperm_sets_of_ann_set (rem_las @ res_vps) }
        in Succ estate
      with (Vperm_Entail_Fail (sv, lhs_ann, rhs_ann)) ->
        let msg = (pr_vp (sv, lhs_ann)) ^ " cannot satisfy " ^ (pr_vp (sv, rhs_ann)) in
        let fctx = mkFailCtx_vp msg estate rhs_p pos in
        Fail fctx

(* let vperm_entail_rhs estate lhs_p rhs_p pos =                                                                       *)
(*   let old_lhs_zero_vars = estate.es_var_zero_perm in                                                                *)
(*   let rhs_vperms, _ = MCP.filter_varperm_mix_formula rhs_p in                                                       *)
(*   (*find a closure of exist vars*)                                                                                  *)
(*   let func v =                                                                                                      *)
(*     if (List.mem v estate.es_evars) then find_closure_mix_formula v lhs_p                                           *)
(*     else [v]                                                                                                        *)
(*   in                                                                                                                *)
(*   (* let lhs_zero_vars = List.concat (List.map (fun v -> find_closure_mix_formula v lhs_p) old_lhs_zero_vars) in *) *)
(*   let lhs_zero_vars = List.concat (List.map func old_lhs_zero_vars) in                                              *)
(*   (* let _ = print_endline ("zero_vars = " ^ (Cprinter.string_of_spec_var_list lhs_zero_vars)) in *)                *)
(*   let _ = if (!Globals.ann_vp) && (lhs_zero_vars!=[] || rhs_vperms!=[]) then                                        *)
(*     Debug.devel_pprint ("heap_entail_empty_rhs_heap: checking " ^                                                   *)
(*                         (string_of_vp_ann VP_Zero) ^                                                                *)
(*                         (Cprinter.string_of_spec_var_list lhs_zero_vars) ^                                          *)
(*                         " |- "  ^ (pr_list Cprinter.string_of_pure_formula rhs_vperms)^"\n") pos                    *)
(*   in                                                                                                                *)
(*   let rhs_val, rhs_vrest = List.partition (fun f -> CP.is_varperm_of_typ f VP_Value) rhs_vperms in                  *)
(*   (* let rhs_ref, rhs_vrest2 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Ref) rhs_vrest in *)              *)
(*   let rhs_full, rhs_vrest3 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Full) rhs_vrest in                  *)
(*   (* let _ = print_endline ("\n LDK: " ^ (pr_list Cprinter.string_of_pure_formula rhs_vrest3)) in *)                *)
(*   let _ = if (rhs_vrest3!=[]) then                                                                                  *)
(*     print_endline ("[Warning] heap_entail_empty_rhs_heap: the conseq should not                                     *)
(*                     include variable permissions other than " ^                                                     *)
(*                     (string_of_vp_ann VP_Value) ^ " and " ^ (string_of_vp_ann VP_Full))                             *)
(*         (*ignore those var perms in rhs_vrest3*)                                                                    *)
(*   in                                                                                                                *)
(*   let rhs_val_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Value)) rhs_val) in          *)
(*   (* let rhs_ref_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Ref)) rhs_ref) in *)      *)
(*   let rhs_full_vars = List.concat (List.map (fun f -> CP.varperm_of_formula f (Some  VP_Full)) rhs_full) in         *)
(*   (* v@zero  |- v@value --> fail *)                                                                                 *)
(*   (* v@zero  |- v@full --> fail *)                                                                                  *)
(*   let tmp1 = Gen.BList.intersect_eq CP.eq_spec_var_ident lhs_zero_vars (rhs_val_vars) in                            *)
(*   let tmp3 = Gen.BList.intersect_eq CP.eq_spec_var_ident lhs_zero_vars (rhs_full_vars) in                           *)
(*   let dup_vars = Gen.BList.find_dups_eq CP.eq_spec_var_ident rhs_full_vars in                                       *)
(*   if (!Globals.ann_vp) && (tmp1!=[] (* || tmp2!=[ ]*) || tmp3!=[] || dup_vars !=[]) then                            *)
(*     begin                                                                                                           *)
(*       (*FAIL*)                                                                                                      *)
(*         let msg1 =                                                                                                  *)
(*           if (dup_vars !=[]) then                                                                                   *)
(*             let msg = (": full permission var " ^                                                                   *)
(*                        (Cprinter.string_of_spec_var_list (dup_vars)) ^                                              *)
(*                       " cannot be duplicated" ^ "\n") in                                                            *)
(*             let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in                                  *)
(*             msg                                                                                                     *)
(*           else ""                                                                                                   *)
(*         in                                                                                                          *)
(*         let msg2 = if tmp1!=[] then                                                                                 *)
(*               let msg = (": pass-by-val var " ^ (Cprinter.string_of_spec_var_list (tmp1)) ^                         *)
(*                          " cannot have possibly zero permission" ^ "\n") in                                         *)
(*               let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in                                *)
(*               msg                                                                                                   *)
(*             else ""                                                                                                 *)
(*         in                                                                                                          *)
(*         let msg3 = if tmp3!=[] then                                                                                 *)
(*               let msg = (": full permission var " ^ (Cprinter.string_of_spec_var_list (tmp3)) ^                     *)
(*                          " cannot have possibly zero permission" ^ "\n") in                                         *)
(*               let _ = Debug.devel_pprint ("heap_entail_empty_rhs_heap" ^ msg) pos in                                *)
(*               msg                                                                                                   *)
(*             else ""                                                                                                 *)
(*         in                                                                                                          *)
(*       Debug.devel_pprint ("heap_entail_empty_rhs_heap: failed in entailing variable permissions in conseq\n") pos;  *)
(*       Debug.devel_pprint ("heap_entail_empty_rhs_heap: formula is not valid\n") pos;                                *)
(*       let rhs_p = List.fold_left (fun mix_f vperm -> memoise_add_pure_N mix_f vperm) rhs_p rhs_vperms in            *)
(*       (* picking original conseq since not found here *)                                                            *)
(*       let conseq = (formula_of_mix_formula rhs_p pos) in                                                            *)
(*       let rhs_b = extr_rhs_b conseq in                                                                              *)
(*       let err_o = mkFailCtx_vperm (msg1 ^ "\n" ^ msg2 ^ "\n" ^ msg3) rhs_b estate conseq (mk_cex true) pos in       *)
(*       Fail err_o                                                                                                    *)
(*     end                                                                                                             *)
(*   else                                                                                                              *)
(*     (* not(v \in S) *)                                                                                              *)
(*     (* -------------------- *)                                                                                      *)
(*     (* S@zero |- v@value  --> S@Z *)                                                                                *)


(*     (*        not(v \in S) *)                                                                                       *)
(*     (* ----------------------- *)                                                                                   *)
(*     (* S@zero |- v@full  --> S+{v}@Z *)                                                                             *)
(*     (*note: use the old_lhs_zero_vars, not use its closure*)                                                        *)
(*     let estate = if not (!Globals.ann_vp) then estate else                                                          *)
(*       let new_lhs_zero_vars = (old_lhs_zero_vars@rhs_full_vars) in (*TO CHECK*)                                     *)
(*       {estate with es_var_zero_perm=new_lhs_zero_vars}                                                              *)
(*     in Succ estate                                                                                                  *)