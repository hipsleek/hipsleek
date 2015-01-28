open Globals
open Cformula
open Cpure
open Mcpure
open Gen
open CvpermUtils

(* module CP = Cpure *)
module CF = Cformula
module MCP = Mcpure
module MCD = Mcpure_D
(* module CVP = CvpermUtils *)

(******************************************************************************)

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
  (CVP.merge_vperm_anns vps, join_conjunctions other_p)

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
  (CVP.merge_vperm_sets vps, join_conjunctions fs)

let strip_vperm_memo_grp mg =
  let b_vperm, memo_grp_cons = List.fold_left (fun (av, am) mc ->
    let vp = extract_vperm_b_formula mc.MCD.memo_formula in
    match vp with
    | Some vp -> (av @ [vp], am)
    | None -> (av, am @ [mc])) ([], []) mg.MCD.memo_group_cons
  in
  let b_vps = CVP.merge_vperm_anns b_vperm in
  let vps, memo_grp_slice = List.split (List.map 
    (fun f -> strip_vperm_pure f) mg.MCD.memo_group_slice) in
  let vps = CVP.merge_vperm_sets (b_vps::vps) in
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
    (CVP.merge_vperm_sets vps_list, MCP.MemoF mp)

let strip_vperm_mix_formula mf =
  let pr1 = !CVP.print_vperm_sets in
  let pr2 = !MCP.print_mix_formula in
  Debug.no_1 "strip_vperm_mix_formula" pr2 (pr_pair pr1 pr2) 
  strip_vperm_mix_formula mf

let strip_vperm_formula (f: CF.formula) : vperm_sets * CF.formula =
  let _, pure_f, _, _, _, _ = CF.split_components f in
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
  (vps, CF.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) f) 

(******************************************************************************)

exception Vperm_Entail_Fail of (spec_var * vp_ann * vp_ann)

type vperm_res = 
  | Fail of CF.list_context
  | Succ of CF.entail_state

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
  in CVP.norm_vperm_sets (helper ans)

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

let vperm_entail_var es sv lhs_ann rhs_ann = 
  let err = Vperm_Entail_Fail (sv, lhs_ann, rhs_ann) in
  match lhs_ann with
  | VP_Full ->
    begin match rhs_ann with
    | VP_Full -> VP_Zero
    | VP_Lend -> if es.CF.es_infer_obj # is_par then raise err else VP_Full 
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
  let rhs = CF.formula_of_mix_formula rhs_p pos in
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
    let rhs_vperm_sets, _ = strip_vperm_mix_formula rhs_p in
    let rhs_vperm_sets = CVP.norm_vperm_sets rhs_vperm_sets in

    let las = ann_set_of_vperm_sets lhs_vperm_sets in
    let ras = ann_set_of_vperm_sets rhs_vperm_sets in
    let pas, rem_las, rem_ras = pair_ann_sets las ras in

    let non_zero_vps = List.find_all (fun (_, ann) -> not (CVP.is_Zero ann)) rem_ras in
    if (non_zero_vps != []) then
      let msg = 
        "Mismatch non-zero variable permission in consequent " ^
        (pr_list pr_vp non_zero_vps) in 
      let fctx = mkFailCtx_vp msg estate rhs_p pos in
      Fail fctx
    else
      try
        let res_vps = List.map (fun (v, la, ra) -> (v, vperm_entail_var estate v la ra)) pas in
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