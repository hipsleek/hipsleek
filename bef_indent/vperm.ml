#include "xdebug.cppo"
open VarGen
open Globals
open Cformula
open Cpure
open Mcpure
open Gen
open CvpermUtils
open Exc.GTable

(* module CP = Cpure *)
module CF = Cformula
    (* module MCP = Mcpure   *)
    (* module MCD = Mcpure_D *)
    (* module CVP = CvpermUtils *)

(******************************************************************************)
let rec add_vperm_sets_formula (vp: vperm_sets) (f: CF.formula): CF.formula = 
  match f with
    | CF.Or ({ formula_or_f1 = f1; formula_or_f2 = f2; } as o) ->
          CF.Or ({ o with 
              formula_or_f1 = add_vperm_sets_formula vp f1; 
              formula_or_f2 = add_vperm_sets_formula vp f2; })
    | CF.Base b -> CF.Base { b with formula_base_vperm = merge_vperm_sets [b.formula_base_vperm; vp]; }
    | CF.Exists e -> CF.Exists { e with formula_exists_vperm = merge_vperm_sets [e.formula_exists_vperm; vp]; }

let add_vperm_sets_list_failesc_ctx (vp: CVP.vperm_sets) ctx =
  let add_vperm_sets_es vp es =
    Ctx { es with es_formula = add_vperm_sets_formula vp es.es_formula; }
  in transform_list_failesc_context (idf, idf, (add_vperm_sets_es vp)) ctx

let rec set_vperm_sets_formula (vp: CVP.vperm_sets) (f: CF.formula): CF.formula = 
  match f with
    | CF.Or ({
          formula_or_f1 = f1; 
          formula_or_f2 = f2; } as o) ->
          CF.Or ({ o with 
              formula_or_f1 = set_vperm_sets_formula vp f1; 
              formula_or_f2 = set_vperm_sets_formula vp f2; })
    | CF.Base b -> CF.Base { b with formula_base_vperm = vp; }
    | CF.Exists e -> CF.Exists { e with formula_exists_vperm = vp; }

let set_vperm_sets_list_failesc_ctx (vp: vperm_sets) ctx =
  let set_vperm_sets_es vp es =
    Ctx { es with es_formula = set_vperm_sets_formula vp es.es_formula; }
  in transform_list_failesc_context (idf, idf, (set_vperm_sets_es vp)) ctx

let rec clear_vperm_sets_formula ann_list (f: CF.formula): CF.formula = 
  match f with
    | CF.Or ({
          formula_or_f1 = f1; 
          formula_or_f2 = f2; } as o) ->
          CF.Or ({ o with 
              formula_or_f1 = clear_vperm_sets_formula ann_list f1; 
              formula_or_f2 = clear_vperm_sets_formula ann_list f2; })
    | CF.Base b -> CF.Base { b with 
          formula_base_vperm = clear_vperm_sets ann_list b.formula_base_vperm; }
    | CF.Exists e -> CF.Exists { e with 
          formula_exists_vperm = clear_vperm_sets ann_list e.formula_exists_vperm; }

let clear_vperm_sets_list_failesc_ctx ann_list ctx =
  let clear_vperm_sets_es ann_list es =
    Ctx { es with es_formula = clear_vperm_sets_formula ann_list es.es_formula; }
  in transform_list_failesc_context (idf, idf, (clear_vperm_sets_es ann_list)) ctx

let clear_inf_par_list_failesc_ctx ctx =
  let clear_inf_par_es es =
    (es.es_infer_obj # reset INF_PAR; Ctx es) 
  in transform_list_failesc_context (idf, idf, clear_inf_par_es) ctx

let set_inf_par_list_failesc_ctx ctx =
  let set_inf_par_es es =
    (es.es_infer_obj # set INF_PAR; Ctx es) 
  in transform_list_failesc_context (idf, idf, set_inf_par_es) ctx

let formula_of_vperm_sets vps = 
  let b = CF.mkTrue_b (mkTrueFlow ()) no_pos in
  Base { b with formula_base_vperm = vps; }

let formula_of_vperm_anns ann_list = 
  let vps = vperm_sets_of_anns ann_list in
  formula_of_vperm_sets vps

let collect_vperm_sets f = 
  let _, _, vp, _, _, _ = split_components f in
  vp

let rec vperm_sets_of_formula f = 
  match f with
    | CF.Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
          let vp1 = vperm_sets_of_formula f1 in
          let vp2 = vperm_sets_of_formula f2 in
          combine_or_vperm_sets vp1 vp2
    | _ -> collect_vperm_sets f

let vperm_sets_list_failesc_context ctx = 
  let f = formula_of_list_failesc_context ctx in
  vperm_sets_of_formula f

let clean_es_heap_h_formula_for_par vars hf =
  let f_h_f hf =
    match hf with
      | DataNode d ->
            if mem d.h_formula_data_node vars then Some HEmp
            else Some hf
      | ViewNode v ->
            if mem v.h_formula_view_node vars then Some HEmp
            else Some hf
      | _ -> None 
  in
  transform_h_formula f_h_f hf

let clean_es_heap_list_failesc_ctx_for_par vars ctx =
  let clean_es_heap_es_for_par es =
    Ctx { es with es_heap = clean_es_heap_h_formula_for_par vars es.es_heap; }
  in transform_list_failesc_context (idf, idf, clean_es_heap_es_for_par) ctx 

let clean_es_heap_list_failesc_ctx_for_par vars ctx =
  let pr1 = !print_svl in
  let pr2 = !print_list_failesc_context in
  Debug.no_2 "clean_es_heap_list_failesc_ctx_for_par" pr1 pr2 pr2
      clean_es_heap_list_failesc_ctx_for_par vars ctx

let norm_list_failesc_context_for_par norm_es ctx = 
  let norm_es_for_par es = Ctx (norm_es es)
    (* Ctx { es with es_formula = norm_f es es.es_formula } *)
  in 
  transform_list_failesc_context (idf, idf, norm_es_for_par) ctx 

let compose_list_failesc_context_formula_for_par case_pre 
      (ctx: list_failesc_context) (post: CF.formula) pos: list_failesc_context =
  let vps = vperm_sets_of_formula post in
  let out_vars = List.map to_primed vps.vperm_full_vars in
  let lend_vars = List.map to_primed vps.vperm_lend_vars in
  let compose_es_formula es =
    if case_pre then
      let compose_ctx = compose_context_formula (Ctx es) post [] false Flow_replace pos in
      (* Do not push exists on @full and @lend vars to get their latest values *)
      let ctx_fv = context_fv compose_ctx in
      let post_ctx = push_exists_context (diff ctx_fv (out_vars @ lend_vars)) compose_ctx in
      map_context (fun es -> { es with 
          es_formula = set_vperm_sets_formula vps es.es_formula; }) post_ctx
    else
      let out_vars = List.filter (fun v -> not (is_node_typ v)) out_vars in 
      let compose_ctx = compose_context_formula (Ctx es) post out_vars false Flow_replace pos in 
      compose_ctx
  in 
  transform_list_failesc_context (idf, idf, compose_es_formula) ctx

let compose_list_failesc_context_formula_for_par case_pre 
      (ctx: list_failesc_context) (post: CF.formula) pos: list_failesc_context = 
  let pr1 = !print_list_failesc_context in
  let pr2 = !CF.print_formula in
  let pr3 b = if b then "FOR CASE POST" else "FOR PAR POST" in  
  Debug.no_3 "compose_list_failesc_context_formula_for_par" pr3 pr1 pr2 pr1
      (fun _ _ _ -> compose_list_failesc_context_formula_for_par case_pre ctx post pos)
      case_pre ctx post

let compose_list_failesc_contexts_for_par case_pre post_ctx ctx pos: list_failesc_context = 
  if case_pre then
    let post = formula_of_list_failesc_context post_ctx in
    let non_heap_ctx = remove_heap_list_failesc_ctx ctx in
    compose_list_failesc_context_formula_for_par case_pre non_heap_ctx post pos
  else
    let non_lend_post_ctx = remove_lend_list_failesc_ctx post_ctx in
    let non_lend_post = formula_of_list_failesc_context non_lend_post_ctx in
    compose_list_failesc_context_formula_for_par case_pre ctx non_lend_post pos

let compose_list_failesc_contexts_for_par case_pre post_ctx ctx pos: list_failesc_context = 
  let pr1 = !print_list_failesc_context in
  let pr2 b = if b then "FOR CASE POST" else "FOR PAR POST" in  
  Debug.no_3 "compose_list_failesc_contexts_for_par" pr2 pr1 pr1 pr1
      (fun _ _ _ -> compose_list_failesc_contexts_for_par case_pre post_ctx ctx pos) 
      case_pre post_ctx ctx

let prepare_list_failesc_ctx_for_par f_ent (vp: vperm_sets) (lh: CF.formula) ctx pos =
  (* Calculate resiue heap and pure part to add back to par_pre_ctx  *)
  (* vp * h_1 * h_2 & p |- vpp * h_1[@L] ~> h_2 * pr                 *)
  (* vp |- vpp ~> vpr                                                *)
  (* Output:                                                         *)
  (*   par_pre_ctx: vpp * h1@L * h2 & pr                             *)
  (*   rem_ctx: vpr * h_1                                            *)
  let non_lend_lh, lh_vars = CF.remove_lend_ann_formula lh in
  let vp_non_lend_lh = set_vperm_sets_formula vp non_lend_lh in
  let rem_ctx, _ = f_ent ctx vp_non_lend_lh in
  let rem_ctx = clean_es_heap_list_failesc_ctx_for_par lh_vars rem_ctx in
  (* let rem_ctx = CF.remove_heap_list_failesc_ctx rem_ctx in *)
  if not (CF.isSuccessListFailescCtx_new rem_ctx) then
    let msg = ("Variable permission/Heap requirement of par cannot be satisfied.") in
    (Debug.print_info ("(" ^ (Cprinter.string_of_label_list_failesc_context rem_ctx) ^ ") ") msg pos;
    Debug.print_info ("(Cause of Par Failure)") (Cprinter.string_of_failure_list_failesc_context rem_ctx) pos;
    Err.report_error { Err.error_loc = pos; Err.error_text = msg })
  else
    (* Add back lend heap for par and normal heap for rem *)
    let par_pre_ctx = compose_list_failesc_context_formula_for_par false rem_ctx lh pos in
    let rem_ctx = compose_list_failesc_context_formula_for_par false 
      (CF.remove_heap_list_failesc_ctx rem_ctx) non_lend_lh pos in
    let par_pre_ctx = set_vperm_sets_list_failesc_ctx vp par_pre_ctx in
    (* let prepare_es_for_par vp es =                                                   *)
    (*   (* Set INF_PAR for proving pre-condition of each par's case *)                 *)
    (*   es.es_infer_obj # set INF_PAR; (* Setting INF_PAR here also affects rem_ctx *) *)
    (*   Ctx { es with es_formula = set_vperm_sets_formula vp es.es_formula; }          *)
    (* in                                                                               *)
    (* let par_pre_ctx = transform_list_failesc_context                                 *)
    (*   (idf, idf, (prepare_es_for_par vp)) par_pre_ctx in                             *)
    par_pre_ctx, rem_ctx

let prepare_list_failesc_ctx_for_par f_ent (vp: vperm_sets) (lh: CF.formula) ctx pos =
  let pr1 = !print_list_failesc_context in
  let pr2 = !CF.print_formula in
  let prr (pre, rem) = ("\nPAR_PRE_CTX:\n" ^ (pr1 pre) ^ "\nREM_CTX:\n" ^ (pr1 rem)) in 
  Debug.no_2 "prepare_list_failesc_ctx_for_par" pr1 pr2 prr
      (fun _ _ -> prepare_list_failesc_ctx_for_par f_ent vp lh ctx pos) ctx lh

(* let update_vperm_sets f vps =                                                  *)
(*   match f with                                                                 *)
(*   | Base b -> Base { b with formula_base_vperm = vps; }                        *)
(*   | Exists e -> Exists { e with formula_exists_vperm = vps; }                  *)
(*   | Or _ -> report_error no_pos "Unexpected OR formula when update_vperm_sets" *)

(******************************************************************************)

exception Vperm_Entail_Fail of (string * spec_var * vp_ann * vp_ann)

type vperm_res = 
  | Fail of CF.list_context
  | Succ of CF.entail_state

let ann_set_of_vperm_sets vps = 
  let full_vars = List.map (fun v -> (v, VP_Full)) vps.vperm_full_vars in
  let lend_vars = List.map (fun v -> (v, VP_Lend)) vps.vperm_lend_vars in
  let value_vars = List.map (fun v -> (v, VP_Value)) vps.vperm_value_vars in
  let zero_vars = List.map (fun v -> (v, VP_Zero)) vps.vperm_zero_vars in
  let frac_vars = List.map (fun (f,v) -> (v,VP_Frac f)) vps.vperm_frac_vars in
  (* TODO:WN *)
  (* let frac_vars = List.concat (List.map (fun (fperm, svl) ->  *)
  (*     List.map (fun v -> (v, VP_Frac fperm)) svl) vps.vperm_frac_vars) in *)
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
            | VP_Frac f -> { vps with vperm_frac_vars = vps.vperm_frac_vars @ [(f,v)]}
                  (* let fperm_svl, others = List.partition (fun (vf, _) -> Frac.eq_frac fperm vf) vps.vperm_frac_vars in *)
                  (* let fperm_svl = v::(List.concat (List.map snd fperm_svl)) in *)
                  (* { vps with vperm_frac_vars = others @ [(fperm, fperm_svl)] } *)
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
            let _, rhs_ann = List.find (fun (vr, _) -> eq_spec_var_unp vl vr) rs in
            let rem_rs = List.filter (fun (vr, _) -> not (eq_spec_var_unp vl vr)) rs in
            (vl, lhs_ann, rhs_ann)::ps, ls, rem_rs
          with Not_found -> (ps, (vl, lhs_ann)::ls, rs)

let vperm_entail_var ?(ver_post_flag=false) ?(par_flag=false) sv lhs_ann rhs_ann = 
  (* let ver_post_flag = es.CF.es_infer_obj # is_ver_post || infer_const_obj # is_ver_post in *)
  (* let par_flag = es.CF.es_infer_obj # is_par || infer_const_obj # is_par in *)
  let err s = Vperm_Entail_Fail (s,sv, lhs_ann, rhs_ann) in
  let rec aux lhs_ann rhs_ann =
    match lhs_ann with
      | VP_Full ->
            begin match rhs_ann with
              | VP_Full -> VP_Zero
              | VP_Lend -> 
                    if par_flag then raise (err "Par") 
                    else if ver_post_flag then raise (err "verify_post")
                    else VP_Full 
              | VP_Value -> 
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Full
              | VP_Zero -> VP_Full
              | VP_Frac f -> aux (VP_Frac Frac.full2frac) rhs_ann
            end
      | VP_Lend ->
            begin match rhs_ann with
              | VP_Full -> raise (err "")
              | VP_Lend -> 
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Lend
              | VP_Value -> 
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Lend
              | VP_Zero -> VP_Lend
              | VP_Frac f -> raise (err "lend -> frac")
            end
      | VP_Value ->
            begin match rhs_ann with
              | VP_Full -> 
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Zero
              | VP_Lend -> 
                    (* VP_Value (\* TODO: to check *\) *)
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Value
              | VP_Value -> 
                    if ver_post_flag then raise (err "verify_post")
                    else VP_Value
              | VP_Zero -> VP_Value
              | VP_Frac f -> aux (VP_Frac Frac.value2frac) rhs_ann
            end
      | VP_Zero ->
            begin match rhs_ann with
              | VP_Zero -> VP_Zero
              | _ -> raise (err "")
            end
      | VP_Frac f ->
            begin match rhs_ann with
              | VP_Zero -> lhs_ann
              | VP_Full ->  aux lhs_ann (VP_Frac Frac.full2frac)
              | VP_Value -> 
                    if ver_post_flag then raise (err "verify_post")
                    else lhs_ann
              | VP_Lend -> 
                    if ver_post_flag then raise (err "verify_post")
                    else lhs_ann
              | VP_Frac f_post ->
                    if Frac.less_eq_frac f_post f
                    then VP_Frac (Frac.subtract f f_post)
                    else raise (err "insufficient to subtract")
            end
  in aux lhs_ann rhs_ann
   (* | _ -> lhs_ann*)

(* let vperm_entail_var es sv lhs_ann rhs_ann =  *)
(*   Debug.no_3 "vperm_entail_var" pr_sv pr_ann pr_ann pr_none (fun _ _ _ -> vperm_entail_var es sv lhs_ann rhs_ann) sv lhs_ann rhs_ann  *)

let mkFailCtx_vp msg estate conseq pos = 
  (* let msg = "Error in VPerm entailment: " ^ msg in *)
  let rhs_b = extr_rhs_b conseq in
  let estate = { estate with es_formula = substitute_flow_into_f !Exc.GTable.top_flow_int estate.es_formula } in
  mkFailCtx_in (
      Basic_Reason (mkFailContext msg estate (Base rhs_b) None pos,
      mk_failure_may msg logical_error, estate.es_trace)) (Ctx {estate with es_formula = CF.substitute_flow_into_f !error_flow_int estate.es_formula}) (mk_cex true)

let vperm_entail_set ?(par_flag=false) ?(ver_post_flag=false) ?(classic_flag=false) lhs_vperm_sets rhs_vperm_sets =
    let pr_vp = pr_pair !print_sv string_of_vp_ann in
    let lhs_vperm_sets = CVP.norm_vperm_sets lhs_vperm_sets in
    let rhs_vperm_sets = CVP.norm_vperm_sets rhs_vperm_sets in
    let las = ann_set_of_vperm_sets lhs_vperm_sets in
    let ras = ann_set_of_vperm_sets rhs_vperm_sets in
    let pas, rem_las, rem_ras = pair_ann_sets las ras in
    let err_vperm_sets = lhs_vperm_sets in
    let non_zero_vps = List.find_all (fun (_, ann) -> not (CVP.is_Zero ann)) rem_ras in
    if (non_zero_vps != []) then
      let msg = 
        "Mismatch non-zero variable permission in consequent " ^
            (pr_list pr_vp non_zero_vps) in 
      (* let fctx = mkFailCtx_vp msg estate conseq pos in *)
      (* Fail fctx *)
      Some msg,err_vperm_sets
    else
      try
        let res_vas = List.map (fun (v, la, ra) -> (v, vperm_entail_var ~par_flag:par_flag ~ver_post_flag:ver_post_flag (* estate *) v la ra)) pas in
        let res_vps = vperm_sets_of_ann_set (rem_las @ res_vas) in
        if classic_flag && (CVP.is_leak_vperm res_vps) then 
          (* TODO:WN *)
          let vp_str = !print_vperm_sets res_vps in
          let () = x_tinfo_hp (add_str "residue vperm" !print_vperm_sets) res_vps no_pos in
          let msg = " var permission leakage "^vp_str in
          (* let fctx = mkFailCtx_vp msg estate conseq pos in *)
          (* Fail fctx *)
          Some msg, err_vperm_sets
        else 
          (* let res_f = set_vperm_sets_formula res_vps estate.es_formula in *)
          (* let estate = { estate with es_formula = res_f; } in *)
          None, res_vps
      with (Vperm_Entail_Fail (s,sv, lhs_ann, rhs_ann)) ->
          let m = if s="" then "" else "(under "^s^") " in
          let msg = (pr_vp (sv, lhs_ann)) ^ " cannot satisfy "^m^ (pr_vp (sv, rhs_ann)) in
          (* let fctx = mkFailCtx_vp msg estate conseq pos in *)
          (* Fail fctx *)
          Some msg, err_vperm_sets

let vperm_entail_set ?(par_flag=false) ?(ver_post_flag=false) ?(classic_flag=false) lhs_vperm_sets rhs_vperm_sets =
  if not (!Globals.ann_vp) then None,CVP.empty_vperm_sets
  else
    let pr1 = !CVP.print_vperm_sets in
    let pr2 = pr_pair (pr_option pr_id) !CVP.print_vperm_sets in
    Debug.no_2 "vperm_entail_set" pr1 pr1 pr2
        (fun _ _ -> vperm_entail_set  ~par_flag ~ver_post_flag ~classic_flag lhs_vperm_sets rhs_vperm_sets) lhs_vperm_sets rhs_vperm_sets

let vperm_entail_rhs estate conseq pos =
  let par_flag = estate.CF.es_infer_obj # is_par || infer_const_obj # is_par in
  let ver_post_flag = estate.CF.es_infer_obj # is_ver_post || infer_const_obj # is_ver_post in
  let classic_flag = estate.CF.es_infer_obj # is_classic || infer_const_obj # is_classic in
  if not (!Globals.ann_vp) then Succ estate
  else
    let lhs_vperm_sets = collect_vperm_sets estate.es_formula in
    let rhs_vperm_sets = collect_vperm_sets conseq in
    let resopt,res_vps = vperm_entail_set ~par_flag:par_flag ~ver_post_flag:ver_post_flag ~classic_flag:classic_flag lhs_vperm_sets  rhs_vperm_sets in
    match resopt with
      | None ->
            let res_f = set_vperm_sets_formula res_vps estate.es_formula in
            let estate = { estate with es_formula = res_f; }
            in Succ estate
      | Some msg -> 
            let fctx = mkFailCtx_vp msg estate conseq pos in
            Fail fctx

    (* let pr_vp = pr_pair !print_sv string_of_vp_ann in *)
    (* let lhs_vperm_sets = CVP.norm_vperm_sets lhs_vperm_sets in *)
    (* let rhs_vperm_sets = CVP.norm_vperm_sets rhs_vperm_sets in *)

    (* let las = ann_set_of_vperm_sets lhs_vperm_sets in *)
    (* let ras = ann_set_of_vperm_sets rhs_vperm_sets in *)
    (* let pas, rem_las, rem_ras = pair_ann_sets las ras in *)

    (* let non_zero_vps = List.find_all (fun (_, ann) -> not (CVP.is_Zero ann)) rem_ras in *)
    (* if (non_zero_vps != []) then *)
    (*   let msg =  *)
    (*     "Mismatch non-zero variable permission in consequent " ^ *)
    (*         (pr_list pr_vp non_zero_vps) in  *)
    (*   let fctx = mkFailCtx_vp msg estate conseq pos in *)
    (*   Fail fctx *)
    (* else *)
    (*   try *)
    (*     let res_vas = List.map (fun (v, la, ra) -> (v, vperm_entail_var ~par_flag:par_flag ~ver_post_flag:ver_post_flag (\* estate *\) v la ra)) pas in *)
    (*     let res_vps = vperm_sets_of_ann_set (rem_las @ res_vas) in *)
    (*     if classic_flag && (CVP.is_leak_vperm res_vps) then  *)
    (*       (\* TODO:WN *\) *)
    (*       let vp_str = !print_vperm_sets res_vps in *)
    (*       let () = x_tinfo_hp (add_str "residue vperm" !print_vperm_sets) res_vps no_pos in *)
    (*       let msg = " var permission leakage "^vp_str in *)
    (*       let fctx = mkFailCtx_vp msg estate conseq pos in *)
    (*       Fail fctx *)
    (*     else  *)
    (*       let res_f = set_vperm_sets_formula res_vps estate.es_formula in *)
    (*       let estate = { estate with es_formula = res_f; } *)
    (*       in Succ estate *)
    (*   with (Vperm_Entail_Fail (s,sv, lhs_ann, rhs_ann)) -> *)
    (*       let m = if s="" then "" else "(under "^s^") " in *)
    (*       let msg = (pr_vp (sv, lhs_ann)) ^ " cannot satisfy "^m^ (pr_vp (sv, rhs_ann)) in *)
    (*       let fctx = mkFailCtx_vp msg estate conseq pos in *)
    (*       Fail fctx *)

let vperm_entail_rhs estate conseq pos =
  if not (!Globals.ann_vp) then Succ estate
  else
    let pr1 = !CF.print_entail_state in
    let pr2 = !CF.print_formula in
    let pr3 = !CF.print_list_context in
    let pr res = match res with
      | Fail ctx -> pr3 ctx
      | Succ es -> pr1 es 
    in 
    Debug.no_2 "vperm_entail_rhs" pr1 pr2 pr 
        (fun _ _ -> vperm_entail_rhs estate conseq pos) estate conseq

(*************************************************************************************)
(************************************* OLD STUFFS ************************************)
(*************************************************************************************)

(* let extract_vperm_b_formula bf =                                                  *)
(*   let (pf, _) = bf in                                                             *)
(*   match pf with                                                                   *)
(*   | VarPerm vp -> Some vp                                                         *)
(*   | _ -> None                                                                     *)

(* let extract_vperm_formula f =                                                     *)
(*   match f with                                                                    *)
(*   | BForm (bf, _) -> extract_vperm_b_formula bf                                   *)
(*   | _ -> None                                                                     *)

(* let strip_vperm_pure_only f =                                                     *)
(*   let mf_ls = split_conjunctions f in                                             *)
(*   let (vps, other_p) = List.fold_left (fun (av, ap) f ->                          *)
(*     let vp = extract_vperm_formula f in                                           *)
(*     match vp with                                                                 *)
(*     | Some vp -> (av @ [vp], ap)                                                  *)
(*     | None -> (av, ap @ [f])) ([], []) mf_ls                                      *)
(*   in                                                                              *)
(*   (CVP.merge_vperm_anns vps, join_conjunctions other_p)                           *)

(* let def_lbl l = LO.is_common l                                                    *)

(* let def_lbl l =                                                                   *)
(*   Debug.no_1 "def_lbl" (LO.string_of) string_of_bool def_lbl l                    *)

(* let strip_vperm_list ls =                                                         *)
(*   let rec aux xs =                                                                *)
(*     match xs with                                                                 *)
(*     | [] -> ([], [])                                                              *)
(*     | ((l, f) as ff)::xs ->                                                       *)
(*       let (l0, r0) = aux xs in                                                    *)
(*       let (l1, r1) =                                                              *)
(*         if def_lbl l then                                                         *)
(*           let (l2, f2) = strip_vperm_pure_only f in                               *)
(*           ([l2], (l, f2))                                                         *)
(*         else ([], ff)                                                             *)
(*       in (l1 @ l0, r1::r0)                                                        *)
(*   in aux ls                                                                       *)

(* let strip_vperm_pure_andlist ls =                                                 *)
(*   List.fold_left (fun (av, af) f ->                                               *)
(*     match f with                                                                  *)
(*     | AndList ls ->                                                               *)
(*       let (vps, nls) = strip_vperm_list ls in                                     *)
(*       (av @ vps, (AndList nls)::af)                                               *)
(*     | _ ->                                                                        *)
(*       let vp, rf = strip_vperm_pure_only f in                                     *)
(*       (av @ [vp], af @ [rf])) ([], []) ls                                         *)

(* let strip_vperm_pure f =                                                          *)
(*   let mf_ls = split_conjunctions f in                                             *)
(*   let (vps, fs) = strip_vperm_pure_andlist mf_ls in                               *)
(*   (CVP.merge_vperm_sets vps, join_conjunctions fs)                                *)

(* let strip_vperm_memo_grp mg =                                                     *)
(*   let b_vperm, memo_grp_cons = List.fold_left (fun (av, am) mc ->                 *)
(*     let vp = extract_vperm_b_formula mc.MCD.memo_formula in                       *)
(*     match vp with                                                                 *)
(*     | Some vp -> (av @ [vp], am)                                                  *)
(*     | None -> (av, am @ [mc])) ([], []) mg.MCD.memo_group_cons                    *)
(*   in                                                                              *)
(*   let b_vps = CVP.merge_vperm_anns b_vperm in                                     *)
(*   let vps, memo_grp_slice = List.split (List.map                                  *)
(*     (fun f -> strip_vperm_pure f) mg.MCD.memo_group_slice) in                     *)
(*   let vps = CVP.merge_vperm_sets (b_vps::vps) in                                  *)
(*   (vps, { mg with                                                                 *)
(*     MCD.memo_group_cons = memo_grp_cons;                                          *)
(*     MCD.memo_group_slice = memo_grp_slice; })                                     *)

(* let strip_vperm_mix_formula (mf: MCP.mix_formula) =                               *)
(*   match mf with                                                                   *)
(*   | MCP.OnePF f ->                                                                *)
(*     let vps, f = strip_vperm_pure f in                                            *)
(*     (vps, MCP.OnePF f)                                                            *)
(*   | MCP.MemoF mp ->                                                               *)
(*     let vps_list, mp = List.split (List.map strip_vperm_memo_grp mp) in           *)
(*     (CVP.merge_vperm_sets vps_list, MCP.MemoF mp)                                 *)

(* let strip_vperm_mix_formula mf =                                                  *)
(*   let pr1 = !CVP.print_vperm_sets in                                              *)
(*   let pr2 = !MCP.print_mix_formula in                                             *)
(*   Debug.no_1 "strip_vperm_mix_formula" pr2 (pr_pair pr1 pr2)                      *)
(*   strip_vperm_mix_formula mf                                                      *)

(* let strip_vperm_formula (f: CF.formula) : vperm_sets * CF.formula =               *)
(*   let _, pure_f, _, _, _, _ = CF.split_components f in                            *)
(*   let (vps, other_p) = strip_vperm_mix_formula pure_f in                          *)
(*   (* Using transform_formula to update the pure part of f *)                      *)
(*   let f_e_f _ = None in                                                           *)
(*   let f_f _ = None in                                                             *)
(*   let f_h_f e = Some e in                                                         *)
(*   let f_m mp = Some (MCP.memo_of_mix other_p) in                                  *)
(*   let f_a _ = None in                                                             *)
(*   let f_p_f pf = Some (MCP.pure_of_mix other_p) in                                *)
(*   let f_b _ = None in                                                             *)
(*   let f_e _ = None in                                                             *)
(*   (vps, CF.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_p_f, f_b, f_e)) f)  *)

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
(*   (* let () = print_endline ("zero_vars = " ^ (Cprinter.string_of_spec_var_list lhs_zero_vars)) in *)                *)
(*   let () = if (!Globals.ann_vp) && (lhs_zero_vars!=[] || rhs_vperms!=[]) then                                        *)
(*     x_dinfo_pp ("heap_entail_empty_rhs_heap: checking " ^                                                   *)
(*                         (string_of_vp_ann VP_Zero) ^                                                                *)
(*                         (Cprinter.string_of_spec_var_list lhs_zero_vars) ^                                          *)
(*                         " |- "  ^ (pr_list Cprinter.string_of_pure_formula rhs_vperms)^"\n") pos                    *)
(*   in                                                                                                                *)
(*   let rhs_val, rhs_vrest = List.partition (fun f -> CP.is_varperm_of_typ f VP_Value) rhs_vperms in                  *)
(*   (* let rhs_ref, rhs_vrest2 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Ref) rhs_vrest in *)              *)
(*   let rhs_full, rhs_vrest3 = List.partition (fun f -> CP.is_varperm_of_typ f VP_Full) rhs_vrest in                  *)
(*   (* let () = print_endline ("\n LDK: " ^ (pr_list Cprinter.string_of_pure_formula rhs_vrest3)) in *)                *)
(*   let () = if (rhs_vrest3!=[]) then                                                                                  *)
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
(*             let () = x_dinfo_pp ("heap_entail_empty_rhs_heap" ^ msg) pos in                                  *)
(*             msg                                                                                                     *)
(*           else ""                                                                                                   *)
(*         in                                                                                                          *)
(*         let msg2 = if tmp1!=[] then                                                                                 *)
(*               let msg = (": pass-by-val var " ^ (Cprinter.string_of_spec_var_list (tmp1)) ^                         *)
(*                          " cannot have possibly zero permission" ^ "\n") in                                         *)
(*               let () = x_dinfo_pp ("heap_entail_empty_rhs_heap" ^ msg) pos in                                *)
(*               msg                                                                                                   *)
(*             else ""                                                                                                 *)
(*         in                                                                                                          *)
(*         let msg3 = if tmp3!=[] then                                                                                 *)
(*               let msg = (": full permission var " ^ (Cprinter.string_of_spec_var_list (tmp3)) ^                     *)
(*                          " cannot have possibly zero permission" ^ "\n") in                                         *)
(*               let () = x_dinfo_pp ("heap_entail_empty_rhs_heap" ^ msg) pos in                                *)
(*               msg                                                                                                   *)
(*             else ""                                                                                                 *)
(*         in                                                                                                          *)
(*       x_dinfo_pp ("heap_entail_empty_rhs_heap: failed in entailing variable permissions in conseq\n") pos;  *)
(*       x_dinfo_pp ("heap_entail_empty_rhs_heap: formula is not valid\n") pos;                                *)
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
