#include "xdebug.cppo"
open VarGen
(*
  The frontend engine of SLEEK.
*)

open Globals
open Wrapper
open Others
open Sleekcommons
open Gen.Basic
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Perm
open Label_only

let process_selective_iview_decls is_all iprog iviews =
  let iviews = if is_all then iprog.I.prog_view_decls else iviews in
  let tmp_views = List.map (fun pdef ->
      let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
      let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
      let wf = Astsimp.case_normalize_struc_formula_view 11 iprog h p pdef.Iast.view_formula false false false [] in
      let inv_lock = pdef.I.view_inv_lock in
      let inv_lock = (
        match inv_lock with
        | None -> None
        | Some f ->
          let new_f = Astsimp.case_normalize_formula iprog h f in (*TO CHECK: h or p*)
          Some new_f
      ) in
      let new_pdef = {pdef with Iast.view_formula = wf;Iast.view_inv_lock = inv_lock} in
      new_pdef
    ) iviews in
  let () = y_tinfo_hp (add_str "view_decls" (pr_list Iprinter.string_of_view_decl)) iprog.I.prog_view_decls in
  let () = y_tinfo_hp (add_str "iviews" (pr_list Iprinter.string_of_view_decl)) iviews in
  let () = y_tinfo_hp (add_str "tmp_views" (pr_list Iprinter.string_of_view_decl)) tmp_views in
  let tmp_views,ls_mut_rec_views = (x_add_1 Astsimp.order_views (List.rev tmp_views)) in
  let () = x_tinfo_pp "after order_views" no_pos in
  let _ = Iast.set_check_fixpt iprog iprog.I.prog_data_decls tmp_views in
  let () = x_tinfo_pp "after check_fixpt" no_pos in
  let () = 
    if is_all then iprog.I.prog_view_decls <- tmp_views
    else 
      (* iprog.I.prog_view_decls <- (iprog.I.prog_view_decls @ iviews) *)
      List.iter (x_add_1 (Cprog_sleek.update_view_decl_iprog ~update_scc:true)) iviews
  in
  (* collect immutable info for splitting view params *)
  let _ = List.map (fun v -> 
      v.I.view_imm_map <- Immutable.icollect_imm v.I.view_formula 
                                                 v.I.view_vars 
                                                 v.I.view_data_name 
                                                 iprog.I.prog_data_decls) 
      iprog.I.prog_view_decls in
  let _ = x_tinfo_hp (add_str "view_decls:" 
      (pr_list (pr_list (pr_pair Iprinter.string_of_imm string_of_int)))) 
      (List.map (fun v -> v.I.view_imm_map) iprog.I.prog_view_decls) no_pos in
  let tmp_views_derv, tmp_views = List.partition (fun v -> v.I.view_derv) tmp_views in
  (* let all_mutrec_vnames = (List.concat ls_mut_rec_views) in *)
  (*   let cviews0,_ = List.fold_left (fun (transed_views view -> *)
  (*       let nview = Astsimp.trans_view iprog mutrec_vnames *)
  (*         transed_views [] view in *)
  (*       transed_views@[nview] *)
  (* ) ([]) tmp_views in *)
  (*   let cviews0 = Fixcalc.compute_inv_mutrec ls_mut_rec_views cviews0a in *)
  let _ = if !Globals.smt_compete_mode then
      let _ = Debug.ninfo_hprint (add_str "tmp_views" (pr_list (fun vdcl -> vdcl.Iast.view_name))) tmp_views no_pos in
      let num_vdecls = List.length tmp_views  in
      (* let _ = if num_vdecls <= gen_baga_inv_threshold then *)
      (*     (\* let _ = Globals.gen_baga_inv := false in *\) *)
      (*   (\* let _ = Globals.dis_pred_sat () in *\) *)
      (*     () *)
      (* else *)
      (*   let _ = Globals.lemma_gen_unsafe := false in *)
      (*   (\* let _ = Globals.lemma_syn := false in *\) *)
      (*   () *)
      (* in *)
      let _ =  if !Globals.graph_norm &&  num_vdecls > !graph_norm_decl_threshold then
          let _ = Globals.graph_norm := false in
          ()
        else ()
      in
      (* let _ = if ls_mut_rec_views != [] (\* || num_vdecls > 2 *\) then *)
      (*   (\* lemma_syn does not work well with mut_rec views. Loc: to improve*\) *)
      (*   let _ = Globals.lemma_syn := false in *)
      (*   () *)
      (* else () in *)
      ()
    else ()
  in
  (* let cur_lem_syn = !Globals.lemma_syn in        *)
  (* (*turn off generate lemma during trans views*) *)
  (* let _ = Globals.lemma_syn := false in          *)
  let tmp_views = List.filter (fun v -> v.Iast.view_kind != View_HREL) tmp_views in
  let cviews0 = x_add Astsimp.trans_views iprog ls_mut_rec_views (List.map (fun v -> (v,[])) tmp_views) in
  (* x_tinfo_pp "after trans_view" no_pos; *)
  (* derv and spec views *)
  let tmp_views_derv1 = Astsimp.mark_rec_and_der_order tmp_views_derv in
  (* TODO: this code is duplicated *)
  let cviews_derv = List.fold_left (fun norm_views v ->
      let der_view = x_add_1 Derive.trans_view_dervs iprog Rev_ast.rev_trans_formula Astsimp.trans_view [] norm_views v in
      (norm_views@der_view)
    ) cviews0 tmp_views_derv1 in
  let _ = x_tinfo_hp (add_str "derv length" (fun ls -> string_of_int (List.length ls))) tmp_views_derv1 no_pos in
  cviews_derv

let process_selective_iview_decls is_all iprog iviews =
  let pr1 = pr_list Iprinter.string_of_view_decl in
  let pr2 = pr_list Cprinter.string_of_view_decl in
  Debug.no_2 "process_selective_iview_decls" string_of_bool pr1 pr2 
    (fun _ _ -> process_selective_iview_decls is_all iprog iviews)
    is_all (if is_all then iprog.I.prog_view_decls else iviews)

let process_all_iview_decls iprog = 
  process_selective_iview_decls true iprog [] (* process all iprog.I.process_selective_iview_decls *)

let norm_cview_decls iprog cprog cviews =
  let old_view_decls = cprog.Cast.prog_view_decls in
  let () = y_tinfo_hp (add_str "old_view_decls" (pr_list Cprinter.string_of_view_decl)) old_view_decls in
  let _ = cprog.Cast.prog_view_decls <- old_view_decls@cviews in
  let () = y_tinfo_hp (add_str "cviews(1)" (pr_list Cprinter.string_of_view_decl(*_short*))) cviews in
  let cviews1 =
    if !Globals.norm_extract then
      Norm.norm_extract_common iprog cprog cviews (List.map (fun vdef -> vdef.Cast.view_name) cviews)
    else cviews
  in
  let cviews2 =
    if !Globals.norm_cont_analysis then
      let cviews2a = Norm.cont_para_analysis cprog cviews1 in
      cviews2a
    else
      cviews1
  in
  let _ = cprog.Cast.prog_view_decls <- old_view_decls@cviews2 in
  let () = y_tinfo_hp (add_str "cviews(2)" (pr_list Cprinter.string_of_view_decl(*_short*))) cviews2 in
  let _ =  (List.map (fun vdef -> x_add Astsimp.compute_view_x_formula cprog vdef !Globals.n_xpure) cviews2) in
  x_tinfo_pp "after compute_view" no_pos;
  let _ = (List.map (fun vdef -> Astsimp.set_materialized_prop vdef) cviews2) in
  let cviews3 = (List.map (fun vdef -> Norm.norm_formula_for_unfold cprog vdef) cviews2) in
  let _ = cprog.Cast.prog_view_decls <-  old_view_decls@cviews3 in
  let () = y_tinfo_hp (add_str "cviews(3)" (pr_list Cprinter.string_of_view_decl(*_short*))) cviews3 in
  x_tinfo_pp "after materialzed_prop" no_pos;
  cviews3

let norm_cview_decls iprog cprog cviews =
  let pr = pr_list Cprinter.string_of_view_decl in
  Debug.no_1 "norm_cview_decls" pr pr
    (fun _ -> norm_cview_decls iprog cprog cviews) cviews
