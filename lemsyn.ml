open Globals
open Wrapper
open Gen
open Others
open Label_only
open Exc.GTable

module I  = Iast
module C  = Cast
module IF = Iformula
module IP = Ipure
module CF = Cformula
(* module CFU = Cfutil *)
module CP = Cpure
module MCP = Mcpure
module H  = Hashtbl


let get_eqset puref =
  let (subs,_) = CP.get_all_vv_eqs puref in
  let eqset = CP.EMapSV.build_eset subs in
  eqset
(*
lem_type = 0: LEFT
lem_type = 1 :RIGHT
lem_type = 2: INFER
*)
let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
      lhs_node0 lhs_b0 rhs_node0 rhs_b0 =
  let lsvl = CF.fv (CF.Base lhs_b0) in
  let rsvl = CF.fv (CF.Base rhs_b0) in
  let ss1 = List.fold_left (fun r ((CP.SpecVar (t, id, p)) as sv1) ->
      if p = Primed then
        r@[(sv1, CP.SpecVar (t, fresh_name (), Unprimed))]
      else r
  ) [] (CP.remove_dups_svl (lsvl@rsvl)) in
  let lhs_node = CF.h_subst ss1 lhs_node0 in
  let rhs_node = CF.h_subst ss1 rhs_node0 in
  let lhs_b0 = CF.subst_b ss1 lhs_b0 in
  let rhs_b0 = CF.subst_b ss1 rhs_b0 in
  let lr = match lhs_node with
    | CF.ViewNode vl -> vl.CF.h_formula_view_node
    | CF.DataNode dl -> dl.CF.h_formula_data_node
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let rr = match rhs_node with
    |  CF.ViewNode vr -> vr.CF.h_formula_view_node
    |  CF.DataNode dr -> dr.CF.h_formula_data_node
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  try
    (*TEMP*)
    (* let lf1 = CF.subst lss (CF.formula_of_heap lhs_node no_pos) in *)
    (* let rf1 = CF.subst rss (CF.formula_of_heap rhs_node no_pos) in *)
    (*NORM lhs-rhs*)
    let ( _,mix_lf,_,_,_) = CF.split_components (CF.Base lhs_b0) in
    let l_emap0 = get_eqset (MCP.pure_of_mix mix_lf) in
    let (_,mix_rf0,_,_,_) = CF.split_components (CF.Base rhs_b0) in
    let r_emap0 = get_eqset (MCP.pure_of_mix mix_rf0) in
    let r_eqsetmap0 = CP.EMapSV.build_eset es.CF.es_rhs_eqset in
    let lhs_b1, rhs_b1, _ = Cfutil.smart_subst_new lhs_b0 rhs_b0 []
           l_emap0 r_emap0 r_eqsetmap0 [] ([lr;rr])
    in
     (*left*)
    (* let lr = lview.CF.h_formula_view_node in *)
    let lselfr = CP.SpecVar (CP.type_of_spec_var lr, self, Unprimed) in
    let cl_lseffr0 = CP.EMapSV.find_equiv_all lr l_emap0 in
    let cl_lseffr = if cl_lseffr0 = [] then [lr] else cl_lseffr0 in
    let lss = List.map (fun lr -> (lr, lselfr)) cl_lseffr in
    (*right*)
    (* let rr = rview.CF.h_formula_view_node in *)
    let rselfr = CP.SpecVar (CP.type_of_spec_var rr, self, Unprimed) in
    let cl_rseffr0 = CP.EMapSV.find_equiv_all rr (CP.EMapSV.merge_eset l_emap0 r_emap0) in
    let cl_rseffr = if cl_rseffr0 = [] then [rr] else cl_rseffr0 in
    (* let rss = List.map (fun rr -> (rr, rselfr)) cl_rseffr in *)
    (*LHS: find reachable heap + pure*)
    let lf1a = CF.subst_b lss lhs_b1 in
    let rf1a = CF.subst_b lss rhs_b1 in
    let lf1 = Cfutil.obtain_reachable_formula prog (CF.Base lf1a) [lselfr] in
    let rf1 = Cfutil.obtain_reachable_formula prog (CF.Base rf1a) [rselfr] in
    (* let lf1 = CF.subst lss  *)
    (*RHS: find reachable heap + pure*)
    let lf2 = formula_rev_fnc lf1 in
    let rf2 = formula_rev_fnc rf1 in
    (*gen lemma*)
    let lemma_name = "cyc" in
    let l_coer = match lem_type with
      | 0 -> I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE I.Left [] lf2 rf2
      | _ (*1*) -> I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE I.Right [] rf2 lf2
    in
    (*add lemma*)
    let iprog = I.get_iprog () in
    let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
    let _ = print_endline (" \n gen lemma:" ^ (Cprinter.string_of_formula lf1) ^ (if lem_type = 0 then " -> " else " <- ")
    ^ (Cprinter.string_of_formula rf1)) in
    ()
  with e ->
      let _ = print_endline (" \n gen lemma: Exception: " ^ (Printexc.to_string e) ) in ()

let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
      lhs_node lhsb rhs_node rhsb =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.string_of_h_formula in
  Debug.no_4 "LEMSYN.gen_lemma" pr2 pr1 pr2 pr1 pr_none
      (fun _ _ _ _ -> gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
          lhs_node lhsb rhs_node rhsb)
      lhs_node lhsb rhs_node rhsb

let add_ihprel iprog chp_dclrs=
  let rec process_one chps res=
    match chps with
      | [] -> res
      | chp::rest ->
            try
              let _ = I.look_up_hp_def_raw res chp.C.hp_name in
               process_one rest res
            with Not_found ->
                let n_ihp = {
                    I.hp_name = chp.C.hp_name;
                    I.hp_typed_inst_vars= List.map
                        (fun (CP.SpecVar (t,id,_), i) -> (t,id,i)) chp.C.hp_vars_inst;
                    I.hp_part_vars = chp.C.hp_part_vars;
                    I.hp_root_pos = chp.C.hp_root_pos;
                    I.hp_is_pre = chp.C.hp_is_pre;
                    I.hp_formula = IF.mkBase IF.HEmp (IP.mkTrue no_pos) top_flow [] no_pos;
                }
                in
                process_one rest (res@[n_ihp])
  in
  let nihp_dclr = process_one chp_dclrs iprog.I.prog_hp_decls in
  let _ = iprog.I.prog_hp_decls <- iprog.I.prog_hp_decls@nihp_dclr in
  nihp_dclr

let gen_lemma_infer_x (prog) ass_stk hpdef_stk
      formula_rev_fnc manage_unsafe_lemmas_fnc manage_infer_pred_lemmas_fnc trans_hprel_2_cview_fnc trans_formula_hp_2_view_fnc
      xpure_heap es lem_type h_vnode0 h_dnode0=
  let vnode0 = match h_vnode0 with
    | CF.ViewNode vl -> vl
    (* | CF.DataNode dl -> dl.CF.h_formula_data_node *)
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let dnode0 = match h_dnode0 with
    (* |  CF.ViewNode vr -> vr.CF.h_formula_view_node *)
    |  CF.DataNode dr -> dr
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  (*for subst*)
  let ( _,mf,_,_,_) = CF.split_components es.CF.es_formula in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let cl_dns = CF.find_close [dnode0.CF.h_formula_data_node] eqs in
  let inter_vargs = CP.intersect_svl cl_dns vnode0.CF.h_formula_view_arguments in
  let _ = Debug.info_hprint (add_str "cl_dns" !CP.print_svl) cl_dns no_pos in
  let _ = Debug.info_hprint (add_str "inter_vargs" !CP.print_svl) inter_vargs no_pos in
  let ss1 = List.map (fun sv -> (dnode0.CF.h_formula_data_node, sv)) inter_vargs in
  let ss2 = List.fold_left (fun r ((CP.SpecVar (t, id, p)) as sv1) ->
      if p = Primed then
        r@[(sv1, CP.SpecVar (t, id, Unprimed))]
      else r
  ) [] dnode0.CF.h_formula_data_arguments in
  let h_dnode1 = (CF.h_subst (ss1@ss2) h_dnode0) in
  let dnode1 = match h_dnode1 with
    (* |  CF.ViewNode vr -> vr.CF.h_formula_view_node *)
    |  CF.DataNode dr -> dr
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let h_vnode1 = CF.h_subst ss2 h_vnode0 in
  let vnode1 = match h_vnode1 with
    | CF.ViewNode vl -> vl
    (* | CF.DataNode dl -> dl.CF.h_formula_data_node *)
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  (*END*)
  (* let vdef = C.look_up_view_def_raw 43 prog.C.prog_view_decls vnode.CF.h_formula_view_name in *)
  let vself = CP.SpecVar (CP.type_of_spec_var vnode1.CF.h_formula_view_node, self, Unprimed) in
  let ss0 = [(vnode1.CF.h_formula_view_node, vself)] in
  let rhs,n_hp =  C.add_raw_hp_rel prog false false [(vself,I);(dnode1.CF.h_formula_data_node,NI)] no_pos in
  (*add ihpdecl*)
  let iprog = I.get_iprog () in
  let hpdclr = C.look_up_hp_def_raw prog.C.prog_hp_decls (CP.name_of_spec_var n_hp) in
  let nihp = add_ihprel iprog [hpdclr] in
  (*lemma infer*)
  let rhs = CF.mkStarH rhs h_dnode1 no_pos in
  let lf1 = CF.formula_of_heap (CF.h_subst ss0 h_vnode1) no_pos in
  let rf1 = CF.formula_of_heap rhs no_pos in
  let lf2 = formula_rev_fnc lf1 in
  let rf2 = formula_rev_fnc rf1 in
  (*gen lemma*)
  let lemma_name = "cyci" in
  let l_coer = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE I.Left [(CP.name_of_spec_var n_hp)] lf2 rf2 in
  (*backup*)
  let cur_ass = ass_stk# get_stk in
  let _ = ass_stk # reset in
  let cur_hpdefs =  hpdef_stk # get_stk in
  let _ = hpdef_stk # reset in
  let r1,hp_defs0,r3 = manage_infer_pred_lemmas_fnc [l_coer] iprog prog xpure_heap in
  (*transform inferred def*)
  let hp_defs = (* CF.rel_def_stk # get_stk *) hp_defs0 in
  let lem_name = if (hp_defs != []) then
    (*from unknown pred into view*)
    let proc_name = "lem_infer" in
    let n_cviews,chprels_decl = trans_hprel_2_cview_fnc iprog prog proc_name hp_defs in
    let in_hp_names = [n_hp] in
    (*transform formula*)
    let rf3 = trans_formula_hp_2_view_fnc iprog prog proc_name
       chprels_decl hp_defs [] rf1 in
    let rf4 = formula_rev_fnc rf3 in
    let lem_name = fresh_any_name lemma_name in
    let l_coer = I.mk_lemma (lem_name) LEM_UNSAFE I.Left [] lf2 rf4 in
    (*add lemma*)
    let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
    let _ = print_endline "\n*******relational definition ********" in
    let defs1 = if !Globals.print_en_tidy then List.map CF.rearrange_def (CF.rel_def_stk # get_stk) else
      (CF.rel_def_stk # get_stk) in
    let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
    let _ = print_endline (pr1 defs1) in
    let _ = print_endline (" \n gen lemma (infer):" ^ (Cprinter.string_of_formula lf1) ^ ( " -> " )
    ^ (Cprinter.string_of_formula rf3)) in
    ()
  else ()
  in
  (*restore*)
  let _ = ass_stk # reset in
  let _ = ass_stk # push_list cur_ass in
  let _ = hpdef_stk # reset in
  let _ = hpdef_stk # push_list cur_hpdefs in
  n_hp

let gen_lemma_infer prog ass_stk hpdef_stk formula_rev_fnc manage_unsafe_lemmas_fnc manage_infer_lemmas_fnc
      trans_hprel_2_cview_fnc trans_formula_hp_2_view_fnc xpure_heap
      es lem_type vnode dnode =
  let pr1 = Cprinter.prtt_string_of_h_formula  in
  Debug.no_3 "LEMSYN.gen_lemma_infer" pr1 pr1 string_of_int !CP.print_sv
      (fun _ _ _ -> gen_lemma_infer_x prog ass_stk hpdef_stk formula_rev_fnc manage_unsafe_lemmas_fnc manage_infer_lemmas_fnc
          trans_hprel_2_cview_fnc trans_formula_hp_2_view_fnc xpure_heap
          es lem_type vnode dnode)
      vnode dnode lem_type
