#include "xdebug.cppo"
open VarGen
open Globals
open Wrapper
open Gen
open Others
open Label_only
open Exc.GTable

(* module I  = Iast *)
module C  = Cast
(* module IF = Iformula *)
(* module IP = Ipure *)
(* module CF = Cformula *)
(* module CFU = Cfutil *)
module CP = Cpure
(* module MCP = Mcpure *)


let get_eqset puref =
  let (subs,_) = CP.get_all_vv_eqs puref in
  let eqset = CP.EMapSV.build_eset subs in
  eqset
(*
lem_type = 0: LEFT
lem_type = 1 :RIGHT
lem_type = 2: INFER
lem_type = 3: tail-rec vs. non tail-rec
*)
let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
    lhs_node0 lhs_b0 rhs_node0 rhs_b0 =
  let lsvl = Cformula.fv (Cformula.Base lhs_b0) in
  let rsvl = Cformula.fv (Cformula.Base rhs_b0) in
  let ss1 = List.fold_left (fun r ((CP.SpecVar (t, id, p)) as sv1) ->
      if p = Primed then
        r@[(sv1, CP.SpecVar (t, fresh_name (), Unprimed))]
      else r
    ) [] (CP.remove_dups_svl (lsvl@rsvl)) in
  let lhs_node = Cformula.h_subst ss1 lhs_node0 in
  let rhs_node = Cformula.h_subst ss1 rhs_node0 in
  let lhs_b0 = Cformula.subst_b ss1 lhs_b0 in
  let rhs_b0 = Cformula.subst_b ss1 rhs_b0 in
  let lr = match lhs_node with
    | Cformula.ViewNode vl -> vl.Cformula.h_formula_view_node
    | Cformula.DataNode dl -> dl.Cformula.h_formula_data_node
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let rr = match rhs_node with
    |  Cformula.ViewNode vr -> vr.Cformula.h_formula_view_node
    |  Cformula.DataNode dr -> dr.Cformula.h_formula_data_node
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let check_iden vn1 vn2=
    String.compare vn1.Cformula.h_formula_view_name vn2.Cformula.h_formula_view_name = 0 &&
    CP.eq_spec_var vn1.Cformula.h_formula_view_node vn2.Cformula.h_formula_view_node
  in
  try
    (*TEMP*)
    (* let lf1 = Cformula.subst lss (Cformula.formula_of_heap lhs_node no_pos) in *)
    (* let rf1 = Cformula.subst rss (Cformula.formula_of_heap rhs_node no_pos) in *)
    (*NORM lhs-rhs*)
    let ( _,mix_lf,_,_,_,_) = Cformula.split_components (Cformula.Base lhs_b0) in
    let l_emap0 = get_eqset (Mcpure.pure_of_mix mix_lf) in
    let (_,mix_rf0,_,_,_,_) = Cformula.split_components (Cformula.Base rhs_b0) in
    let r_emap0 = get_eqset (Mcpure.pure_of_mix mix_rf0) in
    let r_eqsetmap0 = CP.EMapSV.build_eset es.Cformula.es_rhs_eqset in
    let lhs_b1, rhs_b1, _,_ = Cfutil.smart_subst_new lhs_b0 rhs_b0 []
        l_emap0 r_emap0 r_eqsetmap0 [] ([lr;rr])
    in
    (*left*)
    (* let lr = lview.Cformula.h_formula_view_node in *)
    let lselfr = CP.SpecVar (CP.type_of_spec_var lr, self, Unprimed) in
    let cl_lseffr0 = CP.EMapSV.find_equiv_all lr l_emap0 in
    let cl_lseffr = if cl_lseffr0 = [] then [lr] else cl_lseffr0 in
    let lss = List.map (fun lr -> (lr, lselfr)) cl_lseffr in
    (*right*)
    (* let rr = rview.Cformula.h_formula_view_node in *)
    let rselfr = CP.SpecVar (CP.type_of_spec_var rr, self, Unprimed) in
    let cl_rseffr0 = CP.EMapSV.find_equiv_all rr (CP.EMapSV.merge_eset l_emap0 r_emap0) in
    let cl_rseffr = if cl_rseffr0 = [] then [rr] else cl_rseffr0 in
    (* let rss = List.map (fun rr -> (rr, rselfr)) cl_rseffr in *)
    (*LHS: find reachable heap + pure*)
    let lf1a = Cformula.subst_b lss lhs_b1 in
    let rf1a = Cformula.subst_b lss rhs_b1 in
    let lf1 = Cfutil.obtain_reachable_formula prog (Cformula.Base lf1a) [lselfr] in
    let rf1 = Cfutil.obtain_reachable_formula prog (Cformula.Base rf1a) [rselfr] in
    let _, l_hvs,l_hds = Cformula.get_hp_rel_formula lf1 in
    let _, r_hvs,r_hds = Cformula.get_hp_rel_formula rf1 in
    if l_hds = [] && r_hds = [] && List.length l_hvs = 1 && List.length r_hvs = 1 &&
       check_iden (List.hd l_hvs) (List.hd r_hvs) then
      ()
    else
      let () = Debug.info_hprint (add_str "cyc lf1" !Cformula.print_formula) lf1 no_pos in
      let () = Debug.info_hprint (add_str "cyc rf1" !Cformula.print_formula) rf1 no_pos in
      let is_same,_ = Checkeq.checkeq_formulas [self] lf1 rf1 in
      if is_same then () else
        (* let lf1 = Cformula.subst lss  *)
        (*RHS: find reachable heap + pure*)
        let lf2 = formula_rev_fnc lf1 in
        let rf2 = formula_rev_fnc rf1 in
        (*gen lemma*)
        let lemma_name = "cyc" in
        let l_coer = match lem_type with
          | 0
          (*3 is for syn Left lemma for tail-rec and non tail rec*)
          | 3 -> Iast.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN Iast.Left [] lf2 rf2
          | _ (*1*) -> Iast.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN Iast.Right [] rf2 lf2
        in
        Debug.ninfo_hprint (add_str "gen_lemma, l_coer" Iprinter.string_of_coerc_decl) l_coer no_pos;
        (*add lemma*)
        let iprog = Iast.get_iprog () in
        let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
        let _ =
          if not !Globals.smt_compete_mode then
            print_endline_quiet (" \n gen lemma (proof):" ^ (Cprinter.string_of_formula lf1) ^ (if lem_type = 0 ||  lem_type = 3 then " -> " else " <- ")
                                 ^ (Cprinter.string_of_formula rf1))
          else ()
        in
        let () = Globals.lemma_syn_count := !Globals.lemma_syn_count + 1 in
        ()
  with e ->
    let () = if not !Globals.smt_compete_mode then print_endline_quiet (" \n gen lemma: Exception: " ^ (Printexc.to_string e) ) else ()
    in ()

let gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
    lhs_node lhsb rhs_node rhsb =
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.string_of_h_formula in
  Debug.no_5 "LEMSYN.gen_lemma" pr2 pr1 pr2 pr1 string_of_int pr_none
    (fun _ _ _ _ _ -> gen_lemma prog formula_rev_fnc manage_unsafe_lemmas_fnc es lem_type
        lhs_node lhsb rhs_node rhsb)
    lhs_node lhsb rhs_node rhsb lem_type

let add_ihprel iprog chp_dclrs=
  let rec process_one chps res=
    match chps with
    | [] -> res
    | chp::rest ->
      try
        let todo_unk = Iast.look_up_hp_def_raw res chp.C.hp_name in
        process_one rest res
      with Not_found ->
        let n_ihp = {
          Iast.hp_name = chp.C.hp_name;
          Iast.hp_typed_inst_vars= List.map
              (fun (CP.SpecVar (t,id,_), i) -> (t,id,i)) chp.C.hp_vars_inst;
          Iast.hp_part_vars = chp.C.hp_part_vars;
          Iast.hp_root_pos = chp.C.hp_root_pos;
          Iast.hp_is_pre = chp.C.hp_is_pre;
          (* Iast.hp_view = None; *)
          Iast.hp_formula = Iformula.mkBase Iformula.HEmp (Ipure.mkTrue no_pos) IvpermUtils.empty_vperm_sets top_flow [] no_pos;
        }
        in
        process_one rest (res@[n_ihp])
  in
  let nihp_dclr = process_one chp_dclrs iprog.Iast.prog_hp_decls in
  let () = iprog.Iast.prog_hp_decls <- iprog.Iast.prog_hp_decls@nihp_dclr in
  nihp_dclr

let gen_lemma_infer_x (prog) ass_stk hpdef_stk
    formula_rev_fnc manage_unsafe_lemmas_fnc manage_infer_pred_lemmas_fnc trans_hprel_2_cview_fnc trans_formula_hp_2_view_fnc
    xpure_heap es lem_type h_vnode0 h_dnode0=
  let vnode0 = match h_vnode0 with
    | Cformula.ViewNode vl -> vl
    (* | Cformula.DataNode dl -> dl.Cformula.h_formula_data_node *)
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let dnode0 = match h_dnode0 with
    (* |  Cformula.ViewNode vr -> vr.Cformula.h_formula_view_node *)
    |  Cformula.DataNode dr -> dr
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  (*for subst*)
  let ( _,mf,_,_,_,_) = Cformula.split_components es.Cformula.es_formula in
  let eqs = (Mcpure.ptr_equations_without_null mf) in
  let cl_dns = Cformula.find_close [dnode0.Cformula.h_formula_data_node] eqs in
  let inter_vargs = CP.intersect_svl cl_dns vnode0.Cformula.h_formula_view_arguments in
  let () = Debug.info_hprint (add_str "cl_dns" !CP.print_svl) cl_dns no_pos in
  let () = Debug.info_hprint (add_str "inter_vargs" !CP.print_svl) inter_vargs no_pos in
  let ss1 = List.map (fun sv -> (dnode0.Cformula.h_formula_data_node, sv)) inter_vargs in
  let ss2 = List.fold_left (fun r ((CP.SpecVar (t, id, p)) as sv1) ->
      if p = Primed then
        r@[(sv1, CP.SpecVar (t, id, Unprimed))]
      else r
    ) [] dnode0.Cformula.h_formula_data_arguments in
  let h_dnode1 = (Cformula.h_subst (ss1@ss2) h_dnode0) in
  let dnode1 = match h_dnode1 with
    (* |  Cformula.ViewNode vr -> vr.Cformula.h_formula_view_node *)
    |  Cformula.DataNode dr -> dr
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  let h_vnode1 = Cformula.h_subst ss2 h_vnode0 in
  let vnode1 = match h_vnode1 with
    | Cformula.ViewNode vl -> vl
    (* | Cformula.DataNode dl -> dl.Cformula.h_formula_data_node *)
    | _ -> report_error no_pos "LEMSYN.gen_lemma: not handle yet"
  in
  (*END*)
  (* let vdef = x_add C.look_up_view_def_raw x_loc prog.C.prog_view_decls vnode.Cformula.h_formula_view_name in *)
  let vself = CP.SpecVar (CP.type_of_spec_var vnode1.Cformula.h_formula_view_node, self, Unprimed) in
  let ss0 = [(vnode1.Cformula.h_formula_view_node, vself)] in
  let rhs,n_hp = x_add (C.add_raw_hp_rel  ~caller:x_loc) prog false false [(vself,I);(dnode1.Cformula.h_formula_data_node,NI)] no_pos in
  (*add ihpdecl*)
  let iprog = Iast.get_iprog () in
  let hpdclr = C.look_up_hp_def_raw prog.C.prog_hp_decls (CP.name_of_spec_var n_hp) in
  let nihp = add_ihprel iprog [hpdclr] in
  (*lemma infer*)
  let rhs = Cformula.mkStarH rhs h_dnode1 no_pos in
  let lf1 = Cformula.formula_of_heap (Cformula.h_subst ss0 h_vnode1) no_pos in
  let rf1 = Cformula.formula_of_heap rhs no_pos in
  let lf2 = formula_rev_fnc lf1 in
  let rf2 = formula_rev_fnc rf1 in
  (*gen lemma*)
  let lemma_name = "cyci" in
  let l_coer = Iast.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN Iast.Left [(CP.name_of_spec_var n_hp)] lf2 rf2 in
  (*backup*)
  let cur_ass = ass_stk# get_stk in
  let () = ass_stk # reset in
  let cur_hpdefs =  hpdef_stk # get_stk in
  let () = hpdef_stk # reset in
  let r1,hp_defs0,r3 = manage_infer_pred_lemmas_fnc [l_coer] iprog prog xpure_heap in
  (*transform inferred def*)
  let hp_defs = (* Cformula.rel_def_stk # get_stk *) hp_defs0 in
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
      let l_coer = Iast.mk_lemma (lem_name) LEM_UNSAFE LEM_GEN Iast.Left [] lf2 rf4 in
      (*add lemma*)
      let res = manage_unsafe_lemmas_fnc [l_coer] iprog prog in
      let () = print_endline_quiet "\n*******relational definition ********" in
      let defs1 = if !Globals.print_en_tidy then List.map Cfout.rearrange_def (Cformula.rel_def_stk # get_stk) else
          (Cformula.rel_def_stk # get_stk) in
      let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
      let () = print_endline_quiet (pr1 defs1) in
      let () = print_endline_quiet (" \n gen lemma (infer):" ^ (Cprinter.string_of_formula lf1) ^ ( " -> " )
                                    ^ (Cprinter.string_of_formula rf3)) in
      ()
    else ()
  in
  (*restore*)
  let () = ass_stk # reset in
  let () = ass_stk # push_list cur_ass in
  let () = hpdef_stk # reset in
  let () = hpdef_stk # push_list cur_hpdefs in
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
