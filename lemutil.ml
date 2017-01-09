#include "xdebug.cppo"
open VarGen
open Globals
open Wrapper
open Gen
open Others
open Label_only
open Lemma

module C = Cast
module I = Iast
(* module CF=Cformula *)
module CP=Cpure

let checkeq_sem ?(force_pr=false) ?(lemtyp=I.Equiv) iprog0 cprog0 f1 f2  hpdefs to_infer_hps12 to_infer_hps21=
  (*************INTERNAL******************)
  let back_up_progs iprog cprog=
    (iprog.I.prog_view_decls,iprog.I.prog_data_decls, iprog.I.prog_hp_decls, cprog.C.prog_view_decls,
     cprog.C.prog_data_decls, cprog.C.prog_hp_decls,
     Lem_store.all_lemma # get_left_coercion, Lem_store.all_lemma # get_right_coercion)
  in
  let reset_progs (ivdecls, iddecls, ihpdecls, cvdecls, cddecls,chpdecls, left_coers, righ_coers)=
    let () = iprog0.I.prog_view_decls <- ivdecls in
    let () = iprog0.I.prog_hp_decls <- ihpdecls in
    let () = cprog0.C.prog_view_decls <- cvdecls in
    let () = cprog0.C.prog_hp_decls <- chpdecls in
    let () = cprog0.C.prog_data_decls <- cddecls in
    let () = cprog0.C.prog_hp_decls <- chpdecls in
    let () = Lem_store.all_lemma # set_coercion left_coers righ_coers in
    ()
  in
  let rec look_up_hpdef rem_hpdefs (r_unk_hps, r_hpdefs) hp=
    match rem_hpdefs with
    | [] -> (r_unk_hps@[hp], r_hpdefs)
    | ((* (k, _,_,_) as *) hpdef)::rest -> begin
        match hpdef.Cformula.def_cat with
        | CP.HPRelDefn (hp1,_,_) -> if CP.eq_spec_var hp hp1 then
            (*to remove after improve the algo with nested*)
            let todo_unk = List.map (fun (f,_) ->
                let hps = Cformula.get_hp_rel_name_formula f in
                if CP.diff_svl hps [hp] != [] then
                  raise Not_found
                else []
              )  hpdef.Cformula.def_rhs in
            (r_unk_hps, r_hpdefs@[hpdef])
          else look_up_hpdef rest (r_unk_hps, r_hpdefs) hp
        | _ -> look_up_hpdef rest (r_unk_hps, r_hpdefs) hp
      end
  in
  let heap_remove_unk_hps unk_hps hn = match hn with
    | Cformula.HRel (hp,eargs, pos)-> begin
        if CP.mem_svl hp unk_hps then Cformula.HTrue else hn
      end
    | _ -> hn
  in
  (*************END INTERNAL******************)
  (*for each proving: generate lemma; cyclic proof*)
  try begin
    let bc = back_up_progs iprog0 cprog0 in
    let hps = CP.remove_dups_svl ((Cformula.get_hp_rel_name_formula f1)@(Cformula.get_hp_rel_name_formula f2)) in
    let unk_hps, known_hpdefs = List.fold_left (look_up_hpdef hpdefs) ([],[]) hps in
    (*remove unk_hps*)
    let f11,f21 = if unk_hps = [] then (f1, f2) else
        (Cformula.formula_trans_heap_node (heap_remove_unk_hps unk_hps) f1,
         Cformula.formula_trans_heap_node (heap_remove_unk_hps unk_hps) f2)
    in
    (*transform hpdef to view;
      if preds are unknown -> HTRUE
    *)
    let proc_name = "eqproving" in
    let n_cview,chprels_decl = Saout.trans_hprel_2_cview iprog0 cprog0 proc_name known_hpdefs in
    (*trans_hp_view_formula*)
    let f12 = Saout.trans_formula_hp_2_view iprog0 cprog0 proc_name chprels_decl known_hpdefs [] f11 in
    let f22 = Saout.trans_formula_hp_2_view iprog0 cprog0 proc_name chprels_decl known_hpdefs [] f21 in
    (*iform*)
    let if12 = Rev_ast.rev_trans_formula f12 in
    let if22 = Rev_ast.rev_trans_formula f22 in
    (*unfold lhs - rhs*)
    (* let f13 = do_unfold_view cprog0 f12 in *)
    (* let f23 = do_unfold_view cprog0 f22 in *)
    let r=
      let lemma_name = "tmp" in
      let l_coer = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN lemtyp to_infer_hps12 if12 if22 in
      let r1,_ = manage_test_lemmas1 ~force_pr:false [l_coer] iprog0 cprog0 in
      r1
      (* let fnc = wrap_proving_kind PK_SA_EQUIV (fun f1 f2 -> Sleekcore.sleek_entail_check [] cprog0 [(\* (f12,f22) *\)] f1 (Cformula.struc_formula_of_formula f2 no_pos)) in *)
      (* let r1,_,_ = x_add Sleekcore.sleek_entail_check [] cprog0 [(\* (f12,f22) *\)] f13 (Cformula.struc_formula_of_formula f23 no_pos) in *)
      (* let r1,_,_ = fnc f13 f23 in *)
      (* if not r1 then false else *)
      (*   let r_coer = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN I.Left to_infer_hps21 if22 if12 in *)
      (*   let r2,_ = manage_test_lemmas1 ~force_pr:false [r_coer] iprog0 cprog0 in *)
      (*   (\* let r2,_,_ = x_add Sleekcore.sleek_entail_check [] cprog0 [(\\* (f22,f12) *\\)] f23 (Cformula.struc_formula_of_formula f13 no_pos) in *\) *)
      (*   (\* let r2,_,_ = fnc f23 f13 in *\) *)
      (*   r2 *)
    in
    let () = reset_progs bc in
    r
  end
  with _ -> (* let () = Debug.info_hprint (add_str "view_equivs: " pr_id) "1" no_pos in *)
    false

let checkeq_sem  ?(force_pr=false) iprog cprog f1 f2 ?(lemtyp=I.Equiv) hpdefs to_infer_hps12 to_infer_hps21 =
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_5 "LEM.checkeq_sem" pr1 pr1 pr2 (pr_list pr_id) (pr_list pr_id) string_of_bool
    (fun _ _ _ _ _ ->  checkeq_sem  ~force_pr:force_pr iprog cprog f1 f2 ~lemtyp:lemtyp hpdefs to_infer_hps12 to_infer_hps21)
    f1 f2 hpdefs to_infer_hps12 to_infer_hps21

let norm_checkeq_views_x iprog cprog cviews0 =
  (************************************************)
  let gen_view_formula vdcl=
    let self_sv = CP.SpecVar (Named vdcl.Cast.view_data_name ,self, Unprimed) in
    let vnode = Cformula.mkViewNode (self_sv ) vdcl.Cast.view_name (vdcl.Cast.view_vars) no_pos in
    Cformula.formula_of_heap vnode no_pos
  in
  let extract_unknown_preds vdcl=
    let hps = List.fold_left (fun r (f,_) -> r@(Cformula.get_hp_rel_name_formula f)) [] vdcl.Cast. view_un_struc_formula in
    List.map CP.name_of_spec_var hps
  in
  let checkeq_view vdecl1 vdecl2=
    (*compute f1 of view1*)
    let f1 = gen_view_formula vdecl1 in
    let to_infer_hps12 = extract_unknown_preds vdecl1 in
    (*compute f2 of view2*)
    let f2 =  gen_view_formula vdecl2 in
    let to_infer_hps21 = extract_unknown_preds vdecl2 in
    checkeq_sem iprog cprog f1 f2 [] to_infer_hps12 to_infer_hps21
  in
  let rec checkeq_views_loop cviews res=
    match cviews with
    | [] | [_] -> res
    | v::rest -> let new_eqs = List.fold_left (fun r v2 ->
        if checkeq_view v v2 then
          r@[(v.Cast.view_name, v2.Cast.view_name)]
        else r
      ) [] rest in
      checkeq_views_loop rest (res@new_eqs)
  in
  (************************************************)
  let view_eqs = checkeq_views_loop cviews0 [] in
  (* {cprog with Cast.prog_view_equiv = cprog.Cast.prog_view_equiv@view_eqs} *)
  let () = cprog.Cast.prog_view_equiv <- cprog.Cast.prog_view_equiv@view_eqs in
  cprog

let norm_checkeq_views iprog cprog cviews=
  let pr1 = pr_list_ln Cprinter.string_of_view_decl in
  let pr2 prog = (pr_list (pr_pair pr_id pr_id)) prog.Cast.prog_view_equiv in
  Debug.no_2 "norm_checkeq_views" pr2 pr1 pr2
    (fun _ _ -> norm_checkeq_views_x iprog cprog cviews) cprog cviews

let () = Norm.check_lemeq_sem := checkeq_sem
