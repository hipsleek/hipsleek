#include "xdebug.cppo"
open VarGen
(*
  the wrapper of sleek implementation
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

module H = Hashtbl
module I = Iast
(* module Inf = Infer *)
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
(* module LP = Lemproving *)
(* module AS = Astsimp *)
(* module DD = Debug *)
module XF = Xmlfront
module NF = Nativefront
module CEQ = Checkeq
(* module TI = Typeinfer *)
module MCP = Mcpure
module SY_CEQ = Syn_checkeq


let generate_lemma = ref (fun (iprog: I.prog_decl) (cprog: C.prog_decl) n t (ihps: ident list) iante iconseq -> [],[])

(*
  let sleek_entail_check_x itype isvl (cprog: C.prog_decl) proof_traces ante conseq=
*)

(* WN : Is this executed? *)
let sleek_unsat_check isvl cprog ante=
  let () = Debug.ninfo_hprint (add_str "check unsat with graph" pr_id) "\n" no_pos in
  let () = Hgraph.reset_fress_addr () in
  let pos = CF.pos_of_formula ante in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let lem = Lem_store.all_lemma # get_left_coercion in
  let ante = x_add Solver.normalize_formula_w_coers 11 cprog es ante (* cprog.C.prog_left_coercions *) lem in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let init_ctx =  (* CF.transform_context (x_add Solver.elim_unsat_es 9 cprog (ref 1)) *) ctx in
  (* let () = if (CF.isAnyFalseCtx ctx) then *)
  (*   print_endline ("[Warning] False ctx") *)
  (* in *)
  (* let () = print_endline ("1") in *)
  (* let es = match init_ctx with *)
  (*   | CF.Ctx es -> es *)
  (*   | _ -> report_error no_pos "Sleekengine.check_unsat: not handle yet" *)
  (* in *)
  (* let helper f= *)
  (*   (\* let is_heap_conflict,f1 = Frame.norm_dups_pred cprog f in *\) *)
  (*   (\* if is_heap_conflict then true else *\) *)
  (*     Solver.unsat_base_nth 1 cprog (ref 1) f *)
  (* in *)
  (* let fs = (Frame.heap_normal_form cprog ante) in *)
  (* let rec loop_helper fs= *)
  (*   match fs with *)
  (*     | [] -> false, None *)
  (*     | f::rest -> *)
  (*           let res1 = helper f in *)
  (*           if res1 then (true,Some f) else *)
  (*           loop_helper rest *)
  (* in *)
  (* let r,fail_of = *)
  (*   match fs with *)
  (*     | [] -> (\* report_error no_pos "sleekengine.check_unsat" *\) false, None *)
  (*     | _ -> loop_helper fs *)
  (* in *)
  let quans,bare = CF.split_quantifiers ante in
  let ante0a = (CF.simplify_pure_f (CF.force_elim_exists bare quans)) in
  let r,fail_of = Frame.check_unsat_w_norm cprog ante0a false in
  if r then
    let () = print_endline_quiet ("[Warning] False ctx 0") in
    let () = x_dinfo_hp (add_str "pos of false" Cprinter.string_of_pos) pos no_pos in
    (true, CF.SuccCtx [init_ctx], [])
  else
    (false, CF.FailCtx (CF.Trivial_Reason
                          ( {CF.fe_kind = CF.Failure_Must "lhs is not unsat"; CF.fe_name = "unsat check";CF.fe_locs=[]}, []),  init_ctx, CF.mk_cex true),
     [])


(*   (\* let () = print_endline ("1") in *\) *)
let sleek_entail prog ante_ctx conseq pos=
  let pid = None in
  let ante_failesc_ctx = [([],[],[([], ante_ctx, None)])] in
  let rs, prf = x_add Solver.heap_entail_struc_list_failesc_context_init 12 prog false true ante_failesc_ctx conseq None None None pos pid in
  rs, prf

(* WN : why isn't itype added to estate? *)
let rec sleek_entail_check_x itype isvl (cprog: C.prog_decl) proof_traces (ante:CF.formula) (conseq:CF.struc_formula) =
  let () = y_tinfo_hp (add_str "is_pure_field" string_of_bool) (check_is_pure_field ()) in
  let pos2 = CF.pos_of_formula ante in
  let pos3 = CF.pos_of_struc_formula conseq in
  let () = Hgraph.reset_fress_addr () in
  let pr = Cprinter.string_of_struc_formula in
  let () = Debug.ninfo_hprint (add_str "ante(before rem @A)"  Cprinter.string_of_formula) ante no_pos in
  let ante = if (!Globals.remove_abs && not((* !Globals.allow_field_ann *) !Globals.imm_merge)) then 
      Cvutil.remove_imm_from_formula cprog ante (CP.ConstAnn(Accs)) else ante in
  let () = x_tinfo_hp (add_str "ante(after rem @A)"  Cprinter.string_of_formula) ante no_pos in
  let ante = Norm.imm_abs_norm_formula ante cprog  (Solver.unfold_for_abs_merge cprog no_pos) in
  let conseq = if ((!Globals.remove_abs)  && not((* !Globals.allow_field_ann *) !Globals.imm_merge)) then Cvutil.remove_imm_from_struc_formula cprog conseq (CP.ConstAnn(Accs)) else conseq in
  let () = x_tinfo_hp (add_str "conseq(after rem @A)" pr) conseq no_pos in 
  (* Immutable.restore_tmp_ann_formula ante in *)
  (* let conseq = Immutable.restore_tmp_ann_struc_formula conseq in *)
  let conseq = Cvutil.prune_pred_struc cprog true conseq in
  let () = x_tinfo_hp (add_str "conseq(after prune)" pr) conseq no_pos in 
  (* let () = Debug.info_pprint "Andreea : false introduced by add_param_ann_constraints_struc" no_pos in *)
  (* let () = Debug.info_pprint "=============================================================" no_pos in *)
  let conseq = Astsimp.add_param_ann_constraints_struc conseq in
  let () = x_tinfo_hp (add_str "conseq(after add param)" pr) conseq no_pos in 
  (* let conseq = Astsimp.add_param_ann_constraints_struc conseq in  *)
  let () = x_dinfo_zp (lazy ("\nrun_entail_check 2:"
                             ^"\n ### ivars = "^(pr_list !CP.print_sv isvl)
                             ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                             ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                             ^"\n\n")) no_pos in
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let es = {es with CF.es_proof_traces = proof_traces} in
  let lem = Lem_store.all_lemma # get_left_coercion in
  let ante = x_add Solver.normalize_formula_w_coers 11 cprog es ante lem (* cprog.C.prog_left_coercions *) in
  let inf_str = (pr_list string_of_inf_const itype)^(Cprinter.string_of_spec_var_list isvl) in
  let fvs = CF.struc_fv conseq in
  let () = x_tinfo_hp (add_str "conseq" (Cprinter.string_of_struc_formula)) conseq no_pos in
  let () = x_tinfo_hp (add_str "fvs(conseq)" (Cprinter.string_of_spec_var_list)) fvs no_pos in
  let () = x_tinfo_hp (add_str "itype" (pr_list string_of_inf_const)) itype no_pos in
  let () = x_tinfo_hp (add_str "isvl" (Cprinter.string_of_spec_var_list)) isvl no_pos in
  let () = if (!Globals.print_core || !Globals.print_core_all) then print_endline_quiet ("\nINPUT 0: "^inf_str^" \n ### ante = " ^ (Cprinter.string_of_formula ante) ^"\n ### conseq = " ^ (Cprinter.string_of_struc_formula conseq)) else () in
  let () = x_dinfo_zp (lazy ("\nrun_entail_check 3: after normalization"
                             ^ "\n ### ante = "^(Cprinter.string_of_formula ante)
                             ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq)
                             ^"\n\n")) no_pos in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in

  let ctx0 = Solver.elim_exists_ctx ctx in

  let ctx = CF.add_proof_traces_ctx ctx0 proof_traces in
  (* List of vars appearing in original formula *)
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* (\* List of vars needed for abduction process *\) *)
  (* let vars = List.map (fun v -> x_add Typeinfer.get_spec_var_type_list_infer (v, Unprimed) orig_vars no_pos) ivars in *)
  (* Init context with infer_vars and orig_vars *)
  (* let (vrel,iv) = List.partition (fun v -> is_RelT (CP.type_of_spec_var v)(*  ||  *)
      (* CP.type_of_spec_var v == FuncT *)) isvl in
     let (v_hp_rel,iv) = List.partition (fun v -> CP.is_hprel_typ v (*  ||  *) 
              (* CP.type_of_spec_var v == FuncT *)) iv in *)
  let (vrel, vtempl, v_hp_rel, iv) = List.fold_left (fun (vr, vt, vh, iv) v ->
      let typ = CP.type_of_spec_var v in
      if is_RelT typ then (vr@[v], vt, vh, iv)
      else if CP.is_hprel_typ v then (vr, vt, vh@[v], iv)
      else if is_FuncT typ then (vr, vt@[v], vh, iv)
      else (vr, vt, vh, iv@[v])) ([], [], [], []) isvl in
  (* let () = print_endline ("WN: vars rel"^(Cprinter.string_of_spec_var_list vrel)) in *)
  (* let () = print_endline ("WN: vars hp rel"^(Cprinter.string_of_spec_var_list v_hp_rel)) in *)
  (* let () = print_endline ("WN: vars inf"^(Cprinter.string_of_spec_var_list iv)) in *)
  let ctx = Infer.init_vars ctx iv vrel vtempl v_hp_rel orig_vars in
  (* let itype_opt = if List.mem INF_TERM itype then Some INF_TERM else None in *)
  let ctx = Infer.init_infer_type ctx itype in
  (* let () = print_string ((pr_list_ln Cprinter.string_of_view_decl) !cprog.Cast.prog_view_decls)  in *)
  let () = if !Globals.print_core || !Globals.print_core_all
    then print_string ("\nrun_infer:\n"^(Cprinter.string_of_formula ante)
                       ^" "^(pr_list !CP.print_sv isvl)
                       ^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n")
    else ()
  in
  let is_base_conseq,conseq_f = CF.base_formula_of_struc_formula conseq in
  let () = Debug.ninfo_hprint (add_str "graph_norm" string_of_bool) !graph_norm no_pos in
  let () = Debug.ninfo_hprint (add_str "seg_opz" string_of_bool) !Frame.seg_opz no_pos in
  let () = Debug.ninfo_hprint (add_str "is_base_conseq" string_of_bool) is_base_conseq no_pos in
  let () = Debug.ninfo_hprint (add_str "isvl" !CP.print_svl) isvl no_pos in

  if isvl = [] && !Globals.graph_norm && !Frame.seg_opz  && is_base_conseq &&
     Cast.is_complex_entailment_4graph cprog ante conseq
  then
    let () = Debug.ninfo_hprint (add_str "graph optimization" pr_id) "" no_pos in
    let () = Globals.disable_failure_explaining := true in
    let () = Globals.smt_is_must_failure := None in

    if CF.isAnyConstFalse_struc conseq then sleek_unsat_check isvl cprog ante
    else
      check_entail_w_norm cprog proof_traces ctx ante conseq_f
  else

  if (!Globals.prove_invalid && not(!Globals.use_baga (* !Globals.baga_xpure *))) && CF.isAnyConstFalse_struc conseq && Cfutil.is_view_f ante then
    (* TODO : new unsat checking for LHS from Loc *)
    (* need to document; and generalize? *)
    let () = Globals.smt_is_must_failure := None in
    let () = Globals.disable_failure_explaining := true in
    (* let sno = ref (0:int) in *)
    (* let is_unsat = x_add Solver.unsat_base_nth 22 cprog (sno) ante in *)

    let is_unsat0, is_sat, waiting_vis,_ = Cvutil.build_vis cprog ante in
    let is_unsat = if is_unsat0 then true else
      if is_sat then false else
        let is_unsat2 = Cvutil.view_unsat_check_topdown cprog waiting_vis [] [] [] true [] in
        is_unsat2
    in

    if is_unsat then
      (true, (CF.SuccCtx[ctx]), isvl)
    else
      let fctx = CF.FailCtx (CF.Trivial_Reason
                               ( {CF.fe_kind = CF.Failure_Must "rhs is unsat, but not lhs"; CF.fe_name = "unsat check";CF.fe_locs=[]}, []),ctx,  CF.mk_cex true) in
      (false, fctx, isvl)
  else
    (* let () = Globals.disable_failure_explaining := false in *)
    (* let () = Globals.smt_is_must_failure := (Some false) in *)
    let ctx =
      if !Globals.delay_proving_sat then ctx
      else CF.transform_context (x_add Solver.elim_unsat_es 9 cprog (ref 1)) ctx in
    let () = 
      if (CF.isAnyFalseCtx ctx) then
        (* Why is pos of ante 0.0 ? *)
        (* !!! **sleekcore.ml#222:pos of ante: 0:0 *)
        (* !!! **sleekcore.ml#223:pos of conseq: 24:41[Warning] False ctx *)
        let () = x_dinfo_hp (add_str "pos of ante" Cprinter.string_of_pos) pos2 no_pos in
        let () = x_dinfo_hp (add_str "pos of conseq" Cprinter.string_of_pos) pos3 no_pos in
        let () = add_false_ctx pos3 in
        print_endline_quiet ("[Warning] False ctx")
      else last_sat_ctx # set (Some pos3)
    in
    (* let is_arrvar_flag = CF.is_arr_as_var_ctx ctx in *)
    (* let () = x_dinfo_hp (add_str "arrvar_flag" string_of_bool) is_arrvar_flag no_pos in *)
    let conseq = Cfutil.elim_null_vnodes cprog conseq in
    (*****************)
    (* let is_base_conseq,conseq_f = CF.base_formula_of_struc_formula conseq in *)
    (* let ante1a,conseq1 = Syn_checkeq.syntax_contrb_lemma_end_null cprog ante conseq_f in *)
    (************************)
    (* let ctx= if not !Globals.en_slc_ps && Cfutil.is_unsat_heap_model cprog ante then *)
    (*   let () = print_endline ("[Warning] False ctx") in *)
    (*   CF.transform_context (fun es -> CF.false_ctx_with_orig_ante es ante no_pos) ctx *)
    (* else ctx *)
    (* in *)
    (* let () = print_endline ("ctx: "^(Cprinter.string_of_context ctx)) in *)
    let wrap = 
      (* if is_arrvar_flag then Wrapper.wrap_arr_as_var *)
      (* else *) fun f a -> f a in
    let rs1, _ =
      if  not !Globals.disable_failure_explaining then
        (* let () = sleek_entail cprog ctx conseq no_pos in *)
        x_add (wrap Solver.heap_entail_struc_init_bug_inv) cprog false (* false *) true
          (CF.SuccCtx[ctx]) conseq no_pos None
      else
        x_add (wrap Solver.heap_entail_struc_init) cprog false (* false *) true
          (CF.SuccCtx[ctx]) conseq no_pos None
    in
    (* let () = print_endline ("WN# 1:"^(Cprinter.string_of_list_context rs1)) in *)
    (* tut/ex1/bugs-ex31-match.slk *)
    let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
    let () = match last_sat_ctx # get with
      | Some p -> if (CF.isAnyFalseListCtx rs) && not(!Globals.old_collect_false) then
          let contra_flag = last_infer_lhs_contra # get in
          let () = add_false_ctx p in
          if contra_flag then ()
          else
            let () = print_endline_quiet ("[UNSOUNDNESS] WARNING : satisfiable state at "^(string_of_loc p)^" became hfalse") in
            if !Globals.assert_unsound_false then failwith "Unsound false in SLEEK?" 
            else ()
      | None -> () 
    in
    let () = x_tinfo_pp ("WN# 2:"^(Cprinter.string_of_list_context rs)) no_pos in
    (* flush stdout; *)
    let res =
      if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
      else ((not (CF.isFailCtx rs))) in
    (* residues := Some (rs, res); *)
    (res, rs,v_hp_rel)

(*
  proof_traces: (formula*formula) list===> for cyclic proofs
*)
(* let sleek_entail_check itype isvl (cprog: C.prog_decl) proof_traces ante conseq=
*)
and sleek_entail_check i itype isvl (cprog: C.prog_decl) proof_traces ante conseq=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = Cprinter.string_of_struc_formula in
  let pr3 = pr_triple string_of_bool Cprinter.string_of_list_context !CP.print_svl in
  let pr4 = pr_list_ln (pr_pair pr1 pr1) in
  let pr5 = pr_list string_of_inf_const in
  Debug.no_6_num i "sleek_entail_check" 
    pr5 !CP.print_svl pr1 pr2 pr4 (add_str "is_classic" string_of_bool) pr3
    (fun _ _ _ _ _ _ -> sleek_entail_check_x itype isvl cprog proof_traces ante conseq)
    itype isvl ante conseq proof_traces (check_is_classic ())

and check_entail_w_norm prog proof_traces init_ctx ante0 conseq0=
  let _ =
    let () = Lem_store.all_lemma # clear_right_coercion in
    let () = Lem_store.all_lemma # clear_left_coercion in
    ()
  in
  (***************************************)
  let call_sleek ante_f conseq_f=
    let () = Globals.graph_norm := false in
    let () = Globals.disable_failure_explaining := false in
    let conj_ante1, ante_args = Cfutil.norm_rename_clash_args_node [] ante_f in
    let norm_conj_conseq2, _ = Cfutil.norm_rename_clash_args_node ante_args conseq_f in
    let r, lc, isvl = sleek_entail_check 1 [] [] (prog: C.prog_decl) proof_traces conj_ante1 (CF.struc_formula_of_formula norm_conj_conseq2 no_pos) in
    let () = Debug.ninfo_hprint (add_str "r" string_of_bool) r no_pos in
    let () = if not r then
        let () = Globals.smt_is_must_failure := Some true in ()
      else ()
    in
    let () = Globals.graph_norm := true in
    (r, lc, isvl)
  in
  (*****************************************)
  let () = Debug.ninfo_hprint (add_str "ante0" Cprinter.prtt_string_of_formula) ante0 no_pos in
  let () = Debug.ninfo_hprint (add_str "conseq0" Cprinter.prtt_string_of_formula) conseq0 no_pos in
  let f_ctx = CF.FailCtx (CF.Trivial_Reason
                            ( {CF.fe_kind = CF.Failure_Must "rhs is unsat, but not lhs"; CF.fe_name = "unsat check";CF.fe_locs=[]}, []),
                          init_ctx, CF.mk_cex true) in
  let s_ctx = (CF.SuccCtx [init_ctx]) in
  let ante_quans, ante0b = (CF.split_quantifiers ante0) in
  let ante0b = (CF.simplify_pure_f ante0b) in
  let ante0a = Cformula.force_elim_exists ante0b ante_quans in
  let conseq_quans, conseq0b = CF.split_quantifiers conseq0 in
  let conseq0a = Cformula.force_elim_exists conseq0b conseq_quans in
  let () = Debug.ninfo_hprint (add_str "ante_quans" !CP.print_svl) ante_quans no_pos in
  let () = Debug.ninfo_hprint (add_str "conseq_quans" !CP.print_svl) conseq_quans no_pos in
  (******************************************************)
  let prove_conj_conseq_conj_ante (conj_ante, a_hg) ante_nemps1 (norm_conj_conseq,conj_conseq_hg)=
    let () = Debug.ninfo_hprint (add_str "sub ante" Cprinter.prtt_string_of_formula) conj_ante no_pos in
    let r = Frame.check_imply_w_norm prog true a_hg conj_conseq_hg in
    (************use sleek for testing**********)
    (* let r,lc = call_sleek () *)
    (************use sleek for testing**********)
    let lc = if r then s_ctx else f_ctx in
    (r, lc)
  in
  let rec prove_conj_conseq ante_fs1 ante_nemps1 (norm_conj_conseq,conj_conseq_hg) res_conj_ante_fs last_lc=
    match ante_fs1 with
    | [] -> false,res_conj_ante_fs,last_lc
    | ante::rest ->
      (* let is_unsat, norm_conj_conseq,conj_conseq_hg = Frame.norm_dups_pred prog ante_nemps1 conj_conseq false true in *)
      (*  if is_unsat then (false,res_conj_ante_fs, f_ctx) else *)
      let b,lc = prove_conj_conseq_conj_ante ante ante_nemps1 (norm_conj_conseq,conj_conseq_hg) in
      if b then
        (*to remove matched node in ante and put the remain back
          testcase: 10e04
        *)
        let res_ante = Frame.prune_match ante in
        (true, res_conj_ante_fs@rest@[res_ante], lc)
      else prove_conj_conseq rest ante_nemps1 (norm_conj_conseq,conj_conseq_hg) (res_conj_ante_fs@[ante]) lc
  in
  let rec prove_list_conseqs ante_fs2 ante_nemps0 fs ctx=
    match fs with
    | [] -> true, ctx
    | conj_conseq::rest ->
      let () = Debug.ninfo_hprint (add_str "sub conseq" Cprinter.prtt_string_of_formula) conj_conseq no_pos in
      let is_unsat, norm_conj_conseq,conj_conseq_hg = Frame.norm_dups_pred prog ante_nemps0 conj_conseq false true false in
      if is_unsat then (false, ctx) else
        let r,rest_ante_fs, lc = prove_conj_conseq ante_fs2 ante_nemps0 (norm_conj_conseq,conj_conseq_hg) [] ctx in
        if not r then (false ,lc) else
          prove_list_conseqs rest_ante_fs ante_nemps0 rest lc
  in
  (*todo: abs ptos -> seg predicate + add neqs (x3!=x2) also add x2!=x3 if x2::lseg<x3>*)
  (* to return a list of ante_fs2 if ante is not unsat to pair with conseq_fs later *)
  let rec check_unsat_conj_ante fs res_fs=
    match fs with
    | [] -> false, res_fs
    | f::rest ->
      let unsat,f1, hg1 = Frame.norm_dups_pred prog [](*ante_nemps*) f true true false in
      if unsat then
        (unsat, res_fs@(List.map (fun f -> (f, Hgraph.mk_empty_hgraph ())) rest))
      else check_unsat_conj_ante rest (res_fs@[(f,hg1)])
  in
  let is_simple_rhs f=
    let _, hvs,hns = CF.get_hp_rel_formula f in
    hns != [] || (List.length hvs = 1 && hns = [])
  in
  (******************************************************)
  let ante_1b, conseq_1a, ante_unsat0, conseq_unsat0 = Syn_checkeq.syntax_nodes_match
      ante0a conseq0a
  in
  if ante_unsat0 then (true, (CF.SuccCtx [init_ctx]), []) else
    let ante1a,conseq1 = Syn_checkeq.syntax_contrb_lemma_end_null prog ante_1b conseq_1a in
    (* check classic *)
    if  Cfutil.is_empty_heap_f conseq1 then
      call_sleek ante1a conseq1
    else
      let is_matched, new_lhs, new_rhs = Syn_checkeq.syntax_vnodes_match ante1a conseq1 in
      if is_matched && Cfutil.is_empty_heap_f new_rhs then
        call_sleek new_lhs new_rhs
      else
      if is_simple_rhs conseq1 then
        call_sleek ante1a conseq1
      else
        let view_emp_map = Cast.get_emp_map prog in
        let seg_views = List.map (fun (vn,_,_) -> vn) view_emp_map in
        let oamap_data_views = Cvutil.get_oa_node_view prog seg_views in
        let seg_data_names = List.map (fun vn ->
            let vdecl = x_add Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls vn in
            vdecl.Cast.view_data_name
          ) seg_views in
        let ante1,is_pto_inconsistent, ante_nemps, ante_neq = Cfutil.xpure_graph_pto prog seg_data_names oamap_data_views ante1a in
        if is_pto_inconsistent then
          (true, (CF.SuccCtx [init_ctx]), [])
        else
          (* let ante1 = (\* Cfutil.oa_node2view prog ante1a vname *\) ante1a in *)
          (* let ante2 = (CF.mkAnd_pure ante1 *)
          (*     (Mcpure.mix_of_pure ante_neq) no_pos) in *)
          let ante_fs0 = Frame.heap_normal_form prog ante1 Hgraph.hgraph_grp_min_size_entail in
          (*  let ante_unsat = List.exists (fun f -> *)
          (*       (\*todo: abs ptos -> seg predicate + add neqs (x3!=x2) also add x2!=x3 if x2::lseg<x3>*\) *)
          (*       (\*to return a list of ante_fs2 if ante is not unsat to pair with conseq_fs later*\) *)
          (*     let unsat,f1 = Frame.norm_dups_pred prog [](\*ante_nemps*\) f in *)
          (*       unsat *)
          (* ) ante_fs in *)
          let ante_unsat, ante_fs_w_grp_config = check_unsat_conj_ante ante_fs0 [] in
          let () = Debug.ninfo_hprint (add_str "ante_unsat" string_of_bool) ante_unsat no_pos in
          if ante_unsat then
            (true, (CF.SuccCtx [init_ctx]), [])
          else
            (*lhs is not unsat*)
          if conseq_unsat0 then
            (*rhs is unsat*)
            (false, CF.FailCtx (CF.Trivial_Reason
                                  ( {CF.fe_kind = CF.Failure_Must "lhs is not unsat"; CF.fe_name = "unsat check";CF.fe_locs=[]}, []),
                                init_ctx, CF.mk_cex true),
             [])
          else
            (*pi1 =  ptos predicate into pure*)
            (*conseq1 = conseq /\ pi1*)
            let hvs = CF.get_views conseq1 in
            (******ante_neq4conseq***abstract x!=y ******)
            let view_ptrs = List.fold_left (fun r vn ->
                r@(vn.CF.h_formula_view_node::vn.CF.h_formula_view_arguments)
              ) [] hvs in
            let nemps1 = List.filter (fun (sv1,sv2) -> CP.mem_svl sv1 view_ptrs &&
                                                       CP.mem_svl sv2 view_ptrs
                                     ) ante_nemps in
            let ps = List.map (fun (sv1, sv2) -> CP.mkPtrNeqEqn sv1 sv2 no_pos) nemps1 in
            let ante_neq1 = CP.conj_of_list ps no_pos in
            (*********abstract x!=y ******)
            let () = Debug.ninfo_hprint (add_str "view_ptrs" !CP.print_svl) view_ptrs no_pos in
            let () = Debug.ninfo_hprint (add_str "ante_nemps" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) ante_nemps no_pos in
            let () = Debug.ninfo_hprint (add_str "ante_neq1" !CP.print_formula) ante_neq1 no_pos in
            (*partition components on conseq1*)
            let ante_norm_conseq = Frame.heap_normal_form prog
                (CF.mkAnd_pure conseq1 (Mcpure.mix_of_pure ante_neq1) no_pos)
                Hgraph.hgraph_grp_min_size_entail in
            (*for each comp, do norm, matching with ante + add emp if neccessary*)
            let r, f_ctx= prove_list_conseqs ante_fs_w_grp_config (* ante_nemps *)[] ante_norm_conseq
                (CF.SuccCtx [init_ctx]) in
            (r, f_ctx, [])

(*
- guiding_svl is used to guide the syntatic checking.
- guiding_svl is common variables between f1 and f2
*)
let check_equiv iprog cprog guiding_svl proof_traces need_lemma f1 f2=
  let gen_lemma (r_left, r_right) (ante,conseq)=
    let iante = Rev_ast.rev_trans_formula ante in
    let iconseq = Rev_ast.rev_trans_formula conseq in
    let l2r,r2l = !generate_lemma iprog cprog "temp" I.Equiv [] iante iconseq in
    (r_left@l2r, r_right@r2l)
  in
  if not (!Globals.syntatic_mode) then
    let old_l, old_r = if need_lemma then
        let n_l, n_r = List.fold_left gen_lemma ([],[]) proof_traces in
        let old_l = Lem_store.all_lemma # get_left_coercion  in
        let old_r = Lem_store.all_lemma # get_right_coercion  in
        let () = Lem_store.all_lemma # add_left_coercion n_l in
        let () = Lem_store.all_lemma # add_right_coercion n_r in
        (old_l, old_r)
      else ([],[])
    in
    let r =
      let b1, _, _ = (sleek_entail_check 2 [] [] cprog proof_traces f1 (CF.struc_formula_of_formula f2 no_pos)) in
      if b1 then
        let b2,_,_ = (sleek_entail_check 3 [] [] cprog (List.map (fun (f1,f2) -> (f2,f1)) proof_traces)
                        f2 (CF.struc_formula_of_formula f1 no_pos)) in
        b2
      else
        b1
    in
    let () = if need_lemma then
        let () = Lem_store.all_lemma # set_left_coercion old_l in
        let () = Lem_store.all_lemma # set_right_coercion old_r in
        ()
      else ()
    in
    r
  else
    SY_CEQ.check_relaxeq_formula guiding_svl f1 f2

let rec check_equiv_list_x iprog prog guiding_svl proof_traces need_lemma fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
    | [] -> (false, fs1)
    | f1::fss -> if (check_equiv iprog prog guiding_svl proof_traces need_lemma f f1) then
        (true,fs1@fss)
      else look_up_f f fss (fs1@[f1])
  in
  if List.length fs1 = List.length fs2 then
    match fs1 with
    | [] -> true
    | f1::fss1 ->
      begin
        let r,fss2 = look_up_f f1 fs2 [] in
        if r then
          check_equiv_list iprog prog guiding_svl proof_traces need_lemma fss1 fss2
        else false
      end
  else false

and check_equiv_list iprog prog guiding_svl proof_traces need_lemma fs1 fs2: bool=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "check_equiv_list" pr1 pr1 string_of_bool
    (fun _ _ -> check_equiv_list_x iprog prog guiding_svl proof_traces need_lemma fs1 fs2) fs1 fs2


(* let () = Sautility.check_equiv := check_equiv *)
(* let () = Sautility.check_equiv_list := check_equiv_list *)

let checkeq gvars=
  (* SY_CEQ.check_relaxeq_formula gvars *)
  CEQ.checkeq_formulas (List.map CP.name_of_spec_var gvars)

let checkeq_ass gvars ls_ex_ass0 ls_act_ass0=
  let rec look_up_eq ((ex_lhs,ex_rhs) as ex) ls_act_ass done_act_ass=
    match ls_act_ass with
    | [] -> (false, [])
    | (act_lhs, act_rhs)::rest ->
      let b1, _ = (checkeq gvars) ex_lhs act_lhs in
      if b1 then
        let b2, _ = (checkeq gvars) ex_rhs act_rhs in
        if b2 then (true, done_act_ass@rest)
        else look_up_eq ex rest (done_act_ass@[(act_lhs, act_rhs)])
      else
        look_up_eq ex rest (done_act_ass@[(act_lhs, act_rhs)])
  in
  let rec loop_helper ls_ex_ass ls_act_ass =
    match ls_ex_ass with
    | [] -> true, None
    | ex::ex_rest ->
      let b, ls_act_rem = look_up_eq ex ls_act_ass ls_act_ass in
      if not b then
        false, Some ex
      else loop_helper ex_rest ls_act_rem
  in
  loop_helper ls_ex_ass0 ls_act_ass0

let validate_x ls_ex_es0 ls_act_es0=
  (*********INTERNAL********)
  let validate_one (guide_vars, es_f, ls_ex_ass) es=
    (*compare es_formula*)
    (* let b1 = SY_CEQ.check_relaxeq_formula guide_vars es_f es.CF.es_formula in *)
    let b1,_ = (checkeq guide_vars) es_f es.CF.es_formula in
    (*compare constrs*)
    if b1 then
      let b2= if ls_ex_ass = [] then true else
          let ls_act_ass = (List.map (fun hp -> (hp.CF.hprel_lhs, hp.CF.hprel_rhs)) es.CF.es_infer_hp_rel # get_stk_recent)@
                           (List.map (fun (_,lhs,rhs) ->
                                (CF.formula_of_pure_P lhs no_pos,
                                 CF.formula_of_pure_P rhs no_pos)) es.CF.es_infer_rel # get_stk_recent) in
          let b2a,_ = checkeq_ass guide_vars ls_ex_ass ls_act_ass in
          b2a
      in
      b2
    else
      b1
  in
  let rec find_2_validate_helper ls_act_es ex_es done_act_es=
    match ls_act_es with
    | [] -> (false,[])
    | act_es::rest ->
      let b= validate_one ex_es act_es in
      if b then (true,done_act_es@rest) else
        find_2_validate_helper rest ex_es (done_act_es@[act_es])
  in
  let rec find_2_validate ls_ex_es ls_act_es=
    match ls_ex_es with
    | [] -> true
    | ex_es::exp_rest ->
      let b, act_rest = find_2_validate_helper ls_act_es ex_es [] in
      if not b then
        (*diff*)
        false
      else
        find_2_validate exp_rest act_rest
  in
  (*********END INTERNAL********)
  let b = find_2_validate ls_ex_es0 ls_act_es0 in
  (b, None, [])

let validate ls_ex_es ls_act_es=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr2a = (pr_list_ln (pr_pair pr2 pr2)) in
  let pr3 = pr_list_ln (pr_triple pr1 pr2 pr2a) in
  let pr4 = pr_list_ln Cprinter.string_of_entail_state_short in
  let pr5 f_opt = match f_opt with
    | None -> "None"
    | Some f -> pr2 f
  in
  Debug.no_2 "SC.validate" pr3 pr4 (pr_triple string_of_bool pr5 pr2a)
    (fun _ _ -> validate_x ls_ex_es ls_act_es)
    ls_ex_es ls_act_es


let _ = Lemproving.sleek_entail := sleek_entail_check;;
