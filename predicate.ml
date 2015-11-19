#include "xdebug.cppo"
open VarGen
open Globals
open Gen

module DD = Debug
module Err = Error
module I = Iast
(* module CA = Cast *)
module CP = Cpure
module CPP = Cpure_pred
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher



let pure_relation_name_of_heap_pred (CP.SpecVar (_, hp, p))=
  let rec look_up map=
    match map with
    | [] -> report_error no_pos "predicate.pure_relation_name_of_heap_pred"
    | (id1,id2)::rest -> if String.compare id1 hp = 0 then (CP.SpecVar (RelT [], id2, p)) else
        look_up rest
  in
  look_up !Cast.pure_hprel_map


let heap_pred_name_of_pure_relation (CP.SpecVar (_, pure_hp, p))=
  let rec look_up map=
    match map with
    | [] -> None
    | (id1,id2)::rest -> if String.compare id2 pure_hp = 0 then Some (CP.SpecVar(HpT, id1, p)) else
        look_up rest
  in
  look_up !Cast.pure_hprel_map


let pure_of_heap_pred_gen_h hf0=
  let rec helper hf=
    match hf with
    | CF.Star { CF.h_formula_star_h1 = hf1;
                CF.h_formula_star_h2 = hf2;
                CF.h_formula_star_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1,nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ -> CF.Star {CF.h_formula_star_h1 = nh1;
                        CF.h_formula_star_h2 = nh2;
                        CF.h_formula_star_pos = pos}
      in (nh, ps1@ps2)
    | CF.StarMinus { CF.h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF.h_formula_starminus_aliasing = al;
                     CF.h_formula_starminus_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1, nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ -> CF.StarMinus { CF.h_formula_starminus_h1 = nh1;
                              CF.h_formula_starminus_h2 = nh2;
                              CF.h_formula_starminus_aliasing = al;
                              CF.h_formula_starminus_pos = pos}
      in (nh, ps1@ps2)
    | CF.ConjStar { CF.h_formula_conjstar_h1 = hf1;
                    CF.h_formula_conjstar_h2 = hf2;
                    CF.h_formula_conjstar_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1, nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ ->  CF.ConjStar { CF.h_formula_conjstar_h1 = nh1;
                              CF.h_formula_conjstar_h2 = nh2;
                              CF.h_formula_conjstar_pos = pos}
      in (nh, ps1@ps2)
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1, nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ -> CF.ConjConj { CF.h_formula_conjconj_h1 = nh1;
                             CF.h_formula_conjconj_h2 = nh2;
                             CF.h_formula_conjconj_pos = pos}
      in (nh, ps1@ps2)
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1, nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ -> CF.Phase { CF.h_formula_phase_rd = nh1;
                          CF.h_formula_phase_rw = nh2;
                          CF.h_formula_phase_pos = pos}
      in (nh, ps1@ps2)
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let nh1,ps1 = helper hf1 in
      let nh2, ps2 = helper hf2 in
      let nh = match nh1, nh2 with
        | (CF.HEmp,CF.HEmp) -> CF.HEmp
        | (CF.HEmp,_) -> nh2
        | (_, CF.HEmp) -> nh1
        | _ -> CF.Conj { CF.h_formula_conj_h1 = nh1;
                         CF.h_formula_conj_h2 = nh2;
                         CF.h_formula_conj_pos = pos}
      in (nh, ps1@ps2)
    | CF.HRel (hp, eargs, p) ->
      let prel = pure_relation_name_of_heap_pred hp in
      let p= CP.mkRel prel eargs p in
      (CF.HEmp, [(p,hp)])
    | _ -> (hf,[])
  in
  helper hf0

let pure_of_heap_pred_x pos hfs=
  let ps, p_hps = List.fold_left ( fun (ls,ls2) hf ->
      let _, pr_ps =  pure_of_heap_pred_gen_h hf in
      let ps,hprels = List.split pr_ps in
      (ls@ps, ls2@hprels)
    ) ([],[]) hfs
  in
  let p = CP.conj_of_list ps pos in
  p,p_hps

let pure_of_heap_pred pos hfs=
  let pr1 = !CP.print_formula in
  let pr2 = pr_list_ln Cprinter.prtt_string_of_h_formula in
  (* let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  Debug.no_1 "pure_of_heap_pred" pr2 (pr_pair pr1 !CP.print_svl)
    (fun _ -> pure_of_heap_pred_x pos hfs) hfs

(* let pure_of_heap_pred_x f0= *)
(*   let rec helper f= *)
(*     match f with *)
(*       | CF.Base fb -> *)
(*             let nh, ps = pure_of_heap_pred_h fb.CF.formula_base_heap in *)
(*             let new_p = CP.conj_of_list ps fb.CF.formula_base_pos in *)
(*             CF.Base { fb with CF.formula_base_pure = MCP.merge_mems fb.CF.formula_base_pure (MCP.mix_of_pure new_p) true; *)
(*                 CF.formula_base_heap = nh; *)
(*             } *)
(*       | CF.Exists _ -> *)
(*             let qvars, base1 = CF.split_quantifiers f in *)
(*             let nf = helper base1 in *)
(*             CF.add_quantifiers qvars nf *)
(*       | CF.Or orf -> *)
(*             let nf1 = helper orf.CF.formula_or_f1 in *)
(*             let nf2 = helper orf.CF.formula_or_f2 in *)
(*             ( CF.Or {orf with CF.formula_or_f1 = nf1; *)
(*                 CF.formula_or_f2 = nf2;}) *)
(*   in *)
(*   helper f0 *)


let trans_rels_gen pf0 =
  let rec helper pf=
    match pf with
    | CP.BForm (bf,a) -> begin
        match bf with
        | (CP.RelForm (r, eargs, p),x) ->
          let ohp = heap_pred_name_of_pure_relation r in
          (
            match ohp with 
            | None -> (pf,[])
            | Some hp -> (CP.BForm (((CP.BConst (true, p)), x) ,a),  [(CF.HRel (hp, eargs, p))])
          )
        | _ -> (pf, [])
      end
    | CP.And (f1,f2,p) -> let nf1, hf1 = helper f1 in
      let nf2, hf2= helper f2 in
      let np = match (CP.isConstTrue nf1), (CP.isConstTrue nf2) with
        | true,true -> nf1
        | true,_ -> nf2
        | _, true -> nf1
        | _ -> CP.And (nf1,nf2,p)
      in (np, hf1@hf2)
    | CP.AndList lp-> let r,hfs = List.fold_left (fun (ps, hfs) (l, p) ->
        let np, n_hfs = helper p in
        if CP.isConstTrue np then
          (ps, hfs@n_hfs)
        else (ps@[(l,np)], hfs@n_hfs)
      ) ([],[]) lp in
      if r = [] then (CP.mkTrue no_pos, hfs) else (CP.AndList r,hfs)
    | CP.Or (f1,f2,c,p) -> let nf1, hf1 = helper f1 in
      let nf2, hf2= helper f2 in
      let np = match (CP.isConstTrue nf1), (CP.isConstTrue nf2) with
        | true,true -> nf1
        | true,_ -> nf2
        | _, true -> nf1
        | _ -> CP.Or (nf1,nf2, c,p)
      in (np, hf1@hf2)
    | CP.Not (f,b,p) -> let np,hfs = helper f in
      if CP.isConstTrue np then
        (CP.mkTrue p, hfs)
      else (CP.Not (np, b, p), hfs)
    | CP.Forall (a,f,c,p) -> let np,hfs = helper f in
      if CP.isConstTrue np then
        (CP.mkTrue p, hfs)
      else
        (CP.Forall (a,np,c,p), hfs)
    | CP.Exists (a,f,b,p) -> let np,hfs = helper f in
      if CP.isConstTrue np then
        (CP.mkTrue p, hfs)
      else
        (CP.Exists (a,np,b,p), hfs)
  in
  helper pf0

let trans_rels_x pf0 =
  let rec helper pf=
    match pf with
    | CP.BForm (bf,a) -> begin
        match bf with
        | (CP.RelForm (r, eargs, p),x) ->
          let ohp = heap_pred_name_of_pure_relation r in
          (
            match ohp with 
            | None -> None
            | Some hp -> Some (hp, CF.HRel (hp, eargs, p))
          )
        | _ -> None
      end
    | _ -> None
  in
  let ps = CP.list_of_conjs pf0 in
  let pr_hp_rhs = List.map helper ps in
  List.fold_left (fun r (r_opt) -> match r_opt with
      | None -> r
      | Some a -> r@[a]
    ) [] pr_hp_rhs

let trans_rels pf0 =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv Cprinter.prtt_string_of_h_formula) in
  Debug.no_1 "trans_rels" pr1 ( pr2)
    (fun _ -> trans_rels_x pf0) pf0

let heap_pred_of_pure_x p0=
  let _,hfs = trans_rels_gen p0 in
  match hfs with
  | [] -> false, CF.HEmp
  | _ -> let hf = CF.join_star_conjunctions hfs in
    true,hf
(* let pos = CP.pos_of_formula p0 in *)
(* let f0 = CF.formula_of_heap hf pos in *)
(* CF.mkAnd_pure f0 (MCP.mix_of_pure np) pos *)

let heap_pred_of_pure p0=
  let pr1 = !CP.print_formula in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  Debug.no_1 "heap_pred_of_pure" pr1 (pr_pair string_of_bool pr2)
    (fun _ -> heap_pred_of_pure_x p0) p0

(******************************************)
(***************PRED_EXTN**********************)
(******************************************)
(******************************************)
(***************PURE*****************)
(******************************************)
let  partition_extn_svl_x p svl=
  let check_one f=
    let svl0 = CP.fv f in
    (CP.intersect_svl svl0 svl <> [])
  in
  let ps = CP.list_of_conjs p in
  let ps_extn,ps_non_extn = List.partition check_one ps in
  let new_p= CP.conj_of_list ps_extn (CP.pos_of_formula p) in
  let p_non_extn= CP.conj_of_list ps_non_extn (CP.pos_of_formula p) in
  (new_p, p_non_extn)

let partition_extn_svl p svl=
  let pr1 = !CP.print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "partition_extn_svl" pr1 pr2 (pr_pair pr1 pr1)
    (fun _ _ -> partition_extn_svl_x p svl) p svl

(******************************************)
(*************END PURE***************)
(******************************************)


let generate_extn_ho_procs prog cviews extn_view_name extn_args=
  let mk_ho_b args val_extns p =
    fun svl val_extns1 ->
      (* let () =  Debug.info_pprint ("  val_extns: "^ (!CP.print_svl val_extns)) no_pos in *)
      (* let () =  Debug.info_pprint ("  val_extns1: "^ (!CP.print_svl val_extns1)) no_pos in *)
      (*may be nonnull*)
      let ss = if List.length val_extns = List.length val_extns1 then
          List.combine (args@val_extns) (svl@val_extns1)
        else List.combine (args) (svl)
      in
      (* let () =  Debug.info_pprint ("  p: "^ (!CP.print_formula p)) no_pos in *)
      let n_p = CP.subst ss p in
      let n_p1,_ = CPP.norm_exp_min_max n_p in
      (* let () =  Debug.info_pprint ("  n_p: "^ (!CP.print_formula n_p)) no_pos in *)
      (* let () =  Debug.info_pprint ("  n_p1: "^ (!CP.print_formula n_p1)) no_pos in *)
      n_p1
  in
  let mk_ho_ind_rec ann args p =
    match args with
    | [a] -> [a]
    | [] -> [] (*rec null pointer*)
    | _ -> report_error no_pos "astsimp.generate_extn_ho_procs: extend one property"
    (* (args, CP.mkTrue no_pos) *)
  in
  let process_other_const from_args to_args p=
    (*may need some filter: CP.filter_var: omit now*)
    if from_args <> [] then (*ind_case*)
      (* let rec_args0 = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls) in *)
      (* let () =  Debug.info_pprint ("   from_args: "^ (!CP.print_svl from_args)) no_pos in *)
      (* let () =  Debug.info_pprint ("   to_args: "^ (!CP.print_svl to_args)) no_pos in *)
      let ss3 = List.combine from_args to_args in
      let new_p = CP.subst ss3 p in
      (* let () =  Debug.info_pprint ("   p_non_extn1: "^ (!CP.print_formula p_non_extn1)) no_pos in *)
      new_p
    else p
  in
  let mk_ho_ind args val_extns p rec_ls=
    (* let rec_args = List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) in *)
    (* let () =  CP.extract_outer_inner p args val_extns rec_args in [] *)
    fun svl val_extns1 rec_ls1->
      (* let svl1 = List.concat (snd (List.split rec_ls)) in *)
      (*find subformula has svl1*)
      (* let () =  Debug.info_pprint ("   p: "^ (!CP.print_formula p)) no_pos in *)
      (* let () =  Debug.info_pprint ("   svl: "^ (!CP.print_svl svl)) no_pos in *)
      let p_extn, p_non_extn = partition_extn_svl p svl in
      (* let () =  Debug.info_pprint ("   p_extn: "^ (!CP.print_formula p_extn)) no_pos in *)
      let from_rec_args =  List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls) in
      let rec_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
      let ((is_bag_constr,(outer, root_e), (inner_e, first_e)), exquans, irr_ps) =  CPP.extract_outer_inner p_extn args val_extns from_rec_args in
      (*combine bag or non-bag constrs*)
      let comb_fn= if is_bag_constr then CPP.mk_exp_from_bag_tmpl else CPP.mk_exp_from_non_bag_tmpl in
      (*cmb inner most exp*)
      (* let () =  Debug.info_pprint ("   val_extns: "^ (!CP.print_svl val_extns)) no_pos in *)
      (* let () =  Debug.info_pprint ("   val_extns1: "^ (!CP.print_svl val_extns1)) no_pos in *)
      (* let ss1 = List.combine val_extns val_extns1 in *)
      (* let n_first_e = CP.e_apply_subs ss1 first_e in *)
      let n_inner_e = List.fold_left (fun e1 e2 -> comb_fn inner_e e1 e2 no_pos)
          first_e (List.map (fun sv -> CP.Var (sv,no_pos)) (val_extns1@rec_args)) in
      (*outer most pformula*)
      let ss2 = List.combine args svl in
      let n_root_e = CP.e_apply_subs ss2 root_e in
      (* let n_outer = CP.mk_pformula_from_tmpl outer n_root_e n_inner_e no_pos in *)
      (* let n_p = (CP.BForm ((n_outer, None), None)) in *)
      (* let n_p1,quans = CP.norm_exp_min_max n_p in *)
      let n_p2,quans = CPP.mk_formula_from_tmp outer n_root_e n_inner_e exquans irr_ps no_pos in
      (* let () =  Debug.info_pprint ("   n_p: "^ (!CP.print_formula n_p)) no_pos in *)
      (*other constraints*)
      let n_p3= if CP.isConstTrue p_non_extn then n_p2 else
          (*assume we extend one property each*)
          let ls_to_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
          (*this step is necessary for tree like*)
          let new_ps = List.map (fun to_arg -> process_other_const (from_rec_args@val_extns) ([to_arg]@val_extns1) p_non_extn) ls_to_args in
          let pos = CP.pos_of_formula n_p2 in
          let n_p4 = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) n_p2 new_ps in
          n_p4
      in
      (n_p3,quans)
  in
  let extn_v = x_add Cast.look_up_view_def_raw x_loc cviews extn_view_name in
  let extn_fs0 = fst (List.split extn_v.Cast.view_un_struc_formula) in
  let inv_p0 = (MCP.pure_of_mix extn_v.Cast.view_user_inv) in
  let pr_ext_vars = List.combine extn_v.Cast.view_vars extn_args in
  let fr_extn_args,ss = List.fold_left (fun (r1,r2) (CP.SpecVar (t, id, p), new_id) ->
      let n_sv = CP.SpecVar (t, new_id, p) in
      (r1@[n_sv], r2@[(CP.SpecVar (t, id, p), n_sv)])
    ) ([],[]) pr_ext_vars in
  let extn_fs = List.map (fun f -> x_add CF.subst ss f) extn_fs0 in
  let inv_p = CP.subst ss inv_p0 in
  let (brs, val_extns) = CF.classify_formula_branch extn_fs inv_p extn_view_name
      fr_extn_args (* extn_v.Cast.view_vars *) extn_v.Cast.view_prop_extns in
  let b_brs, ind_brs = List.partition (fun (_, ls) -> ls=[]) brs in
  (*now, we assume we always have <= 1 base case and <=1 ind case*)
  let ho_bs = List.map (fun (p,_) ->  mk_ho_b (* extn_v.Cast.view_vars *)fr_extn_args val_extns p) b_brs in
  let ho_inds = List.map (fun (p, ls) -> mk_ho_ind (*extn_v.Cast.view_vars*) fr_extn_args
                             val_extns p ls) ind_brs in
  (* (extn_view_name, b_brs, ind_brs, val_extns, extn_inv) *)
  (* let () =  Debug.info_pprint ("   extn_v.C.view_vars: "^ (!CP.print_svl extn_v.C.view_vars)) no_pos in *)
  (extn_view_name, ho_bs, ho_inds(* , CP.filter_var inv_p extn_v.C.view_vars *))

let extend_pred_one_derv_x (prog : I.prog_decl) cprog hp_defs hp args ((orig_pred_name,orig_args),(extn_view_name,extn_props,extn_args), ls_extn_pos) =
  (*********INTERNAL********)
  let cviews = cprog.Cast.prog_view_decls in
  let rec look_up_hp_def hp defs=
    match defs with
    | [] -> report_error no_pos "Pred.extend_pred_one_derv: base pred has not not defined"
    | def::rest -> let hp1,_ = CF.extract_HRel def.CF.def_lhs in
      if String.compare hp (CP.name_of_spec_var hp1) = 0 then def else
        look_up_hp_def hp rest
  in
  let do_extend_base_case ho_bs extn_args val_svl f=
    match ho_bs with
    | [] -> f
    | ho_fn::_ -> (*now, we just care the first one*)
      let extn_p = ho_fn extn_args val_svl in
      (* let () =  Debug.info_pprint ("  pure np: "^ (!CP.print_formula extn_p)) no_pos in *)
      let nf = CF.mkAnd_pure f (MCP.mix_of_pure extn_p) no_pos in
      (*let () =  Debug.info_pprint ("  nf: "^ (!CF.print_formula nf)) no_pos in *)
      nf
  in
  let do_extend_ind_case ho_inds extn_args (f,val_extns,rec_extns)=
    match ho_inds with
    | [] -> f
    | ho_fn::_ -> (*now, we just care the first one*)
      (*quans: ex quans from normalize min/max*)
      let quans0, bare_f = CF.split_quantifiers f in
      let extn_p,quans = ho_fn extn_args val_extns rec_extns in
      let nf = CF.mkAnd_pure bare_f (MCP.mix_of_pure extn_p) no_pos in
      (*add rec_extns into exists*)
      let new_extn_args = CP.remove_dups_svl (List.concat (snd (List.split rec_extns))) in
      let nf1 = CF.add_quantifiers (quans0@new_extn_args@quans) nf in
      (* let () =  Debug.info_pprint ("  nf1: "^ (!CF.print_formula nf1)) no_pos in *)
      nf1
  in
  (*********END INTERNAL********)
  let extn_view = x_add Cast.look_up_view_def_raw x_loc cviews extn_view_name in
  let (extn_vname, extn_ho_bs, extn_ho_inds(* , extn_user_inv *)) = generate_extn_ho_procs prog cviews extn_view_name extn_args in
  (**********************************)
 (*
   BASE VIEW: (1) abs untruct formula, (2) extract ANN and (3) apply extn_ho
 *)
  (**********************************)
  (*new args*)
  let ss = List.combine extn_args extn_view.Cast.view_vars in
  let n_args = List.map (fun (id, CP.SpecVar (t,_,pr)) ->  CP.SpecVar (t,id,pr)) ss in
  let orig_pred = look_up_hp_def orig_pred_name hp_defs in
  let _,orig_args_in_def = CF.extract_HRel orig_pred.CF.def_lhs in
  let pr_orig_vars = List.combine orig_args_in_def orig_args in
  let orig_args,orig_ss = List.fold_left (fun (r1,r2) (CP.SpecVar (t, id, p), new_id) ->
      let n_sv = CP.SpecVar (t, new_id, p) in
      (r1@[n_sv], r2@[(CP.SpecVar (t, id, p), n_sv)])
    ) ([],[]) pr_orig_vars in
  let orig_pred_data_name = Cast.look_up_hp_decl_data_name cprog.Cast.prog_hp_decls (CP.name_of_spec_var hp) (List.hd ls_extn_pos) in
  (*find data fields anns*)
  let ls_dname_pos = I.look_up_field_ann prog orig_pred_data_name extn_props in
  (*formula: extend with new args*)
  let fs0 = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] orig_pred.CF.def_rhs in
  let fs = List.map (x_add CF.subst orig_ss) fs0 in
  let pure_extn_svl = CF.retrieve_args_from_locs orig_args ls_extn_pos in
  let (base_brs,ind_brs) = x_add CF.extract_abs_formula_branch fs orig_pred_name (CP.name_of_spec_var hp) n_args ls_dname_pos pure_extn_svl false false in
  (*extend base cases*)
  let extn_base_brs = List.map (fun (p,val_svl)-> do_extend_base_case extn_ho_bs n_args val_svl p) base_brs in
  (*extend ind cases*)
  let extn_ind_brs = List.map (do_extend_ind_case extn_ho_inds n_args) ind_brs in


  let rhs = CF.disj_of_list (extn_base_brs@extn_ind_brs) no_pos in
  rhs

let extend_pred_one_derv (prog : I.prog_decl) cprog hp_defs hp args extn_info =
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  let pr3 = pr_triple (pr_pair pr_id (pr_list pr_id)) (pr_triple pr_id (pr_list pr_id) (pr_list pr_id)) (pr_list string_of_int) in
  Debug.no_3 "extend_pred_one_derv" !CP.print_sv pr2 pr3 pr1
    (fun _ _ _ -> extend_pred_one_derv_x prog cprog hp_defs hp args extn_info)
    hp args extn_info


(* let do_sanity_check derv= *)
(*   let derv_args = derv.I.view_vars in *)
(*   let all_extn_args = List.concat (List.map (fun ((_,orig_args),(_,_,extn_args)) -> orig_args@extn_args) derv.I.view_derv_info) in *)
(*   let diff = Gen.BList.difference_eq (fun s1 s2 -> String.compare s1 s2 =0) derv_args all_extn_args in *)
(*   if diff <> [] then *)
(*     report_error no_pos ("in view_extn: " ^ derv.I.view_name ^ ", args: " ^ *)
(*     (String.concat ", " diff) ^ " are not declared.") *)
(*   else () *)

let extend_pred_dervs_x (prog : I.prog_decl) cprog hp_defs hp args derv_info =
  (* let () = do_sanity_check derv_info in *)
  match derv_info with
  | [] -> report_error no_pos (x_loc^"astsimp.trans_view_dervs: 1")
  | [((orig_pred_name,orig_args),(extn_view_name,extn_props,extn_args), extn_poss)] ->
    let der_view(*,s*) =
      (* let extn_view = x_add Cast.look_up_view_def_raw x_loc cprog.Cast.prog_view_decls extn_view_name in *)
      (* if extn_view.C.view_kind = C.View_SPEC then *)
      (*   let der_view = trans_view_one_spec prog cviews derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) in *)
      (*  (der_view(\*,("************VIEW_SPECIFIED*************")*\)) *)
      (* else *)
      let der_view = extend_pred_one_derv prog cprog hp_defs hp args ((orig_pred_name,orig_args),(extn_view_name,extn_props,extn_args), extn_poss) in
      (der_view(*,("************VIEW_DERIVED*************")*))
    in
    der_view
  | _ -> report_error no_pos (x_loc^"astsimp.trans_view_dervs: not handle yet")


let extend_pred_dervs (prog : I.prog_decl) cprog hp_defs hp args derv_info =
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "extend_pred_dervs" !CP.print_sv pr2 pr1
    (fun _ _ -> extend_pred_dervs_x prog cprog hp_defs hp args derv_info) hp args

let leverage_self_info_x xform formulas anns data_name=
  let detect_anns_f f=
    let svl = CF.fv f in
    CP.intersect_svl anns svl <> []
  in
  let fs = CF.list_of_disjs formulas in
  let ls_self_not_null = List.map detect_anns_f fs in
  let self_not_null = List.for_all (fun b -> b) ls_self_not_null in
  let self_info =
    let self_sv = CP.SpecVar (Named data_name,self,Unprimed) in
    if self_not_null then
      CP.mkNeqNull self_sv no_pos
    else CP.mkNull self_sv no_pos
  in
  CP.mkAnd xform self_info (CP.pos_of_formula xform)

let leverage_self_info xform formulas anns data_name=
  let pr1= !CP.print_formula in
  let pr2 = !CF.print_formula in
  Debug.no_3 "leverage_self_info" pr1 pr2 (!CP.print_svl) pr1
    (fun _ _ _ -> leverage_self_info_x xform formulas anns data_name) xform formulas anns

(***************END PRED_EXTN**********************)
