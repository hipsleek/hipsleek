open Globals
open Exc.GTable 
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only

module C = Cast
module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module CF = Cformula
(* module GV = Globalvars*)
module CP = Cpure
module MCP = Mcpure
module H = Hashtbl
module TP = Tpdispatcher
module Chk = Checks


let generate_extn_ho_procs prog cviews extn_view_name=
  let mk_ho_b args p =
    fun svl ->
        let ss = List.combine args svl in
        CP.subst ss p
  in
  let mk_ho_ind_rec ann args p =
    match args with
      | [a] -> [a]
      | [] -> [] (*rec null pointer*)
      | _ -> report_error no_pos "astsimp.generate_extn_ho_procs: extend one property"
    (* (args, CP.mkTrue no_pos) *)
  in
  let mk_ho_ind args val_extns p rec_ls=
    (* let rec_args = List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) in *)
    (* let _ =  CP.extract_outer_inner p args val_extns rec_args in [] *)
    fun svl val_extns1 rec_ls1->
      let svl1 = List.concat (snd (List.split rec_ls)) in
      (*find subformula has svl1--skip now*)
      let rec_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
      let (is_bag_constr,(outer, root_e), (inner_e, first_e)) =  CP.extract_outer_inner p args val_extns rec_args in
      (*combine bag and non-bag constrs*)
      let comb_fn= if is_bag_constr then CP.mk_exp_from_bag_tmpl else CP.mk_exp_from_non_bag_tmpl in
      (*cmb inner most exp*)
      (* let _ =  Debug.info_pprint ("   val_extns: "^ (!CP.print_svl val_extns)) no_pos in *)
      (* let _ =  Debug.info_pprint ("   val_extns1: "^ (!CP.print_svl val_extns1)) no_pos in *)
      (* let ss1 = List.combine val_extns val_extns1 in *)
      (* let n_first_e = CP.e_apply_subs ss1 first_e in *)
      let n_inner_e = List.fold_left (fun e1 e2 -> comb_fn inner_e e1 e2 no_pos)
        first_e (List.map (fun sv -> CP.Var (sv,no_pos)) (val_extns1@rec_args)) in
      (*outer most pformula*)
      let ss2 = List.combine args svl in
      let n_root_e = CP.e_apply_subs ss2 root_e in
      let n_outer = CP.mk_pformula_from_tmpl outer n_root_e n_inner_e no_pos in
      let n_p = (CP.BForm ((n_outer, None), None)) in
      (* let _ =  Debug.info_pprint ("   n_p: "^ (!CP.print_formula n_p)) no_pos in *)
      let n_p1,quans = CP.norm_exp_min_max n_p in
      (n_p1,quans)
  in
  let extn_v = C.look_up_view_def_raw cviews extn_view_name in
  let extn_fs = fst (List.split extn_v.C.view_un_struc_formula) in
  let (brs, val_extns) = CF.classify_formula_branch extn_fs extn_view_name
    extn_v.C.view_vars extn_v.C.view_prop_extns in
  let b_brs, ind_brs = List.partition (fun (_, ls) -> ls=[]) brs in
  (*now, we assume we always have <= 1 base case and <=1 ind case*)
  let ho_bs = List.map (fun (p,_) ->  mk_ho_b extn_v.C.view_vars p) b_brs in
  let ho_inds = List.map (fun (p, ls) -> mk_ho_ind extn_v.C.view_vars
      val_extns p ls) ind_brs in
  (* (extn_view_name, b_brs, ind_brs, val_extns) *)
  (extn_view_name, ho_bs, ho_inds)

let trans_view_one_derv_x (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) view_derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) :
       C.view_decl =
  let do_extend_base_case ho_bs extn_args f=
    match ho_bs with
      | [] -> f
      | ho_fn::_ -> (*now, we just care the first one*)
          let extn_p = ho_fn extn_args in
          let nf = CF.mkAnd_pure f (MCP.mix_of_pure extn_p) no_pos in
          (* let _ =  Debug.info_pprint ("  nf: "^ (!CF.print_formula nf)) no_pos in *)
          nf
  in
  let do_extend_ind_case ho_inds extn_args (f,val_extns,rec_extns)=
    match ho_inds with
      | [] -> f
      | ho_fn::_ -> (*now, we just care the first one*)
          (*quans: ex quans from normalize min/max*)
          let extn_p,quans = ho_fn extn_args val_extns rec_extns in
          let nf = CF.mkAnd_pure f (MCP.mix_of_pure extn_p) no_pos in
          (*add rec_extns into exists*)
          let new_extn_args = CP.remove_dups_svl (List.concat (snd (List.split rec_extns))) in
          let nf1 = CF.add_quantifiers (new_extn_args@quans) nf in
          (* let _ =  Debug.info_pprint ("  nf1: "^ (!CF.print_formula nf1)) no_pos in *)
          nf1
  in
 (**********************************)
 (*
   EXTN: (1) lookup, not found: (2) generate one and store for other use.
   Now, always generate a new one
 *)
 (**********************************)
  let extn_view = C.look_up_view_def_raw cviews extn_view_name in
  let (extn_vname, extn_ho_bs, extn_ho_inds) = generate_extn_ho_procs prog cviews extn_view_name in
 (**********************************)
 (*
   BASE VIEW: (1) abs untruct formula, (2) extract ANN and (3) apply extn_ho
 *)
 (**********************************)
 (*new args*)
  let ss = List.combine extn_args extn_view.C.view_vars in
  let n_args = List.map (fun (id, CP.SpecVar (t,_,pr)) ->  CP.SpecVar (t,id,pr)) ss in
  let orig_view = C.look_up_view_def_raw cviews orig_view_name in
 (*find data fields anns*)
  let ls_dname_pos = I.look_up_field_ann prog orig_view.C.view_data_name extn_props in
 (*formula: extend with new args*)
  let fs,labels = List.split orig_view.C.view_un_struc_formula in
  let (base_brs,ind_brs) = CF.extract_abs_formula_branch fs orig_view.C.view_name view_derv.I.view_name n_args ls_dname_pos in
 (*extend base cases*)
  let extn_base_brs = List.map (do_extend_base_case extn_ho_bs n_args) base_brs in
 (*extend ind cases*)
  let extn_ind_brs = List.map (do_extend_ind_case extn_ho_inds n_args) ind_brs in
 (*unstruct*)
  let new_un_struc_formulas = List.combine (extn_base_brs@extn_ind_brs) labels in
 (*struct*)
  let struct_fs = List.map (fun f -> let p = CF.pos_of_formula f in CF.struc_formula_of_formula f p)
    (extn_base_brs@extn_ind_brs) in
  let new_struct_f = match struct_fs with
    | [] -> orig_view.C.view_formula
    | _ ->
        let p = CF.pos_of_struc_formula orig_view.C.view_formula in
        List.fold_left (fun f1 f2 -> CF.mkEOr f1 f2 p) (List.hd struct_fs) (List.tl struct_fs)
  in
 (*todo: view_base_case*)
 (*raw base case*)
  let rec f_tr_base f = 
    let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
    match f with
      | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
      | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
      | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos
  in
  let rbc = List.fold_left (fun a (c,l)-> 
      let fc = f_tr_base c in
      if (CF.isAnyConstFalse fc) then a 
      else match a with 
        | Some f1  -> Some (CF.mkOr f1 fc no_pos)
        | None -> Some fc) None new_un_struc_formulas
  in
  {orig_view with
      C.view_name = view_derv.I.view_name;
     (* C.view_kind = C.View_DERV; *)
      C.view_vars = orig_view.C.view_vars@n_args;
      C.view_formula = new_struct_f;
      C.view_un_struc_formula = new_un_struc_formulas;
      C.view_raw_base_case = rbc;
      C.view_is_rec = extn_ind_brs <> [];
  }

let trans_view_one_derv (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv view_derv : C.view_decl =
  let pr1= pr_list pr_id in
  let pr = (pr_pair (pr_pair pr_id pr1) (pr_triple pr_id pr1 pr1)) in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view_one_derv" pr pr_r  (fun _ -> trans_view_one_derv_x prog cviews derv view_derv) view_derv

let do_sanity_check derv=
  let derv_args = derv.I.view_vars in
  let all_extn_args = List.concat (List.map (fun ((_,orig_args),(_,_,extn_args)) -> orig_args@extn_args) derv.I.view_derv_info) in
  let diff = Gen.BList.difference_eq (fun s1 s2 -> String.compare s1 s2 =0) derv_args all_extn_args in
  if diff <> [] then
    report_error no_pos ("in view_extn: " ^ derv.I.view_name ^ ", args: " ^
    (String.concat ", " diff) ^ " are not declared.")
  else ()

let trans_view_dervs_x (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv : C.view_decl =
  let _ = do_sanity_check derv in
  match derv.I.view_derv_info with
    | [] -> report_error no_pos "astsimp.trans_view_dervs: 1"
    | [d] -> let der_view = trans_view_one_derv prog cviews derv d in
             let _ =
               if !debug_derive_flag then
                 let _ =  print_endline ("************VIEW_DERIVED*************") in
                 let _ =  print_endline (Cprinter.string_of_view_decl_short der_view)  in
                 ()
               else ()
             in
             der_view
    | _ -> report_error no_pos "astsimp.trans_view_dervs: not handle yet"


let trans_view_dervs (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv : C.view_decl =
  let pr_r = Cprinter.string_of_view_decl in
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "trans_view_dervs" pr pr_r  (fun _ -> trans_view_dervs_x prog cviews derv) derv

(* let trans_view_additional_x cprog cviews pos= *)
(*   let process_one vdef= *)
(*     if vdef.C.view_kind = C.View_DERV then *)
(*       (\*xform*\) *)
(*       let (xform0, addr_vars0, ms) = Solver.xpure_symbolic cprog (C.formula_of_unstruc_view_f vdef) in *)
(*       let addr_vars = CP.remove_dups_svl addr_vars0 in *)
(*       let xform = MCP.simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula xform0 (TP.simplify_a 10) in *)
(*  (\* let _ = print_endline ("\n xform: " ^ (Cprinter.string_of_mix_formula xform)) in *\) *)
(*       let xform1 = (TP.simplify_with_pairwise 1 (CP.drop_rel_formula (MCP.pure_of_mix xform))) in *)
(*       let ls_disj = CP.list_of_disjs xform1 in *)
(*       let xform2 = MCP.mix_of_pure (CP.disj_of_list (Gen.BList.remove_dups_eq CP.equalFormula ls_disj) pos) in *)
(*       { vdef with *)
(*           C.view_kind = C.View_NORM; *)
(*           C.view_x_formula = xform2; *)
(*           C.view_xpure_flag = TP.check_diff vdef.C.view_user_inv xform2; *)
(*           C.view_addr_vars = addr_vars; *)
(*           C.view_baga = (match ms.CF.mem_formula_mset with | [] -> [] | h::_ -> h) ; *)
(*       } *)
(*     else vdef *)
(*   in *)
(*   List.map process_one cviews *)

(* let trans_view_additional cprog cviews pos= *)
(*   let pr1 = pr_list Cprinter.string_of_view_decl in *)
(*   Debug.ho_1 "trans_view_additional" pr1 pr1 *)
(*       (fun _ -> trans_view_additional_x cprog cviews pos) cviews *)
