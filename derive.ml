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

let generate_extn_ho_procs prog cviews extn_view_name=
  let mk_ho_b args p =
    fun svl ->
        let ss = List.combine args svl in
        let n_p = CP.subst ss p in
        let n_p1,_ = CP.norm_exp_min_max n_p in
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
      (* let _ =  Debug.info_pprint ("   from_args: "^ (!CP.print_svl from_args)) no_pos in *)
      (* let _ =  Debug.info_pprint ("   to_args: "^ (!CP.print_svl to_args)) no_pos in *)
      let ss3 = List.combine from_args to_args in
      let new_p = CP.subst ss3 p in
      (* let _ =  Debug.info_pprint ("   p_non_extn1: "^ (!CP.print_formula p_non_extn1)) no_pos in *)
      new_p
    else p
  in
  let mk_ho_ind args val_extns p rec_ls=
    (* let rec_args = List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) in *)
    (* let _ =  CP.extract_outer_inner p args val_extns rec_args in [] *)
    fun svl val_extns1 rec_ls1->
      (* let svl1 = List.concat (snd (List.split rec_ls)) in *)
      (*find subformula has svl1*)
      (* let _ =  Debug.info_pprint ("   p: "^ (!CP.print_formula p)) no_pos in *)
      (* let _ =  Debug.info_pprint ("   svl: "^ (!CP.print_svl svl)) no_pos in *)
      let p_extn, p_non_extn = partition_extn_svl p svl in
      (* let _ =  Debug.info_pprint ("   p_extn: "^ (!CP.print_formula p_extn)) no_pos in *)
      let from_rec_args =  List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls) in
      let rec_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
      let ((is_bag_constr,(outer, root_e), (inner_e, first_e)), exquans, irr_ps) =  CP.extract_outer_inner p_extn args val_extns from_rec_args in
      (*combine bag or non-bag constrs*)
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
      (* let n_outer = CP.mk_pformula_from_tmpl outer n_root_e n_inner_e no_pos in *)
      (* let n_p = (CP.BForm ((n_outer, None), None)) in *)
      (* let n_p1,quans = CP.norm_exp_min_max n_p in *)
      let n_p2,quans = CP.mk_formula_from_tmp outer n_root_e n_inner_e exquans irr_ps no_pos in
      (* let _ =  Debug.info_pprint ("   n_p: "^ (!CP.print_formula n_p)) no_pos in *)
      (*other constraints*)
      let n_p3= if CP.isConstTrue p_non_extn then n_p2 else
      (*assume we extend one property each*)
            let ls_to_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
            (*this step is necessary for tree like*)
            let new_ps = List.map (fun to_arg -> process_other_const from_rec_args [to_arg] p_non_extn) ls_to_args in
            let pos = CP.pos_of_formula n_p2 in
            let n_p4 = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) n_p2 new_ps in
            n_p4
      in
      (n_p3,quans)
  in
  let extn_v = C.look_up_view_def_raw cviews extn_view_name in
  let extn_fs = fst (List.split extn_v.C.view_un_struc_formula) in
  let inv_p = (MCP.pure_of_mix extn_v.C.view_user_inv) in
  let (brs, val_extns) = CF.classify_formula_branch extn_fs inv_p extn_view_name
    extn_v.C.view_vars extn_v.C.view_prop_extns in
  let b_brs, ind_brs = List.partition (fun (_, ls) -> ls=[]) brs in
  (*now, we assume we always have <= 1 base case and <=1 ind case*)
  let ho_bs = List.map (fun (p,_) ->  mk_ho_b extn_v.C.view_vars p) b_brs in
  let ho_inds = List.map (fun (p, ls) -> mk_ho_ind extn_v.C.view_vars
      val_extns p ls) ind_brs in
  (* (extn_view_name, b_brs, ind_brs, val_extns, extn_inv) *)
  (* let _ =  Debug.info_pprint ("   extn_v.C.view_vars: "^ (!CP.print_svl extn_v.C.view_vars)) no_pos in *)
  (extn_view_name, ho_bs, ho_inds(* , CP.filter_var inv_p extn_v.C.view_vars *))

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
  let (extn_vname, extn_ho_bs, extn_ho_inds(* , extn_user_inv *)) = generate_extn_ho_procs prog cviews extn_view_name in
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
  let (base_brs,ind_brs) = CF.extract_abs_formula_branch fs orig_view.C.view_name view_derv.I.view_name n_args ls_dname_pos false in
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
    (* let orig_user_inv = (MCP.pure_of_mix orig_view.C.view_user_inv) in *)
  (* let _ =  Debug.info_pprint ("   extn_inv: "^ (!CP.print_formula extn_user_inv)) no_pos in *)
  (* let n_user_inv =  MCP.mix_of_pure (CP.mkAnd orig_user_inv extn_user_inv (CP.pos_of_formula orig_user_inv)) in *)
  (* let _ =  Debug.info_pprint ("   n_user_inv: "^ (!CP.print_formula (MCP.pure_of_mix n_user_inv))) no_pos in *)
  let der_view = {orig_view with
      C.view_name = view_derv.I.view_name;
        (* C.view_kind = C.View_DERV; *)
      C.view_vars = orig_view.C.view_vars@n_args;
      C.view_formula = new_struct_f;
      C.view_un_struc_formula = new_un_struc_formulas;
      C.view_raw_base_case = rbc;
      C.view_is_rec = extn_ind_brs <> [];
    (* C.view_user_inv = n_user_inv; *)
  }
  in
  der_view

let trans_view_one_derv (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv view_derv : C.view_decl =
  let pr1= pr_list pr_id in
  let pr = (pr_pair (pr_pair pr_id pr1) (pr_triple pr_id pr1 pr1)) in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view_one_derv" pr pr_r  (fun _ -> trans_view_one_derv_x prog cviews derv view_derv) view_derv

let trans_view_one_spec_x (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) view_derv ((orig_view_name,orig_args),(spec_view_name,extn_props,extn_args)) :
       C.view_decl =
  let do_extend_base_case orig_fs spec_fs=
    match orig_fs with
      | [] -> []
      | [(f)] -> [f]
      | _ -> report_error no_pos "derive.trans_view_one_spec_x: not handle yet 1"
  in
  let do_extend_ind_case (f,val_extns,rec_extns) spec_ind_fs=
    let rec helper ls=
      match ls with
        | [] -> f
        | (p,rec_list1)::rest ->
            let rec_extn_spec = List.concat (snd (List.split rec_list1)) in
            let rec_extn = List.concat (snd (List.split rec_extns)) in
            (* let _ =  Debug.info_pprint ("   p: "^ (!CP.print_formula p)) no_pos in *)
            (* let _ =  Debug.info_pprint ("   rec_extn: "^ (!CP.print_svl rec_extn)) no_pos in *)
            (* let _ =  Debug.info_pprint ("   rec_extn_spec: "^ (!CP.print_svl rec_extn_spec)) no_pos in *)
            (* if List.length rec_extn_spec = List.length rec_extn then *)
            if List.length rec_list1 = List.length rec_extn then
              let ss = List.combine rec_extn_spec rec_extn in
              let p1 = CP.subst ss p in
              CF.mkAnd_pure f (MCP.mix_of_pure p1) (CF.pos_of_formula f)
            else
              helper rest
    in
    helper spec_ind_fs
  in
  let spec_view = C.look_up_view_def_raw cviews spec_view_name in
 (**********************************)
 (*
   EXTN: (1) lookup, not found: (2) generate one and store for other use.
   Now, always generate a new one
 *)
 (**********************************)
  let extn_view_name=
    match spec_view.C.view_parent_name with
      | None -> report_error no_pos "derive.trans_view_one_spec_x: a spec view must base on extn view"
      | Some n -> n
  in
  (* let _ =  Debug.info_pprint ("   extn_view_name: "^ extn_view_name) no_pos in *)
  (* let (extn_vname, extn_ho_bs, extn_ho_inds(\* , extn_user_inv *\)) = generate_extn_ho_procs prog cviews extn_view_name in *)
  (* let extn_view = C.look_up_view_def_raw cviews extn_view_name in *)
  (**********************************)
 (*
   SPEC
 *)
 (**********************************)
  (*spec process*)
  let spec_fs,_ = List.split spec_view.C.view_un_struc_formula in
  let inv_p = (MCP.pure_of_mix spec_view.C.view_user_inv) in
  let (spec_brs, spec_val_extns) = CF.classify_formula_branch spec_fs inv_p extn_view_name (* spec_view.C.view_name *)
    spec_view.C.view_vars spec_view.C.view_prop_extns in
  let spec_b_brs, spec_ind_brs = List.partition (fun (_, ls) -> ls=[]) spec_brs in
 (**********************************)
 (*
   BASE VIEW: (1) abs untruct formula, (2) extract ANN and (3) apply extn_ho
 *)
 (**********************************)
  (*formula: spec*)
  (*new args*)
  (* let n_args = List.map (fun (id, CP.SpecVar (t,_,pr)) ->  CP.SpecVar (t,id,pr)) ss in *)
  let orig_view = C.look_up_view_def_raw cviews orig_view_name in
  (*find data fields anns*)
  let ls_dname_pos = I.look_up_field_ann prog orig_view.C.view_data_name extn_props in
  let orig_fs,labels = List.split orig_view.C.view_un_struc_formula in
  let ss = List.combine orig_view.C.view_vars spec_view.C.view_vars in
  let spec_fs = List.map (CF.subst ss) orig_fs in
  let (orig_b_brs,orig_ind_brs) = CF.extract_abs_formula_branch spec_fs orig_view.C.view_name view_derv.I.view_name spec_view.C.view_vars ls_dname_pos true in
  (* let orig_inv_p = (MCP.pure_of_mix spec_view.C.view_user_inv) in *)
  (* let (orig_brs, orig_val_extns) = CF.classify_formula_branch orig_fs orig_inv_p orig_view.C.view_name *)
  (*   orig_view.C.view_vars orig_view.C.view_prop_extns in *)
  (* let orig_b_brs, orig_ind_brs = List.partition (fun (_, ls) -> ls=[]) orig_brs in *)
  (*extend base cases*)
  let extn_base_brs = do_extend_base_case orig_b_brs spec_b_brs in
    (*extend ind cases*)
  let extn_ind_brs = List.map (fun a -> do_extend_ind_case a spec_ind_brs) orig_ind_brs in
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
    (* let orig_user_inv = (MCP.pure_of_mix orig_view.C.view_user_inv) in *)
  (* let _ =  Debug.info_pprint ("   extn_inv: "^ (!CP.print_formula extn_user_inv)) no_pos in *)
  (* let n_user_inv =  MCP.mix_of_pure (CP.mkAnd orig_user_inv extn_user_inv (CP.pos_of_formula orig_user_inv)) in *)
  (* let _ =  Debug.info_pprint ("   n_user_inv: "^ (!CP.print_formula (MCP.pure_of_mix n_user_inv))) no_pos in *)
  let spec_view = {orig_view with
      C.view_name = view_derv.I.view_name;
        (* C.view_kind = C.View_DERV; *)
      C.view_vars = spec_view.C.view_vars;
      C.view_formula = new_struct_f;
      C.view_un_struc_formula = new_un_struc_formulas;
      C.view_raw_base_case = rbc;
      C.view_is_rec = extn_ind_brs <> [];
    (* C.view_user_inv = n_user_inv; *)
  }
  in
  spec_view

let trans_view_one_spec (prog : I.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv view_spec : C.view_decl =
  let pr1= pr_list pr_id in
  let pr = (pr_pair (pr_pair pr_id pr1) (pr_triple pr_id pr1 pr1)) in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view_one_spec" pr pr_r  (fun _ -> trans_view_one_spec_x prog cviews derv view_spec) view_spec

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
    | [((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args))] ->
        let der_view,s =
          let extn_view = C.look_up_view_def_raw cviews extn_view_name in
          if extn_view.C.view_kind = C.View_SPEC then
            let der_view = trans_view_one_spec prog cviews derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) in
           (der_view,("************VIEW_SPECIFIED*************"))
          else
             let der_view = trans_view_one_derv prog cviews derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) in
             (der_view,("************VIEW_DERIVED*************"))
        in
        let _ =
             if !debug_derive_flag then
               let _ =  print_endline s in
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
