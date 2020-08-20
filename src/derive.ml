#include "xdebug.cppo"
open VarGen
open Globals
open Exc.GTable 
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only

(* module C = Cast *)
module E = Env
module Err = Error
(* module I = Iast *)
module IF = Iformula
module IP = Ipure
module CF = Cformula
module C = Cast
(* module GV = Globalvars*)
module CP = Cpure
module MCP = Mcpure
module H = Hashtbl
(* module TP = Tpdispatcher *)
module Chk = Checks
module CFE = Cf_ext

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
let rev_trans_spec_var v = match v with CP.SpecVar (t,v,p)-> (v,p) 

let generate_extn_ho_procs prog cviews extn_view_name=
  let mk_ho_b args val_extns p =
    fun svl val_extns1 ->
      (* let () =  Debug.info_pprint ("  val_extns: "^ (!CP.print_svl val_extns)) no_pos in *)
      (* let () =  Debug.info_pprint ("  val_extns1: "^ (!CP.print_svl val_extns1)) no_pos in *)
      (*may be nonnull*)
      let ss = if List.length val_extns = List.length val_extns1 then
          List.combine (args@val_extns) (svl@val_extns1)
        else List.combine (args) (svl)
      in
      (*let () =  Debug.info_pprint ("  p: "^ (!CP.print_formula p)) no_pos in*)
      let n_p = CP.subst ss p in
      let n_p1,_ = Cpure_pred.norm_exp_min_max n_p in
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
  let mk_ho_ind args val_extns p0 rec_ls=
    (* let rec_args = List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) in *)
    (* let () =  CP.extract_outer_inner p args val_extns rec_args in [] *)
    fun svl val_extns1 rec_ls1->
      (* let svl1 = List.concat (snd (List.split rec_ls)) in *)
      (*find subformula has svl1*)
      let () =  Debug.ninfo_hprint (add_str "   p0: " (!CP.print_formula )) p0 no_pos in
      let () =  Debug.ninfo_hprint (add_str "   svl: "  (!CP.print_svl )) svl no_pos in
      (* let ss = if List.length val_extns = List.length val_extns1 then *)
      (*   List.combine (args@val_extns) (svl@val_extns1) *)
      (* else List.combine (args) (svl) *)
      (* in *)
      let p = (* CP.subst ss *) p0 in
      let () =  Debug.ninfo_hprint (add_str "   p: " (!CP.print_formula )) p no_pos in
      let p_extn, p_non_extn = partition_extn_svl p0 args in
      (* let () =  Debug.info_pprint ("   p_extn: "^ (!CP.print_formula p_extn)) no_pos in *)
      let from_rec_args =  List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls) in
      let rec_args = List.concat (List.map (fun (ann,args) -> mk_ho_ind_rec ann args p) rec_ls1) in
      let ((is_bag_constr,(outer, root_e), (inner_e, first_e)), exquans, irr_ps) =  Cpure_pred.extract_outer_inner p_extn args val_extns from_rec_args in
      (*combine bag or non-bag constrs*)
      let comb_fn= if is_bag_constr then Cpure_pred.mk_exp_from_bag_tmpl else Cpure_pred.mk_exp_from_non_bag_tmpl in
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
      let n_p2,quans = Cpure_pred.mk_formula_from_tmp outer n_root_e n_inner_e exquans irr_ps no_pos in
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
  let extn_v = x_add C.look_up_view_def_raw x_loc cviews extn_view_name in
  let extn_fs = fst (List.split extn_v.C.view_un_struc_formula) in
  let inv_p = (MCP.pure_of_mix extn_v.C.view_user_inv) in
  let (brs, val_extns) = CF.classify_formula_branch extn_fs inv_p extn_view_name
      extn_v.C.view_vars extn_v.C.view_prop_extns in
  let b_brs, ind_brs = List.partition (fun (_, ls) -> ls=[]) brs in
  (*now, we assume we always have <= 1 base case and <=1 ind case*)
  let ho_bs = List.map (fun (p,_) ->  mk_ho_b extn_v.C.view_vars val_extns p) b_brs in
  let ho_inds = List.map (fun (p, ls) -> mk_ho_ind extn_v.C.view_vars
                             val_extns p ls) ind_brs in
  (* (extn_view_name, b_brs, ind_brs, val_extns, extn_inv) *)
  (* let () =  Debug.info_pprint ("   extn_v.C.view_vars: "^ (!CP.print_svl extn_v.C.view_vars)) no_pos in *)
  (extn_view_name, ho_bs, ho_inds(* , CP.filter_var inv_p extn_v.C.view_vars *))

(*
lower_map_views: a map of the transformation of lower views in the hierachy
*)
let trans_view_one_derv_x (prog : Iast.prog_decl) rev_formula_fnc trans_view_fnc lower_map_views
    (cviews (*orig _extn*) : C.view_decl list) view_derv
    ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) :
  C.view_decl =
  let do_extend_base_case ho_bs extn_args val_svl f=
    match ho_bs with
    | [] -> f
    | ho_fn::_ -> (*now, we just care the first one*)
      let extn_p = ho_fn extn_args val_svl in
      (* let () =  Debug.ninfo_pprint ("  np: "^ (!CP.print_formula extn_p)) no_pos in *)
      let nf = CF.mkAnd_pure f (MCP.mix_of_pure extn_p) no_pos in
      (* let () =  Debug.ninfo_pprint ("  nf: "^ (!CF.print_formula nf)) no_pos in *)
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
      (* let () =  Debug.ninfo_pprint ("  nf1: "^ (!CF.print_formula nf1)) no_pos in *)
      nf1
  in
  (**********************************)
 (*
   EXTN: (1) lookup, not found: (2) generate one and store for other use.
   Now, always generate a new one
 *)
  (**********************************)
  let extn_view = x_add C.look_up_view_def_raw x_loc cviews extn_view_name in
  (*subst args of extn and extn_args*)
  let ss = List.combine extn_args extn_view.C.view_vars in
  let (extn_vname, extn_ho_bs, extn_ho_inds(* , extn_user_inv *)) = generate_extn_ho_procs prog cviews extn_view_name in
  (**********************************)
 (*
   BASE VIEW: (1) abs untruct formula, (2) extract ANN and (3) apply extn_ho
 *)
  (**********************************)
  (*new args*)
  let n_args = List.map (fun (id, CP.SpecVar (t,_,pr)) ->  CP.SpecVar (t,id,pr)) ss in
  let orig_view = x_add C.look_up_view_def_raw x_loc cviews orig_view_name in
  (*find data fields anns*)
  let ls_dname_pos = Iast.look_up_field_ann prog orig_view.C.view_data_name extn_props in
  (*formula: extend with new args*)
  let fs,labels = List.split orig_view.C.view_un_struc_formula in
  let fs1 = List.map (fun f -> fst (Cfutil.subst_views_form lower_map_views false f)) fs in
  let fs = List.map Cformula.elim_exists (List.map Cfutil.fresh_exists fs1) in
  let pos = view_derv.Iast.view_pos in
  let () =  Debug.ninfo_hprint (add_str "   orig_view.C.view_data_name: " (pr_id )) orig_view.C.view_data_name pos in
  let self_sv = (CP.SpecVar (Named (orig_view.C.view_data_name),self, Unprimed)) in
  let pure_extn_svl = [self_sv] in
  let (base_brs,ind_brs) = x_add CF.extract_abs_formula_branch fs orig_view.C.view_name view_derv.Iast.view_name n_args ls_dname_pos  pure_extn_svl false true in
  (*extend base cases*)
  let extn_base_brs = List.map (fun (p,val_svl)-> do_extend_base_case extn_ho_bs n_args val_svl p) base_brs in
  (*extend ind cases*)
  let extn_ind_brs = List.map (do_extend_ind_case extn_ho_inds n_args) ind_brs in
  (*unstruct*)
  let view_sv = orig_view.C.view_vars@n_args in
  let n_pure_domains = [(extn_view_name, 0, List.length view_sv)] in
  (*OLD**)
  (* let new_un_struc_formulas = List.combine (extn_base_brs@extn_ind_brs) labels in *)
  (*   (\*struct*\) *)
  (* let struct_fs = List.map (fun f -> let p = CF.pos_of_formula f in CF.struc_formula_of_formula f p) *)
  (*   (extn_base_brs@extn_ind_brs) in *)
  (* let new_struct_f = match struct_fs with *)
  (*   | [] -> orig_view.C.view_formula *)
  (*   | _ -> *)
  (*     CF.EList (List.map  (fun sf -> (Label_only.empty_spec_label_def, sf)) struct_fs) *)
  (* in *)
  (*   (\*todo: view_base_case*\) *)
  (*   (\*raw base case*\) *)
  (* let rec f_tr_base f =  *)
  (*   let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in *)
  (*   match f with *)
  (*     | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos *)
  (*     | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos *)
  (*     | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos *)
  (* in *)
  (* let rbc = List.fold_left (fun a (c,l)->  *)
  (*     let fc = f_tr_base c in *)
  (*     if (CF.isAnyConstFalse fc) then a  *)
  (*     else match a with  *)
  (*       | Some f1  -> Some (CF.mkOr f1 fc no_pos) *)
  (*       | None -> Some fc) None new_un_struc_formulas *)
  (* in *)
  (* let orig_user_inv = (MCP.pure_of_mix orig_view.C.view_user_inv) in *)
  (* (\* let () =  Debug.info_pprint ("   extn_inv: "^ (!CP.print_formula extn_user_inv)) no_pos in *\) *)
  (* let extn_user_inv = try *)
  (*   let ss = List.combine extn_view.C.view_vars n_args in *)
  (*   CP.subst ss (MCP.pure_of_mix extn_view.C.view_user_inv) *)
  (* with _ -> CP.mkTrue no_pos *)
  (* in *)
  (* let n_user_inv =  MCP.mix_of_pure (CP.mkAnd orig_user_inv extn_user_inv (CP.pos_of_formula orig_user_inv)) in *)
  (* let iview_orig = Iast.look_up_view_def_raw x_loc prog.Iast.prog_view_decls orig_view.C.view_name in *)
  (* (\* let () =  Debug.info_pprint ("  iview_orig.Iast.view_imm_map: "^ ( *\) *)
  (* (\*   (pr_list (pr_pair Ipure.string_of_ann string_of_int)) iview_orig.Iast.view_imm_map)) no_pos in *\) *)
  (* let view_derv = {view_derv with Iast.view_labels = (List.map (fun _ -> Label_only.LOne.unlabelled) view_sv_vars, false); *)
  (*      Iast.view_imm_map = iview_orig.Iast.view_imm_map@(List.map (fun _ -> (Ipure.ConstAnn Mutable, 0)) n_args); *)
  (* } in *)
  (* let view_sv, labels, ann_params, view_vars_gen = Immutable.split_sv view_sv_vars view_derv in *)
  (* (\* let () =  Debug.info_pprint ("  ann_params: "^ ( *\) *)
  (* (\*   (pr_list (pr_pair !CP.print_annot_arg string_of_int)) ann_params)) no_pos in *\) *)
  (* (\* let () =  Debug.info_pprint ("  C.view_ann_params: "^ ( *\) *)
  (* (\*   (pr_list (pr_pair !CP.print_annot_arg string_of_int)) orig_view.C.view_ann_params)) no_pos in *\) *)
  (* (\* let () =  Debug.info_pprint ("  view_vars_gen: "^ ( *\) *)
  (* (\*       (pr_list (pr_pair CP.print_view_arg string_of_int)) (view_vars_gen))) no_pos in *\) *)
  (* (\*always generate the new arg to the end, root is 0*\) *)
  (* let der_view = {orig_view with *)
  (*     C.view_name = view_derv.Iast.view_name; *)
  (*       (\* C.view_kind = View_DERV; *\) *)
  (*     C.view_vars = view_sv ; *)
  (*     C.view_labels = labels; *)
  (*     C.view_ann_params  = ann_params; *)
  (*     C.view_params_orig = view_vars_gen; *)
  (*     C.view_formula = new_struct_f; *)
  (*     C.view_un_struc_formula = new_un_struc_formulas; *)
  (*     C.view_raw_base_case = rbc; *)
  (*     C.view_is_rec = extn_ind_brs <> []; *)
  (*     C.view_domains = orig_view.C.view_domains@n_pure_domains; *)
  (*     C.view_user_inv = n_user_inv; *)
  (* } *)
  (* in *)
  (*END **** OLD**)
  let is_fs, tis = List.fold_left (fun (r_ifs, r_tis) f_body ->
      let f_body1,tis = Cfutil.norm_free_vars f_body ( self_sv::view_sv) in
      let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} f_body1 in
      let (h ,mf,_,_,_,_) = Cformula.split_components f_body in
      let eqsets = (MCP.ptr_equations_without_null mf) in
      let hdns, hvns,_ = Cformula.get_hp_rel_h_formula h in
      let dnodes = List.map (fun dn -> dn.Cformula.h_formula_data_node) hdns in
      let dnodes_cl = Cformula.find_close dnodes eqsets in
      let vnodes = List.map (fun vn -> vn.Cformula.h_formula_view_node) hvns in
      let vnodes_cl = Cformula.find_close vnodes eqsets in
      let i_body = rev_formula_fnc new_body in
      let isf = Iformula.normal_formula (List.map rev_trans_spec_var dnodes_cl)
          (List.map rev_trans_spec_var vnodes_cl) i_body in
      (r_ifs@[ isf], r_tis@tis)
    ) ([],[]) (extn_base_brs@extn_ind_brs) in
  let struc_body = Iformula.EList (List.map (fun sf -> (Label_only.empty_spec_label_def, sf)) is_fs) in
  let data_name = orig_view.C.view_data_name in
  let vars =  List.map (fun (CP.SpecVar (_, v, p))-> (v^(match p with Primed -> "PRM"| _ -> ""))
    ) view_sv in
  let tvars = (List.map (fun (CP.SpecVar (t, v, _))-> (t,v)) (view_sv)) in
  let imm_map = Immutable.icollect_imm struc_body vars data_name prog.Iast.prog_data_decls in
  let () =  Debug.ninfo_hprint (add_str "  data_name " pr_id) data_name no_pos in
  let n_iview = { view_derv with
                  Iast.view_data_name = data_name;
                  Iast.view_vars = vars;
                  Iast.view_imm_map = imm_map;
                  Iast.view_labels = List.map (fun _ ->  Label_only.LOne.unlabelled) vars, false;
                  Iast.view_modes = List.map (fun _ -> ModeOut) vars ;
                  Iast.view_typed_vars =  tvars;
                  Iast.view_kind = View_NORM;
                  Iast.view_derv = false;
                  Iast.view_parent_name = None;
                  Iast.view_prop_extns = [];
                  Iast.view_derv_info = [];
                  Iast.view_pt_by_self  = [];
                  Iast.view_formula = struc_body;
                  Iast.view_inv_lock = None;
                  Iast.view_is_prim = false;
                  Iast.view_is_hrel = None;
                  Iast.view_invariant = Ipure.mkTrue no_pos;
                  Iast.view_mem = None;
                  Iast.view_materialized_vars = List.map (fun mp -> CP.name_of_spec_var mp.C.mater_var) orig_view.C.view_materialized_vars;
                  Iast.try_case_inference = false; }
  in
  let () = try
      let der_vdecl = Iast.look_up_view_def_raw x_loc prog.Iast.prog_view_decls view_derv.Iast.view_name in
      let () = der_vdecl.Iast.view_data_name <- data_name in
      ()
    with _ ->
      let () = prog.Iast.prog_view_decls <- prog.Iast.prog_view_decls@[n_iview] in
      ()
  in
  let der_view0 = trans_view_fnc prog [] cviews tis n_iview in
  let der_view = {der_view0 with C.view_domains = orig_view.C.view_domains@n_pure_domains;} in
  der_view

let trans_view_one_derv_wrapper prog rev_form_fnc trans_view_fnc lower_map_views cviews derv
    (((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) as view_derv)=
  let orig_view = x_add C.look_up_view_def_raw x_loc cviews orig_view_name in
  if List.for_all (fun (l_extn_view,_,_) ->
      String.compare l_extn_view extn_view_name !=0) orig_view.C.view_domains then
    let new_vdef = trans_view_one_derv_x prog rev_form_fnc trans_view_fnc lower_map_views cviews derv view_derv in
    let () =  x_tinfo_hp (add_str "   pure extension" pr_id) (derv.Iast.view_name ^ ": extend " ^ orig_view_name ^ " to " ^ extn_view_name ^"\n") no_pos in
    let () = x_tinfo_hp (add_str "(raw) new view (donot have base case, addr, material)" Cprinter.string_of_view_decl_short) new_vdef no_pos in
    let () = x_add_1 Cprog_sleek.update_view_decl_scc_only new_vdef in
    (true,new_vdef)
  else
    let () =  x_dinfo_hp (add_str "   pure extension" pr_id) (orig_view_name ^ " has been extended to " ^ extn_view_name^ " already \n") no_pos in
    (false,orig_view)

let trans_view_one_derv (prog : Iast.prog_decl) rev_form_fnc trans_view_fnc lower_map_views
      (cviews (*orig _extn*) :  C.view_decl list) derv view_derv: (bool*C.view_decl) =
  let pr1= pr_list pr_id in
  let pr = (pr_pair (pr_pair pr_id pr1) (pr_triple pr_id pr1 pr1)) in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view_one_derv" pr (pr_pair string_of_bool pr_r)
    (fun _ -> trans_view_one_derv_wrapper prog rev_form_fnc trans_view_fnc lower_map_views
        cviews derv view_derv) view_derv

let trans_view_one_spec_x (prog : Iast.prog_decl) (cviews (*orig _extn*) : C.view_decl list) view_derv ((orig_view_name,orig_args),(spec_view_name,extn_props,extn_args)) :
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
        (* let () =  Debug.info_pprint ("   p: "^ (!CP.print_formula p)) no_pos in *)
        (* let () =  Debug.info_pprint ("   rec_extn: "^ (!CP.print_svl rec_extn)) no_pos in *)
        (* let () =  Debug.info_pprint ("   rec_extn_spec: "^ (!CP.print_svl rec_extn_spec)) no_pos in *)
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
  let spec_view = x_add C.look_up_view_def_raw x_loc cviews spec_view_name in
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
  (* let () =  Debug.info_pprint ("   extn_view_name: "^ extn_view_name) no_pos in *)
  (* let (extn_vname, extn_ho_bs, extn_ho_inds(\* , extn_user_inv *\)) = generate_extn_ho_procs prog cviews extn_view_name in *)
  (* let extn_view = x_add C.look_up_view_def_raw x_loc cviews extn_view_name in *)
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
  let orig_view = x_add C.look_up_view_def_raw x_loc cviews orig_view_name in
  (*find data fields anns*)
  let ls_dname_pos = Iast.look_up_field_ann prog orig_view.C.view_data_name extn_props in
  let orig_fs,labels = List.split orig_view.C.view_un_struc_formula in
  let ss = List.combine orig_view.C.view_vars spec_view.C.view_vars in
  let spec_fs = List.map (x_add CF.subst ss) orig_fs in
  let pure_extn_svl = [ (CP.SpecVar (Named (view_derv.Iast.view_data_name),self, Unprimed))] in
  let (orig_b_brs,orig_ind_brs) = x_add CF.extract_abs_formula_branch spec_fs orig_view.C.view_name view_derv.Iast.view_name spec_view.C.view_vars ls_dname_pos pure_extn_svl true true in
  (* let orig_inv_p = (MCP.pure_of_mix spec_view.C.view_user_inv) in *)
  (* let (orig_brs, orig_val_extns) = CF.classify_formula_branch orig_fs orig_inv_p orig_view.C.view_name *)
  (*   orig_view.C.view_vars orig_view.C.view_prop_extns in *)
  (* let orig_b_brs, orig_ind_brs = List.partition (fun (_, ls) -> ls=[]) orig_brs in *)
  (*extend base cases*)
  let extn_base_brs = do_extend_base_case (fst (List.split orig_b_brs)) spec_b_brs in
  (*extend ind cases*)
  let extn_ind_brs = List.map (fun a -> do_extend_ind_case a spec_ind_brs) orig_ind_brs in
  (*unstruct*)
  let new_un_struc_formulas = List.combine (extn_base_brs@extn_ind_brs) labels in
  (*struct*)
  let struct_fs = List.map (fun f -> let p = CF.pos_of_formula f in CF.struc_formula_of_formula f p)
      (extn_base_brs@extn_ind_brs) in
  let new_struct_f = match struct_fs with
    | [] -> orig_view.C.view_formula
    | _ -> CF.EList (List.map  (fun sf -> (Label_only.empty_spec_label_def, sf)) struct_fs)
    (* let p = CF.pos_of_struc_formula orig_view.C.view_formula in *)
    (* List.fold_left (fun f1 f2 -> CF.mkEOr f1 f2 p) (List.hd struct_fs) (List.tl struct_fs) *)
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
  (* let () =  Debug.info_pprint ("   extn_inv: "^ (!CP.print_formula extn_user_inv)) no_pos in *)
  (* let n_user_inv =  MCP.mix_of_pure (CP.mkAnd orig_user_inv extn_user_inv (CP.pos_of_formula orig_user_inv)) in *)
  (* let () =  Debug.info_pprint ("   n_user_inv: "^ (!CP.print_formula (MCP.pure_of_mix n_user_inv))) no_pos in *)
  let spec_view = {orig_view with
                   C.view_name = view_derv.Iast.view_name;
                   (* C.view_kind = View_DERV; *)
                   C.view_vars = spec_view.C.view_vars;
                   C.view_formula = new_struct_f;
                   C.view_un_struc_formula = new_un_struc_formulas;
                   C.view_raw_base_case = rbc;
                   C.view_is_rec = extn_ind_brs <> [];
                   (* C.view_user_inv = n_user_inv; *)
                  }
  in
  spec_view

let trans_view_one_spec (prog : Iast.prog_decl) (cviews (*orig _extn*) : C.view_decl list) derv view_spec : C.view_decl =
  let pr1= pr_list pr_id in
  let pr = (pr_pair (pr_pair pr_id pr1) (pr_triple pr_id pr1 pr1)) in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view_one_spec" pr pr_r  (fun _ -> trans_view_one_spec_x prog cviews derv view_spec) view_spec

let do_sanity_check derv =
  let derv_args = derv.Iast.view_vars in
  let all_extn_args = List.concat (List.map (fun ((_,orig_args),(_,_,extn_args)) -> orig_args@extn_args) derv.Iast.view_derv_info) in
  let all_extn_args2 = List.concat (List.map (fun (_,_,extn_args) -> extn_args) derv.Iast.view_derv_extns) in
  let all_extn_args = all_extn_args@all_extn_args2 in
  let diff = Gen.BList.difference_eq (fun s1 s2 -> String.compare s1 s2 =0) derv_args all_extn_args in
  if diff <> [] then
    report_error no_pos (x_loc^"in view_extn: " ^ derv.Iast.view_name ^ ", args: " ^
                         (String.concat ", " diff) ^ " are not declared.")
  else ()

let trans_view_dervs (prog : Iast.prog_decl) rev_form_fnc trans_view_fnc lower_map_views
    (cviews (*orig _extn*): C.view_decl list) derv : C.view_decl =
  let () = do_sanity_check derv in
  let old_flag = !Globals.do_infer_inv in
  let () = Globals.do_infer_inv := true in
  let res =
    match derv.Iast.view_derv_info with
    | [] ->
      begin
        match derv.Iast.view_derv_from with
        | Some rgx ->
          let () = y_tinfo_hp (add_str "view_scc_obj" pr_id) HipUtil.view_scc_obj # string_of in
          let scc = HipUtil.view_scc_obj # get_scc in
          let () = y_tinfo_hp (add_str "view_scc_obj" (pr_list (fun v -> v.C.view_name)))  cviews in
          let () = y_tinfo_hp (add_str "view_name" pr_id)  derv.Iast.view_name in
          let () = y_tinfo_hp (add_str "derv_from" (string_of_regex_list (pr_pair pr_id string_of_bool)))  rgx in
          let pr = pr_list pr_id in
          let () = y_tinfo_hp (add_str "derv_extns" (pr_list (pr_triple pr_id pr pr))) derv.Iast.view_derv_extns in
          let sel = List.map (fun mr -> List.filter (fun e -> true) mr) scc in
          let () = y_tinfo_hp (add_str "scc selected" (pr_list (pr_list pr_id))) scc in
          failwith x_tbi
        | None ->
          report_error no_pos (x_loc^"astsimp.trans_view_dervs: (unknown command)")
      end
    | [((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args))] ->
      let der_view(*,s*) =
        let extn_view = x_add C.look_up_view_def_raw x_loc cviews extn_view_name in
        if extn_view.C.view_kind = View_SPEC then
          let der_view = trans_view_one_spec prog cviews derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) in
          (der_view(*,("************VIEW_SPECIFIED*************")*))
        else
          let _,der_view = trans_view_one_derv prog rev_form_fnc trans_view_fnc lower_map_views
              cviews derv ((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args)) in
          let iderv_view = Iast.look_up_view_def_raw x_loc prog.Iast.prog_view_decls derv.Iast.view_name in
          let () = iderv_view.Iast.view_data_name <- der_view.C.view_data_name in
          let () = iderv_view.Iast.view_derv <- false in
          (der_view(*,("************VIEW_DERIVED*************")*))
      in
      (* let () = *)
      (*      if !debug_derive_flag then *)
      (*        let () =  print_endline s in *)
      (*        let () =  print_endline (Cprinter.string_of_view_decl_short der_view)  in *)
      (*        () *)
      (*      else () *)
      (* in *)
      let () = y_tinfo_hp (add_str "der_view(old)" Cprinter.string_of_view_decl) der_view in
      der_view
    | _ -> report_error no_pos (x_loc^"astsimp.trans_view_dervs: not handle yet")
  in
  let () = Globals.do_infer_inv := old_flag in
  res


(* let trans_view_dervs_old (prog : Iast.prog_decl) rev_form_fnc trans_view_fnc lower_map_views *)
(*       (cviews (\*orig _extn*\): C.view_decl list) derv : C.view_decl = *)
(*   let pr_r = Cprinter.string_of_view_decl in *)
(*   let pr = Iprinter.string_of_view_decl in *)
(*   Debug.no_1 "trans_view_dervs" pr pr_r  (fun _ -> trans_view_dervs_x prog rev_form_fnc trans_view_fnc *)
(*       lower_map_views cviews derv) derv *)

let pr_sv = CP.print_sv

(* class datatable = *)
(*   object (self) *)
(*     val mutable lst = [] (\* (ptr,value) list *\) *)
(*     method add_data dn param =  *)
(*       lst <- (dn,param)::lst *)
(*     method find_tags dn =  *)
(*       try *)
(*         snd(List.find (fun (n,_) -> n=dn) lst) *)
(*       with _ -> failwith (x_loc^"does not exist :"^dn) *)
(*     method get_tag_mask dn (t:string) =  *)
(*       try  *)
(*         let tags = self # find_tags dn in *)
(*         List.map (fun ls -> List.mem t ls) tags *)
(*       with _ ->  *)
(*         if dn="node" then [false;true] *)
(*         else [false;true;true] *)
(*   end *)

let data_decl_obj = CFE.data_decl_obj

let global_extn_name =
  object (self) 
    val mutable lst = [] 
    val mutable seg_lst = []
    val id = ref 0

    method get_fresh_id = 
      let () = id := !id + 1 in !id
    
    method logging (s:string): unit =
      (* let h = "\n**global_extn_name** " in *)
      (* let () = print_endline_quiet (h^s) in *)
      ()
    method add_segmented (vn:string) res =
      match res with
      | None -> ()
      | Some (p:CP.spec_var) -> seg_lst <- (vn,p)::seg_lst 
    method get_segmented vn =
      try
        Some(snd(List.find (fun (v,_) -> vn=v) seg_lst))
      with _ -> None

    (* Check whether given_name has been used *)
    method check_dup given_name = 
      List.exists (fun (_, n) -> eq_str n given_name) lst

    (* method reserve_name given_name vn prop_name =                                       *)
    (*   let err_msg = "Cannot reserve "^given_name^" for ("^vn^", "^prop_name^")"^": " in *)
    (*   let n = self # find vn prop_name in                                               *)
    (*   match n with                                                                      *)
    (*   | Some pn -> y_winfo_pp (err_msg ^ "It has already named " ^ pn)                  *)
    (*   | None ->                                                                         *)
    (*     if self # check_dup given_name then                                             *)
    (*       y_winfo_pp (err_msg ^ "The name has been used for another")                   *)
    (*     else lst <- ((vn, prop_name), given_name)::lst                                  *)
      
    method mk_name given_name ?(vn_of_given_name=None) (vn:string) (prop_name:string) : string =
      (* let pname =                                 *)
      (*   if given_name = "" then vn^" "^prop_name  *)
      (*   else given_name in                        *)
      let n = self # find vn prop_name in
      let mut_r = HipUtil.view_scc_obj # is_mutual_rec vn in 
      let () = y_binfo_hp (add_str "mut_r" (string_of_bool)) mut_r in
      let () = y_binfo_hp (add_str "vn" pr_id) vn in
      let () = y_tinfo_hp (add_str "prop_name" pr_id) prop_name in
      let () = y_tinfo_hp (add_str "n" (pr_option pr_id)) n in
      match n with
      | Some pn -> 
        (* if given_name="" then pn                                        *)
        (* else if not(given_name=pn) then                                 *)
        (*   let () = y_tinfo_pp (given_name^" diff from existing "^pn) in *)
        (*   pn                                                            *)
        (* else pn                                                         *)
        let () = if not (given_name = "") && not (given_name = pn) then
          y_binfo_pp (given_name^" diff from existing "^pn)
        in pn
      | None ->
        let pname = 
          let for_vn = match vn_of_given_name with
            | Some pvn -> eq_str pvn vn 
            | None -> true (* given_name is not reserved *)
          in
          if given_name = "" || self # check_dup given_name || not for_vn then 
            let pvn = vn^"_"^prop_name in
            if not (eq_str pvn given_name) then pvn
            else pvn^"_"^(string_of_int (self # get_fresh_id))
          else given_name
        in
        self # logging ("Created "^pname);
        let () = lst <- ((vn, prop_name), pname)::lst in
        pname

    method find (vn:string) (prop_name:string): string option =
      try
        let (_,n) = List.find (fun ((v1,v2),_) -> v1=vn && v2=prop_name) lst in
        let () = self # logging ("Found "^n) in
        Some(n)
      with _ -> None
    method not_processed (vn:string) (prop_name:string) =
      ((self # find vn prop_name) = None)
    method retr_name (vn:string) (prop_name:string) : string =
      match self # find vn prop_name with
      | Some n -> n
      | None -> 
        let () = y_binfo_pp ((add_str "retr_name (Not found)" (pr_pair pr_id pr_id)) (vn,prop_name)) in
        ""
    method retr_prop (pname:string) : string =
      try
        let (f,s) = List.find (fun ((v1,v2),n) -> n=pname) lst in
        snd(f)
      with _ ->
        let () = self # logging ((add_str "retr_prop (Not found)" pr_id) pname) in
        ""
  end;;

(* let mk_extn_pred_name vn pname prop_name =      *)
(*   global_extn_name # mk_name pname vn prop_name *)

let retr_extn_pred_name vn pname  =
  global_extn_name # retr_name vn pname 

class prop_table pname (* name of extn *) ?(vn_of_pname=None) (prop_name, pview) (* extension view *) eq nnn_s tag_s =
  object (self)
    val mutable lst = [] (* (ptr,value) list *)
    val mutable def_lst = [] (* list of ptr with defined value *)
    val mutable pure_lst = []
    val mutable vns = []
    val mutable quan_vs = []
    val nnn = List.hd nnn_s
    val tag = List.hd tag_s
    val fresh = CP.fresh_spec_var
    val pr = !pr_sv
    val orig_sv = CP.mk_typed_spec_var Int (List.hd nnn_s) 
    val mutable self_sv = CP.mk_self None
    (* val mk_base = (fun v -> (!pr_sv v)^"=0") *)
    (* val mk_max = (fun v v1 v2 -> (!pr_sv v)^" = max("^(!pr_sv v1)^","^(!pr_sv v2)^")") *)
    (* val mk_inc = (fun v1 v2 -> (!pr_sv v1)^" = 1+"^(!pr_sv v2)) *)
    (* val pr_pure = fun x -> x *)
    val mk_eq = (fun v1 v2 -> CP.mk_eq_vars v1 v2)
    val mutable mk_base = (fun v -> CP.mk_eq_zero v)
    val mutable mk_max = (fun v v1 v2 -> CP.mk_max v v1 v2)
    val mutable mk_inc = (fun v v1 -> CP.mk_inc v v1)
    val mutable mk_sum = (fun v v1 v2 -> CP.mk_sum v v1 v2)
    (* val mk_inv = (fun  -> CP.mk_inc v v1) *)
    val pr_pure = fun x -> !CP.print_formula x
    val mutable inv = CP.mkTrue no_pos
    val mutable emap = CP.EMapSV.mkEmpty
    method logging s =
      (* let h = "\n**prop_table** " in *)
      (* let () =print_endline_quiet (h^s) in *)
      ()
    method mk_extn_pred_name vn (* pname *) =
      (* let n_pname =                                         *)
      (*   match vn_of_pname with                              *)
      (*   | None -> pname (* pname is not reserved *)         *)
      (*   | Some pvn -> (* pname has been reserved for pvn *) *)
      (*     if eq_str pvn vn then pname else ""               *)
      (* in                                                    *)
      let n = global_extn_name # mk_name pname ~vn_of_given_name:vn_of_pname vn prop_name in
      (* let () = self # logging ("mk_extn_pred_name:"^n) in *)
      n
    method create_from_prop_name vn =
      let n = global_extn_name # mk_name "" vn prop_name in
      let () = self # logging ("create_from_prop_name "^n^" "^(prop_name)) in
      n
    method mk_emap p =
      emap <- CP.EMapSV.build_eset (CP.pure_ptr_equations p)
    method set_inv = 
      inv <- CP.mk_geq orig_sv 0
    method get_inv =
      inv
    method reset_disj f =
      let (h,p,_,_,_,_) = CF.split_components f in
      self # mk_emap (MCP.pure_of_mix p);
      def_lst <- [];
      lst <- [(self_sv,orig_sv)];
      quan_vs <- [];
      pure_lst <- []
    method reset_view typ =
      self_sv <- CP.mk_self (Some typ);
      (* self # reset_disj *)
    method reset_mut vs =
      let () = y_tinfo_hp (add_str "p_table:name" pr_id) pname in
      (match pview with
       | None -> ()
       | Some vd -> 
         let () = y_winfo_pp "TODO : need to build functions of views here" in
         y_tinfo_hp (add_str "p_table:prop view" pr_id) vd.C.view_name);
      vns <- vs;
      (* self # reset_disj *)
    method is_mut_view (vn:string) : bool =
      if List.exists (fun v -> v=vn) vns then true
      else 
        (* check if non-rec view already processed *)
        not(global_extn_name # not_processed vn prop_name) 
    method proc_data ptr name args =
      let () = self # logging ((add_str "proc_data" (pr_triple pr pr_id (pr_list pr))) (ptr,name,args)) in
      let filter_mask mask ptrs =
        let rec aux mask ptrs =
          match mask,ptrs with
          | [],ptrs -> ptrs
          | _,[] -> []
          | x::ms,p::ps -> if x then p::(aux ms ps) else aux ms ps
        in aux mask ptrs
      in
      (* let () = y_tinfo_hp (add_str "proc_data" (pr_triple pr pr_id (pr_list pr))) (ptr,name,args) in *)
      let mask = data_decl_obj # get_tag_mask name tag in
      let to_ptrs = filter_mask mask args in
      self # add_node ptr to_ptrs
    method add_node ptr to_ptrs =
      let () = self # logging ((add_str "add_node " (pr_pair !CP.print_sv !CP.print_svl)) (ptr,to_ptrs)) in
      if to_ptrs==[] then self # mk_zero ptr
      else 
        let v0 = self # find_or_add ptr in
        let vs = List.map (fun p -> (self # find_or_add p)) to_ptrs in
        let rec aux v xs acc = match xs with
          | [] -> (v,acc)
          | x::rest -> 
            let fr_v = self # fresh_var in
            let p = mk_max fr_v x v in
            (* (pr fr_v)^" = max("^(pr x)^","^pr v^")" in *)
            aux fr_v rest (p::acc) in
        let (v,pure) = match vs with
          | [] -> failwith "impossible"
          | x::xs -> aux x xs [] in
        let final = mk_inc v0 v in
        (* (pr v0)^" = 1+"^(pr v) in *)
        self # push_def ptr;
        self # push_pure_lst (final::pure)
    method add_seg ptr sz opt_ptr =
      (* this is to support ptr::lseg<sz,opt_ptr> views *)
      let () = self # logging ((add_str "add_seg" (pr_pair !CP.print_sv (pr_opt !CP.print_sv))) (ptr,opt_ptr)) in
      let v0 = self # find_or_add ptr in
      begin
        match opt_ptr with
        | None -> self # push_pure (mk_eq v0 sz)
        | Some nptr -> 
          let v1 = self # find_or_add nptr in
          self # push_pure (mk_sum v0 sz v1)
      end
    method proc_view ptr vn (args:CP.spec_var list) =
      (* ptr=None means header of view vn *)
      let () = self # logging ((add_str "proc_view " (pr_triple (pr_opt !CP.print_sv) pr_id !CP.print_svl)) (ptr,vn,args)) in
      if self # is_mut_view vn then
        let new_vname = self # mk_extn_pred_name vn (* pname *) (* vn^"_"^pname *) in
        let (root,new_sv) = 
          match ptr with
          | None ->  (self_sv,orig_sv)
          | Some ptr -> 
            self # push_def ptr; 
            let prop_var = self # find_or_add ptr in
            let () = y_tinfo_hp (add_str "prop_var" !CP.print_sv) prop_var in
            let () = y_tinfo_hp (add_str "ptr" !CP.print_sv) ptr in
            let () = y_tinfo_hp (add_str "args" !CP.print_svl) args in
            (* !!! **derive.ml#772:prop_var:nnn_61 *)
            (* !!! **derive.ml#773:ptr:q *)
            (* !!! **derive.ml#774:args:[p_14] *)
            (* !!! **derive.ml#778:proc_view(C):(q,(WFSeg_sz,nnn_61)) *)
            begin
              match args with
              | qq::_ ->
                let fresh_v = self # fresh_var in
                let prop_qq = self # find_or_add qq in
                let () = self # push_pure (mk_sum prop_var fresh_v prop_qq) in
                (ptr,fresh_v)
              | [] -> (ptr,prop_var) 
            end
        in
        let r = (new_vname,new_sv) in
        let () = y_tinfo_hp (add_str "proc_view(C)" (pr_pair pr (pr_pair pr_id pr))) (root,r) in
        r
      else 
        let () = self # logging ("Not a mut-rec view.."^vn) in
        failwith "not a recursive view?"
    method get_pure = pure_lst
    method get_quan = quan_vs
    method add ptr new_nnn =
      lst <- (ptr,new_nnn):: lst
    method push_def ptr =
      def_lst <- ptr::def_lst
    method push_pure s =
      let () = self # logging ((add_str "push_pure" !CP.print_formula) s) in
      pure_lst <- s::pure_lst
    method push_pure_lst s =
      let () = self # logging ((add_str "push_pure_lst" (pr_list !CP.print_formula)) s) in
      pure_lst <- s@pure_lst
    method fresh_var =
      let v = fresh orig_sv in
      let () = quan_vs <-v::quan_vs in
      v
    method find_or_add ptr =
      (* let fresh nnn = nnn in *)
      let () = self # logging ((add_str "find_or_add " !CP.print_sv) ptr) in
      try
        snd(List.find (fun (x,_) -> 
            eq x ptr || CP.EMapSV.is_equiv emap x ptr) lst)
      with _ -> 
        let new_nnn = self # fresh_var in
        self # add ptr new_nnn;
        new_nnn
    method get_undef =
      let und = Gen.BList.difference_eq (fun (p1,_) p2 -> eq p1 p2 || CP.EMapSV.is_equiv emap p1 p2) lst def_lst in
      List.map fst und 
    method mk_zero ptr =
      let v = self # find_or_add ptr in
      self # push_def ptr;
      self # push_pure (mk_base v)
    method mk_undef_zero =
      let lst = self # get_undef in
      List.iter (fun p -> self # mk_zero p) lst
    method string_of_pure =
      ((pr_list pr_pure) pure_lst)
    method string_of_quan =
      (!CP.print_svl quan_vs)
    method string_of =
      let str = (pr_list (pr_pair pr pr)) lst in
      str^"\n pure:"^(self # string_of_pure)
      ^"\n quan:"^(self # string_of_quan)
  end;;

let compute_view_x_formula: (C.prog_decl -> C.view_decl -> int -> unit) ref =
  ref (fun _ _ _ -> failwith "TBI")
  
(* let prc_heap ptab = CFE.process_heap_prop_extn ptab *)

let store_segmented_view x vd =
  let opt = Cast.is_segmented_view vd in
  let () = global_extn_name # add_segmented x opt in
  (x,opt)

let extend_size pname (* name of extn *) ?(vn_of_pname=None) scc_vdecls (* selected views *) ((prop_name, prop_view) as xx) field_tag_s (* property *) 
    nnn_s (* extended parameter *) =
  (* let nnn_sv = CP.mk_typed_spec_var NUM nnn in (\* an integer *\) *)
  let () = y_tinfo_hp (add_str "prop_name" pr_id) prop_name in
  let seg_lst = List.map (List.map (fun (x,vd) ->  store_segmented_view x vd)) scc_vdecls in
  let () = y_tinfo_hp (add_str "seg_lst" (pr_list (pr_list (pr_pair pr_id (pr_opt !CP.print_sv))))) seg_lst in
  let p_tab = new prop_table pname ~vn_of_pname:vn_of_pname xx (CP.eq_spec_var) nnn_s field_tag_s in
  let () = y_binfo_hp (add_str "p_tab" pr_id) (p_tab # string_of) in
  let extend_size_disj vns (*mutual call*) f =
    let () = p_tab # reset_disj f in
    let map_h h = CFE.process_heap_prop_extn p_tab h in
    let new_f = CF.map_formula_heap_only map_h f in
    (* collected pure property and extended predicates *)
    (* base cases for size here *)
    let base_vars = p_tab # mk_undef_zero in
    let pure_lst = p_tab # get_pure in
    let qv = p_tab # get_quan in
    let () = y_binfo_hp (add_str "f" (!CF.print_formula)) f in
    let () = y_binfo_hp (add_str "new_f" (!CF.print_formula)) new_f in
    (* let () = y_tinfo_hp (add_str "pure_lst computed" (pr_id)) pure_lst in *)
    let () = y_binfo_hp (add_str "p_tab" (fun x -> x # string_of)) p_tab in
    let pure = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) pure_lst in
    let res = CF.add_pure_formula_to_formula pure new_f in
    let res = CF.push_exists qv res in
    res
    (* if base_vars!=[] then *)
    (*   begin *)
    (*     let () = y_tinfo_hp (add_str "bases not yet added= 0" !pr_svl) base_vars in *)
    (*     () *)
    (*   end; *)
    (* new_f *)
  in
  let extend_size_vdecl vns (*mutual call*) vd =
    (* let nnn = CP.mk_typed_spec_var NUM nnn in (\* an integer *\) *)
    (* let new_name = vd.C.view_name^"_"^pname in *)
    let typ = Named (vd.C.view_data_name) in
    let vars = vd.C.view_vars in
    let () = p_tab # reset_view typ in
    let () = p_tab # set_inv in
    let new_name,nnn_sv = p_tab # proc_view None vd.C.view_name vars in
    let vars = vd.C.view_vars in
    let new_vs = vars@[nnn_sv] in
    let new_labels = vd.C.view_labels@[LOne.unlabelled] in
    let uinv = MCP.pure_of_mix (vd.C.view_user_inv) in
    let uinv = CP.mkAnd uinv (p_tab # get_inv) no_pos in
    let new_domains = vd.C.view_domains@[(prop_name (* extn_view.C.view_name *),0,List.length new_vs)] in
    (* let spec_view = x_add C.look_up_view_def_raw x_loc cviews spec_view_name in *)
    (* let nc_view = {nc_view with C.view_domains = view.C.view_domains@[(extn_view.C.view_name,0,List.length vars -1)]} in *)
    let vparams = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list new_vs) in
    let body = vd.C.view_un_struc_formula in
    (* (Cformula.formula * formula_label) list *)
    let body = List.map (fun (f,l) -> (extend_size_disj vns f,l)) body in
    let () = y_binfo_hp (add_str "body" (pr_list !CF.print_formula)) (List.map fst body) in
    let new_vd = { vd with 
        C.view_vars = new_vs; C.view_name = new_name; C.view_un_struc_formula=body;
        C.view_labels = new_labels; C.view_params_orig = vparams; C.view_domains = new_domains;
        C.view_user_inv = MCP.mix_of_pure uinv;
        (* reset the inv to re-compute later, *)
        (* as previous view's computed inv may be incorrect *)
        C.view_baga_over_inv = None;
        C.view_baga_x_over_inv = None;
        C.view_baga_inv = None;
        C.view_baga_under_inv = None; } 
    in
    let vn = new_vd.C.view_name in
    let () = y_tinfo_hp (add_str "b4 update_view" pr_id) vn  in
    let () = x_add_1 (Cprog_sleek.update_view_decl_both ~update_scc:true) new_vd in
    (* let () = y_tinfo_hp (add_str "new_vd(after update)" Cprinter.string_of_view_decl_short) new_vd in *)
    let () = y_tinfo_hp (add_str "vd(orig)" Cprinter.string_of_view_decl_short) vd in
    let () = y_tinfo_hp (add_str "aft update_view" pr_id) vn  in
    new_vd
  in
  let extend_size_vdecl vns (*mutual call*) vd =
    let pr = !C.print_view_decl in
    Debug.no_1 "extend_size_vdecl" pr pr 
      (fun _ -> extend_size_vdecl vns vd) vd
  in
  
  let all_vd_names = List.map (List.map (fun (s,vd) -> s)) scc_vdecls in
  let extend_size_scc scc =
    let (vns,vds) = List.split scc in
    let () = p_tab # reset_mut vns in
    let vds = List.map (extend_size_vdecl vns) vds in
    let vds = x_add FixUtil.compute_inv_baga all_vd_names vds in
    (* let () = List.iter (fun vd -> x_add !compute_view_x_formula cprog vd !Globals.n_xpure) vds in *)
    let () = List.iter (fun vd ->
        let body = vd.C.view_un_struc_formula in
        let () = Typeinfer.update_view_new_body ~base_flag:true vd body in
        let () = y_tinfo_hp (add_str "aft Typeinfer.update_view" pr_id) vd.C.view_name  in
        let () = y_tinfo_hp (add_str "new_vd" Cprinter.string_of_view_decl_short) vd in
        let () = y_tinfo_hp (add_str "new_vd(inv)" Cprinter.string_of_view_decl_inv) vd in
        ()
      ) vds in
     let () = y_tinfo_hp (add_str "der_view(new)" (pr_list Cprinter.string_of_view_decl)) vds in
    (* let () = failwith (x_tbi^"Chanh: update_view_new_body/update_view_decl_both of view body are incomplete, see todo.txt with ex25a5.slk") in *)
    vds in
  let new_vdecls = List.map (extend_size_scc) scc_vdecls in
  new_vdecls

let reserve_derv_name_for_first lst_opt =
  match lst_opt with
  | Some (REGEX_LIST ((vn, _)::_)) -> Some vn
  | _ -> None

let trans_view_dervs_new (prog : Iast.prog_decl) rev_form_fnc trans_view_fnc lower_map_views
    (cviews0 (*orig _extn*): C.view_decl list) derv : C.view_decl list =
  let () = y_binfo_hp (add_str "view_scc_obj" pr_id) HipUtil.view_scc_obj # string_of in
  let scc = HipUtil.view_scc_obj # get_scc in
  let () = y_binfo_hp (add_str "scc" (pr_list_ln (pr_list pr_id))) scc in
  let vname = derv.Iast.view_name in
  let () = y_binfo_hp (add_str "view_name" pr_id) vname in
  let pr = pr_list pr_id in
  let d = derv.Iast.view_derv_extns in
  let () = y_binfo_hp (add_str "derv_extns" (pr_list (pr_triple pr_id pr pr))) d in
  let property, field_s, nnn_s = (
      match d with
      | (prop, ((_::_) as field_s), ((_::_) as nnn_s))::_ -> prop, field_s, nnn_s
      | _-> failwith (x_loc^" no prop")) in
  let opt = derv.Iast.view_derv_from in
  let vn_of_vname = reserve_derv_name_for_first opt in
  let cviews = List.filter (fun v -> v.C.view_kind = View_NORM) cviews0 in
  let () = y_binfo_hp (add_str "(norm) cviews" (pr_list (fun v -> v.C.view_name))) cviews in
  let view_list = cviews in
  let () = y_binfo_hp (add_str "selected" (pr_opt string_of_regex_id_star_list)) opt in
  let vd_lst = Cast.get_selected_views ~get_trans:true opt view_list in
  let prop_view = 
    try Some (List.find (fun v -> v.C.view_name = property) cviews0)
    with e -> 
      let ()= y_binfo_hp (add_str "Property view cannot be found (using default depth view)" pr_id) property in
      None
  in
  (*   match opt with *)
  (*   | Some rgx -> *)
  (*     let () = y_binfo_hp (add_str "derv_from" (string_of_regex_list (pr_pair pr_id string_of_bool)))  rgx in *)
  (*     let view_list = Cast.get_selected_views opt view_list in *)
  (*     view_list *)
  (*   | None -> failwith x_tbi *)
  (* in *)
  let vd_lst = List.filter (fun vd -> global_extn_name # not_processed vd.C.view_name property) vd_lst in
  let () = y_binfo_hp (add_str "vd_lst" (pr_list (fun v -> v.C.view_name))) vd_lst in
  let () = y_binfo_hp (add_str "scc(before)" (pr_list (pr_list pr_id))) scc in
  let scc = List.filter (fun mr -> 
      let common = Gen.BList.intersect_eq (fun n v -> v.C.view_name = n) mr vd_lst in
      common != []
    ) scc in
  let () = y_binfo_hp (add_str "scc(after)" (pr_list (pr_list pr_id))) scc in
  let scc_vdecls = List.map (fun mr -> 
      List.map (fun n ->
          try 
            let v = List.find (fun v -> v.C.view_name = n) cviews in
            (n,v)
          with _ -> failwith (x_loc^" view "^n^" not found!!!")
        ) mr) scc in
  let () = y_binfo_hp (add_str "scc_vdecls" (pr_list (pr_list (fun (vn, vd) -> vn^"+"^vd.C.view_name)))) scc_vdecls in
  let vdecls = extend_size vname ~vn_of_pname:vn_of_vname scc_vdecls (property, prop_view) field_s nnn_s in
  let vdecls = List.concat vdecls in
  let () = y_binfo_pp "TODO: need to keep entire mutual-rec vdecl generated?" in  
  let () = y_binfo_hp (add_str "vdecls" (pr_list_ln (Cprinter.string_of_view_decl_short ~pr_inv:true))) vdecls in
  vdecls
  
(* TODO : why is this method call in many places, code clone? *)
let trans_view_dervs (prog : Iast.prog_decl) rev_form_fnc trans_view_fnc lower_map_views
      (cviews (*orig _extn*): C.view_decl list) derv : C.view_decl list =
  let pr_r = pr_list Cprinter.string_of_view_decl in
  let pr = Iprinter.string_of_view_decl in
  let fn a b c d e f = 
    if !Globals.old_pred_extn then [trans_view_dervs a b c d e f]
    else trans_view_dervs_new a b c d e f in
  Debug.no_1 "trans_view_dervs" pr pr_r  
    (fun _ -> fn prog rev_form_fnc trans_view_fnc lower_map_views cviews derv) derv

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

(*****************************************************************************************)
(*     BUILD PURE EXTN MAP  *)
(*****************************************************************************************)

let expose_pure_extn_one_view iprog cprog rev_formula_fnc trans_view_fnc lower_map_views (view: C.view_decl) extn_view=
  let get_extns d_name=
    let d_dclr = Iast.look_up_data_def 67 no_pos iprog.Iast.prog_data_decls d_name in
    let extn_fields = List.fold_left (fun acc ((t,_),_,_,props) -> begin
        match t with
          | Named id -> if string_eq id d_name then acc@props else acc
          | _ -> acc
        end
    ) [] d_dclr.Iast.data_fields in
    Gen.BList.remove_dups_eq string_eq extn_fields
  in
  let iview_dclr = Iast.look_up_view_def_raw x_loc iprog.Iast.prog_view_decls view.C.view_name in
  let orig_view_name = view.C.view_name in
  let orig_args = iview_dclr.Iast.view_vars in
  let extn_view_name = extn_view.C.view_name in
  let extn_props = get_extns view.C.view_data_name in
  let n_arg = fresh_any_name extn_view.C.view_name in
  let extn_args = [n_arg] in
  let vars = iview_dclr.Iast.view_vars@extn_args in
  let extn_targs = [(Int,n_arg)] in
  let der_view_dclr = 
    { Iast.view_name = iview_dclr.Iast.view_name ^"_"^extn_view.C.view_name;
          Iast.view_pos = no_pos;
          Iast.view_data_name = "";
          Iast.view_type_of_self = None;
          Iast.view_imm_map = [];
          Iast.view_vars = vars;
          Iast.view_ho_vars = []; 
          Iast.view_derv = true;
          Iast.view_derv_from = None;
          Iast.view_derv_extns = [];
          Iast.view_parent_name = None;
          Iast.view_labels =  List.map (fun _ ->  Label_only.LOne.unlabelled) vars,false;
          Iast.view_modes = iview_dclr.Iast.view_modes;
          Iast.view_typed_vars = iview_dclr.Iast.view_typed_vars@extn_targs;
          Iast.view_pt_by_self  = [];
          Iast.view_formula = Iformula.mkETrue top_flow no_pos;
          Iast.view_inv_lock = None;
          Iast.view_is_prim = false;
          Iast.view_is_hrel = None;
          Iast.view_kind = View_DERV;
          Iast.view_prop_extns = [];
          Iast.view_derv_info = [((orig_view_name,orig_args),(extn_view_name,extn_props,extn_args))];
          Iast.view_invariant = Ipure.mkTrue no_pos;
          Iast.view_baga_inv = None;
          Iast.view_baga_over_inv = None;
          Iast.view_baga_under_inv = None;
          Iast.view_mem = None;
	  Iast.view_materialized_vars = iview_dclr.Iast.view_materialized_vars;
          Iast.try_case_inference = false;
  }
  in
  let _ = iprog.Iast.prog_view_decls <- iprog.Iast.prog_view_decls@[der_view_dclr] in
  (* let old_flag = !Globals.do_infer_inv in *)
  (* let () = Globals.do_infer_inv := true in *)
  let () =  Debug.ninfo_hprint (add_str "orig_view_name" pr_id) orig_view_name no_pos in
  let nc_view_lst = x_add_1 trans_view_dervs iprog rev_formula_fnc trans_view_fnc lower_map_views cprog.C.prog_view_decls der_view_dclr in
  let nc_view = List.hd nc_view_lst in
  (* let () = Globals.do_infer_inv := old_flag in *)
  let nc_view = {nc_view with C.view_domains = view.C.view_domains@[(extn_view.C.view_name,0,List.length vars -1)]} in
  (* let _ = cprog.C.prog_view_decls <- cprog.C.prog_view_decls@[nc_view] in *)
  nc_view

let expose_pure_extn_one_view iprog cprog rev_trans_formula trans_view lower_map_views view extn_view=
  let pr1 = pr_list (pr_triple pr_id string_of_int string_of_int) in
  let pr2 v = v.C.view_name ^ "<" ^ (!CP.print_svl v.C.view_vars) ^ ">, "
              ^ (pr1 v.C.view_domains) in
  let pr3 v =  v.C.view_name ^ "<" ^ (!CP.print_svl v.C.view_vars) ^ ">" in
  Debug.no_2 "expose_pure_extn_one_view" pr2 pr3 pr2
    (fun _ _ -> expose_pure_extn_one_view iprog cprog rev_trans_formula trans_view lower_map_views view extn_view)
    view extn_view
(*
  build extn map.
  pair extn prop in views with view_extn
*)
let expose_pure_extn iprog cprog rev_trans_formula trans_view views extn_views=
  List.fold_left (fun acc v ->
      let lst_view = List.fold_left (fun r extn_view ->
          expose_pure_extn_one_view iprog cprog rev_trans_formula trans_view acc v extn_view
      ) v extn_views in
      let new_map = ((v.C.view_name, v.C.view_vars), (lst_view.C.view_name, lst_view.C.view_vars)) in
      acc@[new_map]
    ) [] views

let expose_pure_extn iprog cprog rev_trans_formula trans_view views extn_views=
  let pr1 = pr_list (pr_triple pr_id string_of_int string_of_int) in
  let pr2 v = v.C.view_name ^ "<" ^ (!CP.print_svl v.C.view_vars) ^ ">, "
              ^ (pr1 v.C.view_domains) in
  let pr3 =  pr_pair (pr_pair pr_id !CP.print_svl) (pr_pair pr_id !CP.print_svl) in
  Debug.no_2 "expose_pure_extn" (pr_list_ln pr2) (pr_list_ln pr2) (pr_list pr3)
      (fun _ _ -> expose_pure_extn iprog cprog rev_trans_formula trans_view views extn_views)
      views extn_views

(*****************************************************************************************)
(*    END BUILD PURE EXTN MAP  *)
(****************hip*************************************************************************)
