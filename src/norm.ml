#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cformula
open Exc.GTable

module DD = Debug
module CF=Cformula
module CFU = Cfutil
module CP=Cpure
module MCP=Mcpure
module C = Cast
module I = Iast
module TP = Tpdispatcher
(* module SAU = Sautility *)

let check_lemeq_sem = ref (fun ?(force_pr=false) (iprog:Iast.prog_decl)
  (prog:C.prog_decl) (f1:CF.formula) (f2:CF.formula) ?(lemtyp=I.Equiv)
  (hpdefs:CF.hp_rel_def list) (ls1:ident list) (ls2:ident list) -> false)


(***********************************************)
(*****ELIM unused parameters of view **********)
let norm_elim_useless_para useless_stk view_name sf args=
  let extract_svl f=
    let f1 = CF.elim_exists f in
    let new_f = CF.drop_views_formula f1 [view_name] in
    (* let () = Debug.info_zprint  (lazy  (" new_f:" ^ (Cprinter.prtt_string_of_formula new_f) )) no_pos in *)
    (CF.fv new_f)
  in
  let rec build_keep_pos_list rem_args res index all=
    match rem_args with
    | [] -> res
    | a::ass -> if (CP.mem_svl a all) then
        build_keep_pos_list ass (res@[index]) (index+1) all
      else build_keep_pos_list ass (res) (index+1) all
  in
  if args = [] then (view_name, args, []) else
    let svl = extract_svl (CF.struc_to_formula sf) in
    (* let () = Debug.info_zprint  (lazy  (" svl:" ^ (!CP.print_svl svl) )) no_pos in *)
    (* let () = Debug.info_zprint  (lazy  (" args:" ^ (!CP.print_svl args) )) no_pos in *)
    let new_args = CP.intersect_svl args svl in
    (* let () = Debug.info_zprint  (lazy  (" new_args:" ^ (!CP.print_svl new_args) )) no_pos in *)
    if List.length args > List.length new_args then
      let keep_pos = build_keep_pos_list args [] 0 new_args in
      let new_vname = CP.fresh_old_name view_name in
      let ss = [(view_name,new_vname,keep_pos)] in
      (* let n_sf = CF.drop_view_paras_struc_formula sf ss in *)
      (* let n_ufs = List.map ( fun (uf, ufl) -> (CF.drop_view_paras_formula uf ss, ufl)) ufs in *)
      let dropped_args = CP.diff_svl args svl in
      let () = y_tinfo_hp  (add_str "ELIMINATE parameters" !CP.print_svl) dropped_args in
      let () = y_tinfo_hp  (add_str "Keep parameters" !CP.print_svl) svl in
      let () = y_tinfo_hp  (add_str "args" !CP.print_svl) args in
      let () = y_tinfo_hp  (add_str "new_args" !CP.print_svl) new_args in
      let () = y_tinfo_hp  (add_str "View" pr_id) view_name in
      let () = y_tinfo_hp  (add_str "new_View" pr_id) new_vname in
      let () = y_tinfo_hp  (add_str "keep_pos" (pr_list string_of_int)) keep_pos in
      let () = useless_stk # push (view_name,dropped_args) in
      (new_vname, new_args, ss)
    else
      (view_name, args, [])

let norm_elim_useless_para stk view_name sf args =
  let pr1 = Cprinter.string_of_struc_formula in
  let pr2 = pr_triple pr_id !CP.print_svl (pr_list (pr_triple pr_id pr_id (pr_list string_of_int))) in
  Debug.no_2 "norm_elim_useless_para" pr1 !CP.print_svl pr2
    (fun _ _ -> norm_elim_useless_para stk view_name sf args) sf args

(*assume views are sorted*)
let norm_elim_useless vdefs sel_vns=
  (* let () = Cast.cprog_obj # check_prog_upd x_loc !Cprog_sleek.cprog in *)
  let useless_stk = new stack_pr ""  (pr_pair pr_id !CP.print_svl) (=) in
  let elim_vdef ss vdef=
    let new_vdef = { vdef with
                     Cast.view_formula = CF.drop_view_paras_struc_formula vdef.Cast.view_formula ss;
                     Cast.view_un_struc_formula =  List.map ( fun (uf, ufl) -> (CF.drop_view_paras_formula uf ss, ufl)) vdef.Cast.view_un_struc_formula;
                   }
    in
    new_vdef
  in
  let process_one_view vdef rem_vdefs=
    if List.exists (fun vn -> String.compare vn vdef.Cast.view_name = 0) sel_vns then
      (*update vdef*)
      let new_vname, view_sv_vars, ss = norm_elim_useless_para useless_stk vdef.Cast.view_name vdef.Cast.view_formula  vdef.Cast.view_vars in
      (*push it back*)
      if ss = [] then ([vdef],rem_vdefs) else
        let vn = CF.mkViewNode (CP.SpecVar (Named new_vname, self, Unprimed))
            new_vname view_sv_vars no_pos in
        let f = CF.formula_of_heap vn no_pos in
        let cf = CF.struc_formula_of_heap vn no_pos in
        let link_view={vdef with
                       C.view_formula = cf;
                       C.view_xpure_flag = true;
                       C.view_addr_vars = [];
                       C.view_baga = [];
                       C.view_complex_inv = None;
                       C.view_mem = None;
                       C.view_inv_lock = None;
                       C.view_un_struc_formula = [(f, (0,"0"))];
                       C.view_base_case = None;
                       C.view_is_rec = false;
                       C.view_pt_by_self = [new_vname];
                       C.view_case_vars = [];
                       C.view_raw_base_case = None;
                       C.view_prune_branches = [];
                       C.view_prune_conditions = [];
                       C.view_prune_conditions_baga = [];
                       C.view_prune_invariants = []
                      } in
        let () = y_tinfo_hp (add_str "link_view" Cprinter.string_of_view_decl(* _short *)) link_view in
        let vars = vdef.Cast.view_vars in
        let len = List.length vars in
        let mk_mask len keep_pos =
          let len = len - 1 in
          let rec aux n =
            if n>len then []
            else if List.exists (fun v -> v=n) keep_pos then n::(aux (n+1))
            else (-1)::(aux (n+1))
          in aux 0 in
        let get_useless_para_mask ss = match ss with
          | [] -> []
          | (_,_,keep_pos)::_ -> mk_mask len keep_pos in
        let select_w_mask s mask vars =
          try
            let tmp = List.combine vars mask in
            let tmp = List.filter (fun (_,v) -> v>=0) tmp in
            List.map fst tmp
          with _ ->
            let () = y_winfo_pp (s^"mismatched vars and ss") in vars in
        let mask = get_useless_para_mask ss in
        let view_sv_vars2 = select_w_mask x_loc mask vars in
        let new_def = {vdef with
                       Cast.view_name = new_vname;
                       Cast.view_vars = view_sv_vars2;
                       (* Cast.view_ann_params = select_w_mask x_loc mask vdef.Cast.view_ann_params; *)
                       (* Cast.view_cont_vars = select_w_mask x_loc mask vdef.Cast.view_cont_vars; *)
                       Cast.view_labels = select_w_mask x_loc mask vdef.Cast.view_labels;
                       Cast.view_params_orig = select_w_mask x_loc mask vdef.Cast.view_params_orig;
                       (* Cast.view_domains = select_w_mask x_loc mask vdef.Cast.view_domains; *)
                      } in
        let () = y_tinfo_hp (add_str "mask" (pr_list string_of_int)) mask in
        let () = y_tinfo_hp (add_str "view_vars2" !CP.print_svl) view_sv_vars2 in
        let () = y_tinfo_hp (add_str "view_vars" !CP.print_svl) view_sv_vars in
        let () = y_tinfo_hp (add_str "vars" !CP.print_svl) vars in
        let () = y_tinfo_hp (add_str "new_def" Cprinter.string_of_view_decl(* _short *)) new_def in
        (*update rem_vdefs*)
        let new_def = elim_vdef ss new_def in
        let () = x_add_1 (Cprog_sleek.update_view_decl_both ~update_scc:true) link_view in
        (* let () = Cprog_sleek.update_view_decl_iprog ~update_scc:true  (Rev_ast.rev_trans_view_decl link_view) in *)
        let () = x_add_1 (Cprog_sleek.update_view_decl_both ~update_scc:true) new_def in
        (* let () = Cprog_sleek.update_view_decl_iprog ~update_scc:true  (Rev_ast.rev_trans_view_decl new_def) in *)
        (* let () = y_winfo_pp "Need to update iprog views too" in *)
        ([link_view;new_def], List.map (elim_vdef ss) rem_vdefs)
    else
      ([vdef],rem_vdefs)
  in
  let rec interate_helper rem_vdefs done_vdefs=
    match rem_vdefs with
    | [] -> done_vdefs
    | vdef::rest -> let new_defs,new_rest = process_one_view vdef rest in
      interate_helper new_rest (done_vdefs@new_defs)
  in
  let normal_view, rest_views = List.partition (fun vdcl -> vdcl.Cast.view_kind = View_NORM) vdefs in
  let n_normal_view = interate_helper normal_view [] in
  let () = if not(useless_stk # is_empty) then y_binfo_hp (add_str "USELESS Parameters eliminated" (fun s -> s # string_of)) useless_stk in
  (* let () = Cast.cprog_obj # check_prog_upd x_loc !Cprog_sleek.cprog in *)
  (rest_views@n_normal_view)

let norm_elim_useless vdefs sel_vns =
  let pr1 = pr_list pr_id in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  Debug.no_2 "norm_elim_useless" pr2 pr1 pr2
    (fun _ _ -> norm_elim_useless vdefs sel_vns) vdefs sel_vns

let norm_reuse_one_frm_view iprog prog ?(all=true)
    cur_equivs frm_vdcl (to_vdcls: C.view_decl list)=
  let check_equiv frm_vdcl to_vdcl =
    let frm_view_name =  frm_vdcl.Cast.view_name in
    let to_view_name =  to_vdcl.Cast.view_name in
    let () = y_tinfo_hp (add_str "Equiv (from,to) " (pr_pair pr_id pr_id)) (frm_view_name,to_view_name) in
    (* let () = y_tinfo_hp (add_str "to_vdcl" pr_id) to_vdcl.Cast.view_name in *)
    (* let () = y_tinfo_hp (add_str "frm_to_name" pr_id) (frm_view_name^to_view_name) in *)
    if string_eq frm_view_name to_view_name || HipUtil.view_scc_obj # compare frm_view_name to_view_name < 0
    then [(* to_view_name *)]
    else if string_eq frm_vdcl.Cast.view_data_name to_vdcl.Cast.view_data_name
    (* && *)
    (* does not handle transitivity *)
    (* not (List.exists (fun (vn1,vn2) -> *)
    (*     (string_eq frm_vdcl.Cast.view_name vn1 && *)
    (*      string_eq to_vdcl.Cast.view_name vn2) || (string_eq frm_vdcl.Cast.view_name vn2 && *)
    (*                                                string_eq to_vdcl.Cast.view_name vn1) *)
    (*   ) cur_equivs) *)
    then
      (* let (to_vdcl,finish_flag) = Cast.change_to_view_decl frm_vdcl to_vdcl in *)
      if frm_vdcl.view_equiv_set # is_avail then []
      else
        let () = x_tinfo_hp (add_str "to_vdcl.Cast.view_name:" pr_id) to_vdcl.Cast.view_name no_pos in
        let self_t = (Named frm_vdcl.Cast.view_data_name) in
        let self_sv = CP.SpecVar (self_t ,self, Unprimed) in
        let frm_args = frm_vdcl.Cast.view_vars in
        let to_args = to_vdcl.Cast.view_vars in
        if List.length frm_args != List.length to_args
        then []
        else
          let get_name_typ v = (string_of_typ (CP.type_of_spec_var v),v) in
          let name_to_args = List.map get_name_typ to_args in
          let name_frm_args = List.map get_name_typ frm_args in
          let ntyp_to_args = add_num name_to_args in
          let ntyp_frm_args = add_num name_frm_args in
          let cmp ((s1,_),_) ((s2,_),_) = String.compare s1 s2 in
          let sort_to_args = List.sort cmp ntyp_to_args in
          let sort_frm_args = List.sort cmp ntyp_frm_args in
          let pr2 ((_,sv),n) = pr_pair !CP.print_sv string_of_int (sv,n) in
          let () = y_tinfo_hp (add_str "sort from" (pr_list pr2)) sort_frm_args in
          let pr = pr_list (pr_pair (pr_pair pr_id !CP.print_sv) string_of_int) in
          let () = y_tinfo_hp (add_str "sort to"  (pr_list pr2)) sort_to_args in
          let sst_ntyp = List.combine sort_frm_args sort_to_args in
          (* let sst_typ = List.combine typ_frm_args typ_to_args in *)
          let (f_eq,eq_str) = List.fold_left (fun (f_eq,f_eq_str) (((t1,_),n1),((t2,_),n2)) ->
              let flag = f_eq && string_eq t1 t2 in
              (flag, f_eq_str && flag && n1==n2)) (true,true) sst_ntyp in
          let sst = List.map (fun (((t1,s1),n1),((t2,s2),n2)) -> (s1,s2)) sst_ntyp in
          let keep_sst = if eq_str then [] else
              let sst = List.map (fun (((t1,s1),n1),((t2,s2),n2)) -> (n1,n2)) sst_ntyp in
              let sst_from = List.sort (fun (n1,_) (n2,_) -> n1-n2) sst in
              List.map snd sst_from
          in
          (* let str_diff = List.exists (fun (sv1, sv2) -> not (cmp_typ (get_typ sv1) (get_typ sv2))) sst in *)
          let () = y_tinfo_hp (add_str "sort_to_args" pr) sort_to_args in
          let () = y_tinfo_hp (add_str "sort_frm_args" pr) sort_frm_args in
          let () = y_tinfo_hp (add_str "(f_eq,eq_str)" (pr_pair string_of_bool string_of_bool))
              (f_eq,eq_str) in
          (*type comparison*)
          if not(f_eq)  (* str_diff *) then []
          else
            let () = x_tinfo_hp (add_str "sst" (pr_list (pr_pair
                                                           !CP.print_sv !CP.print_sv))) sst no_pos in
            let frm_vnode = Cformula.mkViewNode (self_sv ) frm_vdcl.Cast.view_name
                (frm_vdcl.Cast.view_vars) no_pos in

            let to_vnode = Cformula.mkViewNode (self_sv ) to_vdcl.Cast.view_name
                (to_vdcl.Cast.view_vars) no_pos in
            let f1_frm = Cformula.formula_of_heap frm_vnode no_pos in
            let f1 = x_add Cformula.subst sst f1_frm in
            let f2 = Cformula.formula_of_heap to_vnode no_pos in
            let is_rec_flag = HipUtil.view_scc_obj # is_rec frm_view_name in
            (* put non-rec call on RHS where it can be unfolded *)
            let (f1,f2) = if is_rec_flag then (f1,f2) else
                let () = y_tinfo_pp "Swapping non-rec view to RHS" in
                (f2,f1)
            in
            let flag = Wrapper.wrap_exc_as_false ~msg:("check_lemeq_sem"^x_loc) (!check_lemeq_sem iprog prog f1 f2 [] []) [] in
            let msg = if flag then "\n Proven :" else "\n Failed :" in
            let () = y_tinfo_pp (msg ^ (!CF.print_formula f1) ^ " <-> " ^ (!CF.print_formula f2)) in
            if flag (* !check_lemeq_sem iprog prog f1 f2 [] [] [] *) then
              (* let matched_vnode = Cformula.mkViewNode r vdcl.Cast.view_name paras no_pos in *)
              (* let frm_view_name = frm_vdcl.Cast.view_name in *)
              (* let () = to_vdcl.Cast.view_equiv_set # push from_view_name in *)
              (* let to_view_name = to_vdcl.Cast.view_name in *)
              let () = Cast.add_equiv_to_view_decl frm_vdcl keep_sst to_vdcl in
              [to_view_name]
            else []
    else []
  in
  let rec to_vdcls_iter vdcls acc =
    match vdcls with
    | [] -> acc
    | v::rest ->
      let eq_views = check_equiv frm_vdcl v in
      if eq_views = [] || all then
        to_vdcls_iter rest (acc@eq_views)
      else
        eq_views
  in
  let () = x_tinfo_hp (add_str "frm vdecl" pr_id) frm_vdcl.Cast.view_name no_pos in
  let eq_views = to_vdcls_iter to_vdcls [] in
  List.map (fun vn -> (frm_vdcl.Cast.view_name, vn)) eq_views

let norm_reuse_one_frm_view iprog prog ?(all=true) cur_equivs frm_vdecl (to_vdecls: C.view_decl list)=
  let pr1 = Cprinter.string_of_view_decl_short in
  let pr2 = pr_list pr1 in
  let pr_out = pr_list (pr_pair pr_id pr_id) in
  Debug.no_2 "norm_reuse_one_frm_view" pr1 pr2 pr_out
    (fun _ _-> norm_reuse_one_frm_view iprog prog ~all:all cur_equivs frm_vdecl to_vdecls)
    frm_vdecl to_vdecls

(* change body of view to equiv *)
let norm_reuse_mk_eq iprog prog edefs =
  List.iter (fun e ->
      if e.C.view_equiv_set # is_empty then ()
      else
        let name = e.C.view_name in
        let (sst,to_n) = e.C.view_equiv_set # get in
        let args = e.C.view_vars in
        let new_args = CF.trans_args sst args in
        let () = y_ninfo_hp (add_str "TBI: view" Cprinter.string_of_view_decl_short) e in
        let () = y_ninfo_hp (add_str "TBI: from" (pr_pair pr_id !CP.print_svl)) (name,args) in
        let () = y_ninfo_hp (add_str "TBI: to" (pr_pair pr_id !CP.print_svl)) (to_n,new_args) in
        let self_node = CP.SpecVar (Named name, Globals.self, Unprimed) in
        let view_node = CF.mkViewNode self_node to_n new_args no_pos in
        let view_body = CF.set_flow_in_formula_override
            { CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link = None }
            (CF.formula_of_heap view_node no_pos)
        in
        let () = y_tinfo_hp (add_str "view_body" !CF.print_formula) view_body in
        let new_view_body = Typeinfer.case_normalize_renamed_formula iprog args [] view_body in
        let view_struc = CF.formula_to_struc_formula new_view_body in
        let () = y_tinfo_hp (add_str "view_body(new)" !CF.print_formula) new_view_body in
        let () = y_tinfo_hp (add_str "view_struc(new)" !CF.print_struc_formula) view_struc in
        (* let new_view = Typeinfer.create_view iprog name args view_body in *)
        (* let () = y_tinfo_hp (add_str "new view" Cprinter.string_of_view_decl) new_view in *)
        let () = y_tinfo_hp (add_str "old view" Cprinter.string_of_view_decl) e in
        let () = C.update_un_struc_formula_one view_body e in
        let () = C.update_view_formula (fun _ -> view_struc) e in
        let () = C.update_view_raw_base_case (fun _ -> view_body) e in
        let () = y_tinfo_hp (add_str "updated view" Cprinter.string_of_view_decl) e in
        ()
    ) edefs

(* type: ('a -> Globals.ident -> bool) -> *)
(*   'a list -> (CF.formula * 'b) list -> 'a list *)
let uses_views_fn fn eq_lst f = (* does f uses views from eq_lst? *)
  if eq_lst ==[] then []
  else
    let p_lst = List.concat (List.map (fun (f,_) -> CF.extr_pred_list f) f) in
    (BList.intersect_eq fn eq_lst p_lst)

(* type: ('a -> Globals.ident -> bool) -> 'a list -> CF.formula list -> 'a list *)

let uses_views_set eq_lst f = uses_views_fn string_eq eq_lst f

let uses_views eq_lst f = (* does f uses views from eq_lst? *)
  (uses_views_set eq_lst f)!=[]

let perform_unfold_decls iprog unfold_fn ans =
    List.iter (fun (v,unf_lst) -> (* transform body of views *)
        let vn = v.C.view_name in
        let fn = unfold_fn (* CF.complex_unfold *) vn unf_lst in
        let () = C.update_un_struc_formula fn v in
        let view_body_lbl = v.C.view_un_struc_formula in
        let old_sf = v.C.view_formula in
        let view_body = CF.convert_un_struc_to_formula view_body_lbl in
        let args = v.C.view_vars in
        (* struc --> better to re-transform it *)
        let new_view_body = Typeinfer.case_normalize_renamed_formula iprog args [] view_body in
        let view_struc = CF.formula_to_struc_formula new_view_body in
        let view_struc = CF.add_label_to_struc_formula view_struc old_sf in
        let () = C.update_view_formula (fun _ -> view_struc) v in
        (* let () = C.update_view_raw_base_case (x_add CF.repl_equiv_formula find_f) v in *)
        ()
      ) ans


let norm_complex_unfold iprog
    vdefs  (* all views *)
    (to_vns:ident list) (* pred to transform *) =
    (* let unfold_set0 = C.get_unfold_set vdefs (\* set of unfoldable views *\) in *)
    let unfold_set1 = C.get_unfold_set_gen vdefs (* set of unfoldable views *) in
    let pr = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in
    let pr2 = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in
    let pr = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in
    let pr2 = pr_list (pr_triple pr_id !CP.print_svl (pr_list !CF.print_formula)) in
    (* unfold_set0 - single disj unfold set *)
    (* let () = y_tinfo_hp (add_str "unfold_set0" pr) unfold_set0 in *)
    (* unfold_set1 - multiple disjs unfold set *)
    let unfold_set1 = List.filter (fun (_,_,l) -> List.length l > 1) unfold_set1 in
    let () = y_tinfo_hp (add_str "unfold_set1" pr2) unfold_set1 in
    let uses_unfold_set1 vd =
      let f = vd.C.view_un_struc_formula in
      let vn =  vd.C.view_name in
      let unfold_set1 = List.filter (fun (n,_,_) -> not(n=vn)) unfold_set1 in
      let svl = List.concat (List.map (fun (f,_) -> fv ~vartype:Vartypes.var_with_view_only f) f) in
      let () = y_tinfo_hp (add_str "svl" !CP.print_svl) svl in
      let unf = Gen.BList.intersect_eq (fun (e,_,_) sv -> e=(CP.name_of_spec_var sv)) unfold_set1 svl in
      let () = y_tinfo_hp (add_str "unf" (pr_list (fun (e,_,_) ->e))) unf in
      unf
    in
    let vdefs = List.filter (fun vd ->
        let n = vd.C.view_name in
        List.exists (fun vn -> string_eq vn n) to_vns
      ) vdefs in
    let ans = List.map (fun vd -> (vd,uses_unfold_set1 vd)) vdefs in
    let () = y_tinfo_hp (add_str "selected vdefs" (pr_list (pr_pair (fun vd -> vd.C.view_name ) (pr_list (fun (v,_,_)->v)) ))) ans in
    let ans = List.filter (fun (_,lst) -> lst!=[]) ans in
    let unfold_fn = CF.complex_unfold in
    perform_unfold_decls iprog unfold_fn ans
    (* List.iter (fun (v,unf_lst) -> (\* transform body of views *\) *)
    (*     let vn = v.C.view_name in *)
    (*     let fn = CF.complex_unfold vn unf_lst in *)
    (*     let () = C.update_un_struc_formula fn v in *)
    (*     let view_body_lbl = v.C.view_un_struc_formula in *)
    (*     let old_sf = v.C.view_formula in *)
    (*     let view_body = CF.convert_un_struc_to_formula view_body_lbl in *)
    (*     let args = v.C.view_vars in *)
    (*     (\* struc --> better to re-transform it *\) *)
    (*     let new_view_body = Typeinfer.case_normalize_renamed_formula iprog args [] view_body in *)
    (*     let view_struc = CF.formula_to_struc_formula new_view_body in *)
    (*     let view_struc = CF.add_label_to_struc_formula view_struc old_sf in *)
    (*     let () = C.update_view_formula (fun _ -> view_struc) v in *)
    (*     (\* let () = C.update_view_raw_base_case (x_add CF.repl_equiv_formula find_f) v in *\) *)
    (*     () *)
    (*   ) ans *)

let app_to_views iprog to_vns vdefs uses_unfold_set unfold_fn =
    let vdefs = List.filter (fun vd ->
        let n = vd.C.view_name in
        List.exists (fun vn -> string_eq vn n) to_vns
      ) vdefs in
    let ans = List.map (fun vd -> (vd,uses_unfold_set vd.C.view_un_struc_formula)) vdefs in
    let ans = List.filter (fun (_,lst) -> lst!=[]) ans in
    (* let pr_vn v = v.C.view_name in *)
    (* let pr2 (v,_,f) = (pr_pair pr_id !CF.print_formula) (v,f) in *)
    (* let () = y_tinfo_hp (add_str "views selected for unfolding" *)
    (*                        (pr_list (pr_pair pr_vn (pr_list pr2)))) ans in *)
    perform_unfold_decls iprog unfold_fn ans

let norm_unfold qual iprog
    vdefs  (* all views *)
    (to_vns:ident list) (* pred to transform *) =
  if qual!=None then norm_complex_unfold iprog vdefs to_vns
  else
    let () = y_tinfo_hp (add_str "Perform simple unfolding for" (pr_list pr_id)) to_vns in
    let unfold_set0 = C.get_unfold_set vdefs (* set of unfoldable views *) in
    (* let unfold_set1 = C.get_unfold_set_gen vdefs (\* set of unfoldable views *\) in *)
    (* let pr = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in *)
    (* let pr2 = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in *)
    (* let pr = pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula) in *)
    (* let pr2 = pr_list (pr_triple pr_id !CP.print_svl (pr_list !CF.print_formula)) in *)
    (* (\* unfold_set0 - single disj unfold set *\) *)
    (* let () = y_tinfo_hp (add_str "unfold_set0" pr) unfold_set0 in *)
    (* unfold_set1 - multiple disjs unfold set *)
    (* let unfold_set1 = List.filter (fun (_,_,l) -> List.length l > 1) unfold_set1 in *)
    (* let () = if qual!=None then  *)
    (*     y_tinfo_hp (add_str "unfold_set1" pr2) unfold_set1 in *)
    (* let unfold_set = List.map (fun (m,vd) -> m) unfold_set0 in *)
    let uses_unfold_set f = uses_views_fn
        (fun (m,_,_) m2 -> string_eq m m2) unfold_set0 f in
    let unfold_fn = CF.repl_unfold_formula in
    app_to_views iprog to_vns vdefs  uses_unfold_set unfold_fn
    (* let vdefs = List.filter (fun vd ->  *)
    (*     let n = vd.C.view_name in *)
    (*     List.exists (fun vn -> string_eq vn n) to_vns *)
    (*   ) vdefs in *)
    (* let ans = List.map (fun vd -> (vd,uses_unfold_set vd.C.view_un_struc_formula)) vdefs in *)
    (* let ans = List.filter (fun (_,lst) -> lst!=[]) ans in *)
    (* (\* let pr_vn v = v.C.view_name in *\) *)
    (* (\* let pr2 (v,_,f) = (pr_pair pr_id !CF.print_formula) (v,f) in *\) *)
    (* (\* let () = y_tinfo_hp (add_str "views selected for unfolding" *\) *)
    (* (\*                        (pr_list (pr_pair pr_vn (pr_list pr2)))) ans in *\) *)
    (* let unfold_fn = CF.repl_unfold_formula in *)
    (* perform_unfold_decls iprog unfold_fn ans            *)
    (* List.iter (fun (v,unf_lst) -> (\* transform body of views *\) *)
    (*     let vn = v.C.view_name in *)
    (*     let fn = CF.repl_unfold_formula vn unf_lst in *)
    (*     let () = C.update_un_struc_formula fn v in *)
    (*     let view_body_lbl = v.C.view_un_struc_formula in *)
    (*     let old_sf = v.C.view_formula in *)
    (*     let view_body = CF.convert_un_struc_to_formula view_body_lbl in *)
    (*     let args = v.C.view_vars in *)
    (*     (\* struc --> better to re-transform it *\) *)
    (*     let new_view_body = Typeinfer.case_normalize_renamed_formula iprog args [] view_body in *)
    (*     let view_struc = CF.formula_to_struc_formula new_view_body in *)
    (*     let view_struc = CF.add_label_to_struc_formula view_struc old_sf in *)
    (*     let () = C.update_view_formula (fun _ -> view_struc) v in *)
    (*     (\* let () = C.update_view_raw_base_case (x_add CF.repl_equiv_formula find_f) v in *\) *)
    (*     () *)
    (*   ) ans *)

(*
           let view_body_lbl = List.map (fun (f,l) -> (CF.repl_unfold_formula v.C.view_name unf_lst f,l)) view_body_lbl in
      (* let () = C.update_un_struc_formula (CF.repl_unfold_formula v.C.view_name unf_lst) v in *)
      (* let view_body_lbl = v.C.view_un_struc_formula in *)
      Typeinfer.update_view_new_body ~iprog:(Some iprog) v view_body_lbl
*)

(* type: C.view_decl list -> *)
(*   (((CF.formula * 'a) list -> *)
(*     (String.t * C.P.spec_var list * C.F.formula) list) -> *)
(*    (String.t -> *)
(*     (String.t * CF.CP.spec_var list * CF.formula) list -> *)
(*     CF.formula -> CF.formula) -> *)
(*    'b -> 'c) -> *)
(*   'b -> 'c *)

let uses_views_fn_new fn eq_lst f = (* does f uses views from eq_lst? *)
  if eq_lst ==[] then []
  else
    let p_lst = CF.extr_pred_list f in
    (BList.intersect_eq fn eq_lst p_lst)

(* requires split_ctx_or to be applied *)
let norm_unfold_formula vdefs f =
  let unfold_set0 = C.get_unfold_set vdefs in
  let uses_unfold_set f = uses_views_fn_new
      (fun (m,_,_) m2 -> string_eq m m2) unfold_set0 f in
  let unf_set = uses_unfold_set f in
  CF.repl_unfold_formula "" unf_set f

let norm_unfold_formula vdefs f =
  let lst = CF.split_or f in
  let lst = List.map (norm_unfold_formula vdefs) lst in
  CF.join_or lst

let norm_unfold_formula vdefs f =
  let pr1 = !CF.print_formula in
  let pr2 = pr_list_ln !C.print_view_decl_short in
  Debug.no_2 "norm_unfold_formula" pr2 pr1 pr1
    norm_unfold_formula vdefs f

let norm_reuse_subs iprog cprog vdefs to_vns =
  let equiv_set = C.get_all_view_equiv_set vdefs in
  let eq_lst = List.map (fun (m,_) -> m) equiv_set in
  let in_equiv_set n = List.exists (string_eq n) eq_lst in
  let uses_eq_view f = uses_views eq_lst f
      (* f uses views from eq_lst? *)
    (* if eq_lst ==[] then false *)
    (* else  *)
    (*   let p_lst = List.concat (List.map (fun (f,_) -> CF.extr_pred_list f) f) in *)
    (*   (BList.intersect_eq string_eq eq_lst p_lst) != [] *)
  in
  let vdefs = List.filter (fun vd ->
      let n = vd.C.view_name in
      List.exists (fun vn -> string_eq vn n) to_vns
    ) vdefs in
  let (edefs,vdefs) = List.partition
      (fun vd -> vd.C.view_equiv_set # is_avail) vdefs in
  let to_decls = List.filter (fun vdcl ->
      uses_eq_view vdcl.C.view_un_struc_formula) vdefs in
  let find_f name =
    try
      let (m,ans) = List.find (fun (m,_) -> string_eq m name) equiv_set in
      Some ans
    with _ -> None
  in
  let () = y_tinfo_hp (add_str "equiv_set" (pr_list (pr_pair pr_id (pr_pair pr_none pr_id)))) equiv_set in
  let () = y_tinfo_hp (add_str "to_decls" (pr_list Cprinter.string_of_view_decl_short)) to_decls in
  let () = norm_reuse_mk_eq iprog cprog edefs in
  List.iter (fun v -> (* transform body of views *)
      let () = C.update_un_struc_formula (x_add CF.repl_equiv_formula find_f) v in
      let () = C.update_view_formula (x_add CF.repl_equiv_struc_formula find_f) v in
      let () = C.update_view_raw_base_case (x_add CF.repl_equiv_formula find_f) v in
      ()
    ) to_decls

let norm_reuse_subs iprog cprog vdefs to_vns =
  let pr1 = pr_list Cprinter.string_of_view_decl_short in
  let pr2 = pr_list idf in
  Debug.no_2 "norm_reuse_subs" pr1 pr2 (fun () -> pr1 cprog.C.prog_view_decls)
    (fun _ _ -> norm_reuse_subs iprog cprog vdefs to_vns) vdefs to_vns

(* to be invoked after reuse to maintain transitivity of equiv *)
(* assumes vdefs in topo sorted order *)
let norm_trans_equiv iprog cprog vdefs =
  let ordered xs =
    let rec aux xs n =
      match xs with
      | [] -> true
      | x::xs -> n<x && (aux xs x)
    in match xs with
    | [] -> true
    | x::xs -> aux xs x in
  let comp sst1 sst2 =
    try
      let new_sst = List.combine sst1 sst2 in
      let new_sst = List.sort (fun (_,n1) (_,n2) -> n1-n2) new_sst in
      let sst = List.map fst new_sst in
      if ordered sst then []
      else sst
    with _ -> failwith(x_loc^"mismatching sst") in
  let comp_sst sst1 sst2 =
    match sst1 with
    | [] -> sst2
    | _ ->
      begin
        match sst2 with
        | [] -> sst1
        | _ ->
          let pr_sst = pr_list string_of_int in
          let final_sst = comp sst1 sst2 in
          let () = y_tinfo_hp (add_str "Composing -> " (pr_triple pr_sst pr_sst pr_sst)) (sst1,sst2,final_sst) in
          final_sst
      end
  in
  let find_trans vn =
    try
      let vd = List.find (fun vd -> vn=vd.Cast.view_name) vdefs in
      if vd.Cast.view_equiv_set # is_avail then
        Some (vd)
      else None
    with _ -> None in
  List.iter (fun frm_vd ->
      if frm_vd.Cast.view_equiv_set # is_avail then
        begin
          let (sst1,to_name) = frm_vd.Cast.view_equiv_set # get in
          match find_trans to_name with
          | None -> ()
          | Some to_vd ->
            let frm_name = frm_vd.Cast.view_name in
            let (sst2,last_name) = to_vd.Cast.view_equiv_set # get in
            let () = y_tinfo_hp (add_str "trans" (pr_triple pr_id pr_id pr_id)) (frm_name,to_name,last_name) in
            let new_sst = comp_sst sst1 sst2 in
            let () = frm_vd.Cast.view_equiv_set # set (new_sst,last_name) in
            ()
        end
    ) vdefs


(*
 assume frm_vns and to_vns are topo sorted
*)
let norm_reuse iprog cprog vdefs frm_vns to_vns =
  (*filter vdefs to keep order*)
  let () = y_tinfo_hp (add_str "norm_reuse (from_vns)" (pr_list pr_id)) frm_vns in
  let () = y_tinfo_hp (add_str "norm_reuse (to_vns)" (pr_list pr_id)) to_vns in
  let frm_vdcls = List.filter (fun vdcl ->
      List.exists (fun vn -> string_eq vn vdcl.C.view_name) frm_vns
  ) vdefs in
  let to_vdcls = List.filter (fun vdcl ->
      List.exists (fun vn -> string_eq vn vdcl.C.view_name) to_vns
  ) vdefs in
  List.fold_left (fun acc frm_vdcl ->
      let new_eqs = norm_reuse_one_frm_view iprog cprog ~all:false acc
        frm_vdcl to_vdcls in
      acc@new_eqs
  ) [] frm_vdcls

let norm_reuse iprog cprog vdefs frm_vns to_vns=
  let pr1 = pr_list pr_id in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  let pr3 = pr_list (pr_pair pr_id pr_id) in
  Debug.no_3 "norm_reuse" pr2 pr1 pr1 pr3
    (fun _ _ _ -> norm_reuse iprog cprog vdefs frm_vns to_vns) vdefs frm_vns to_vns

let regex_search reg_id vdefs =
  match reg_id with
    | REGEX_LIST ids -> ids
    | REGEX_STAR ->
      let all_ids = List.map (fun vdcl -> vdcl.Cast.view_name) vdefs in
      all_ids

let norm_reuse_rgx iprog cprog vdefs reg_frm_vns reg_to_vns =
  let frm_vns = regex_search reg_frm_vns vdefs in
  let to_vns = regex_search reg_to_vns vdefs in
  norm_reuse iprog cprog vdefs frm_vns to_vns

(*=============**************************================*)
(*=============PRED SPLIT================*)
(*=============**************************================*)
let build_args_aset args eqs eqNulls=
  let acc_alias_from_eq_pairs tpl0 eqs=
    List.fold_left (fun tpl (sv1,sv2) -> CP.add_equiv_eq tpl sv1 sv2) tpl0 eqs
  in
  (*ls_eqs: all svs in this list are aliasing*)
  let rec acc_alias_from_eq_list tpl0 ls_eqs=
    match ls_eqs with
    | [] -> tpl0
    | sv::rest ->
      let eqs = List.map (fun sv2 -> (sv,sv2)) rest in
      let n_tpl =  acc_alias_from_eq_pairs tpl0 eqs in
      acc_alias_from_eq_list n_tpl rest
  in
  let rec partition_args_aset args tpl res=
    match args with
    | sv::rest -> let lst_eq_sv = CP.EMapSV.find_equiv_all sv tpl in
      let inter_rest,rest2 = List.partition (fun sv2 -> CP.mem_svl sv2 lst_eq_sv) rest in
      let n_res = if inter_rest = [] then res else
          res@[sv::inter_rest]
      in
      partition_args_aset rest2 tpl n_res
    | [] -> res
  in
  let tpl_aset = CP.EMapSV.mkEmpty in
  let tpl_aset1 = acc_alias_from_eq_pairs tpl_aset eqs in
  let tpl_aset2 = acc_alias_from_eq_list tpl_aset1 eqNulls in
  partition_args_aset args tpl_aset2 []


let view_split_cands_one_branch_x prog vdecl f=
  (*******************INTERNAL************************)
  (*partition args into dependent groups*)
  let do_partition hns hvs p eqs args=
    let rec intersect_with_pre_parts parts svl r_parts r_svl=
      match parts with
      | [] -> (r_parts,r_svl)
      | svl1::tl->
        if CP.intersect_svl (r_svl@svl) svl1 = [] then
          intersect_with_pre_parts tl svl (r_parts@[svl1]) r_svl
        else intersect_with_pre_parts tl svl r_parts (CP.remove_dups_svl (r_svl@svl1))
    in
    let rec part_helper args0 parts=
      match args0 with
      | [] -> parts
      | [a] -> (parts@[[a]])
      | a::tl ->
            let () = Debug.ninfo_hprint (add_str "a" (!CP.print_sv)) a no_pos in
        let part1 = CF.find_close [a] eqs in
        let () = Debug.ninfo_hprint (add_str "part1" (!CP.print_svl)) part1 no_pos in
        let part2 = CF.look_up_reachable_ptr_args prog hns [] (CP.remove_dups_svl part1) in
        let part2a = (CF.find_close part2 eqs) in
        let () = Debug.ninfo_hprint (add_str "part2" (!CP.print_svl)) part2 no_pos in
        let new_parts,part2b = intersect_with_pre_parts parts part2a [] [] in
        let part3 = CP.remove_dups_svl (a::(CP.intersect_svl part2a tl)) in
        let () = Debug.ninfo_hprint (add_str "part3" (!CP.print_svl)) part3 no_pos in
        part_helper (CP.diff_svl tl part3) (new_parts@[part2b@part3])
    in
    let () = Debug.ninfo_hprint (add_str "args" (!CP.print_svl)) args no_pos in
    let parts = part_helper args [] in
    let () = Debug.ninfo_hprint (add_str "parts" (pr_list !CP.print_svl)) parts no_pos in
    (*if all args is partitioned in one group, do not split*)
    match parts with
    | [args0] -> if List.length args0 = List.length args then []
      else parts
    | _ -> parts
  in
  (* let acc_alias_from_eq_pairs tpl0 eqs= *)
  (*   List.fold_left (fun tpl (sv1,sv2) -> CP.add_equiv_eq tpl sv1 sv2) tpl0 eqs *)
  (* in *)
  (* (\*ls_eqs: all svs in this list are aliasing*\) *)
  (* let rec acc_alias_from_eq_list tpl0 ls_eqs= *)
  (*   match ls_eqs with *)
  (*   | [] -> tpl0 *)
  (*   | sv::rest -> *)
  (*     let eqs = List.map (fun sv2 -> (sv,sv2)) rest in *)
  (*     let n_tpl =  acc_alias_from_eq_pairs tpl0 eqs in *)
  (*     acc_alias_from_eq_list n_tpl rest *)
  (* in *)
  (* let rec partition_args_aset args tpl res= *)
  (*   match args with *)
  (*   | sv::rest -> let lst_eq_sv = CP.EMapSV.find_equiv_all sv tpl in *)
  (*     let inter_rest,rest2 = List.partition (fun sv2 -> CP.mem_svl sv2 lst_eq_sv) rest in *)
  (*     let n_res = if inter_rest = [] then res else *)
  (*         res@[sv::inter_rest] *)
  (*     in *)
  (*     partition_args_aset rest2 tpl n_res *)
  (*   | [] -> res *)
  (* in *)
  (* let build_args_aset args eqs eqNulls= *)
  (*   let tpl_aset = CP.EMapSV.mkEmpty in *)
  (*   let tpl_aset1 = acc_alias_from_eq_pairs tpl_aset eqs in *)
  (*   let tpl_aset2 = acc_alias_from_eq_list tpl_aset1 eqNulls in *)
  (*   partition_args_aset args tpl_aset2 [] *)
  (* in *)
  (*******************END INTERNAL************************)
  let () = Debug.ninfo_hprint (add_str "f" (Cprinter.string_of_formula)) f no_pos in
  let ( _,mf,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let quans,bare = CF.split_quantifiers f in
  let () = Debug.ninfo_hprint (add_str "quans" !CP.print_svl) quans no_pos in
  let quans_eqs = List.fold_left (fun acc (sv1,sv2) ->
      if CP.mem_svl sv1 quans (* && not (CP.mem_svl sv2 quans) *) then
        acc@[(sv1,sv2)]
      else acc
  ) [] eqs in
  let () = Debug.ninfo_hprint (add_str "eqs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) eqs no_pos in
  let () = Debug.ninfo_hprint (add_str "quans_eqs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) quans_eqs no_pos in
  let f1 = CF.subst quans_eqs bare in
  let () = Debug.ninfo_hprint (add_str "f1" (Cprinter.string_of_formula)) f1 no_pos in
  let ( _,mf,_,_,_,_) = CF.split_components f1 in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs mf) in
  let hns, hvs, hrs = CF.get_hp_rel_formula f1 in
  let self_sv = (CP.SpecVar (Named (vdecl.Cast.view_data_name),self, Unprimed)) in
  let cands0 = (vdecl.Cast.view_name, self_sv::vdecl.Cast.view_vars, vdecl.C.view_pos)::
    (List.map (fun vnode -> (vnode.CF.h_formula_view_name, vnode.CF.h_formula_view_node::vnode.CF.h_formula_view_arguments, vnode.CF.h_formula_view_pos)) hvs) in
  let cands1 = List.filter (fun (_,args,_) -> (List.length args) >= 2) cands0 in
  let cands2 = List.map (fun (vn,args,l) ->
      let parts = do_partition hns hvs (MCP.pure_of_mix mf) eqs args in
      (*build aliasing info*)
      let lst_aset = build_args_aset args eqs eqNulls in
      (vn,args, parts,l, lst_aset)
    ) cands1
  in
  (cands2)

let view_split_cands_one_branch prog vdecl f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2  = Cprinter.string_of_view_decl_short in
  let pr3 = pr_list_ln (pr_penta pr_id !CP.print_svl
                          (pr_list !CP.print_svl) string_of_full_loc (pr_list !CP.print_svl)) in
  Debug.no_2 "view_split_cands_one_branch" pr2 pr1 pr3
    (fun _ _ ->  view_split_cands_one_branch_x prog vdecl f)
    vdecl f

let view_split_cands_x prog vdecls=
  (*******INTERNAL*******)
  let rec process_one_view vdecl cands fs=
    match fs with
    | [] -> true, cands
    | f::rest ->
      let n_cands = view_split_cands_one_branch prog vdecl f in
      let is_split = List.fold_left (fun b (vn1, args1, parts, _, _) ->
          if string_eq vdecl.C.view_name vn1 && CP.eq_spec_var_order_list vdecl.C.view_vars (List.tl args1) then
            (b && parts <> [])
          else b
        ) true n_cands in
      if not is_split then (false, [])
      else
        process_one_view vdecl (cands@n_cands) rest
  in
  (*******END INTERNAL*******)
  let cands, non_split_vns = List.fold_left (fun (r, non_split_vns) vdecl ->
      let fs = List.map (fun (f,_) -> f) vdecl.C.view_un_struc_formula in
      let to_split, n_cands =  process_one_view vdecl [] fs in
      if to_split then
        (r@n_cands, non_split_vns)
      else
        (r, non_split_vns@[vdecl.C.view_name])
  ) ([],[]) vdecls
  in
  let cands1 = List.filter (fun (id, _,_,_,_) -> not (List.exists (fun id1 -> string_eq id id1) non_split_vns)) cands in
  let cands2 = Gen.BList.remove_dups_eq (fun (id1, args1,_,_,_) (id2, args2, _,_,_) ->
      string_eq id2 id1 && CP.eq_spec_var_order_list args2 args1
  ) cands1 in
  cands2

let view_split_cands prog vdecls =
  let pr1 = pr_list_ln Cprinter.string_of_view_decl_short in
  let pr2 = pr_list_ln (pr_penta pr_id !CP.print_svl (pr_list !CP.print_svl)
                          string_of_full_loc (pr_list !CP.print_svl)) in
  Debug.no_1 "view_split_cands" pr1 pr2
    (fun _ -> view_split_cands_x prog vdecls) vdecls

(*split one hp -> mutiple hp and produce corresponding heap formulas for substitution
  - one cand: (hp,args, parts,p)
*)
let check_view_split_global_x iprog prog cands =
  let rec partition_cands_by_view_name cands0 parts=
    match cands0 with
    | [] -> parts
    | (vn,args, ls_args,p,ls_eqs)::xs ->
      let part,remains= List.partition (fun (vn1,_,_,_,_) -> string_eq vn1 vn) xs in
      partition_cands_by_view_name remains (parts@[[(vn,args,ls_args,p,ls_eqs)]@part])
  in
  (*each partition, create new hp and its corresponding HRel formula*)
  let pred_helper1 pos args =
    let args1 = List.map (fun sv -> (sv,I)) args in
    let hf,new_hp_sv = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog true false args1 pos in
    (*add rel decl in iprog*)
    let ihp_decl = { Iast.hp_name = CP.name_of_spec_var new_hp_sv;
                      Iast.hp_typed_inst_vars = List.map (fun (CP.SpecVar (t,id,_), i) -> (t,id,i)) args1;
                      Iast.hp_root_pos = None;
                      Iast.hp_part_vars = [];
                      Iast.hp_is_pre = false;
                      Iast.hp_formula = Iformula.mkTrue_nf pos;
                    }
    in
    let () = iprog.Iast.prog_hp_decls <- (ihp_decl :: iprog.Iast.prog_hp_decls) in
    ((new_hp_sv,args), hf)
  in
  (*each partition, create new rel and its corresponding rel pure formula*)
  let rel_helper pos args =
    let new_rel_sv = Sautil.add_raw_rel prog args pos in
    (*add rel decl in iprog*)
    let irel_decl = { Iast.rel_name = CP.name_of_spec_var new_rel_sv;
                      Iast.rel_typed_vars = List.map (fun (CP.SpecVar (t,id,_)) -> (t,id)) args;
                      Iast.rel_formula = Ipure.mkTrue pos;
                    }
    in
    let () = iprog.Iast.prog_rel_decls <- (irel_decl :: iprog.Iast.prog_rel_decls) in
    let p_rel = CP.mkRel new_rel_sv (List.map (fun sv -> CP.mkVar sv pos) args) pos in
    ((new_rel_sv,args), p_rel)
  in
  (*if two args are aliasing, infer shape of one*)
  let refine_infer_pred ls_eqs args=
    let ls_eq1 = List.fold_left (fun r ls ->
        let inter = CP.intersect_svl args ls in
        if List.length inter > 1 then r@[inter] else r
      ) [] ls_eqs in
    ( List.fold_left (fun r aset ->
         match aset with
         | sv::rest -> CP.diff_svl r rest
         | _ -> r
       ) args ls_eq1)
  in
  (*for each grp*)
  let intersect_cand_one_view grp=
    let rec parts_norm args0 grp0 res res_eqs=
      match grp0 with
      | [] -> res,res_eqs
      | (_,args1,parts1,_,ls_eqs1)::tl ->
        let ss = List.combine args1 args0 in
        let parts11 = List.map (fun largs -> List.map (CP.subs_one ss) largs) parts1 in
        let ls_eqs11 = List.map (fun largs -> List.map (CP.subs_one ss) largs ) ls_eqs1 in
        parts_norm args0 tl (res@[parts11]) (res_eqs@[ls_eqs11])
    in
    let rec cmp_two_list_args ls_args1 ls_args2=
      match ls_args1,ls_args2 with
      | [],[] -> true
      | args1::tl1,args2::tl2 ->
        if CP.eq_spec_var_order_list args1 args2 then
          cmp_two_list_args tl1 tl2
        else false
      | _ -> false
    in
    let (vn,args0,parts0,p0,lst_eqs0)=
      match grp with
      | [] -> report_error no_pos "norm.intersect_cand_one_hp"
      | hd::_ -> hd
    in
    let size = List.length parts0 in
    if size = 0 || List.exists (fun (_,args1,parts1,_,_) -> (List.length parts1)!=size) (List.tl grp) then
      []
    else
      let tl_parts, tl_lst_eqparts = parts_norm args0 (List.tl grp) [] [] in
      if List.for_all (fun part -> cmp_two_list_args parts0 part) tl_parts then
        let lst_eqs = if tl_lst_eqparts = [] then [] else
            List.fold_left (fun lst_eqs1 lst_eqs2 ->
                List.fold_left (fun r svl1 ->
                    if svl1=[] then r else
                      let ls_svl11 = List.map (fun svl2 -> CP.intersect_svl svl1 svl2) lst_eqs2 in
                      let ls_svl12 = List.filter (fun svl -> List.length svl > 1) ls_svl11 in
                      if ls_svl12 = [] then r else r@[(List.hd ls_svl12)]
                  ) [] lst_eqs1
              ) lst_eqs0 tl_lst_eqparts
        in
        [(vn,args0, List.map (refine_infer_pred lst_eqs) parts0,p0,lst_eqs)]
      else []
  in
  (*todo: generalize lst_eqs to lst_pure*)
  let generate_split (vn,args0,parts0,p0, lst_eqs0) =
    let hps = List.map (pred_helper1 p0) parts0 in
    let new_hp_args,new_hrel_fs = List.split hps in
    let rels = List.map (rel_helper p0) lst_eqs0 in
    let new_rel_args,new_rel_ps = List.split rels in
    let new_hrels_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 p0)
        (List.hd new_hrel_fs) (List.tl new_hrel_fs) in
    let new_rel_comb = List.fold_left (fun p1 p -> CP.mkAnd p1 p p0) (CP.mkTrue p0) new_rel_ps in
    let vn_hf0 = CF.mkViewNode (List.hd args0) vn (List.tl args0) p0 in
    (vn, args0, new_hp_args,new_rel_args, vn_hf0,new_hrels_comb, new_rel_comb)
  in
  (**************END INTERNAL******************)
  let grps = partition_cands_by_view_name cands [] in
  (*each group, the partition should be similar*)
  let to_split = List.concat (List.map intersect_cand_one_view grps) in
  let res = List.map generate_split to_split in
  res

let check_view_split_global iprog prog cands =
  let pr1 = pr_list_ln (pr_penta pr_id !CP.print_svl (pr_list !CP.print_svl) string_of_full_loc
                          (pr_list !CP.print_svl)) in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_list_ln (pr_hepta pr_id !CP.print_svl pr4 pr4 pr2 pr2 !CP.print_formula) in
  Debug.no_1 "check_view_split_global" pr1 pr3
    (fun _ -> check_view_split_global_x iprog prog cands) cands

let add_v vn name=
  vn^"#"^ name

let part_v name=
  let indx = String.index name '#' in
  (String.sub name 0 (indx), String.sub name (indx+1) ((String.length name) - indx - 1))

let update_scc_view_args prog vdecl=
  let rec update_scc_alias svl done_svl=
    match svl with
      | [] -> ()
      | sv::rest ->
            let () = HipUtil.view_args_scc_obj # add x_loc sv (done_svl@rest) in
             update_scc_alias rest (done_svl@[sv])
  in
  let update_scc_view_args_alias args eqs =
    let parts = build_args_aset args eqs [] in
    List.iter (fun svl ->
        update_scc_alias (List.map (fun sv ->
            let name = CP.name_of_spec_var sv in
            add_v vdecl.Cast.view_name name
        ) svl) []
    ) (List.filter (fun ls -> List.length ls >= 2) parts)
  in
  let update_scc_view_args_ptos sv eqs hns hvs =
    let part1 = CF.find_close [sv] eqs in
    let () = Debug.ninfo_hprint (add_str "part1" (!CP.print_svl)) part1 no_pos in
    let part2 = CF.look_up_reachable_ptr_args prog hns [] (CP.remove_dups_svl part1) in
    let part2a = (CF.find_close part2 eqs) in
    let inter_hvs = List.fold_left (fun acc hv ->
        let v_args = (hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments) in
        let inter_svl = CP.intersect_svl v_args part2a in
        if inter_svl != [] then
          let vdecl1 = Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls hv.CF.h_formula_view_name in
          let self_sv = CP.SpecVar ((Named vdecl1.Cast.view_data_name) ,self, Unprimed) in
          let sst = List.combine v_args (self_sv::vdecl1.Cast.view_vars) in
          let inter_rename = CP.subst_var_list sst inter_svl in
          let ids = List.map (fun sv ->
              let name = CP.name_of_spec_var sv in
              add_v vdecl1.Cast.view_name name
          ) inter_rename in
          acc@[ids]
        else
          acc
    ) [] hvs in
    let name = CP.name_of_spec_var sv in
    let src_id = add_v vdecl.Cast.view_name name in
    List.iter (fun dest_names ->
        HipUtil.view_args_scc_obj # add x_loc src_id dest_names
    ) inter_hvs
  in
  let update_scc_view_args_branch args f =
    let () = Debug.ninfo_hprint (add_str "f" (Cprinter.string_of_formula)) f no_pos in
    let ( _,mf,_,_,_,_) = CF.split_components f in
    let eqs = (MCP.ptr_equations_without_null mf) in
    let quans,bare = CF.split_quantifiers f in
    let () = Debug.ninfo_hprint (add_str "quans" !CP.print_svl) quans no_pos in
    let quans_eqs = List.fold_left (fun acc (sv1,sv2) ->
        if CP.mem_svl sv1 quans then
          acc@[(sv1,sv2)]
        else acc
    ) [] eqs in
    let () = Debug.ninfo_hprint (add_str "eqs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) eqs no_pos in
    let () = Debug.ninfo_hprint (add_str "quans_eqs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) quans_eqs no_pos in
    let f1 = CF.subst quans_eqs bare in
    let () = Debug.ninfo_hprint (add_str "f1" (Cprinter.string_of_formula)) f1 no_pos in
    let ( _,mf,_,_,_,_) = CF.split_components f1 in
    let eqs = (MCP.ptr_equations_without_null mf) in
    let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs mf) in
    let hns, hvs, _ = CF.get_hp_rel_formula f1 in
    let () =  update_scc_view_args_alias args eqs in
    let () =  List.iter (fun sv -> update_scc_view_args_ptos sv eqs hns hvs) args in
    ()
  in
  (******************)
  let self_sv = (CP.SpecVar (Named (vdecl.Cast.view_data_name),self, Unprimed)) in
  let args = self_sv::vdecl.Cast.view_vars in
  if List.length args < 2 then ()
  else
    let fs = List.map (fun (f,_) -> f) vdecl.C.view_un_struc_formula in
    List.iter (update_scc_view_args_branch args) fs

let norm_split_x iprog prog vdefs sel_vns=
  let rec group ls_vn_args parts=
    match ls_vn_args with
      | [] -> parts
      | (vn,args)::rest ->
            let same,others = List.partition (fun (vn1,_) -> string_eq vn vn1) rest in
            group others (parts@[(vn, args::(List.map snd same))])
  in
  let group_view_args pairs=
    let ls_vn_args = List.map (fun name -> part_v name) pairs in
    group ls_vn_args []
  in
  let rec bubble_fst_root svl root_cands done_svl=
    match svl with
      | [] -> done_svl
      | sv::rest -> if CP.mem_svl sv root_cands then
          sv::(done_svl@rest)
        else bubble_fst_root rest root_cands (done_svl@[sv])
  in
  let rec examine_one_arg fs a res=
    match fs with
    | [] -> res
    | f::fs_tl ->
      (*get ptos of all nodes*)
      let hds = Sautil.get_hdnodes f in
      let ptos = List.map (fun hd -> hd.CF.h_formula_data_node) hds in
      let args = List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds) in
      let new_res = if not (CP.mem_svl a ptos) || CP.mem_svl a args then res else true
      in
      examine_one_arg fs_tl a new_res
  in
  let add_view_args (vn, parts)=
    let vdecl = C.look_up_view_def_raw x_loc vdefs vn in
    let self_sv = CP.SpecVar ((Named vdecl.Cast.view_data_name) ,self, Unprimed) in
    let args = self_sv::vdecl.C.view_vars in
    let sv_parts = List.map (fun ids ->
        List.map (fun id -> List.find (fun sv ->
            string_eq (CP.name_of_spec_var sv) id
        ) args) ids
    ) parts in
    let fs = List.map (fun (f,_) -> f) vdecl.C.view_un_struc_formula in
    let root_cands = List.filter (fun sv -> examine_one_arg fs sv false) args in
    let () = y_tinfo_hp (add_str ("root_cands") !CP.print_svl) root_cands in
    let sv_parts_rooted = List.map ( fun svl -> match svl with
      | [] -> []
      | [x] -> [x]
      | _ ->  bubble_fst_root svl root_cands []
    ) sv_parts in
    (vn, args, sv_parts_rooted, no_pos, [])
  in
  let () = y_tinfo_hp (add_str "\n" pr_id) (HipUtil.view_scc_obj # string_of) in
  let scclist = HipUtil.view_scc_obj # get_scc in
  let sel_scclist = List.filter (fun scc -> (Gen.BList.intersect_eq string_eq scc sel_vns) != []) scclist in
  let cl_sel_vns = List.concat sel_scclist in
  let () = y_tinfo_hp (add_str "\n" pr_id) ((pr_list pr_id) cl_sel_vns) in
  let sel_vdecls = List.map (C.look_up_view_def_raw x_loc vdefs) sel_vns in
  (* split candidate *)
  let () = List.iter (update_scc_view_args prog) sel_vdecls in
  (* let split_cands = view_split_cands prog sel_vdecls in *)
  HipUtil.view_args_scc_obj # set_sorted;
  let () = y_tinfo_hp (add_str "\n" pr_id) (HipUtil.view_args_scc_obj # string_of) in
  let view_args_scclist = HipUtil.view_args_scc_obj # get_scc in
  let parts = List.fold_left (fun acc pair ->
      let res = group_view_args pair in
      let () = y_tinfo_hp (add_str ("res") (pr_list(pr_pair pr_id (pr_list pr_id)))) res in
      acc@(List.filter (fun (vn,_) -> List.exists (fun id -> string_eq id vn) sel_vns) res)
  )
    [] view_args_scclist in
  let () = y_tinfo_hp (add_str ("parts") (pr_list(pr_pair pr_id  (pr_list pr_id)))) parts in
  let parts1 = group parts [] in
  let () = y_tinfo_hp (add_str ("parts1") (pr_list(pr_pair pr_id (pr_list (pr_list pr_id))))) parts1 in
  let split_cands = List.map add_view_args parts1 in
  let () = y_tinfo_hp (add_str ("split_cands") (pr_list (fun (vn,args,parts,_,_) ->
      (pr_triple pr_id !CP.print_svl (pr_list !CP.print_svl)) (vn,args,parts) ))) split_cands in
  (* check global + generate unknown preds *)
  let split_map_view_subst = check_view_split_global iprog prog split_cands in
  split_map_view_subst

let norm_split iprog cprog vdefs sel_vns=
  let pr1 = pr_list pr_id in
  let pr2a = pr_list_ln Cprinter.string_of_view_decl_short in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_list_ln (pr_hepta pr_id !CP.print_svl pr4 pr4 pr2 pr2 !CP.print_formula) in
  Debug.no_2 "norm_split" pr1 pr2a pr3
      (fun _ _ -> norm_split_x iprog cprog vdefs sel_vns)
      sel_vns vdefs

(***********************************************)
(********EXTRACT common pattern **********)
(***********************************************)
let view_to_hprel_h_formula hf0=
  let rec helper hf=
    match hf with
    | CF.Star {h_formula_star_h1 = hf1;
               h_formula_star_h2 = hf2;
               h_formula_star_pos = pos} ->
      let n_hf1,hvs1 = helper hf1 in
      let n_hf2,hvs2 = helper hf2 in
      let new_hf=
        match n_hf1,n_hf2 with
        | (HEmp,HEmp) -> HEmp
        | (HEmp,_) -> n_hf2
        | (_,HEmp) -> n_hf1
        | _ -> (Star {h_formula_star_h1 = n_hf1;
                      h_formula_star_h2 = n_hf2;
                      h_formula_star_pos = pos})
      in
      (new_hf,hvs1@hvs2)
    | CF.Conj { h_formula_conj_h1 = hf1;
                h_formula_conj_h2 = hf2;
                h_formula_conj_pos = pos} ->
      let n_hf1,hvs1 = helper hf1 in
      let n_hf2,hvs2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos},hvs1@hvs2)
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 h_formula_phase_pos = pos} ->
      let n_hf1,hvs1 = helper hf1 in
      let n_hf2,hvs2 = helper hf2 in
      (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                  CF.h_formula_phase_rw = n_hf2;
                  CF.h_formula_phase_pos = pos},hvs1@hvs2)
    | CF.DataNode hd -> (hf,[])
    | CF.ThreadNode ht -> (hf,[])
    | CF.ViewNode hv ->
      let eargs = List.map (fun v -> CP.mkVar v no_pos) (hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments) in
      let nh = CF.HRel (CP.SpecVar (HpT, hv.CF.h_formula_view_name, Unprimed ),eargs, no_pos) in
      (nh, [hv])
    | CF.HRel _
    | CF.Hole _ | CF.FrmHole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> (hf,[])
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> report_error no_pos "NORM.view_to_hprel_h_formula: not handle yet"
  in
  helper hf0

let view_to_hprel_x (f0:CF.formula) : (CF.formula*CF.h_formula_view list)=
  let rec helper f2_f=
    match f2_f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let nf1,hvs1 = helper f1 in
      let nf2,hvs2 = helper f2 in
      (Or {formula_or_f1 = nf1 ; formula_or_f2 =  nf2 ; formula_or_pos = pos}, hvs1@hvs2)
    | Base b ->
      let nh,hvs= view_to_hprel_h_formula b.formula_base_heap in
      (Base { b with formula_base_heap =nh;}, hvs)
    | Exists b ->
      let nh,hvs = view_to_hprel_h_formula b.formula_exists_heap in
      (Exists {b with formula_exists_heap = nh;}, hvs)
  in
  helper f0

let view_to_hprel (f2_f:formula): (CF.formula*CF.h_formula_view list) =
  let pr1 hv= Cprinter.prtt_string_of_h_formula (CF.ViewNode hv) in
  let pr2 =pr_list pr1 in
  Debug.no_1 "view_to_hprel" !print_formula (pr_pair !print_formula pr2)
    view_to_hprel_x f2_f

let hprel_to_view_h_formula hf0=
  let rec helper hf=
    match hf with
    | CF.Star {h_formula_star_h1 = hf1;
               h_formula_star_h2 = hf2;
               h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let new_hf=
        match n_hf1,n_hf2 with
        | (HEmp,HEmp) -> HEmp
        | (HEmp,_) -> n_hf2
        | (_,HEmp) -> n_hf1
        | _ -> (Star {h_formula_star_h1 = n_hf1;
                      h_formula_star_h2 = n_hf2;
                      h_formula_star_pos = pos})
      in
      (new_hf)
    | CF.Conj { h_formula_conj_h1 = hf1;
                h_formula_conj_h2 = hf2;
                h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos})
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                  CF.h_formula_phase_rw = n_hf2;
                  CF.h_formula_phase_pos = pos})
    | CF.DataNode hd -> (hf)
    | CF.ViewNode hv -> hf
    | CF.ThreadNode ht -> hf
    | CF.HRel (hp, eargs, p) ->
      let args = List.fold_left List.append [] (List.map CP.afv eargs) in
      (CF.mkViewNode (List.hd args) (CP.name_of_spec_var hp) (List.tl args) p)
    | CF.Hole _ | CF.FrmHole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> (hf)
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> hf
  in
  helper hf0

let hprel_to_view_x (f0:formula): (CF.formula) =
  let rec helper f=
    match f with
    | CF.Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let nf1 = helper f1 in
      let nf2 = helper f2 in
      (Or {formula_or_f1 = nf1 ; formula_or_f2 =  nf2 ; formula_or_pos = pos})
    | CF.Base b ->
      let nh= hprel_to_view_h_formula b.formula_base_heap in
      (Base { b with formula_base_heap =nh;})
    | CF.Exists b ->
      let qvars, base1 = CF.split_quantifiers f in
      let nf = helper base1 in
      CF.add_quantifiers qvars nf
  in
  helper f0

let hprel_to_view (f2_f:formula): (CF.formula) =
  Debug.no_1 "hprel_to_view" !print_formula !print_formula
    hprel_to_view_x f2_f

let rec look_for_anonymous_h_formula_x hf0=
  let rec helper hf=
    match hf with
    | CF.Star { h_formula_star_h1 = hf1;
                h_formula_star_h2 = hf2}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2} ->
      let hr1 = helper hf1 in
      let hr2 = helper hf2 in
      (hr1@hr2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;} ->
      let hr1 = (helper hf1)in
      let hr2 = (helper hf2) in
      (hr1@hr2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      let hr1 = (helper hf1) in
      let hr2 = (helper hf2) in
      (hr1@hr2)
    | DataNode hd -> (* hd.CF.h_formula_data_node:: *)hd.CF.h_formula_data_arguments
    | ViewNode hv -> hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments
    | ThreadNode ht ->
      let rec helper (f:CF.formula) : (CP.spec_var list) =
        match f with
        | CF.Or ({formula_or_f1 = f1; formula_or_f2 = f2;}) -> (helper f1)@(helper f2)
        | CF.Base b -> look_for_anonymous_h_formula b.formula_base_heap
        | CF.Exists e ->
          let qvars= look_for_anonymous_h_formula e.CF.formula_exists_heap in
          CP.diff_svl qvars e.CF.formula_exists_qvars
      in
      ht.CF.h_formula_thread_node::(helper ht.CF.h_formula_thread_resource)
    | HRel _
    | Hole _ | CF.FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> []
  in
  let svl = CP.remove_dups_svl (helper hf0) in
  svl

and look_for_anonymous_h_formula hf0=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_1 "look_for_anonymous_h_formula" pr1 !CP.print_svl
    (fun _ -> look_for_anonymous_h_formula_x hf0) hf0

and convert_anonym_to_exist_formula_x f0 args=
  let rec helper f=
    match f with
    | CF.Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let nf1 = helper f1 in
      let nf2 = helper f2 in
      (Or {formula_or_f1 = nf1 ; formula_or_f2 =  nf2 ; formula_or_pos = pos})
    | CF.Base b ->
      let qvars= look_for_anonymous_h_formula b.formula_base_heap in
      let qvars1 = CP.diff_svl qvars args in
      CF.add_quantifiers qvars1 f
    | CF.Exists e ->
      let qvars= look_for_anonymous_h_formula e.CF.formula_exists_heap in
      let qvars1 = CP.diff_svl qvars (args@e.CF.formula_exists_qvars) in
      CF.add_quantifiers qvars1 f
  in
  helper f0

and convert_anonym_to_exist_formula f0 args=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_1 "convert_anonym_to_exist_formula" pr1 pr1
    (fun _ -> convert_anonym_to_exist_formula_x f0 args) f0

let recover_view_decl_x old_vdecl vname vvars ir f=
  let pos = CF.pos_of_struc_formula old_vdecl.C.view_formula in
  let f1 = convert_anonym_to_exist_formula f vvars in
  let cf = CF.formula_to_struc_formula f1 in
  let cf = CF.struc_formula_set_lhs_case false cf in
  (*inv = true*)
  let inv_pf = (CP.mkTrue pos) in
  let new_pf = inv_pf in
  let memo_pf_P = MCP.memoise_add_pure_P (MCP.mkMTrue pos) new_pf in
  let memo_pf_N = MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_pf in
  let xpure_flag = x_add TP.check_diff memo_pf_N memo_pf_P in
  let n_un_str =  CF.get_view_branches cf in
  let sf = [] in
  let rec f_tr_base f =
    let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
    match f with
    | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
    | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
    | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos
  in
  let rbc =
    if old_vdecl.C.view_is_prim then None
    else List.fold_left (fun a (c,l)->
        let fc = f_tr_base c in
        if (CF.isAnyConstFalse fc) then a
        else match a with
          | Some f1  -> Some (CF.mkOr f1 fc no_pos)
          | None -> Some fc) None n_un_str
  in
  { old_vdecl with
    C.view_name = vname;
    C.view_vars = vvars;
    C.view_formula = cf;
    C.view_x_formula = memo_pf_P;
    C.view_xpure_flag = xpure_flag;
    C.view_user_inv = memo_pf_N;
    C.view_mem = None;
    C.view_un_struc_formula = n_un_str;
    C.view_is_rec = ir;
    C.view_pt_by_self = sf;
    C.view_case_vars = CP.intersect_svl vvars (CF.guard_vars cf);
    C.view_raw_base_case = rbc;
  }

let recover_view_decl old_vdecl vname vvars ir f=
  let pr1 = Cprinter.string_of_view_decl in
  let pr2 = Cprinter.prtt_string_of_formula in
  Debug.no_4 "recover_view_decl" pr1 pr_id !CP.print_svl pr2 pr1
    (fun _ _ _ _ -> recover_view_decl_x old_vdecl vname vvars ir f) old_vdecl vname vvars f


let norm_extract_common_one_view_x iprog cprog cur_m cviews vdecl=
  let extract_view_name hf=
    match hf with
    | CF.ViewNode hv -> hv.CF.h_formula_view_name
    | _ -> report_error no_pos "Norm.norm_extract_common_one_view: hf must be a hv node"
  in
  let self_var = Cpure.SpecVar ((Named vdecl.C.view_data_name), self, Unprimed) in
  let hp = CP.SpecVar (HpT, vdecl.C.view_name, Unprimed) in
  let args = self_var::vdecl.C.view_vars in
  let unk_hps = [] in let unk_svl = [] in
  let cdefs = [] in
  let fs = CF.list_of_disjs (CF.struc_to_formula vdecl.C.view_formula) in
  (***views to hprels*******)
  let fs1 = List.map CF.elim_exists fs in
  let fs2,map = List.split (List.map view_to_hprel fs1) in
  let defs,elim_ss = Sautil.get_longest_common_hnodes_list cprog false cdefs unk_hps unk_svl
      hp self_var vdecl.C.view_vars args (List.map (fun f-> (f,None)) fs2) in
  match defs with
  | [a] -> [vdecl]
  | [(hp1,(* (_,hrel1,_,f1) *) def1);(hp2,(* (a,hrel2,_,f2) *) def2)] ->
    let () = Debug.info_zprint  (lazy  ("  DO EXTRACT on view: "^ (!CP.print_sv hp1) ^ "\n")) no_pos in
    let f1 = CF.disj_of_list (List.map fst def1.CF.def_rhs) no_pos in
    let f2 = CF.disj_of_list (List.map fst def2.CF.def_rhs) no_pos in
    let n_f1 =
      if !Globals.pred_elim_useless then
        CF.subst_hrel_f f1 elim_ss
      else
        f1
    in
    (* let () = Debug.info_zprint  (lazy  ("  hp2: "^ (!CP.print_sv hp2))) no_pos in *)
    (*IMPORTANT: process hp2 first + check equiv then hp1*)
    (*matching with current views*)
    let (_, eq_hfs) = Sautil.match_one_hp_views iprog cprog cur_m cviews def2 in
    let n_vdecl2, view_ss=
      if eq_hfs = [] then
        let () = Debug.info_zprint  (lazy  ("  DO SYNTHESIZE view: "^ (!CP.print_sv hp2) ^ "\n")) no_pos in
        let _,args2 = CF.extract_HRel def2.CF.def_lhs in
        let vname2 = (CP.name_of_spec_var hp2) in
        let self_var2 = Cpure.SpecVar ((Named vname2), self, Unprimed) in
        let ss = [(List.hd args2, self_var2)] in
        let n_f21 = hprel_to_view f2 in
        let n_f22 = x_add CF.subst ss n_f21 in
        let n_vdecl2 = recover_view_decl vdecl vname2 (List.tl args2) vdecl.C.view_is_rec n_f22 in
        ([n_vdecl2],None)
      else
        let eq_hf = List.hd eq_hfs in
        let eq_vn = extract_view_name eq_hf in
        let () = Debug.info_zprint  (lazy  ("  DO NOT SYNTHESIZE. MATCHED view: "^ (eq_vn) ^ "\n")) no_pos in
        let to_hp = CP.SpecVar (HpT, eq_vn, Unprimed) in
        ([], Some ([hp2], to_hp))
    in
    (*hp1 must equal hp*)
    (* let () = Debug.info_zprint  (lazy  ("  hp1: "^ (!CP.print_sv hp1))) no_pos in *)
    (***hprels to views*******)
    let n_f10 =
      match view_ss with
      | None -> n_f1
      | Some (from_hps, to_hp) -> CF.subst_hprel n_f1 from_hps to_hp
    in
    let n_f11 = hprel_to_view n_f10 in
    let n_vdecl1 = recover_view_decl vdecl vdecl.C.view_name vdecl.C.view_vars false n_f11 in
    n_vdecl2@[n_vdecl1]
  | _ -> report_error no_pos "norm:norm_extract_common_one_view: sth wrong"

let norm_extract_common_one_view iprog cprog cur_m cviews vdecl=
  let pr1 = Cprinter.string_of_view_decl in
  Debug.no_1 "norm_extract_common_one_view" pr1 (pr_list_ln pr1)
    (fun _ -> norm_extract_common_one_view_x iprog cprog cur_m cviews vdecl) vdecl

let norm_extract_common iprog cprog cviews sel_vns=
  let rec process_helper rem_vs done_vs=
    match rem_vs with
    | [] -> done_vs
    | vdecl::rest ->
      let n_vdecls =
        if List.exists (fun vn -> String.compare vn vdecl.Cast.view_name = 0) sel_vns then
          norm_extract_common_one_view iprog cprog [] (done_vs@rest) vdecl
        else [vdecl]
      in
      process_helper rest (done_vs@n_vdecls)
  in
  (*not sure it is necessary*)
  (* process_helper cviews [] *)
  cviews


(*****************************************************************)
(********END EXTRACT common pattern **********)
(*****************************************************************)
let cont_para_analysis_view cprog vdef other_vds=
  (* cont paras are the paras that are
     - reachable from self
     - not defined in inductive branch
      (from Trung:
        + the "not defined" condition is incorrect for tail predicate, eg. tail-dll
        + relax to not_null condition? )
  *)
  let self_sv = CP.SpecVar (Named vdef.Cast.view_data_name, self, Unprimed) in
  let process_branch_x vname args f=
    let _, vns, _ = CF.get_hp_rel_formula f in
    if vns = [] then args else
      let _, reach_dns, reach_vns = CFU.look_up_reachable_ptrs_w_alias cprog f [self_sv] 3 in
      let ( _,mix_f,_,_,_,_) = CF.split_components f in
      let eqs = (MCP.ptr_equations_without_null mix_f) in
      let rec_vns, other_vns = List.partition (fun vn ->
          String.compare vn.CF.h_formula_view_name vname = 0
        ) vns in
      (*cont paras are para not changed, just forwarded*)
      (* let cont_paras = List.fold_left (fun cur_cont_paras vn -> *)
      (*     let closed_rec_args = if eqs = [] then vn.CF.h_formula_view_arguments else *)
      (*       CF.find_close vn.CF.h_formula_view_arguments eqs *)
      (*     in *)
      (*     CP.intersect_svl cur_cont_paras closed_rec_args *)
      (* ) args rec_vns *)
      (* in *)
      let root_dn_svl, para_dn_svl = List.fold_left (fun (r1,r2) dn ->
          (r1@[dn.CF.h_formula_data_node], r2@dn.CF.h_formula_data_arguments)
        ) ([],[]) reach_dns in
      let root_vn_svl, para_vn_svl = List.fold_left (fun (r1,r2) vn ->
          (r1@[vn.CF.h_formula_view_node], r2@vn.CF.h_formula_view_arguments)
        ) ([],[]) reach_vns in
      let null_svls = CP.remove_dups_svl ((MCP.get_null_ptrs mix_f) ) in
      (* let defined_svl = CF.find_close (root_dn_svl@root_vn_svl@null_svls) eqs in *)
      let defined_svl = CF.find_close (null_svls) eqs in
      let cont_svl = CP.diff_svl ( CF.find_close (para_dn_svl@para_vn_svl) eqs) defined_svl in
      let cont_vars = CP.intersect_svl args  cont_svl in
      Debug.ninfo_hprint (add_str "root_dn_svl" (pr_list !CP.print_sv)) root_dn_svl no_pos;
      Debug.ninfo_hprint (add_str "root_vn_svl" (pr_list !CP.print_sv)) root_vn_svl no_pos;
      Debug.ninfo_hprint (add_str "null_svls" (pr_list !CP.print_sv)) null_svls no_pos;
      Debug.ninfo_hprint (add_str "defined_svl" (pr_list !CP.print_sv)) defined_svl no_pos;
      Debug.ninfo_hprint (add_str "cont_svl" (pr_list !CP.print_sv)) cont_svl no_pos;
      Debug.ninfo_hprint (add_str "cont_vars" (pr_list !CP.print_sv)) cont_vars no_pos;
      cont_vars
      (* process other_vns*)
      (* try *)
      (*   let cont_paras1 = List.fold_left (fun cur_cont_paras vn -> *)
      (*       let cont_args = Cast.look_up_cont_args vn.CF.h_formula_view_arguments vn.CF.h_formula_view_name other_vds in *)
      (*       let closed_rec_args = *)
      (*         if eqs = [] then cont_args else *)
      (*           CP.remove_dups_svl ((CF.find_close cont_args eqs)@cont_args) *)
      (*       in *)
      (*       CP.intersect_svl cur_cont_paras closed_rec_args *)
      (*   ) cont_paras other_vns *)
      (*   in *)
      (*   cont_paras1 *)
      (* with Not_found -> cont_paras *)
  in
  let process_branch vname args f=
    let pr1 = Cprinter.prtt_string_of_formula in
    let pr2 = !CP.print_svl in
    Debug.no_3 "cont_process_branch" pr_id pr2 pr1 pr2
      (fun _ _ _ -> process_branch_x vname args f) vname args f
  in
  let vname = vdef.Cast.view_name in
  let args = vdef.Cast.view_vars in
  let cont_paras = List.fold_left (fun cur_cont_paras (f,_) ->
      let br_cont_paras = (process_branch vname args f) in
      CP.intersect_svl cur_cont_paras br_cont_paras
    ) args vdef.Cast.view_un_struc_formula
  in
  {vdef with Cast.view_cont_vars = cont_paras}

(*assume cviews are sorted*)
let cont_para_analysis_x cprog cviews=
  let rec loop_helper rem_cviews done_cviews=
    match rem_cviews with
    | [] -> done_cviews
    | vdef::rest ->
      (*if non recursive then not check*)
      let new_vdef = if vdef.Cast.view_is_rec then
          cont_para_analysis_view cprog vdef done_cviews
        else vdef
      in
      loop_helper rest (done_cviews@[new_vdef])
  in
  loop_helper cviews []

let cont_para_analysis cprog cviews=
  (* let pr0 = pr_list_ln Cprinter.string_of_view_decl in *)
  (* let pr1 = pr_pair pr_id !CP.print_svl in *)
  let pr2a = Cprinter.string_of_view_decl in
  (* let pr2 vdef = pr1 (vdef.Cast.view_name, vdef.Cast.view_cont_vars) in *)
  let pr3 = pr_list pr2a in
  Debug.no_1 "cont_para_analysis" pr3 pr3
    (fun _ -> cont_para_analysis_x cprog cviews) cviews


let norm_split_args iprog cprog cview=
  cview


(*****************************************************************)
(********END PARA CONTINUATION ANALYSIS **********)
(*****************************************************************)
let compute_base_case_raw branches=
  let rec get_base r f=
    match f with
    | CF.Base b ->
      if is_empty_heap b.CF.formula_base_heap then
        r@[(MCP.pure_of_mix b.CF.formula_base_pure)]
      else r
    | CF.Exists _ ->
      let _, base = CF.split_quantifiers f in
      get_base r base
    | CF.Or _ -> r
  in
  let ps = List.fold_left (fun r (f,_) -> get_base r f) [] branches in
  match ps with
  | [p] -> Some p
  | _ -> None


let norm_ann_seg_opz_x iprog cprog cviews=
  (*************INTERNAL***************)
  (*a view can be applied for seg optimization if:
    - seg (form smt-compete, only with 1 segment para + data node has one pointer)
    - exists base case = emp
    - non-touch
  *)
  let check_seg_view_smt_compete vdcl=
    if !Globals.smt_compete_mode then
      let is_one_dir = try
          let ddclr = x_add Cast.look_up_data_def_raw cprog.Cast.prog_data_decls vdcl.Cast.view_data_name in
          let ptr_fields = List.filter (fun ((t,_),_) -> match t with
              | Named _ -> true
              | _ -> false
            ) ddclr.Cast.data_fields in
          List.length ptr_fields <= 2
        with _ -> false
      in
      List.length vdcl.Cast.view_vars != 1 || not is_one_dir
    else false
  in
  let compute_seg_opz view=
    let is_seg, seg_emp_base = if view.Cast.view_cont_vars = [] ||
                                  not view.Cast.view_is_segmented || view.Cast.view_is_touching ||
                                  check_seg_view_smt_compete view
      then
        (false, None)
      else
        match view.Cast.view_base_case with
        | None -> begin
            (*re-compute by other ways*)
            match compute_base_case_raw view.Cast.view_un_struc_formula with
            | Some p -> (true, Some p)
            | None -> (false, None)
          end
        | Some (p,_) -> begin
            let neq_null_svl = Cpure.get_neq_null_svl p in
            if neq_null_svl != [] then
              (false, None)
            else
              (true, Some p)
          end
    in
    is_seg, {view with Cast.view_seg_opz = seg_emp_base}
  in
  (*************END INTERNAL***************)
  let cviews1 = if !Globals.norm_cont_analysis then cviews
    else cont_para_analysis cprog cviews
  in
  List.fold_left (fun (b, r) v ->
      let b1, n_v = compute_seg_opz v in
      (b || b1, r@[n_v])
    ) (false, []) cviews1

let norm_ann_seg_opz iprog cprog cviews=
  let pr1 v =
    let pr = pr_hexa pr_id Cprinter.string_of_struc_formula
        !CP.print_svl string_of_bool string_of_bool
        (pr_opt !CP.print_formula) in
    pr (v.Cast.view_name, v.Cast.view_formula,
        v.Cast.view_cont_vars, v.Cast.view_is_segmented, v.Cast.view_is_touching,
        v.Cast.view_seg_opz)
  in
  let pr2 = pr_list_ln pr1 in
  Debug.no_1 "norm_ann_seg_opz" pr2 (pr_pair string_of_bool pr2)
    (fun _ -> norm_ann_seg_opz_x iprog cprog cviews) cviews

(************* NORM for the FORMULA USED DURING UNFOLDING ***************)

and norm_formula_for_unfold cprog vdef =
  let new_un_formula = List.map (fun (def,l) -> ((Cvutil.remove_imm_from_formula cprog def (CP.ConstAnn(Lend))), l)) vdef.C.view_un_struc_formula in
  {vdef with C.view_un_struc_formula =  new_un_formula;}

(*********** end NORM for the FORMULA USED DURING UNFOLDING *************)

(************* MERGE STATES with IDENTICAL FORMULAS (syntactic check) ***************)
let octx_2_es_list (ctx: CF.context): CF.entail_state list =
  let rec helper ctx =
    match ctx with
    | CF.Ctx es       -> [es]
    | CF.OCtx (c1,c2) -> (helper c1)@(helper c2)
  in helper ctx

let eq_estate (es1: CF.entail_state) (es2: CF.entail_state): bool =
  let equals =
    try
      let fv1 = CF.fv es1.CF.es_formula in
      let fv2 = CF.fv es2.CF.es_formula in
      (* let intrs =  Gen.BList.intersect_eq CP.eq_spec_var fv1 fv2 in *)
      let intrs = fv1@fv2 in
      let intrs = List.map CP.name_of_spec_var intrs in
      fst (Checkeq.checkeq_formulas intrs es1.CF.es_formula es2.CF.es_formula)
    with _ -> false in
  equals

let eq_context (ctx1: CF.context) (ctx2: CF.context): bool =
  match ctx1, ctx2 with
  | CF.Ctx es1, CF.Ctx es2 -> eq_estate es1 es2
  | CF.OCtx _, CF.OCtx _   ->
    let es_l1, es_l2 = octx_2_es_list ctx1, octx_2_es_list ctx2 in
    Gen.BList.list_setequal_eq  eq_estate es_l1 es_l2
  | _, _ -> false

(* WN : such equality need to take into account inference result too, not just final states *)
let merge_contexts_x (ctx: CF.list_context): CF.list_context =
  match ctx with
  | FailCtx _        -> ctx
  | SuccCtx ctx_list -> SuccCtx (Gen.BList.remove_dups_eq eq_context ctx_list)

let merge_contexts (ctx: CF.list_context): CF.list_context =
  let pr = Cprinter.string_of_list_context in
  Debug.no_1 "merge_contexts" pr pr  merge_contexts_x ctx

(********** end MERGE STATES with IDENTICAL FORMULAS (syntactic check) ***************)

(************* CONVERT TAIL-REC to LINEAR vdef ***************)
let convert_substitution_helper_x from_sv to_sv h p emap subs_pure =
  let aliases     = from_sv::(CP.EMapSV.find_equiv_all from_sv emap) in
  let from_sv_lst = aliases in
  let to_sv_lst   = List.map (fun a -> to_sv) aliases in
  let h = CF.subst_avoid_capture_h from_sv_lst to_sv_lst h in
  let p = if subs_pure then  CP.subst_avoid_capture from_sv_lst to_sv_lst p else p in
  (h,p)

let convert_substitution_helper from_sv to_sv h p emap subs_pure =
  let pr1 = Cprinter.string_of_spec_var in
  let pr3 = Cprinter.string_of_h_formula in
  let pr4 = Cprinter.string_of_pure_formula in
  let pr_out = pr_pair pr3 pr4 in
  Debug.no_4 "convert_substitution_helper" pr1 pr1 pr3 pr4 pr_out (fun _ _ _ _ -> convert_substitution_helper_x from_sv to_sv h p emap subs_pure) from_sv to_sv h p

let convert_substitution_helper_opt from_sv to_sv h p emap subs_pure =
  let (h,p) =
    match from_sv, to_sv with
    | Some from_sv0, Some to_sv0 ->  convert_substitution_helper from_sv0 to_sv0 h p emap subs_pure
    | _ -> (h,p)
  in (h,p)

let elim_useless_exists (h: CF.h_formula) (p: CP.formula)  (qvars: CP.spec_var list) =
  let unused_qvars, qvars = Gen.BList.diff_split_eq CP.eq_spec_var qvars (CF.h_fv h) in
  let new_pure = CP.mkExists unused_qvars p (CP.get_pure_label p) (CP.pos_of_formula p) in
  let () = Debug.ninfo_hprint (add_str "unused qvars" (pr_list Cprinter.string_of_spec_var) ) unused_qvars no_pos in
  let () = Debug.ninfo_hprint (add_str "qvars" (pr_list Cprinter.string_of_spec_var) ) qvars no_pos in
  let () = Debug.ninfo_hprint (add_str "p: " ( Cprinter.string_of_pure_formula) ) p no_pos in
  let () = Debug.ninfo_hprint (add_str "new_pure: " ( Cprinter.string_of_pure_formula) ) new_pure no_pos in
  let new_pure = CP.elim_exists new_pure in
  (new_pure, qvars)

let combine_opt_ptrs f1 f2 =
  let res = match f1, f2 with
    | Some f1, _
    | _, Some f1 -> Some f1  (* WARNING, might lose a bck ptr here if you support mulptiple bck ptrs *)
    | _          -> None
  in res

let back_ptr_of_heap_x (h: CF.h_formula) fwd_ptr_of_prev_node emap  (vdef: C.view_decl) pos =
  let aliases = fwd_ptr_of_prev_node::(CP.EMapSV.find_equiv_all fwd_ptr_of_prev_node emap) in
  let rec helper h (ddecl,fld_name) =
    match h with
    | CF.DataNode d ->
      if (Gen.BList.mem_eq CP.eq_spec_var d.CF.h_formula_data_node aliases) then
        if (String.compare d.CF.h_formula_data_name ddecl.C.data_name == 0) then
          let ddecl_fields = List.map (fun (a,b) -> snd a) ddecl.C.data_fields in
          let lst = List.combine ddecl_fields d.CF.h_formula_data_arguments in
          let () = Debug.info_hprint (add_str "field:" (pr_id) ) fld_name no_pos in
          let bck_sv = List.fold_left (fun acc (f,a) -> if (String.compare fld_name f == 0 )then acc@[a] else acc) [] lst in
          if (List.length bck_sv >=1) then Some (List.hd bck_sv)
          else None
        else None
      else None
    | CF.ViewNode v ->
      let () = Debug.info_hprint (add_str "view:" (pr_id) ) v.CF.h_formula_view_name no_pos in
      if (String.compare v.CF.h_formula_view_name vdef.C.view_name == 0) then
        let () = Gen.report_warning pos "[norml.ml] trying to linearize a view but not support 2 recursive calls yet" in
        None
      else
      if (Gen.BList.mem_eq CP.eq_spec_var v.CF.h_formula_view_node aliases) then
        let () = Gen.report_warning pos "[norml.ml] trying to linearize a view but we do not support mix defs" in
        None
      else
        None
    | CF.Star({CF.h_formula_star_h1 = h1;
               CF.h_formula_star_h2 = h2;}) ->
      let bk1 = helper h1 (ddecl,fld_name) in
      let bk2 = helper h2 (ddecl,fld_name) in
      combine_opt_ptrs bk1 bk2
    | _ ->
      let () = Gen.report_warning pos "[norml.ml] trying to linearize a view but we do not support linearization of non-star formulas" in
      None (* rec *)
  in
  if (List.length vdef.C.view_backward_fields != 1) then
    None
  else
    let bck_field_ptr = List.hd vdef.C.view_backward_fields in
    (helper h bck_field_ptr)

let back_ptr_of_heap (h: CF.h_formula) fwd_ptr_of_prev_node emap  (vdef: C.view_decl) pos =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = pr_opt Cprinter.string_of_spec_var in
  Debug.no_1 "back_ptr_of_heap" pr1 pr2(fun _ ->  back_ptr_of_heap_x (h: CF.h_formula) fwd_ptr_of_prev_node emap  (vdef: C.view_decl) pos ) h

let subs_head_with_free vdef hd p emap =
  let head =
    match hd with
    | CF.ViewNode h ->
      (* identify fwd ptr of head *)
      let args_lst = List.combine h.CF.h_formula_view_arguments vdef.C.view_vars in
      let free = List.filter (fun (n,v) -> not(Gen.BList.mem_eq CP.eq_spec_var v (vdef.C.view_forward_ptrs@vdef.C.view_backward_ptrs))) args_lst in
      let () = Debug.info_hprint (add_str "free" (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var))) free no_pos in
      let new_head = List.fold_left (fun acc_head (f,t) ->
          let h,p =  convert_substitution_helper f t acc_head p emap false in
          h) hd free in
      new_head
    | _ -> hd
  in head

(* swap the bk and fwd ptrs of head and tail:
 * -- bk of tail becomes bk of head
 * -- fwd of tail becomes fwd of head
 * -- fwd of head become fwd of tail
 * -- bk of head becomes exit node of processed tail.
*)
let convert_substitution prog fwd_ptrs bk_ptrs tail head pp emap qvars vdef =
  let (fwd_ptr_v, fwd_ptr_n) = List.hd fwd_ptrs in (* check that fwd_ptrs has exactly size 1, was done earlier *)
  let () = Debug.info_hprint (add_str "fwd_ptrs:" (pr_pair Cprinter.string_of_spec_var  Cprinter.string_of_spec_var) )  (fwd_ptr_v, fwd_ptr_n)  no_pos in
  let (bk_ptrs_v, bk_ptr_n) =
    if (List.length bk_ptrs == 1) then
      let (bk_ptr_v, bk_ptr_n) = List.hd bk_ptrs in
      (Some bk_ptr_v, Some bk_ptr_n)
    else (None, None) in
  (* substitute the pointer corresponding to the fwd ptr of the self view, with "self" inside the tail *)
  let self_temp = CP.fresh_spec_var (CP.mk_self None) in
  let bk_tn = back_ptr_of_heap tail fwd_ptr_n emap vdef (CF.pos_of_h_formula tail) in
  let (tail, p) = convert_substitution_helper_opt bk_tn bk_ptr_n tail pp emap false in
  let (tail, p) = convert_substitution_helper fwd_ptr_n self_temp tail p emap true in
  (* let (tail, p) = convert_substitution_helper new_self.field.bk fwd_ptr_n tail pp emap false in *)
  (* substitue the fwd pointer of view def the fwd pointer of initial self view *)
  let fresh_sv_n = CP.fresh_spec_var fwd_ptr_n in
  let (tail, p) = convert_substitution_helper fwd_ptr_v fresh_sv_n tail p emap false in
  (* substitute self fwd pointer with fwd ptr of view in the head *)
  let fresh_sv_v= CP.fresh_spec_var fwd_ptr_v in
  let (head, p) = convert_substitution_helper fwd_ptr_n fresh_sv_v head p emap true in (* need a new var, as a normalization step -- instead of fwd_ptr_v *)
  let aux_p = CP.mkEqVar fresh_sv_v fwd_ptr_v no_pos in (*  to update on pos *)
  (* substitute self var with fwd pointer of self in the head *)
  let (head, p) = convert_substitution_helper (CP.mk_self None) fresh_sv_n head p emap false in
  (* get last node of tail and set it to be the bck ptr of head view *)
  let heap_chain = List.hd (Acc_fold.collect_heap_chains tail (MCP.mix_of_pure p) self_temp vdef prog) in
  let (_, _, new_bk_of_nv, _) = fst heap_chain in
  let (head, p) = convert_substitution_helper_opt bk_ptr_n (Some new_bk_of_nv) head p emap false in
  let head   = subs_head_with_free vdef head p emap in
  (* remove temp vars *)
  let (tail, p) = convert_substitution_helper self_temp (CP.mk_self None) tail p emap true in
  let qvars = fresh_sv_v::fresh_sv_n::qvars in
  let pp = CP.mkAnd p aux_p no_pos in
  (tail, head, pp,qvars)

(* to update below after fix on fwd & bck ptr *)
let convert_h_formula_to_linear_recursive_helper  prog (head: CF.h_formula) (tail: CF.h_formula) (p: MCP.mix_formula)
    (vdef: C.view_decl) (qvars: CP.spec_var list) emap (orig_f: h_formula):
  (CF.h_formula * MCP.mix_formula * ( CP.spec_var list)) =
  (* let self_tmp_sv =  CP.mk_spec_var (self ^ "_orig_" ^ Globals.fresh_int) in *)
  (* let tail = CF.subst_one_by_one_h [(CP.mk_self None), self_tmp_sv] tail in *)
  let pos = CF.pos_of_h_formula orig_f in
  let h,p,q =
    match head with
    | CF.ViewNode hd ->
      let fwd_ptrs_vdef = vdef.C.view_forward_ptrs in
      let bk_ptrs_vdef = vdef.C.view_backward_ptrs in
      let pp = (Mcpure.pure_of_mix p) in
      if (String.compare vdef.C.view_name hd.CF.h_formula_view_name == 0 && (List.length fwd_ptrs_vdef == 1)) then
        let () = Gen.report_warning pos "[norml.ml] linearizing a tail-rec def into a linear one " in
        (* identify fwd ptr of head *)
        let args_lst = List.combine vdef.C.view_vars hd.CF.h_formula_view_arguments in
        let fwd_ptrs = List.filter (fun (v,n) -> Gen.BList.mem_eq CP.eq_spec_var v fwd_ptrs_vdef) args_lst in
        let bk_ptrs  = List.filter (fun (v,n) -> Gen.BList.mem_eq CP.eq_spec_var v bk_ptrs_vdef) args_lst in
        let () = Debug.info_hprint (add_str "fwd_ptrs:" (pr_list (pr_pair Cprinter.string_of_spec_var  Cprinter.string_of_spec_var) )) fwd_ptrs no_pos in
        let (tail, head, pp, qvars) = convert_substitution prog fwd_ptrs bk_ptrs (* fwd_ptr_v fwd_ptr_n *) tail head pp emap qvars vdef in
        let new_f = CF.mkStarH tail head pos in
        let new_pure, new_qvars = elim_useless_exists new_f pp qvars in
        let p = MCP.mix_of_pure new_pure in
        (new_f, p, new_qvars)
      else
        (* base case with non-emp heap? *)
        let () = Gen.report_warning pos "[norml.ml] trying to linearize a view which is not tail-rec? 1 " in
        (orig_f, p, qvars)            (* self does not point to the recursive node *)
    | _ ->
      (* base case with non-emp heap? *)
      let () = Gen.report_warning pos "[norml.ml] trying to linearize a view which is not tail-rec? 2 " in
      (orig_f, p, qvars)           (* if pred is well defined and tail-rec, should never reach here *)
  in
  (h,p,q)

let prepare_leftover_pure () = ()

let prepare_push_pure p qvars = (p,qvars)
(* let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations p) in  *)
(* let pure_to_be_pushed, qvars_to_be_pushed = elim_useless_exists CF.HEmp p qvars in *)
(* let args_aliases = List.fold_left (fun acc v->  v::(CP.EMapSV.find_equiv_all v emap)@acc ) [] vdef.C.view_vars in *)
(* let fv_push_pure = CP.fv pure_to_be_pushed in *)
(* let new_args = CP.BList.difference_eq CP.eq_spec_var fv_push_pure args_aliases in *)
(* let renamed_new_args = List.map CP.fresh_spec_var new_args in *)
(* let push_pure =  CP.subst_avoid_capture new_args renamed_new_args pure_to_be_pushed in *)
(* let push_pure = MCP.mix_of_pure push_pure in *)

(* to update below after fix on fwd & bck ptr *)
let convert_h_formula_to_linear_base_helper (head: CF.h_formula) (p: MCP.mix_formula)
    (vdef: C.view_decl) (qvars: CP.spec_var list) emap (orig_f: h_formula):
  ((CF.h_formula * MCP.mix_formula * ( CP.spec_var list)) *  ((ident * (CP.spec_var list) * MCP.mix_formula) option) ) =
  let pos = CF.pos_of_h_formula orig_f in
  let name_new_view =  vdef.C.view_name ^ "_A" ^ (string_of_int (Globals.fresh_int())) in
  let fresh_sv = CP.SpecVar(Named name_new_view, "u",Unprimed) in
  let fresh_sv = CP.fresh_spec_var fresh_sv in
  let new_node = CF.mkViewNode fresh_sv name_new_view vdef.C.view_vars no_pos in
  let fwd_ptrs_vdef = vdef.C.view_forward_ptrs in
  if (List.length fwd_ptrs_vdef == 1) then
    let p = MCP.pure_of_mix p in
    (* currently, we can only handle tail-rec with one fwd ptr *)
    let fwd_ptr_v = List.hd fwd_ptrs_vdef in
    (* connect base case heap with a node pointing to the new view *)
    let (head, _) = convert_substitution_helper fwd_ptr_v fresh_sv head p emap false in
    let new_base_case_heap =  CF.mkStarH head new_node pos in
    (* eliminate leftover eq of form q=x, where q is equantif and x is free. Moreover, q is not used in the heap *)
    let (new_pure, qvars) = elim_useless_exists new_base_case_heap p qvars in
    (* compute the set of new args for the new view *)

    let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations new_pure) in
    (* TODO: add the eq (alias info) in the new base case as formula *)
    let pure_to_be_pushed, qvars_to_be_pushed = elim_useless_exists CF.HEmp new_pure qvars in
    let args_aliases = List.fold_left (fun acc v->  v::(CP.EMapSV.find_equiv_all v emap)@acc ) [] vdef.C.view_vars in
    let fv_push_pure = CP.fv pure_to_be_pushed in
    let new_args = Gen.BList.difference_eq CP.eq_spec_var fv_push_pure args_aliases in
    let renamed_new_args = List.map CP.fresh_spec_var new_args in
    let push_pure =  CP.subst_avoid_capture new_args renamed_new_args pure_to_be_pushed in
    let push_pure = MCP.mix_of_pure push_pure in
    (* let new_pure =  *)
    ((new_base_case_heap, push_pure, fresh_sv::qvars), (Some (name_new_view, new_args@renamed_new_args, push_pure)))
  else
    (* cannot handle multiple fwd ptrs *)
    ((orig_f, p, qvars), None)


let convert_h_formula_to_linear prog (vdef: C.view_decl) (f: CF.h_formula) (p: MCP.mix_formula) (qvars: CP.spec_var list) :
  (CF.h_formula * MCP.mix_formula * ( CP.spec_var list)) * ((ident * (CP.spec_var list) * MCP.mix_formula) option) =
  let new_f =
    match f with
    | HEmp -> ((f, p, qvars), None)           (* base_case *)
    | _    ->
      let pp = (Mcpure.pure_of_mix p) in
      let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations pp) in
      let self = (CP.mk_self None) in
      let aliases = CP.EMapSV.find_equiv_all self emap in
      (* remove self node from f, and save it in orig_self *)
      let aliases = self::aliases in
      (* TODO: modify below, so that self can accomodate all inductive self connected nodes, not just the self *)
      let orig_self_ls, tail =  Cvutil.crop_h_formula f aliases in
      let (new_h, new_p, qvar), new_view =
        match orig_self_ls with
        | h::[]  ->
          if (CF.h_formula_contains_node_name h vdef.C.view_name) then
            (* inductive case *)
            (convert_h_formula_to_linear_recursive_helper prog h tail p vdef qvars emap f, None)
          else
            ((f, p, qvars), None)
        (* base case with non-emp heap *)
        (* convert_h_formula_to_linear_base_helper h p vdef qvars emap f *)
        | h::t   ->  ((f, p, qvars), None) (* if using only *, will never reach here *)
        | []     ->  ((f, p, qvars), None) (* if pred is well defined, will never reach this *)
      in
      ((new_h, new_p, qvar), new_view)
  in
  if not((List.length vdef.C.view_forward_ptrs == 1) && (List.length vdef.C.view_backward_ptrs <= 1)) then
    let pos = CF.pos_of_h_formula f in
    let () = Gen.report_warning pos "[norml.ml] we currently do not support tail conversion of views with more than 1 fwd ptr or more than 1 bk ptr " in
    ((f, p, qvars), None)
  else
    new_f

let convert_formula_to_linear_x prog (vdef: C.view_decl) (f: CF.formula): CF.formula = (* f *)
  let rec helper f =
    match f with
    | CF.Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let rf1 = helper f1 in
      let rf2 = helper f2 in
      let resform = CF.mkOr rf1 rf2 pos in
      resform
    | CF.Base f1 ->
      let f1_pure = f1.CF.formula_base_pure in
      let ((f1_heap, f1_pure, f1_qv), new_view) = convert_h_formula_to_linear prog vdef f1.CF.formula_base_heap  f1_pure [] in
      if not(Gen.is_empty f1_qv) then
        (* should never reach this branch if normalization works ok *)
        CF.mkExists_w_lbl f1_qv f1_heap f1_pure f1.CF.formula_base_vperm f1.CF.formula_base_type
          f1.CF.formula_base_flow  f1.CF.formula_base_and f1.CF.formula_base_pos f1.CF.formula_base_label
      else
        CF.Base({f1 with formula_base_heap = f1_heap; formula_base_pure = f1_pure})
    | CF.Exists f1 ->
      let f1_pure = f1.CF.formula_exists_pure in
      let f1_qv   = f1.CF.formula_exists_qvars in
      let ((f1_heap, f1_pure, f1_qv), new_view) = convert_h_formula_to_linear prog vdef f1.CF.formula_exists_heap f1_pure f1_qv in
      CF.Exists({f1 with formula_exists_heap = f1_heap; formula_exists_pure = f1_pure; formula_exists_qvars = f1_qv;})
  in
  helper f

let convert_formula_to_linear prog (vdef: C.view_decl) (f: CF.formula): CF.formula =
  let pr0 = Cprinter.string_of_view_decl in
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "convert_formula_to_linear" pr0 pr1 pr1 (fun _ _ -> convert_formula_to_linear_x prog vdef f) vdef f

let convert_struc_formula_to_linear prog (vdef: C.view_decl) (f: CF.struc_formula): CF.struc_formula =
  let rec helper f =
    match f with
    | CF.EList el  -> CF.EList  (map_l_snd (fun c-> helper c) el)
    | CF.ECase ec  -> CF.ECase  {ec with
                                 formula_case_branches = map_l_snd (fun c -> helper c) ec.CF.formula_case_branches;}
    | CF.EBase eb  -> CF.EBase  {eb with
                                 formula_struc_base = convert_formula_to_linear prog vdef eb.CF.formula_struc_base ;
                                 formula_struc_continuation = map_opt (fun c-> helper c) eb.CF.formula_struc_continuation;}
    | CF.EAssume a -> CF.EAssume{a with
                                 formula_assume_simpl = convert_formula_to_linear prog vdef a.CF.formula_assume_simpl;
                                 formula_assume_struc = helper a.CF.formula_assume_struc ;}
    | CF.EInfer ei ->  CF.EInfer{ei with
                                 formula_inf_continuation = helper ei.CF.formula_inf_continuation }
  in helper f

(*
   Initial assumptions - to be improved:
   * predicate captures no pure info
   * base case contains empty heap
TODO0: remove unused qvars, true relations, and emp, and add check for vdef with only one fwd ptr
TODO1: transform the above assumptions into conditions
TODO2: consider the non-empty heap for base case by introducing an extra pred
 *)
let convert_vdef_to_linear_x prog (vdef: C.view_decl): C.view_decl =
  if not(vdef.C.view_is_tail_recursive) then vdef
  else
    let vd = vdef in
    let f0 = vd.C.view_un_struc_formula in
    let f1 = map_l_fst (fun f -> convert_formula_to_linear prog vdef f) f0 in
    {vd with
     (* C.view_is_tail_recursive = false; *)
     (* view_formula : F.struc_formula *)
     C.view_linear_formula = f1;
     C.view_un_struc_formula = f1;
     (* view_materialized_vars : mater_property list; *)
    }

let convert_vdef_to_linear prog (vdef: C.view_decl): C.view_decl =
  let pr = Cprinter.string_of_view_decl in
  Debug.no_1 "convert_vdef_to_linear" pr pr (fun _ -> convert_vdef_to_linear_x prog vdef ) vdef

let convert_tail_vdefs_to_linear prog =
  let vdecls = prog.C.prog_view_decls in
  let vdecls = List.map (convert_vdef_to_linear prog) vdecls in
  (* { prog with C.prog_view_decls = vdecls } *)
  let () = prog.C.prog_view_decls <- vdecls in
  prog

(************* end CONVERT TAIL-REC to LINEAR vdef ***************)

let imm_abs_norm_formula (f:CF.formula) prog unfold_fun : CF.formula  =
  x_add Immutable.merge_alias_nodes_formula prog f [] (x_add Cvutil.xpure_heap_symbolic 13 prog) unfold_fun
(* Cvutil.crop_h_formula f svl *)

let imm_abs_norm_struc_formula (f:CF.struc_formula) conseq prog  unfold_fun: CF.struc_formula  =
  x_add Immutable.merge_alias_nodes_struc_formula prog f (x_add Cvutil.xpure_heap_symbolic 14 prog) conseq  unfold_fun
(* Cvutil.crop_h_formula f svl *)

let imm_norm_formula prog f unfold_fun pos =
  (* imm_abs_norm_formula modifies f only when Globals.imm_merge is set *)
  let f = imm_abs_norm_formula f prog (unfold_fun prog pos) in
  let f = if(!Globals.allow_field_ann) then Mem.compact_nodes_with_same_name_in_formula f else f in
  f

let imm_norm_h_formula prog fh fp unfold_fun pos =
  let form = CF.mkBase_simp fh fp in
  let form = imm_norm_formula prog form unfold_fun pos in
  match form with
  | CF.Base b -> b.CF.formula_base_heap, b.CF.formula_base_pure
  | _ -> let () = report_warning no_pos "could not perform alias node merge" in
    fh,fp

let imm_norm_struc prog f (conseq: bool) unfold_fun pos =
  (* imm_abs_norm_formula modifies f only when Globals.imm_merge is set *)
  let f = imm_abs_norm_struc_formula f conseq prog (unfold_fun prog pos) in
  let f = if(!Globals.allow_field_ann) then Mem.compact_nodes_with_same_name_in_struc f else f in
  f

let find_rec_data iprog cprog ids =
  let data_d_lst = cprog.Cast.prog_data_decls in
  let () = y_tinfo_hp (add_str "data_decls" (pr_list (fun d -> d.Cast.data_name))) data_d_lst in
  let () = List.iter (fun d ->
      let n = d.Cast.data_name in
      let () = y_tinfo_hp (add_str "name" pr_id) n in
      let fields = List.map (fun ((t,id),_) -> t) d.Cast.data_fields in
      let fields = List.filter (fun t -> is_node_typ t) fields in
      let fields = List.map (fun t -> match t with Named id -> id | _ -> failwith ("impossible"^x_loc)) fields in
      (* let () = y_tinfo_hp (add_str "fields" (pr_list (pr_pair CF.string_of_typed_ident (pr_list pr_id)))) d.Cast.data_fields in *)
      let () = y_tinfo_hp (add_str "fields" (pr_list pr_id)) fields in
      let () = HipUtil.data_scc_obj # replace x_loc n fields in
      ()
    ) data_d_lst in
  let () = y_tinfo_hp (add_str "data_scc_obj" pr_id) HipUtil.data_scc_obj # string_of in
  let lst = HipUtil.data_scc_obj # get_scc in
  let () = y_tinfo_hp (add_str "scc" (pr_list (pr_list pr_id))) lst in
  let sel_scc = Cast.get_selected_scc_each ids (fun x -> x) lst in
  let sel_data_d = build_sel_scc sel_scc (fun d -> d.Cast.data_name) data_d_lst in
  let () = y_tinfo_hp (add_str "sel_scc" (pr_list (pr_list pr_id))) sel_scc in
  let () = y_tinfo_hp (add_str "sel_data" (pr_list (pr_list Cprinter.string_of_data_decl))) sel_data_d in
  (* let sel_scc = List.map List.concat sel_scc in *)
  let com_scc = List.combine sel_data_d sel_scc in
  let com_scc = List.map (fun (d_lst, vns) ->
      List.iter (fun dd ->
          let lst = dd.Cast.data_fields in
          let new_lst = List.map (fun (id, acc) ->
              let t = name_of_typ (fst(id)) in
              (id, if List.mem t vns then rec_field_id::acc else acc)) lst
          in
          dd.Cast.data_fields <- new_lst;
          try
            let idd = I.look_up_data_def_raw iprog.I.prog_data_decls dd.Cast.data_name in
            idd.Iast.data_fields <- List.map (fun (i, ann) -> (i, no_pos, false, ann)) new_lst;
          with _ -> ()
        ) d_lst;
        d_lst
    ) com_scc in
  let () = y_tinfo_hp (add_str "sel_data" (pr_list (pr_list Cprinter.string_of_data_decl))) sel_data_d in
  let data_lst = List.concat  sel_data_d in
  let () = Cf_ext.add_data_tags_to_obj data_lst in
  (* let () = y_tinfo_hp (add_str "iprog_data_decls" (pr_list Iprinter.string_of_data_decl)) iprog.Iast.prog_data_decls in *)
  (* let () = y_tinfo_hp (add_str "cprog_data_decls" (pr_list Cprinter.string_of_data_decl)) cprog.Cast.prog_data_decls in *)
  ()

