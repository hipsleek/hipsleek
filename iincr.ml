open Globals
open Wrapper
open Others
open Exc.GTable
open Gen

open Cformula

module CP = Cpure


let get_infer_type its0 inf0=
  (* let rec look_up ifts inf rem= *)
  (*   match ifts with *)
  (*     | [] -> raise Not_found *)
  (*     | it::rest -> if it == inf then it,rem@rest else *)
  (*         look_up rest inf (rem@[it]) *)
  (* in *)
  (* look_up its0 inf0 [] *)
  List.find (fun inf1 -> inf0==inf1) its0

let extract_inf_props prog scc=
  let rec get_from_one_spec spec=
    match (spec) with
    | (   EList el) -> List.fold_left (fun acc (_,sf) ->
          acc@(get_from_one_spec sf)
      ) [] el
    |    EInfer ei -> let inf_obj = ei.formula_inf_obj # clone in
      if inf_obj # is_size then
        [INF_SIZE]
      else []
    | _ -> []
  in
  List.fold_left (fun acc spec -> acc@(get_from_one_spec spec)) [] scc

(*
  for each view in scc: extd with ext_pred_name
  output: [old_vn, new_vn]
*)
let extend_views iprog prog ext_pred_name scc=
  let vns = List.fold_left (fun r proc ->
      r@(get_views_struc proc.Cast.proc_stk_of_static_specs # top)
  ) [] scc in
  let vns1 = Gen.BList.remove_dups_eq string_compare (List.map (fun vn -> vn.h_formula_view_name) vns) in
  let vdcls = List.map (Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls) vns1 in
  let pure_extn_view = Cast.look_up_view_def_raw 65 prog.Cast.prog_view_decls ext_pred_name in
  let n_views = Derive.expose_pure_extn  iprog prog vdcls [pure_extn_view] in
  []

let extend_inf iprog prog ext_pred_name proc=
  let vnames = get_views_struc proc.Cast.proc_stk_of_static_specs # top in
  proc


let extend_pure_props_x iprog cprog props sccs hp_rel_defs
      scc_sel_hps scc_sel_post_hps=
  (* *********************************)
  (*equivalent matching already?*)
  let is_matched view_equivs def=
    match def.Cformula.def_cat with
      | Cpure.HPRelDefn (hp,_,_) ->
            let hp_id = CP.name_of_spec_var hp in
            List.exists (fun (m_hp_id,_) -> string_compare hp_id m_hp_id) view_equivs
      | _ -> false
  in
  let rec get_sst_hp hp_defs res=
    match hp_defs with
      | [] -> res
      | hp_def::rest -> begin
          let rec_fnc = get_sst_hp rest res in
          match hp_def.def_cat with
            | Cpure.HPRelDefn (hp,r,args) -> begin
                let fs = List.fold_left (fun r (f,_) -> r@(list_of_disjs f) ) [] hp_def.def_rhs in
                match fs with
                  | [f] -> begin
                      try
                        let hpargs = extract_HRel_f f in
                        let hpargs0 = extract_HRel  hp_def.def_lhs in
                        get_sst_hp rest (res@[(hpargs0, hpargs)])
                      with _ -> rec_fnc
                    end
                  | _ -> rec_fnc
              end
            | _ -> rec_fnc
        end
  in
  let rec do_extend props equivs defs=
    match props with
      | [] -> defs,equivs
      | p::rest -> begin
          let exted_defs,n_equivs = match p with
            | INF_SIZE ->  List.fold_left (fun (acc,sst) def ->
                  let nhp,_,ext_svl,ndef= Iutil.size_ext_hpdef iprog cprog def in
                   let hp,args = extract_HRel def.def_lhs in
                   let equiv = ((hp,args),(nhp, ext_svl)) in
                  acc@[ndef],sst@[equiv]
              ) ([],[]) defs
            | _ -> defs,[]
          in
          do_extend rest (equivs@n_equivs) exted_defs
          end
  in
   let hn_hprel_subst_trans sst_hps hn = match hn with
    | HRel (hp, eargs,p) -> begin
       try
         let ((hp1,frm_args1),(hp2,frm_args2)) = List.find (fun ((hp1,_),_) -> CP.eq_spec_var hp hp1) sst_hps in
         let to_args1 = List.concat (List.map CP.afv eargs) in
         let sst0 = List.combine frm_args1 to_args1 in
         let to_args2 = CP.subst_var_list sst0 frm_args2 in
         let eargs2 = List.map (fun sv -> CP.mkVar sv no_pos) to_args2 in
         HRel (hp2, eargs2, p)
       with _ -> hn
      end
    | _ -> hn
   in
   let subst_hps sst_hps proc=
     let s_spec =  proc.Cast.proc_static_specs in
     let n_sspec = struc_formula_trans_heap_node [] (formula_map (hn_hprel_subst_trans sst_hps)) s_spec in
   {proc with Cast.proc_static_specs = n_sspec}
   in
  (* *********************************)
  let view_equivs = cprog.Cast.prog_view_equiv in
  let _ =  Debug.ninfo_hprint (add_str "  view_equivs: " (pr_list_ln (pr_pair pr_id pr_id))) (view_equivs) no_pos in
  (* partition views equiv matched, do not need extend *)
  let matched_defs, rem_defs = List.partition (is_matched view_equivs) hp_rel_defs in
  let equivs_form = get_sst_hp rem_defs [] in
  let _ =  Debug.ninfo_hprint (add_str "  equivs_form" (pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) (pr_pair !CP.print_sv !CP.print_svl)))) equivs_form no_pos in
  let equiv_defs,rem_defs1 = List.partition (fun def ->
      let hp = get_hpdef_name def.def_cat in
      List.exists (fun ((hp1,_),_) -> CP.eq_spec_var hp hp1) equivs_form
  ) rem_defs in
  let _ =  Debug.ninfo_hprint (add_str "  rem_defs1: " (pr_list_ln Cprinter.string_of_hp_rel_def_short)) (rem_defs1) no_pos in
  let exted_defs,equivs = do_extend props [] rem_defs1 in
  let n_sccs,nscc_sel_hps, nscc_sel_post_hps = if equivs = [] then
    sccs,scc_sel_hps, scc_sel_post_hps
  else
    let ex_equivs = if equivs_form = [] then [] else
      List.fold_left (fun acc ((hp1,args1),(hp2,args2)) -> begin
        try
          (*look up the extended pred of hp2*)
          let (_,(hp3,ex_args3)) = List.find (fun ((hp,_),_) -> CP.eq_spec_var hp2 hp) equivs in
          acc@[((hp1,args1),(hp3, CP.fresh_spec_vars ex_args3))]
        with _ -> acc
      end
      ) [] equivs_form in
    let _ =  Debug.ninfo_hprint (add_str " ex_equivs" (pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) (pr_pair !CP.print_sv !CP.print_svl)))) ex_equivs no_pos in
    let equivs_hps,sst0 = List.fold_left (fun (r1,r2) ((hp1,args1),(hp2,ex_args)) ->
        r1@[((hp1,args1),(hp2,args1@ex_args))], r2@[(hp1,hp2)]
    ) ([],[]) (equivs@ex_equivs) in
    let n_sccs = List.map (fun spec ->
        subst_hps equivs_hps spec
    ) sccs in
    let nscc_sel_hps = CP.subst_var_list sst0 scc_sel_hps in
    let nscc_sel_post_hps = CP.subst_var_list sst0 scc_sel_post_hps in
    n_sccs,nscc_sel_hps, nscc_sel_post_hps
  in
  (*update procs delcares*)
  let old_procs = cprog.Cast.new_proc_decls in
  let proc_decls = Hashtbl.fold (fun i p acc -> begin
    try
      let np =  List.find (fun p1 ->
          String.compare p.Cast.proc_name p1.Cast.proc_name == 0
      ) n_sccs in
      acc@[(i,np)]
    with _ -> acc@[(i,p)]
  end
  ) old_procs [] in
  let _ = Hashtbl.reset old_procs in
  let _ = List.iter (fun (i,p) -> Hashtbl.add old_procs i p) proc_decls in
  let nproc = if props = [] || equivs = [] then cprog else
    {cprog with Cast.new_proc_decls = old_procs} in
  (************END update**************)
  nproc,n_sccs,matched_defs@exted_defs@equiv_defs,nscc_sel_hps,nscc_sel_post_hps

let extend_pure_props iprog cprog props sccs hp_rel_defs scc_sel_hps scc_sel_post_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
  let pr2 proc = Cprinter.string_of_struc_formula proc.Cast.proc_static_specs in
  Debug.no_2 "extend_pure_props" pr1 (pr_list string_of_inf_const)
      (pr_penta pr_none (pr_list_ln pr2) pr1 !CP.print_svl !CP.print_svl)
      (fun _ _ ->  extend_pure_props_x iprog cprog props sccs hp_rel_defs scc_sel_hps scc_sel_post_hps) hp_rel_defs props
