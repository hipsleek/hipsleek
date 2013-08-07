open Globals
open Gen
open Cformula

module DD = Debug
module CF=Cformula
module CP=Cpure
module MCP=Mcpure
module C = Cast
module TP = Tpdispatcher
module SAU = Sautility

(***********************************************)
(*****ELIM unused parameters of view **********)
let norm_elim_useless_para_x view_name sf args=
  let extract_svl f=
    let f1 = CF.elim_exists f in
    let new_f = CF.drop_view_formula f1 [view_name] in
    (* let _ = Debug.info_pprint (" new_f:" ^ (Cprinter.prtt_string_of_formula new_f) ) no_pos in *)
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
    (* let _ = Debug.info_pprint (" svl:" ^ (!CP.print_svl svl) ) no_pos in *)
    (* let _ = Debug.info_pprint (" args:" ^ (!CP.print_svl args) ) no_pos in *)
    let new_args = CP.intersect_svl args svl in
    (* let _ = Debug.info_pprint (" new_args:" ^ (!CP.print_svl new_args) ) no_pos in *)
    if List.length args > List.length new_args then
      let keep_pos = build_keep_pos_list args [] 0 new_args in
      let new_vname = CP.fresh_old_name view_name in
      let ss = [(view_name,new_vname,keep_pos)] in
      (* let n_sf = CF.drop_view_paras_struc_formula sf ss in *)
      (* let n_ufs = List.map ( fun (uf, ufl) -> (CF.drop_view_paras_formula uf ss, ufl)) ufs in *)
      let dropped_args = CP.diff_svl args svl in
      let _ = Debug.info_pprint ("  ELIMINATE parameters:" ^ (!CP.print_svl dropped_args) ^ " of view " ^ view_name ^ "\n" ) no_pos in
      (new_vname, new_args, ss)
    else
      (view_name, args, [])

let norm_elim_useless_para view_name sf args=
  let pr1 = Cprinter.string_of_struc_formula in
  let pr2 = pr_triple pr_id !CP.print_svl (pr_list (pr_triple pr_id pr_id (pr_list string_of_int))) in
  Debug.no_2 "norm_elim_useless_para" pr1 !CP.print_svl pr2
      (fun _ _ -> norm_elim_useless_para_x view_name sf args) sf args

(*assume views are sorted*)
let norm_elim_useless_x vdefs sel_vns=
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
      let new_vname, view_sv_vars, ss = norm_elim_useless_para vdef.Cast.view_name vdef.Cast.view_formula  vdef.Cast.view_vars in
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
        let new_def = {vdef with
            Cast.view_name = new_vname;
            Cast.view_vars = view_sv_vars;} in
        (*update rem_vdefs*)
        ([link_view;(elim_vdef ss new_def)], List.map (elim_vdef ss) rem_vdefs)
    else
      ([vdef],rem_vdefs)
  in
  let rec interate_helper rem_vdefs done_vdefs=
    match rem_vdefs with
      | [] -> done_vdefs
      | vdef::rest -> let new_defs,new_rest = process_one_view vdef rest in
        interate_helper new_rest (done_vdefs@new_defs)
  in
  interate_helper vdefs []

let norm_elim_useless vdefs sel_vns=
  let pr1 = pr_list pr_id in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  Debug.no_2 "norm_elim_useless" pr2 pr1 pr2
      (fun _ _ -> norm_elim_useless_x vdefs sel_vns) vdefs sel_vns
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
      | CF.ViewNode hv ->
          let eargs = List.map (fun v -> CP.mkVar v no_pos) (hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments) in
          let nh = CF.HRel (CP.SpecVar (HpT, hv.CF.h_formula_view_name, Unprimed ),eargs, no_pos) in
          (nh, [hv])
      | CF.HRel _
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf,[])
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
      | CF.HRel (hp, eargs, p) ->
          let args = List.fold_left List.append [] (List.map CP.afv eargs) in
          (CF.mkViewNode (List.hd args) (CP.name_of_spec_var hp) (List.tl args) p)
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf)
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

let look_for_anonymous_h_formula_x hf0=
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
      | HRel _
      | Hole _
      | HTrue
      | HFalse
      | HEmp -> []
  in
  let svl = CP.remove_dups_svl (helper hf0) in
  svl

let look_for_anonymous_h_formula hf0=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_1 "look_for_anonymous_h_formula" pr1 !CP.print_svl
      (fun _ -> look_for_anonymous_h_formula_x hf0) hf0

let convert_anonym_to_exist_formula_x f0 args=
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

let convert_anonym_to_exist_formula f0 args=
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
  let xpure_flag = TP.check_diff memo_pf_N memo_pf_P in
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

let norm_extract_common_one_view_x cprog cviews vdecl=
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
  let defs,elim_ss = SAU.get_longest_common_hnodes_list cprog false cdefs unk_hps unk_svl
    hp self_var vdecl.C.view_vars args fs2 [] in
  match defs with
    | [a] -> [vdecl]
    | [(hp1,(_,hrel1,_,f1));(hp2,(a,hrel2,_,f2))] ->
        let _ = Debug.info_pprint ("  DO EXTRACT on view: "^ (!CP.print_sv hp1) ^ "\n") no_pos in 
        let n_f1 =
          if !Globals.pred_elim_useless then
            CF.subst_hrel_f f1 elim_ss
          else
            f1
        in
        (* let _ = Debug.info_pprint ("  hp2: "^ (!CP.print_sv hp2)) no_pos in *)
        (*IMPORTANT: process hp2 first + check equiv then hp1*)
        (*matching with current views*)
        let (_, eq_hfs) = SAU.match_one_hp_views cviews (a,hrel2,None,f2) in
        let n_vdecl2, view_ss=
          if eq_hfs = [] then
             let _ = Debug.info_pprint ("  DO SYNTHESIZE view: "^ (!CP.print_sv hp2) ^ "\n") no_pos in 
            let _,args2 = CF.extract_HRel hrel2 in
            let vname2 = (CP.name_of_spec_var hp2) in
            let self_var2 = Cpure.SpecVar ((Named vname2), self, Unprimed) in
            let ss = [(List.hd args2, self_var2)] in
            let n_f21 = hprel_to_view f2 in
            let n_f22 = CF.subst ss n_f21 in
            let n_vdecl2 = recover_view_decl vdecl vname2 (List.tl args2) vdecl.C.view_is_rec n_f22 in
            ([n_vdecl2],None)
          else
            let eq_hf = List.hd eq_hfs in
            let eq_vn = extract_view_name eq_hf in
            let _ = Debug.info_pprint ("  DO NOT SYNTHESIZE. MATCHED view: "^ (eq_vn) ^ "\n") no_pos in 
            let to_hp = CP.SpecVar (HpT, eq_vn, Unprimed) in
            ([], Some ([hp2], to_hp))
        in
        (*hp1 must equal hp*)
        (* let _ = Debug.info_pprint ("  hp1: "^ (!CP.print_sv hp1)) no_pos in *)
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

let norm_extract_common_one_view cprog cviews vdecl=
  let pr1 = Cprinter.string_of_view_decl in
  Debug.no_1 "norm_extract_common_one_view" pr1 (pr_list_ln pr1)
      (fun _ -> norm_extract_common_one_view_x cprog cviews vdecl) vdecl

let norm_extract_common cprog cviews sel_vns=
  let rec process_helper rem_vs done_vs=
    match rem_vs with
      | [] -> done_vs
      | vdecl::rest ->
          let n_vdecls =
            if List.exists (fun vn -> String.compare vn vdecl.Cast.view_name = 0) sel_vns then
              norm_extract_common_one_view cprog (done_vs@rest) vdecl
            else [vdecl]
          in
          process_helper rest (done_vs@n_vdecls)
  in
  process_helper cviews []


(*****************************************************************)
   (********END EXTRACT common pattern **********)
(*****************************************************************)
let cont_para_analysis_view cprog vdef other_vds=
  let process_branch vname args f=
    let _, vns, _ = CF.get_hp_rel_formula f in
    if vns = [] then args else
      let ( _,mix_f,_,_,_) = CF.split_components f in
      let eqs = (MCP.ptr_equations_without_null mix_f) in
      let rec_vns, other_vns = List.partition (fun vn -> String.compare vn.CF.h_formula_view_name vname = 0) vns in
      (*cont paras are para not changed, just forwarded*)
      let cont_paras = List.fold_left (fun cur_cont_paras vn ->
          let closed_rec_args = CF.find_close vn.CF.h_formula_view_arguments eqs in
          CP.intersect_svl cur_cont_paras closed_rec_args
      ) args rec_vns
      in
      (* process other_vns*)
      try
        let cont_paras1 = List.fold_left (fun cur_cont_paras vn ->
            let cont_args = Cast.look_up_cont_args vn.CF.h_formula_view_arguments vn.CF.h_formula_view_name other_vds in
            let closed_rec_args = CF.find_close cont_args eqs in
            CP.intersect_svl cur_cont_paras closed_rec_args
        ) cont_paras other_vns
        in
        cont_paras1
      with Not_found -> []
  in
  let vname = vdef.Cast.view_name in
  let args = vdef.Cast.view_vars in
  let cont_paras = List.fold_left (fun cur_cont_paras (f,_) ->
      let br_cont_paras = process_branch vname args f in
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
            let new_vdef = cont_para_analysis_view cprog vdef done_cviews in
            loop_helper rest (done_cviews@[new_vdef])
  in
  loop_helper cviews []

let cont_para_analysis cprog cviews=
  (* let pr0 = pr_list_ln Cprinter.string_of_view_decl in *)
  let pr1 = pr_pair pr_id !CP.print_svl in
  let pr2 vdef = pr1 (vdef.Cast.view_name, vdef.Cast.view_cont_vars) in
  let pr3 = pr_list pr2 in
  Debug.no_1 "cont_para_analysis" pr3 pr3
      (fun _ -> cont_para_analysis_x cprog cviews) cviews
(*****************************************************************)
   (********END PARA CONTINUATION ANALYSIS **********)
(*****************************************************************)
