open Globals
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer
open Cformula

open Cast

module CP = Cpure


let base_brs_closure_x prog transed_views vname0 args0 n_un_str=
  (*********************************************************************)
  (*********************************************************************)
  let extract_info_rec_brs (f, lbl)=
    let hf, mf, _, _ ,_ =  split_components f in
    let (ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf) =
      Satutil.extract_callee_view_info prog hf mf
    in
    match hvs with
      | [hv] -> if String.compare vname0 hv. h_formula_view_name = 0 then
          let act_args = hv.h_formula_view_node::hv.h_formula_view_arguments in
          ([((ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf), (f,lbl,act_args))],[]) else [],[(f,lbl)]
      | _ ->  [],[(f,lbl)]
  in
  let extract_info_base_brs f=
    let hf, mf, _, _ ,_ =  split_components f in
    let (ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf) = Satutil.extract_callee_view_info prog hf mf in
     (ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf)
  in
  let gen_base_x (b_f, b_lbl) (r_f, r_lbl) =
    let r_f1 = drop_views_formula r_f [vname0] in
    let f1,lb3 = (Cfutil.mkStar_combine_w_quans r_f1 b_f Flow_replace no_pos, r_lbl) in
    (Cfutil.filter_vars_pure args0 f1, r_lbl)
  in
  let gen_base (b_f, b_lbl) (r_f, r_lbl) =
    let pr1 (f,_) = !Cformula.print_formula f in
    Debug.no_2 "gen_base" pr1 pr1 pr1
        (fun _ _ -> gen_base_x (b_f, b_lbl) (r_f, r_lbl))
        (b_f, b_lbl) (r_f, r_lbl)
  in
  let rec look_up_consisten_rec_brs rec_brs b_f done_rs=
    match rec_brs with
      | [] -> raise Not_found
      | (c_abs, (c_f,c_lbl,act_args))::rest -> begin
          let sst = List.combine args0 act_args in
          let base_f_inst = subst sst b_f in
          let base_abs = extract_info_base_brs base_f_inst in
          let (ptos, eqs, neqs, cl_eqNulls, cl_neqNulls, hvs , mf) = Satutil.combine_formula_abs false c_abs base_abs in
          if not (Satutil.is_inconsistent transed_views ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf) then
            (c_f,c_lbl,base_f_inst), (done_rs@rest)
          else
            look_up_consisten_rec_brs rest b_f (done_rs@[(c_abs, (c_f,c_lbl,act_args))])
        end
  in
  let rec generate_base_brs base_fs rec_abs base_brs=
    match base_fs with
      | [] -> base_brs
      |  (b_f,b_lbl)::rest -> begin
           try
             let (r_f,r_lbl,substed_b_f), rest_rec = look_up_consisten_rec_brs rec_abs b_f [] in
             let (n_base, n_lbl) = gen_base (substed_b_f,b_lbl) (r_f,r_lbl) in
             generate_base_brs (rest@[(n_base, n_lbl)]) rest_rec ((n_base,n_lbl)::(base_brs))
           with Not_found -> generate_base_brs rest rec_abs base_brs
         end
  in
  (*********************************************************************)
  (*********************************************************************)
  if List.exists (fun a -> not (CP.is_node_typ a)) args0 then n_un_str else
    let base_fs, rec_fs = List.partition (fun (f,_) -> Cfutil.is_empty_heap_f f) n_un_str in
    (* let base_abs = List.map extract_info_base_brs base_fs in *)
    let rec_abs, rem_rec_brs = List.fold_left (fun (r1,r2)  (f, lbl) ->
        let l1,l2 = extract_info_rec_brs (f, lbl) in
        (r1@l1, r2@l2)
    ) ([],[]) rec_fs in
    let gen_base_brs = generate_base_brs base_fs rec_abs [] in
    gen_base_brs@base_fs@rec_fs

let base_brs_closure prog transed_views vname0 args0 n_un_str=
  let pr1 (f,_) = !Cformula.print_formula f in
  let pr2 = pr_list_ln pr1 in
  Debug.no_3 "base_brs_closure" pr_id !CP.print_svl pr2 pr2
      (fun _ _ _ -> base_brs_closure_x prog transed_views vname0 args0 n_un_str)
       vname0 args0 n_un_str

let unfold_nrec_pred_x prog mutrec_vnames transed_views vname0 self_sv0 args0 is_rec n_un_str=
  let all_args0 = (self_sv0::args0) in
  let rec list_combine svl1 svl2 res=
    match svl1,svl2 with
      | sv1::rest1,sv2::rest2 ->
            if CP.eq_spec_var sv1 sv2 then
              list_combine rest1 rest2 res
            else list_combine rest1 rest2 (res@[(sv1,sv2)])
      | [],[] -> res
      | _ -> raise Not_found
  in
  (*******************************************************)
  let unfold_one_nrec_view_x (vnode:h_formula_view)=
  let vname = vnode.h_formula_view_name in
  let act_args = vnode.h_formula_view_node::vnode.h_formula_view_arguments in
  let caller_eqs, act_args1 = Satutil.fresh_dupl_svl act_args [] [] in
  let vdecl = Cast.look_up_view_def_raw 63 transed_views vname in
  let pos = vdecl.Cast.view_pos in
  if vdecl.Cast.view_is_rec || vdecl.C.view_kind != Cast.View_NORM then ([],[]) else
    let self_sv = (* if String.compare vdecl.Cast.view_data_name "" != 0 then *)
      CP.SpecVar (Named vdecl.Cast.view_data_name,self,Unprimed)
    (* else *)
    (*   let p_root = List.hd act_args in *)
    (*   let st = CP.type_of_spec_var p_root in *)
    (*   try *)
    (*     match st with *)
    (*       | Named tname -> *)
    (*             if String.compare tname "" != 0 then *)
    (*               CP.SpecVar (st,self,Unprimed) *)
    (*             else raise Not_found *)
    (*       | _ -> raise Not_found *)
    (*   with _ -> *)
    (*       Cvutil.find_self_sv vdecl.Cast.view_un_struc_formula *)
    in
    let all_vars = (self_sv::vdecl.Cast.view_vars) in
    let sst = list_combine all_vars act_args1 [] in
    let fs = List.map (fun (f, lb) -> (CF.subst sst f,lb)) vdecl.Cast.view_un_struc_unfolded_formula in
    (*base case should be the first*)
    let base_fs, rec_fs = List.partition (fun (f,_) -> Cfutil.is_empty_heap_f f) fs in
    let fs1 = base_fs@rec_fs in
    let fs2 = match caller_eqs with
      | [] -> fs1
      | (sv11,sv12)::rest ->
            let p = List.fold_left (fun p (svi1,svi2) ->
                CP.mkAnd p (CP.mkPtrEqn svi1 svi2 no_pos) no_pos
            ) (CP.mkPtrEqn sv11 sv12 no_pos) rest
            in
            let mf = (MCP.mix_of_pure p) in
            List.map (fun (f,lb) -> (mkAnd_pure f mf pos, lb)) fs1
    in
    (* let fs3 = List.map (fun (f,lb) -> *)
    (*     let f0a = elim_exists f in *)
    (*     let quans,f0b = split_quantifiers f0a in *)
    (*     let fr_quans = CP.fresh_spec_vars quans in *)
    (*     let f2 = subst (List.combine quans fr_quans) f0b in *)
    (*     (f2,lb) *)
    (* ) (fs2) *)
    (* in *)
    fs2, [vname]
  in
  let unfold_one_nrec_view (vnode:h_formula_view)=
    let pr1 vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
    let pr2 (f,_) =  Cprinter.prtt_string_of_formula f in
    Debug.no_1 "unfold_one_nrec_view" pr1 (pr_pair (pr_list_ln pr2) (pr_list pr_id))
        (fun _ -> unfold_one_nrec_view_x vnode) vnode
  in
  (*****************remove redudant*********************)
  let rec find_first_eq p ps res=
    match ps with
      | [] -> false,res
      | p1::rest1 -> if CP.equalFormula p p1 then
          true,res@rest1
        else find_first_eq p rest1 (res@[p1])
  in
  let rec eq_pure_ps ps ps0=
    match ps with
      | [] -> true
      | p::rest ->
            let is_found, rest0 = find_first_eq p ps0 [] in
            if not is_found then false
            else eq_pure_ps rest rest0
  in
  let rec check_dup_x ps acc_pure_brs=
    match acc_pure_brs with
      | [] -> false
      | ps1:: rest -> if eq_pure_ps ps1 ps then true else
           check_dup_x ps rest
  in
  let check_dup ps acc_pure_brs=
    let pr1 = pr_list !CP.print_formula in
    Debug.no_2 "check_dup" pr1 (pr_list_ln pr1) string_of_bool
        (fun _ _ ->  check_dup_x ps acc_pure_brs)
        ps acc_pure_brs
  in
  (*****************remove redudant*********************)
  (* let rec unfold ls_brs unfolding_fs non_check_sat res= *)
  (*   match ls_brs with *)
  (*     | [unfolded_vn_brs] -> *)
  (*           (\* unfold last view. remove redundant*\) *)
            
  (*     | unfolded_vn_brs::rest -> *)
  (*           (\* unfold *\) *)
  (*     | [] -> res *)
  (* in *)
  (*****************************************)
  let unfold_one (f0, lb)=
    let f = elim_exists f0 in
    let _ = DD.ninfo_hprint (add_str "f" Cprinter.prtt_string_of_formula) f no_pos in
    let base_quans, f1 = split_quantifiers f in
    let vns = get_views f1 in
    let vns1 = List.filter (fun vn ->
        (String.compare vname0 vn.h_formula_view_name!=0) &&
            List.for_all (fun mutrec_v -> String.compare mutrec_v vn.h_formula_view_name!=0) mutrec_vnames
    ) vns in
    if vns1 = [] then [(f0,lb)] else
      (* unfold non_rec views*)
      let ls_brs, to_unfold_vnames = List.fold_left (fun (acc_unfolded_brs, acc_vnames) vn ->
          let unfolded_brs, unfolded_vnames = unfold_one_nrec_view vn in
          if unfolded_vnames = [] then (acc_unfolded_brs, acc_vnames) else
          (acc_unfolded_brs@[unfolded_brs],acc_vnames@unfolded_vnames)
      ) ([],[]) vns1 in
      let non_check_sat = List.length vns1 = 1 in
      (* drop to_unfold_v_names of f *)
      let f1 = drop_views_formula f to_unfold_vnames in
      (* combine *)
      let new_brs = List.fold_left (fun (r) unfolded_vn_brs ->
          let _ = Debug.ninfo_hprint (add_str  "***1***" pr_id) "\n" no_pos in
          let fs_one_view,_ = List.fold_left (fun (outer_acc,outer_base_brs) (f,lb2) ->
              (*filter branch that consistent*)
              let unfolded_vn_brs1 = if non_check_sat then unfolded_vn_brs
              else
                Satutil.filter_consistent all_args0 f unfolded_vn_brs
              in
              let new_cmbs,n_inner_base_brs = List.fold_left (fun (inner_r,inner_base_brs) (unfolded_vn_br, lb_br) ->
                  let _ = Debug.ninfo_hprint (add_str  "unfolding" !print_formula) f no_pos in
                  let _ = Debug.ninfo_hprint (add_str  "br" !print_formula) unfolded_vn_br no_pos in
                  let f1,lb3 = (Cfutil.mkStar_combine_w_quans f unfolded_vn_br Flow_replace no_pos, lb2) in
                   let is_dup,pure_br_ps= if is_rec || non_check_sat then
                    false,inner_base_brs
                   else
                     let h,mf,_,_,_ = split_components f1 in
                    if h=HEmp then
                       let p = CP.filter_var (MCP.pure_of_mix mf) all_args0 in
                       let ps = CP.remove_redundant_helper2 (CP.list_of_conjs p) [] in
                       let is_dup = check_dup ps inner_base_brs in
                      if not is_dup then is_dup, inner_base_brs@[ps]
                      else is_dup, inner_base_brs
                    else false,inner_base_brs
                   in
                   if is_dup then inner_r, pure_br_ps else
                     let f2 = add_quantifiers base_quans f1 in
                     let _ = Debug.ninfo_hprint (add_str  "f2" !print_formula) f2 no_pos in
                     let _ = Debug.ninfo_hprint (add_str  "***3***" pr_id) "\n" no_pos in
                     (inner_r@[(f2,lb3)], pure_br_ps)
              ) ([],outer_base_brs) unfolded_vn_brs1 in
              (* let new_cmbs1 = List.filter ( fun (f,_) -> Satutil.is_consitent_ptrs prog f) new_cmbs in *)
              outer_acc@new_cmbs,n_inner_base_brs
          ) ([],[]) r in
          fs_one_view
      ) ([(f1, lb)]) ls_brs in
      (* let new_brs1 = List.map (fun (f,lb) -> (elim_exists f,lb)) new_brs in *)
      (* let arg_ids = (self::(List.map CP.name_of_spec_var args0)) in *)
      (* Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) -> let is_eq,_ = Checkeq.checkeq_formulas arg_ids f1 f2 in is_eq) *) new_brs
  in
  (*******************************************************)
  (*************************INTERNAL**************************)
  (*******************************************************)
  let new_brs = List.fold_left (fun r br -> r@(unfold_one br)) [] n_un_str in
  if is_rec && !Globals.pred_ext_base then
    let n_brs1 = base_brs_closure prog transed_views vname0 all_args0 new_brs in
    (* base_brs_closure prog transed_views vname0 all_args0 n_brs1 *)
    n_brs1
  else new_brs

let unfold_nrec_pred prog mutrec_vnames transed_views vname0 self_sv args0 is_rec n_un_str=
  let pr1 (f,_) = !Cformula.print_formula f in
  Debug.no_3 "unfold_nrec_pred" (pr_list pr_id) pr_id (pr_list_ln pr1) (pr_list_ln pr1)
      (fun _ _ _ -> unfold_nrec_pred_x prog mutrec_vnames transed_views vname0 self_sv args0 is_rec n_un_str)
      mutrec_vnames vname0 n_un_str



