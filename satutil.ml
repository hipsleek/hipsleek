open VarGen

open Globals
open Others
open Gen

open Cformula
module CP = Cpure

let is_sat_pure_fnc f = (Tpdispatcher.is_sat_sub_no 20 f (ref 0))

let simplify_pure f = Tpdispatcher.simplify_raw f

let rec fresh_dupl_svl svl res new_svl=
  match svl with
    | [] -> res,new_svl
    | sv::rest -> begin
        if CP.mem_svl sv rest then
          let fr_sv = CP.fresh_spec_var sv in
          fresh_dupl_svl rest (res@[(fr_sv,sv)]) (new_svl@[fr_sv])
        else fresh_dupl_svl rest res (new_svl@[sv])
      end

let find_close_eq a eq2=
  if CP.EMapSV.is_empty a then eq2 else
    let aset2 = CP.EMapSV.build_eset eq2 in
    let aset11 = CP.EMapSV.merge_eset a aset2 in
    CP.EMapSV.get_equiv aset11

let rec find_close_neq_x (a:CP.EMapSV.emap) neqs res=
  if CP.EMapSV.is_empty a then neqs else
  match neqs with
    | [] -> Gen.BList.remove_dups_eq (fun (sv11,sv12) (sv21,sv22) -> CP.eq_spec_var sv11 sv21 && CP.eq_spec_var sv12 sv22) res
    | (sv1,sv2)::rest ->
          let cl_svl1 = CP.EMapSV.find_equiv_all_new sv1 a in
          let cl_svl2 = CP.EMapSV.find_equiv_all_new sv2 a in
          let n_res =res@(List.fold_left (fun r sv1 -> r@(List.map (fun sv2 -> (sv1,sv2) ) cl_svl2)) [] cl_svl1) in
          find_close_neq_x a rest n_res

let find_close_neq (a:CP.EMapSV.emap) neqs res=
  let pr1 =pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "find_close_neq" CP.string_of_var_eset pr1 pr1
      (fun _ _ -> find_close_neq_x (a:CP.EMapSV.emap) neqs res) a neqs

let find_closure_svl a svl=
  if CP.EMapSV.is_empty a then svl else
    CP.find_eq_closure a svl


let rec poss_pair_of_list svl res=
  match svl with
    | sv1::rest -> let prs = List.map (fun sv2 -> (sv1,sv2)) rest in
      poss_pair_of_list rest (res@prs)
    | [] -> res

let is_inconsistent_x cviews ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf=
  let rec is_intersect ls1 ls2 cmp_fn=
    match ls1 with
      | [] -> false
      | sv1::rest -> if Gen.BList.mem_eq cmp_fn sv1 ls2 then true else
          is_intersect rest ls2 cmp_fn
  in
  let pr_sv_cmp (sv11,sv12) (sv21,sv22) = ((CP.eq_spec_var sv11 sv21) && (CP.eq_spec_var sv12 sv22)) ||
    ((CP.eq_spec_var sv11 sv22) && (CP.eq_spec_var sv12 sv21))
  in
  let (neqs, cl_neqNulls)= if ptos=[] then (neqs, cl_neqNulls) else
    let neqs2 = poss_pair_of_list ptos [] in
    let a = CP.EMapSV.build_eset eqs in
    let cl_neqNulls1 = find_closure_svl a ptos in
    let neqs3 = find_close_neq a (neqs2) [] in
    let neqs = neqs3@neqs in
    let cl_neqNulls = cl_neqNulls@cl_neqNulls1 in
    (neqs, cl_neqNulls)
  in
  (* List.exists (fun (sv1,sv2) -> CP.mem_svl sv1 ptos && CP.mem_svl sv2 ptos) eqs || *)
  (*     is_intersect ptos cl_eqNulls CP.eq_spec_var || *)
  is_intersect eqs neqs pr_sv_cmp ||
      is_intersect cl_eqNulls cl_neqNulls CP.eq_spec_var

let is_inconsistent cviews ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_5 "is_inconsistent" pr1 pr2 pr2 pr1 pr1 string_of_bool
      (fun _ _ _ _ _ -> is_inconsistent_x cviews ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf)
     ptos eqs neqs cl_eqNulls cl_neqNulls

let is_inconsistent_general_x cviews ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf=
  (*****************************)
  let rec gen_pure_addrs ptos1 n res=
    match ptos1 with
      | [] -> res
      | sv::rest ->
            let addr_p = CP.mkIConst n no_pos in
            let eq_p = CP.mkEqExp (CP.mkVarNull sv no_pos) addr_p no_pos in
            gen_pure_addrs rest (n+1) (res@[eq_p])
  in
  let get_inv vnode=
    Cast.look_up_view_inv_simp cviews (vnode.h_formula_view_node::vnode.h_formula_view_arguments)
    vnode.h_formula_view_name Fixcalc.compute_inv
  in
  (*****************************)
  let p_addrs = gen_pure_addrs ptos 1 [] in
  let p_eqs = List.map (fun (sv1, sv2) -> CP.mkPtrEqn sv1 sv2 no_pos) eqs in
  let p_neqs = List.map (fun (sv1, sv2) -> CP.mkPtrNeqEqn sv1 sv2 no_pos) neqs in
  let zero = CP.mkIConst 0 no_pos in
  let p_eqNulls =  List.map (fun sv -> CP.mkEqExp (CP.mkVarNull sv no_pos) zero no_pos) cl_eqNulls in
  let p_neqNulls =  List.map (fun sv -> CP.mkNeqExp (CP.mkVarNull sv no_pos) zero no_pos) cl_neqNulls in
  let vinvs = List.map get_inv hvs in
  let p_total = List.fold_left (fun p1 p2 ->
      CP.mkAnd p1 p2 no_pos
  ) (MCP.pure_of_mix mf) (p_addrs@p_eqs@p_neqs@p_eqNulls@p_neqNulls@vinvs) in
  (* let () = print_endline (!CP.print_formula p_total) in *)
  let r = not(is_sat_pure_fnc p_total) in
  (* let () = print_endline ("r=" ^ (string_of_bool r)) in *)
  r

(* let sat_count = ref (0: int) *)

let is_inconsistent_general transed_views ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf=
  (* let () = sat_count := !sat_count + 1 in *)
  (* let () = print_endline (string_of_int !sat_count) in *)
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 vnode = Cprinter.prtt_string_of_h_formula (ViewNode vnode) in
  Debug.no_7 "is_inconsistent_general" pr1 pr2 pr2 pr1 pr1 (pr_list pr3) (Cprinter.string_of_mix_formula) string_of_bool
      (fun _ _ _ _ _ _ _ -> is_inconsistent_general_x transed_views ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf)
     ptos eqs neqs cl_eqNulls cl_neqNulls hvs mf

let extract_callee_view_info_x prog h mf=
  (*******************)
  let extract_pto vn= [(* vn.h_formula_view_node *)]
  in
  (*******************)
  (* local info *)
  (* let h,mf, _, _, _ = split_components f in *)
  let p = (MCP.pure_of_mix mf) in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let neqs = CP.get_neqs_new p in
  let eqNulls = (MCP.get_null_ptrs mf) in
  let neqNull_svl = CP.get_neq_null_svl p in
  let hns,hvs,_=Cformula.get_hp_rel_h_formula h in
  let ptos0 = List.map (fun hn -> hn.h_formula_data_node) hns in
  (* let ptos1 = List.fold_left (fun r vn -> r@(extract_pto vn)) [] hvs in *)
  (* let ptos = ptos0@ptos1 in *)
  (* let neqs2 = poss_pair_of_list ptos [] in *)
  let neqs3, cl_eqNulls, cl_neqNulls = if eqs=[] then (neqs, eqNulls, (neqNull_svl@ptos0)) else
  let a = CP.EMapSV.build_eset eqs in
  let cl_eqNulls = find_closure_svl a eqNulls in
  let cl_neqNulls = find_closure_svl a (neqNull_svl@ptos0) in
  let neqs3 = find_close_neq a (neqs) [] in
  ((* find_closure_svl a ptos0, *) neqs3, cl_eqNulls, cl_neqNulls)
  in
  (ptos0, eqs, neqs3, cl_eqNulls, CP.remove_dups_svl cl_neqNulls, hvs,mf)

let extract_callee_view_info prog hf mf=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 hv = (!print_h_formula (ViewNode hv)) in
  Debug.no_1 "sat.extract_callee_view_info" !print_h_formula (pr_hepta pr1 pr2 pr2 pr1 pr1 (pr_list pr3)
      Cprinter.string_of_mix_formula)
      (fun _ -> extract_callee_view_info_x prog hf mf) hf

let combine_formula_abs is_shape_only (ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1)
                  (ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2)=
  let ptos = ptos1@ptos2 in
  let eqs = eqs1@eqs2 in
  let neqs = neqs1@neqs2 in
  let null_svl = null_svl1@null_svl2 in
  let neqNull_svl = neqNull_svl1@neqNull_svl2 in
  let hvs = hvs1@hvs2 in
  (* let p = CP.mkAnd (MCP.pure_of_mix mf1) (MCP.pure_of_mix mf2) no_pos in *)
  (* let p1 = if is_shape_only then *)
  (*   p *)
  (* else *)
  (*   simplify_pure p *)
  (* in *)
  (* let mf = MCP.mix_of_pure p1 in *)
  let mf = Mcpure.merge_mems mf1 mf2 false in
  let cl_null_svl, cl_neqNulls, neqs = if eqs1 != [] || eqs2 != [] then
     let a = CP.EMapSV.build_eset eqs in
     let cl_null_svl = find_closure_svl a null_svl in
     let cl_neqNulls = find_closure_svl a ( (neqNull_svl@ptos)) in
     let neqs1 = find_close_neq a (neqs) [] in
     (cl_null_svl, cl_neqNulls, neqs1)
  else (null_svl, neqNull_svl,neqs)
  in
  (ptos, eqs, neqs, cl_null_svl, cl_neqNulls, hvs, mf)


let is_bool_inconsistent mf=
  let p = Mcpure.pure_of_mix mf in
  let b_true_svl,b_false_svl, b_true,b_false = Cpure.extract_bexpr p in
  (b_true=true && b_false=true) || (List.exists (fun sv ->  Cpure.mem_svl sv b_true_svl) b_false_svl)

(*
This function is used for heap + (dis)eq constraints only.
Do NOT use Z3 for sat check
*)
let form_red_eq_x prog check_unsat f=
  let hf, mf, _, _ ,_,_ =  split_components f in
  if MCP.isConstMFalse mf || is_bool_inconsistent mf then (true, [], [],[],[],[], [], mf) else
  let (ptos, eqs, neqs, null_svl, neqNull_svl, hvs,_) = extract_callee_view_info prog hf mf in
  let is_unsat = (* if check_unsat then *)
    is_inconsistent prog.Cast.prog_view_decls ptos eqs neqs null_svl neqNull_svl hvs mf
  (* else false *)
  in
  (is_unsat,ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf)

let form_red_eq prog check_unsat f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 (a1,a2,a3,a4,a5,a6,a7,a8) =
    (pr_hepta (pr_pair string_of_bool !CP.print_svl) pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) pr1b)
  ((a1,a2),a3,a4,a5,a6,a7,a8) in
  Debug.no_1 "form_red_eq" pr1 pr3
      (fun _ -> form_red_eq_x prog check_unsat f) f

(*
This function is used for general fragment of SL.
Do use Z3 for sat check
*)
let form_red_general_x prog check_unsat f=
  let hf, mf, _, _ ,_,_ =  split_components f in
  if MCP.isConstMFalse mf || is_bool_inconsistent mf then (true, [], [], [], [], [],[], mf) else
  let (ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf) = extract_callee_view_info prog hf mf in
  let is_unsat = is_inconsistent prog.Cast.prog_view_decls ptos eqs neqs null_svl neqNull_svl hvs mf in
  let is_unsat1 = if is_unsat then true else
    if check_unsat then
    is_inconsistent_general prog.Cast.prog_view_decls ptos eqs neqs null_svl neqNull_svl hvs mf
    else false
  in
  (is_unsat1,ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf
      (* MCP.mix_of_pure (Cputil.arith_simp (MCP.pure_of_mix mf)) *)
  )

let form_red_general prog check_unsat f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 (a1,a2,a3,a4,a5,a6,a7,a8) =
    (pr_hepta (pr_pair string_of_bool !CP.print_svl) pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) pr1b)
  ((a1,a2),a3,a4,a5,a6,a7,a8) in
  Debug.no_1 "form_red_general" pr1 pr3
      (fun _ -> form_red_general_x prog check_unsat f) f
(*****************************************)
(*****************************************)

let is_consitent_ptrs prog f=
  let (is_unsat,_, _, _, _, _, _, _) = 
    (* if is_only_eq then form_red_eq prog f else form_red_all prog f *)
    form_red_eq prog true f
  in
  not is_unsat


let filter_consistent_x args f0 unfolded_vn_brs=
  let helper1 mf=
    let neqNull_svl = CP.get_neq_null_svl (MCP.pure_of_mix mf) in
    let null_ptrs = MCP.get_null_ptrs mf in
    (null_ptrs, neqNull_svl)
  in
  let rec helper f=
    match f with
      | Base fb ->
           helper1 (fb.formula_base_pure)
      | Exists fe ->
          helper1 (fe.formula_exists_pure)
      | Or orf -> report_error no_pos "satutil.filter_consistent"
  in
  let is_consistent null_svl neqNull_svl f2=
    let null_svl2, neqNull_svl2 = helper f2 in
    List.for_all (fun sv -> not (CP.mem_svl sv neqNull_svl2)) null_svl &&  List.for_all (fun sv -> not (CP.mem_svl sv null_svl2)) neqNull_svl
  in
  let null_svl, neqNull_svl = helper f0 in
  (* let null_svl1 = CP.intersect_svl null_svl args in *)
  (* let neqNull_svl1 = CP.intersect_svl neqNull_svl args in *)
  if null_svl=[] && neqNull_svl =[] then unfolded_vn_brs else
    List.filter (fun (f,_) -> is_consistent null_svl neqNull_svl f) unfolded_vn_brs

let filter_consistent args f0 unfolded_vn_brs=
  let pr1 = !print_formula in
  let pr2 (f,_) = pr1 f in
  Debug.no_2 "filter_consistent" pr1 (pr_list_ln pr2) (pr_list_ln pr2)
      (fun _ _ -> filter_consistent_x args f0 unfolded_vn_brs)
      f0 unfolded_vn_brs

let checkeq_formula (hvs1,mf1) (hvs2,mf2)=
  match hvs1,hvs2 with
    | [],[] -> CP.equalFormula (MCP.pure_of_mix mf1) (MCP.pure_of_mix mf2)
    | [hv1],[hv2] ->
          if string_eq hv1.h_formula_view_name hv2.h_formula_view_name then
            let sst = List.combine (hv1.h_formula_view_node::hv1.h_formula_view_arguments) (hv2.h_formula_view_node::hv2.h_formula_view_arguments) in
            let p1 = (MCP.pure_of_mix mf1) in
            let p2 = (MCP.pure_of_mix mf2) in
            CP.equalFormula (CP.subst sst p1) p2
          else false
    | _ -> false

let rec checkeq_formula_list_x fs1 fs2=
  let rec look_up_f ((_, _, _, _, _, hvs,mf) as f) fs fs1=
    match fs with
      | [] -> (false, fs1)
      | ((_, _, _, _, _, hvs1,mf1) as f1)::fss -> if (checkeq_formula  (hvs,mf) (hvs1,mf)) then
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
                checkeq_formula_list fss1 fss2
              else false
          end
  else false

and checkeq_formula_list fs1 fs2=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 hv = (!print_h_formula (ViewNode hv)) in
  let pr4 = pr_list_ln (pr_hepta pr1 pr2 pr2 pr1 pr1 (pr_list pr3)
      Cprinter.string_of_mix_formula) in
  Debug.no_2 "satutil.checkeq_formula_list" pr4 pr4 string_of_bool
      (fun _ _ -> checkeq_formula_list_x fs1 fs2) fs1 fs2
