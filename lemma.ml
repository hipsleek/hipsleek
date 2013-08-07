open Globals
open Wrapper
open Gen
open Others
open Label_only

module AS = Astsimp
module C  = Cast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module H  = Hashtbl
module I  = Iast
module SC = Sleekcore

let generate_ilemma iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody=
  (*check entailment*)
  let (res,_,_) =  if coer_type = I.Left then
    SC.sleek_entail_check [] cprog [(chead,cbody)] lhs (CF.struc_formula_of_formula rhs no_pos)
  else SC.sleek_entail_check [] cprog [(cbody,chead)] rhs (CF.struc_formula_of_formula lhs no_pos)
  in
  if res then
    (*generate ilemma*)
    let ilemma = { I.coercion_type = coer_type;
    I.coercion_exact = false;
    I.coercion_name = (fresh_any_name lemma_n);
    I.coercion_head = (IF.subst_stub_flow IF.top_flow ihead);
    I.coercion_body = (IF.subst_stub_flow IF.top_flow ibody);
    I.coercion_proof = I.Return ({ I.exp_return_val = None;
    I.exp_return_path_id = None ;
    I.exp_return_pos = no_pos })}
    in
    (*transfrom ilemma to clemma*)
    let ldef = AS.case_normalize_coerc iprog ilemma in
    let l2r, r2l = AS.trans_one_coercion iprog ldef in
    l2r, r2l
  else
    [],[]


let final_inst_analysis_view_x cprog vdef=
  let process_branch (r1,r2)vname args f=
    let hds, vns, hdrels = CF.get_hp_rel_formula f in
    if vns <> [] then (r1,r2) else
      let self_hds = List.filter (fun hd ->
          CP.is_self_spec_var hd.CF.h_formula_data_node
      ) hds in
      if self_hds = [] then
        let ( _,mix_f,_,_,_) = CF.split_components f in
        let eqNulls = CP.remove_dups_svl ((MCP.get_null_ptrs mix_f) ) in
        let self_eqNulls = List.filter (CP.is_self_spec_var) eqNulls in
        ([], self_eqNulls)
      else ( self_hds, [])
  in
  let vname = vdef.Cast.view_name in
  let args = vdef.Cast.view_vars in
  let s_hds, s_null = List.fold_left (fun (is_node, is_null) (f,_) ->
      process_branch (is_node, is_null) vname args f
  ) ([],[]) vdef.Cast.view_un_struc_formula
  in
  (s_hds, s_null)

let final_inst_analysis_view cprog vdef=
  let pr1 = Cprinter.string_of_view_decl in
  let pr2 hd= Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  Debug.ho_1 "final_inst_analysis_view" pr1 (pr_pair (pr_list pr2) !CP.print_svl)
      (fun _ -> final_inst_analysis_view_x cprog vdef) vdef

let subst_cont vn cont_args f ihf chf self_hns self_null pos=
  let rec subst_helper ss f0=
    match f0 with
      | CF.Base _ -> let _, vns, _ = CF.get_hp_rel_formula f0 in
        if (* List.exists (fun hv -> String.compare hv.CF.h_formula_view_name vn = 0) vns *) vns<> [] then
          f0
        else CF.subst ss f0
      | CF.Exists _ ->
            let qvars, base_f1 = CF.split_quantifiers f0 in
            let nf = subst_helper ss base_f1 in
            CF.add_quantifiers qvars nf
      | CF.Or orf ->
            CF.Or {orf with CF.formula_or_f1 = subst_helper ss orf.CF.formula_or_f1;
                CF.formula_or_f2 = subst_helper ss orf.CF.formula_or_f2;
            }
  in
  if self_null <> [] then
    let cont = match cont_args with
      | [a] -> a
      | _ -> report_error no_pos "Lemma.subst_cont: to handle"
    in
    let null_sv = CP.SpecVar (CP.type_of_spec_var cont, null_name, Unprimed) in
    let ss = [(cont, null_sv)] in
    let n = IP.Null no_pos in
    let ip = IP.mkEqExp (IP.Var (((CP.name_of_spec_var cont, CP.primed_of_spec_var cont)), no_pos)) (IP.Null no_pos) no_pos in
    let cp = CP.mkNull cont pos in
    (subst_helper ss f, IF.mkBase ihf ip IF.n_flow [] pos,
    CF.mkBase chf (MCP.mix_of_pure cp) CF.TypeTrue (CF.mkNormalFlow()) [] pos)
  else if self_hns <> [] then
    let _ = report_warning no_pos ("Lemma.subst_cont: to handle") in
    (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)
  else (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)

(*if two views are equiv (subsume), generate an equiv (left/right) lemma*)
let check_view_subsume iprog cprog view1 view2 need_cont_ana=
  (*todo, subst parameters if any*)
  (* let hn_c_trans (sv1, sv2) hf = match hf with *)
  (*   | CF.ViewNode vn -> *)
  (*         let nhf = *)
  (*           if String.compare sv1 vn.CF.h_formula_view_name = 0 then *)
  (*             CF.ViewNode {vn with CF.h_formula_view_name = sv2 } *)
  (*           else hf *)
  (*         in *)
  (*         nhf *)
  (*   | _ -> hf *)
  (* in *)
  let v_f1 = CF.formula_of_disjuncts (List.map fst view1.C.view_un_struc_formula) in
  let v_f2 = CF.formula_of_disjuncts (List.map fst view2.C.view_un_struc_formula) in
  let v_f11 = (* CF.formula_trans_heap_node (hn_c_trans (view1.C.view_name, view2.C.view_name)) *) v_f1 in
  let pos1 = (CF.pos_of_formula v_f1) in
  let pos2 = (CF.pos_of_formula v_f2) in
  let ihf1 = IF.mkHeapNode (self, Unprimed) (view1.C.view_name)
    0  false  (IF.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view1.C.view_vars) []  None pos1 in
  let chf1 = CF.mkViewNode (CP.SpecVar (Named view1.C.view_name,self, Unprimed)) view1.C.view_name
    view1.C.view_vars no_pos in
  let ihf2 = IF.mkHeapNode (self, Unprimed) (view2.C.view_name)
    0  false (IF.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view2.C.view_vars) [] None pos2 in
  let chf2 = CF.mkViewNode (CP.SpecVar (Named view2.C.view_name,self, Unprimed)) view2.C.view_name
    view1.C.view_vars no_pos in
  let v_f1, v_f2, iform_hf1, cform_hf1, iform_hf2, cform_hf2=
    if not need_cont_ana then
      (v_f11, v_f2, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1,
      IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
    else
      if List.length view1.C.view_vars > List.length view2.C.view_vars && view1.C.view_cont_vars != [] then
        let self_hds, self_null = final_inst_analysis_view cprog view2 in
        let v_f12, ihf_12, cform_chf12 = subst_cont view1.C.view_name view1.C.view_cont_vars
          v_f11 ihf1 chf1 self_hds self_null pos1 in
        (v_f12, v_f2, ihf_12, cform_chf12, IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
      else if List.length view1.C.view_vars < List.length view2.C.view_vars && view2.C.view_cont_vars != [] then
        let self_hds, self_null = final_inst_analysis_view cprog view1 in
        let v_f22, ihf_22, cform_chf22 = subst_cont view2.C.view_name view2.C.view_cont_vars v_f2 ihf2 chf2 self_hds self_null pos2 in
        (v_f11, v_f22, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1, ihf_22, cform_chf22)
      else (v_f11, v_f2, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1,
      IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
  in
  let lemma_n = view1.C.view_name ^"_"^ view2.C.view_name in
  let l2r1, r2l1 = generate_ilemma iprog cprog lemma_n I.Left v_f1 v_f2
    iform_hf1 cform_hf1 iform_hf2 cform_hf2 in
  let l2r2, r2l2 = generate_ilemma iprog cprog lemma_n I.Right v_f1 v_f2
    iform_hf1 cform_hf1 iform_hf2 cform_hf2 in
  (l2r1@l2r2, r2l1@r2l2)

let generate_lemma_4_views_x iprog cprog=
  let rec helper views l_lem r_lem=
    match views with
      | [] -> (l_lem,r_lem)
      | [v] -> (l_lem,r_lem)
      | v::rest ->
            let l,r = List.fold_left (fun (r1,r2) v1 ->
                if List.length v.C.view_vars = List.length v1.C.view_vars then
                  let l, r = check_view_subsume iprog cprog v v1 false in
                  (r1@l,r2@r)
                else if (List.length v.C.view_vars > List.length v1.C.view_vars &&
                    List.length v.C.view_vars = List.length v1.C.view_vars + List.length v.C.view_cont_vars) ||
                  (List.length v.C.view_vars < List.length v1.C.view_vars &&
                      List.length v1.C.view_vars = List.length v.C.view_vars + List.length v1.C.view_cont_vars)
                then
                  (*cont paras + final inst analysis*)
                  let _ = report_warning no_pos ("cont paras + final inst analysis " ^ (v.C.view_name) ^ " ..." ^
                      v1.C.view_name) in
                  let l, r = check_view_subsume iprog cprog v v1 true in
                  (r1@l,r2@r)
                else
                  (r1,r2)
            ) ([],[]) rest
            in
            helper rest (l_lem@l) (r_lem@r)
  in
  let l2r, r2l = helper cprog.C.prog_view_decls [] [] in
  (* let _ = cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions in *)
  (* let _ = cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions in *)
  (l2r,r2l)

let generate_lemma_4_views iprog cprog=
  let pr1 cp = (pr_list_ln Cprinter.string_of_view_decl_short) cp.C.prog_view_decls in
  let pr2 = pr_list_ln Cprinter.string_of_coerc_short in
  Debug.no_1 "generate_lemma_4_views" pr1 (pr_pair pr2 pr2)
      (fun _ -> generate_lemma_4_views_x iprog cprog)
      cprog
