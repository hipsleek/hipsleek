#include "xdebug.cppo"
open VarGen
open Globals
open Wrapper
open Exc.GTable
open Gen
open Others
open Label_only

(* module AS = Astsimp *)
module C  = Cast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module H  = Hashtbl
module I  = Iast
module TP = Tpdispatcher
(* module SC = Sleekcore *)
(* module LP = Lemproving *)
(* module SAO = Saout *)
(* module FP = Fixpoint *)

let infer_shapes = ref (fun (iprog: I.prog_decl) (cprog: C.prog_decl) (proc_name: ident)
                         (hp_constrs: CF.hprel list) (sel_hp_rels: CP.spec_var list) (sel_post_hp_rels: CP.spec_var list)
                         (hp_rel_unkmap: ((CP.spec_var * int list) * CP.xpure_view) list)
                         (unk_hpargs: (CP.spec_var * CP.spec_var list) list)
                         (link_hpargs: (int list * (Cformula.CP.spec_var * Cformula.CP.spec_var list)) list)
                         (need_preprocess: bool) (detect_dang: bool) (iflow: nflow) -> let a = ([] : CF.hprel list) in
                         let b = ([] : CF.hp_rel_def list) in
                         let c = ([] : CP.spec_var list) in
                         (a, b, c)
                       )

let generate_lemma_helper iprog cprog lemma_name coer_type ihps ihead ibody=
  (*generate ilemma*)
  let ilemma = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN coer_type ihps ihead ibody in
  (*transfrom ilemma to clemma*)
  let ldef = Astsimp.case_normalize_coerc iprog ilemma in
  let l2r, r2l = Astsimp.trans_one_coercion iprog cprog ldef in
  l2r, r2l

let generate_lemma_x iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody
  : (C.coercion_decl list * C.coercion_decl list) =
  (*check entailment*)
  let (res,_,_) = (
    if coer_type = I.Left then
      Sleekcore.sleek_entail_check 4 [] [] cprog [(chead,cbody)] lhs (CF.struc_formula_of_formula rhs no_pos)
    else Sleekcore.sleek_entail_check 5 [] [] cprog [(cbody,chead)] rhs (CF.struc_formula_of_formula lhs no_pos)
  ) in
  if res then
    let l2r, r2l = generate_lemma_helper iprog cprog lemma_n coer_type [] ihead ibody in
    l2r, r2l
  else [],[]

let generate_lemma iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody
  : (C.coercion_decl list * C.coercion_decl list) =
  let pr_out = pr_pair !C.print_coerc_decl_list !C.print_coerc_decl_list in
  let pr_str = idf in
  Debug.no_1 "generate_lemma" pr_str pr_out
    (fun _ -> generate_lemma_x iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody)
    lemma_n

let final_inst_analysis_view_x cprog vdef=
  let process_branch (r1,r2)vname args f=
    let hds, vns, hdrels = CF.get_hp_rel_formula f in
    if vns <> [] then (r1,r2) else
      let self_hds = List.filter (fun hd ->
          CP.is_self_spec_var hd.CF.h_formula_data_node
        ) hds in
      if self_hds = [] then
        let ( _,mix_f,_,_,_,_) = CF.split_components f in
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
  Debug.no_1 "final_inst_analysis_view" pr1 (pr_pair (pr_list pr2) !CP.print_svl)
    (fun _ -> final_inst_analysis_view_x cprog vdef) vdef

let subst_cont vn cont_args f ihf chf self_hns self_null pos=
  let rec subst_helper ss f0=
    match f0 with
    | CF.Base fb -> (* let _, vns, _ = CF.get_hp_rel_formula f0 in *)
      (* if (\* List.exists (fun hv -> String.compare hv.CF.h_formula_view_name vn = 0) vns *\) vns<> [] then *)
      (*   f0 *)
      (* else *)
      (* let nfb = CF.subst_b ss fb in *)
      let np = CP.subst_term ss (MCP.pure_of_mix fb.CF.formula_base_pure) in
      CF.Base {fb with CF.formula_base_pure = MCP.mix_of_pure np}
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
    let null_exp = CP.Null pos in
    let ss = [(cont, null_exp)] in
    (* let n = IP.Null no_pos in *)
    let ip = IP.mkEqExp (IP.Var (((CP.name_of_spec_var cont, CP.primed_of_spec_var cont)), no_pos)) (IP.Null no_pos) no_pos in
    let cp = CP.mkNull cont pos in
    let emp_vps = CvpermUtils.empty_vperm_sets in
    (subst_helper ss f, IF.mkBase ihf ip IvpermUtils.empty_vperm_sets IF.top_flow [] pos,
     CF.mkBase chf (MCP.mix_of_pure cp) emp_vps CF.TypeTrue (CF.mkNormalFlow()) [] pos)
  else if self_hns <> [] then
    let () = report_warning no_pos ("Lemma.subst_cont: to handle") in
    (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)
  else (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)

(*if two views are equiv (subsume), generate an equiv (left/right) lemma*)
let check_view_subsume iprog cprog view1 view2 need_cont_ana=
  let v_f1 = CF.formula_of_disjuncts (List.map fst view1.C.view_un_struc_formula) in
  let v_f2 = CF.formula_of_disjuncts (List.map fst view2.C.view_un_struc_formula) in
  let v_f11 = (* CF.formula_trans_heap_node (hn_c_trans (view1.C.view_name, view2.C.view_name)) *) v_f1 in
  let pos1 = (CF.pos_of_formula v_f1) in
  let pos2 = (CF.pos_of_formula v_f2) in
  let ihf1 = IF.mkHeapNode (self, Unprimed) (view1.C.view_name) [] (* TODO:HO *)
      0  false SPLIT0 (IP.ConstAnn Mutable) false false false None
      (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view1.C.view_vars) []  None pos1 in
  let chf1 = CF.mkViewNode (CP.SpecVar (Named view1.C.view_name,self, Unprimed)) view1.C.view_name
      view1.C.view_vars no_pos in
  let ihf2 = IF.mkHeapNode (self, Unprimed) (view2.C.view_name) [] (* TODO:HO *)
      0  false SPLIT0 (IP.ConstAnn Mutable) false false false None
      (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view2.C.view_vars) [] None pos2 in
  let chf2 = CF.mkViewNode (CP.SpecVar (Named view2.C.view_name,self, Unprimed)) view2.C.view_name
      view2.C.view_vars no_pos in
  let v_f1, v_f2, iform_hf1, cform_hf1, iform_hf2, cform_hf2=
    if not need_cont_ana then
      (v_f11, v_f2, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1,
       IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
    else
    if List.length view1.C.view_vars > List.length view2.C.view_vars && view1.C.view_cont_vars != [] then
      (* let () = print_endline ("xxx1") in *)
      let self_hds, self_null = final_inst_analysis_view cprog view2 in
      let v_f12, ihf_12, cform_chf12 = subst_cont view1.C.view_name view1.C.view_cont_vars
          v_f11 ihf1 chf1 self_hds self_null pos1 in
      (v_f12, v_f2, ihf_12, cform_chf12, IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
    else if List.length view2.C.view_vars > List.length view1.C.view_vars && view2.C.view_cont_vars != [] then
      (* let () = print_endline ("xxx2") in *)
      let self_hds, self_null = final_inst_analysis_view cprog view1 in
      let v_f22, ihf_22, cform_chf22 = subst_cont view2.C.view_name view2.C.view_cont_vars v_f2 ihf2 chf2 self_hds self_null pos2 in
      (v_f11, v_f22, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1, ihf_22, cform_chf22)
    else (v_f11, v_f2, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1,
          IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
  in
  let lemma_n = view1.C.view_name ^"_"^ view2.C.view_name in
  let l2r1, r2l1 = generate_lemma iprog cprog lemma_n I.Left v_f1 v_f2
      iform_hf1 cform_hf1 iform_hf2 cform_hf2 in
  let l2r2, r2l2 = generate_lemma iprog cprog lemma_n I.Right v_f1 v_f2
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
            (* let () = report_warning no_pos ("cont paras + final inst analysis " ^ (v.C.view_name) ^ " ..." ^ *)
            (*     v1.C.view_name) in *)
            let l, r = check_view_subsume iprog cprog v v1 true in
            (r1@l,r2@r)
          else
            (r1,r2)
        ) ([],[]) rest
      in
      helper rest (l_lem@l) (r_lem@r)
  in
  let l2r, r2l = helper cprog.C.prog_view_decls [] [] in
  (* let () = cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions in *)
  (* let () = cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions in *)
  (l2r,r2l)

let generate_lemma_4_views iprog cprog=
  let pr1 cp = (pr_list_ln Cprinter.string_of_view_decl_short) cp.C.prog_view_decls in
  let pr2 = pr_list_ln Cprinter.string_of_coerc_short in
  Debug.no_1 "generate_lemma_4_views" pr1 (pr_pair pr2 pr2)
    (fun _ -> generate_lemma_4_views_x iprog cprog)
    cprog

(* ============================ lemma translation and store update================================= *)
(* Below are methods used for lemma transformation (ilemma->lemma), lemma proving and lemma store update *)


let unfold_body_lemma iprog ldef ulst =
  if !Globals.old_lemma_unfold || ulst==[] then ldef
  else
    try
      let pr = Iprinter.string_of_coerc_decl      in
      let body = ldef.Iast.coercion_body in
      (* WN: collect heap views to see if overlaps with unfold set *)
      let fvars = IF.all_fv ~vartype:Vartypes.var_with_view_only body in
      let () = y_tinfo_hp (add_str "views" (pr_list string_of_primed_ident)) fvars in
      let rs = BList.intersect_eq (fun (v,_) (w,_,_) -> v=w) fvars ulst in
      if rs==[] then ldef
      else
        let cbody = Typeinfer.trans_iformula_to_cformula iprog body in
        let cbody_uf = CF.repl_unfold_formula "" ulst cbody in
        let ibody_uf = !CF.rev_trans_formula cbody_uf in
        let res = { ldef with Iast.coercion_body = ibody_uf } in
        let () = y_tinfo_hp (add_str "ldef" pr) ldef in
        let () = y_tinfo_hp (add_str "res_ldef" pr) res in

        res
    with _ ->
      (* linearize_heap(dup)@14 EXIT ExceptionFailure("malfunction with float out exp: n-1")Occurred! *)
      ldef

let unfold_body_lemma iprog ldef ulst =
  let pr1 = Iprinter.string_of_coerc_decl      in
  let pr2 = (add_str "unfold_lst" (pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula))) in
  Debug.no_2 "lemma_unfold" pr1 pr2 pr1 (fun _ _ -> unfold_body_lemma iprog ldef ulst) ldef ulst

(* ilemma  ----> (left coerc list, right coerc list) *)
let process_one_lemma unfold_flag iprog cprog ldef =
  let pr = Iprinter.string_of_coerc_decl      in
  (* let () = y_tinfo_pp "unfold RHS of lemma" in *)
  let vdefs = Cprog_sleek.get_sorted_view_decls () in
  let ulst = Cast.get_unfold_set vdefs (* set of unfoldable views *) in
  (* type: (Globals.ident * Cast.P.spec_var list * Cformula.formula) list *)
  let ldef = if unfold_flag then x_add unfold_body_lemma iprog ldef ulst else ldef in
  let () = y_tinfo_hp (add_str "unfold_lst" (pr_list (pr_triple pr_id !CP.print_svl !CF.print_formula))) ulst in
  let () = y_tinfo_hp (add_str "unfold_flag" string_of_bool) unfold_flag in
  let () = y_tinfo_hp (add_str "lemma(after unfold)" Iprinter.string_of_coerc_decl) ldef in

  (* let left = List.map (Cast.repl_unfold_lemma ulst) left in *)
  let ldef = Astsimp.case_normalize_coerc iprog ldef in
  let pr = Cprinter.string_of_coerc_decl_list in
  let l2r, r2l = Astsimp.trans_one_coercion iprog cprog ldef in
  (* let () = y_tinfo_hp (add_str "l2r" pr) l2r in *)
  (* let () = y_tinfo_hp (add_str "r2l" pr) r2l in *)
  let l2r = List.concat (List.map (fun c-> Astsimp.coerc_spec cprog c) l2r) in
  let r2l = List.concat (List.map (fun c-> Astsimp.coerc_spec cprog c) r2l) in
  let () = if (!Globals.print_input || !Globals.print_input_all) then
      let () = print_string (Iprinter.string_of_coerc_decl ldef) in
      let () = print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") in
      () else () in
  let () = x_tinfo_pp "lemma : end of process_one_lemma" no_pos in
  (l2r,r2l,ldef.I.coercion_type)


(* ilemma repo ----> (left coerc list, right coerc list, typ, name) *)
let process_one_repo unfold_flag repo iprog cprog =
  List.map (fun ldef ->
      let l2r,r2l,typ = process_one_lemma unfold_flag iprog cprog ldef in
      (l2r,r2l,typ,(ldef.I.coercion_name))
    ) repo

let verify_one_repo lems cprog =
  let res = List.fold_left (fun ((fail_ans,res_so_far) as res) (l2r,r2l,typ,name) ->
      match fail_ans with
      | None ->
        let res = x_add Lemproving.verify_lemma 3 l2r r2l cprog name typ in
        let chk_for_fail =  if !Globals.disable_failure_explaining then CF.isFailCtx else CF.isFailCtx_gen in
        let res_so_far = res::res_so_far in
        let fail = if chk_for_fail res then Some (name^":"^(Cprinter.string_of_coercion_type typ)) else None in
        (fail, res_so_far)
      (* ((if CF.isFailCtx res then Some (name^":"^(Cprinter.string_of_coercion_type typ)) else None), res_so_far) *)
      | Some n ->
        res
    ) (None,[]) lems in
  res

let verify_one_repo lems cprog =
  let pr = pr_list (fun (_, _, _, name) -> name) in
  let pr_out = pr_pair (pr_opt pr_id) (pr_list Cprinter.string_of_list_context) in
  Debug.no_1 "verify_one_repo" pr pr_out
    (fun _ -> verify_one_repo lems cprog) lems

(* update store with given repo without verifying the lemmas *)
let manage_lemmas_x(* _new *) ?(unfold_flag=true) ?(force_pr=false) ?(vdefs=[]) repo iprog cprog  =
  let lems = process_one_repo unfold_flag repo iprog cprog in
  let () = x_tinfo_pp "sleek : after process_one_repo" no_pos in
  let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in
  let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in
  (* let vdefs = Cprinter.get_sorted_view_decls () in *)
  (* let ulst = Cast.get_unfold_set vdefs (\* set of unfoldable views *\) in *)
  (* let left = List.map (Cast.repl_unfold_lemma ulst) left in *)
  (* let right = List.map (Cast.repl_unfold_lemma ulst) right in *)
  let () = Lem_store.all_lemma # add_coercion left right in
  if force_pr (*&& !Globals.dump_lem_proc *) then
    begin
      let lnames = (List.map (fun (_,_,_,n)-> n) lems) in
      let () = x_tinfo_hp (add_str "Updated lemma store with unsafe repo:" ( pr_list pr_id)) lnames no_pos (* else () *) in
      ()
    end;
  lems

let manage_unsafe_lemmas ?(force_pr=false) repo iprog cprog : (CF.list_context list option) =
  let (_:'a list) = manage_lemmas_x(* _new *) ~unfold_flag:false ~force_pr:force_pr repo iprog cprog in
  None

let manage_unsafe_lemmas ?(force_pr=false) repo iprog cprog: (CF.list_context list option) =
  Debug.no_1 "manage_unsafe_lemmas"
    (pr_list !I.print_coerc_decl) pr_none
    (fun _ -> manage_unsafe_lemmas ~force_pr:force_pr repo iprog cprog) repo

(* update the lemma store with the lemmas in repo and check for their validity *)
let update_store_with_repo ?(force_pr=false) ?(vdefs=[]) repo iprog cprog =
  (* let lems = process_one_repo repo iprog cprog in *)
  (* let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in *)
  (* let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in *)
  (* let () = Lem_store.all_lemma # add_coercion left right in *)
  let lems = manage_lemmas_x ~vdefs:vdefs ~force_pr:force_pr repo iprog cprog in
  let () = x_tinfo_pp "lemma : after manage_lemmas_x" no_pos in
  let (invalid_lem, lctx) = x_add verify_one_repo lems cprog in
  (invalid_lem, lctx)

let update_store_with_repo ?(force_pr=false) repo iprog cprog =
  let pr1 = pr_list Iprinter.string_of_coerc_decl in
  let pr_out = pr_pair (pr_opt pr_id) (pr_list Cprinter.string_of_list_context) in
  Debug.no_1 "update_store_with_repo"  pr1 pr_out (fun _ -> update_store_with_repo ~force_pr:force_pr repo iprog cprog) repo

(* pop only if repo is invalid *)
(* return None if all succeed, and result of first failure otherwise *)
let manage_safe_lemmas ?(force_pr=false) repo iprog cprog =
  let force_pr = !Globals.lemma_ep && !Globals.lemma_ep_verbose && force_pr in
  let (invalid_lem, nctx) = update_store_with_repo ~force_pr:force_pr repo iprog cprog in
  match invalid_lem with
  | Some name ->
    let () = Log.last_cmd # dumping (name) in
    let () = if force_pr then
        print_endline_quiet ("\nFailed to prove "^ (name) ^ " in current context.")
      else ()
    in
    Lem_store.all_lemma # pop_coercion;
    let () = if force_pr then
        print_endline_quiet ("Removing invalid lemma (lemma store restored).")
      else ()
    in
    Some([List.hd(nctx)])
  | None ->
    let lem_str = pr_list pr_id (List.map (fun i ->
        i.I.coercion_name^":"^(Cprinter.string_of_coercion_type i.I.coercion_type)) repo) in
    let () = if force_pr then
        print_endline_quiet ("\nValid Lemmas : "^lem_str^" added to lemma store.")
      else ()
    in
    None

(* update store with given repo without verifying the lemmas *)
(* let manage_unsafe_lemmas repo iprog cprog : (CF.list_context list option) = *)
(*   let (left,right, lnames) = List.fold_left (fun (left,right,names) ldef -> *)
(*       try *)
(*         let l2r,r2l,typ = process_one_lemma iprog cprog ldef in *)
(*         (l2r@left,r2l@right,((ldef.I.coercion_name)::names)) *)
(*       with e -> *)
(*         (\*This will mask all errors*\) *)
(*         let () = print_endline_quiet ("manage_unsafe_lemmas: error(s) occurred") in *)
(*         raise e *)
(*         (\* (left,right,names) *\) *)
(*     ) ([],[], []) repo in *)
(*   let () = Lem_store.all_lemma # add_coercion left right in *)
(*   let () = if  (!Globals.dump_lem_proc) then *)
(*     x_tinfo_hp (add_str "\nUpdated lemma store with unsafe repo:" ( pr_list pr_id)) lnames no_pos (\* else () *\) in *)
(*   let () = Debug.info_ihprint (add_str "\nUpdated store with unsafe repo." pr_id) "" no_pos in *)
(*   None *)


let manage_lemmas ?(force_pr=false) repo iprog cprog =
  if !Globals.check_coercions then manage_safe_lemmas ~force_pr:force_pr repo iprog cprog
  else manage_unsafe_lemmas ~force_pr:force_pr repo iprog cprog

(* update store with given repo, but pop it out in the end regardless of the result of lemma verification *)
(* let manage_test_lemmas repo iprog cprog orig_ctx =  *)
(*   let new_ctx = CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in  *)
(*   (\* what is the purpose of new_ctx? *\) *)
(*   let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog new_ctx in *)
(*   Lem_store.all_lemma # pop_coercion; *)
(*   let _  = match nctx with *)
(*     | CF.FailCtx _ ->  *)
(*           let () = Log.last_cmd # dumping (invalid_lem) in *)
(*           print_endline ("\nFailed to prove "^(invalid_lem) ^ " ==> invalid repo in current context.") *)
(*     | CF.SuccCtx _ -> *)
(*           print_endline ("\nTemp repo proved valid in current context.") in *)
(*   let () = print_endline ("Removing temp repo ---> lemma store restored.") in *)
(*   Some nctx *)


(* update store with given repo, but pop it out in the end regardless of the result of lemma verification *)
(* return None if all succeed, return first failed ctx otherwise *)
let manage_infer_lemmas_x ?(force_pr=false) ?(pop_all=true) str repo iprog cprog =
  let (invalid_lem, nctx) = update_store_with_repo ~force_pr:force_pr repo iprog cprog in
  let res_print = !Globals.lemma_ep_verbose && not(force_pr) in
  let () = if pop_all then
    Lem_store.all_lemma # pop_coercion
  else ()
  in
  match invalid_lem with
  | Some name ->
    let () = Log.last_cmd # dumping (name) in
    let () =
      if res_print (* !Globals.lemma_ep *) then
        print_endline_quiet ("\nFailed to infer "^str^" for "^ (name) ^ " (invalid lemma encountered).")
      else ()
    in
    false,Some([List.hd(nctx)])
  | None ->
    let () =
      if res_print (* !Globals.lemma_ep *) then
        print_endline_quiet ("\n Lemma infer "^str^" succeeded in current context.")
      else ()
    in
    let hprels = List.map (fun x -> List.concat (CF.collect_hp_rel_all x)) nctx in
    let () = y_tinfo_hp (add_str "hprels" (pr_list (pr_list pr_none))) hprels in
    let () = match hprels with
      | lst::_ -> CF.sleek_hprel_assumes # set lst
      | _ -> () in
    true,Some nctx

let manage_infer_lemmas_x ?(force_pr=false) ?(pop_all=true) str repo iprog cprog =
  let pr1 = pr_list Iprinter.string_of_coerc_decl in
  let pr2 = pr_list !CF.print_list_context in
  let pr3 = Iprinter.string_of_program in
  let pr4 = Cprinter.string_of_program in
  (* Debug.no_3 "manage_infer_lemmas_x" pr3 pr4 pr1 (pr_pair string_of_bool (pr_opt pr2))               *)
  (*   (fun _ _ _ -> manage_infer_lemmas_x ~force_pr:force_pr ~pop_all:pop_all str repo iprog cprog)  *)
  (*   iprog cprog repo                                                                                 *)
  Debug.no_2 "manage_infer_lemmas_x" pr1 (add_str "is_classic" string_of_bool) (pr_pair string_of_bool (pr_opt pr2))
    (fun _ _ -> manage_infer_lemmas_x ~force_pr:force_pr ~pop_all:pop_all str repo iprog cprog)
    repo (check_is_classic ())

(* for lemma_test, we do not return outcome of lemma proving *)
let manage_test_lemmas repo iprog cprog =
  manage_infer_lemmas_x "proved" repo iprog cprog; None (*Loc: while return None? instead full result*)

let manage_test_lemmas1 ?(force_pr=false) repo iprog cprog =
  manage_infer_lemmas_x ~force_pr:force_pr "proved" repo iprog cprog

let manage_infer_lemmas ?(pop_all=true) repo iprog cprog =
  (manage_infer_lemmas_x ~pop_all:pop_all "inferred" repo iprog cprog)

(* (\* verify  a list of lemmas *\) *)
(* (\* if one of them fails, return failure *\) *)
(* (\* otherwise, return a list of their successful contexts  *)
(*    which may contain inferred result *\) *)
(* let sa_verify_one_repo cprog l2r r2l =  *)
(*   let res = List.fold_left (fun ((valid_ans,res_so_far) as res) coer -> *)
(*       match valid_ans with *)
(*       | true -> *)
(*         let (flag,lc) = Lemproving.sa_verify_lemma cprog coer in  *)
(*         (flag, lc::res_so_far) *)
(*       | false -> res *)
(*     ) (true,[]) (l2r@r2l) in *)
(*   res *)

(* (\* update the lemma store with the lemmas in repo and check for their validity *\) *)
(* let sa_update_store_with_repo cprog l2r r2l = *)
(*   let () = Lem_store.all_lemma # add_coercion l2r r2l in *)
(*   let (invalid_lem, lctx) =  sa_verify_one_repo cprog l2r r2l in *)
(*   (invalid_lem, lctx) *)

(* (\* l2r are left to right_lemmas *\) *)
(* (\* r2l are right to right_lemmas *\) *)
(* (\* return None if some failure; return list of contexts if all succeeded *\) *)
(* let sa_infer_lemmas iprog cprog lemmas  =  *)
(*   (\* let (l2r,others) = List.partition (fun c -> c.C.coercion_type==I.Left) lemmas in  *\) *)
(*   (\* let (r2l,equiv) = List.partition (fun c -> c.C.coercion_type==I.Right) others in  *\) *)
(*   (\* let l2r = l2r@(List.map (fun c -> {c with C.coercion_type = I.Left} ) equiv) in *\) *)
(*   (\* let r2l = r2l@(List.map (fun c -> {c with C.coercion_type = I.Right} ) equiv) in *\) *)
(*   (\* let (valid_lem, nctx) = sa_update_store_with_repo cprog l2r r2l in *\) *)
(*   (\* Lem_store.all_lemma # pop_coercion; *\) *)
(*   (\* match valid_lem with *\) *)
(*   (\*   | false ->  *\) *)
(*   (\*         (\\* let () = Log.last_cmd # dumping (name) in *\\) *\) *)
(*   (\*         let () = x_tinfo_pp ("\nFailed to prove a lemma ==> during sa_infer_lemmas.") no_pos in *\) *)
(*   (\*         None *\) *)
(*   (\*   | true -> Some nctx *\) *)
(*   let (invalid_lem, nctx) = update_store_with_repo lemmas iprog cprog in *)
(*   Lem_store.all_lemma # pop_coercion; *)
(*   match invalid_lem with *)
(*   | Some name ->  *)
(*     let () = x_tinfo_pp ("\nFailed to prove a lemma ==> during sa_infer_lemmas.") no_pos in *)
(*     None *)
(*   | None -> *)
(*     Some nctx *)

(* (\* WN : this method does not seem to be called *\) *)
(* let sa_infer_lemmas iprog cprog lemmas  = *)
(*   let pr1 = pr_list pr_none in *)
(*   Debug.no_1 "sa_infer_lemmas" pr1 pr_none (fun _ -> sa_infer_lemmas iprog cprog lemmas) lemmas *)

(*pure*)
let partition_pure_oblgs constrs post_rel_ids=
  let pre_invs, pre_constrs, post_constrs = List.fold_left (fun (r0,r1,r2) (cat,lhs_p,rhs_p) ->
      match cat with
      | CP.RelAssume _ | CP.RelDefn _ -> begin
          try
            let rel = CP.name_of_rel_form rhs_p in
            if CP.mem_svl rel post_rel_ids then
              r0,r1,r2@[(lhs_p, rhs_p)]
            else
            if CP.isConstTrue rhs_p then
              (r0@[lhs_p], r1, r2)
            else
              (r0, r1@[(lhs_p, rhs_p)], r2)
          with _ ->
            if CP.isConstTrue rhs_p then
              (r0@[(lhs_p)], r1, r2)
            else (r0, r1@[(lhs_p, rhs_p)], r2)
        end
      | _ -> (r0,r1,r2)
    ) ([],[],[]) constrs in
  (pre_invs, pre_constrs, post_constrs)

(*todo: use the following precedure for manage_infer_pred_lemmas*)
let preprocess_fixpoint_computation cprog xpure_fnc lhs oblgs rel_ids post_rel_ids =
  let pre_invs, pre_rel_oblgs, post_rel_oblgs = partition_pure_oblgs oblgs post_rel_ids in
  let pre_rel_ids = CP.diff_svl rel_ids post_rel_ids in
  let proc_spec = CF.mkETrue_nf no_pos in
  let _,bare = CF.split_quantifiers lhs in
  let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
    CF.get_pre_post_vars [] xpure_fnc (CF.struc_formula_of_formula bare no_pos) cprog in
  let () = Debug.ninfo_hprint (add_str "pre_fmls" (pr_list !CP.print_formula)) pre_fmls no_pos in
  let pre_rel_fmls = List.concat (List.map CF.get_pre_rels pre_fmls) in
  let pre_rel_fmls = List.filter (fun x -> CP.intersect (CP.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
  let pre_vnodes = CF.get_views bare in
  let ls_rel_args = CP.get_list_rel_args (CF.get_pure bare) in
  let () = Debug.ninfo_hprint (add_str "coercion_body" !CF.print_formula) bare no_pos in
  (* let () = Debug.info_hprint (add_str "pre_rel_ids" !CP.print_svl) pre_rel_ids no_pos in *)
  let pre_rel_args = List.fold_left (fun r (rel_id,args)-> if CP.mem_svl rel_id pre_rel_ids then r@args
                                      else r
                                    ) [] ls_rel_args in
  let invs = List.map (Fixpoint.get_inv cprog pre_rel_args) pre_vnodes in
  let rel_fm = CP.filter_var (CF.get_pure bare) pre_rel_args in
  (* let invs = CF.get_pre_invs pre_rel_ids (Fixpoint.get_inv cprog) *)
  (*   (CF.struc_formula_of_formula coer.C.coercion_body no_pos) in *)
  let inv = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) rel_fm (pre_invs@invs) in
  let pre_inv_ext = [inv] in
  Fixpoint.rel_fixpoint_wrapper pre_inv_ext pre_fmls pre_rel_oblgs post_rel_oblgs pre_rel_ids post_rel_ids proc_spec
  (*grp_post_rel_flag*)1
let plug_inferred_pure cprog coer defs post_vars pre_vars=
  if defs = [] then coer else
    let lst_defs = List.map (fun (a,b,_,d) -> (a,b,d)) defs in
    let new_head = Fixpoint.simplify_pre coer.Cast.coercion_head (lst_defs) in
    let new_body,_ = Fixpoint.simplify_post coer.Cast.coercion_body post_vars cprog (Some lst_defs)  pre_vars
      true [] [] in
    {coer with Cast.coercion_head = new_head;
        Cast.coercion_body = new_body}


let infer iprog cprog left hp_lst_assume oblgs=
  let print_relational_def_shape defs0 =
    let defs0 = List.sort CF.hpdef_cmp defs0 in
    if defs0 = [] then () else
      let defs = if !Globals.print_en_tidy then List.map Cfout.rearrange_def defs0 else defs0 in
      print_endline_quiet "\n*********************************************************";
      let () = print_endline_quiet ("*******relational definition" ^"********") in
      print_endline_quiet "*********************************************************";
      let pr1 = pr_list_ln Cprinter.string_of_hprel_def_short in
      print_endline_quiet (pr1 defs);
      print_endline_quiet "*************************************";
      ()
  in
  let print_res r=
    if r = [] then () else
      let () = Debug.info_hprint (add_str "fixpoint"
          (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in
      let () = print_endline_quiet "" in
      ()
  in
  let plug_inferred_shape coer defs=
    let hp_decls = cprog.Cast.prog_hp_decls in
    let new_head, new_body = Saout.plug_shape_into_lemma iprog cprog [] [] coer.Cast.coercion_head coer.Cast.coercion_body defs in
    let () = cprog.C.prog_hp_decls <- hp_decls in
    {coer with Cast.coercion_head = new_head;
        Cast.coercion_body = new_body}
  in
  (****************************************************************)
  (****************************************************************)
  let is_exist, post_hps, post_rel_ids, sel_hps, rel_ids = match left  with
    | [] -> false,[],[],[],[]
    | [coer] -> begin
          let post_hps, post_rel_ids = match coer.Cast.coercion_type with
            | Iast.Left ->
            CP.remove_dups_svl (CF.get_hp_rel_name_formula coer.C.coercion_body),
            CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_body)))
            | Iast.Right ->
                  CP.remove_dups_svl (CF.get_hp_rel_name_formula coer.C.coercion_head),
                  CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_head)))
            | _ -> [],[]
          in
          ( true,post_hps, post_rel_ids,
          List.filter (fun sv -> CP.is_hprel_typ sv) coer.C.coercion_infer_vars,
          List.filter (fun sv -> CP.is_rel_typ sv) coer.C.coercion_infer_vars
          )
      end
    | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas"
  in
  let new_coers, rl, lshape = if is_exist then
    let l_coer = List.hd left in
    let lshape = if sel_hps = [] || hp_lst_assume = [] then [] else
      let _, hp_defs, _ = !infer_shapes iprog cprog "temp" hp_lst_assume sel_hps post_hps
        [] [] [] true true (!norm_flow_int) in
      hp_defs
    in
    let defs0 = CF.rel_def_stk# get_stk in
    let () = print_relational_def_shape defs0 in
    (* to incorp inferred result into lemma *)
    let inferred_coer = if defs0 = [] then l_coer
    else
      let new_coer = plug_inferred_shape l_coer lshape in
      new_coer
    in
    let () = CF.rel_def_stk# reset in
    (*pure fixpoint*)
    let new_coer2, rl = if rel_ids = [] || oblgs = [] then (inferred_coer,[]) else
      let pre_invs, pre_rel_oblgs, post_rel_oblgs = partition_pure_oblgs oblgs post_rel_ids in
      let proc_spec = CF.mkETrue_nf no_pos in
      let pre_rel_ids = CP.diff_svl rel_ids post_rel_ids in
      let r = Fixpoint.rel_fixpoint_wrapper pre_invs [] pre_rel_oblgs post_rel_oblgs pre_rel_ids post_rel_ids proc_spec 1 in
      (* let () = Debug.info_hprint (add_str "fixpoint" *)
      (*                               (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in *)
      (* let () = print_endline_quiet "" in *)
      let () = print_res r in
      let inferred_coer2 = if r = [] then inferred_coer
    else
      let new_coer = plug_inferred_pure cprog inferred_coer r post_rel_ids (CP.diff_svl rel_ids post_rel_ids) in
      new_coer
    in
      inferred_coer2, r
    in
    [new_coer2], rl, lshape
  else left,[],[]
  in
  (new_coers, rl, lshape)

let manage_infer_pred_lemmas repo iprog cprog xpure_fnc =
  (****************************)
  let print_res r=
    if r = [] then () else
      let () = Debug.info_hprint (add_str "fixpoint"
          (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in
      let () = print_endline_quiet "" in
      ()
  in
  let print_relational_ass_shape hprels =
    if hprels = [] then () else begin
      print_endline_quiet "";
      print_endline_quiet "*************************************";
      print_endline_quiet "*******shape relational assumptions ********";
      print_endline_quiet "*************************************";
    end;
    let ras = List.rev(hprels) in
    let ras1 = if !Globals.print_en_tidy then List.map Cfout.rearrange_rel ras else ras in
    let pr = pr_list_ln (fun x -> Cprinter.string_of_hprel_short_inst cprog [] x) in
    let ()  = print_endline_quiet (pr (ras1)) in
    ()
  in
  let print_inferred_lemma coer=
    let () = print_endline_quiet "\n*********************************************************" in
    let () = print_endline_quiet ("*******INFERRED LEMMA" ^"********") in
    let () =  print_endline_quiet ((Cprinter.string_of_coerc_med) coer) in
    let () = print_endline_quiet "*************************************"in
    ()
  in
  (****************************)
  let rec helper coercs rel_fixs hp_rels res_so_far=
    match coercs with
    | [] -> (rel_fixs, hp_rels, Some res_so_far)
    | coer::rest -> begin
        (* let lems = process_one_repo [coer] iprog cprog in *)
        (* let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in *)
        (* let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in *)
        (* let () = Lem_store.all_lemma # add_coercion left right in *)
        (* let (invalid_lem, lcs) =  verify_one_repo lems cprog in *)
        let (invalid_lem, lcs_opt) = manage_infer_lemmas_x ~pop_all:false "inferred_pred" [coer] iprog cprog in
        let left = Lem_store.all_lemma # get_left_coercion in
        let right = Lem_store.all_lemma # get_right_coercion in
        Lem_store.all_lemma # pop_coercion;
        let lcs = match lcs_opt with
          | Some ls -> ls
          | None -> []
        in
        match invalid_lem with
        | true -> begin
            let hprels = List.fold_left (fun r_ass lc -> r_ass@(Infer.collect_hp_rel_list_context lc)) [] lcs in
              (* let hprels = Infer.rel_ass_stk # get_stk in *)
              let () =  print_relational_ass_shape hprels in
              let () = Infer.rel_ass_stk # reset in
          let (_,hp_rest) = List.partition (fun hp ->
              match hp.CF.hprel_kind with
              | CP.RelDefn _ -> true
              | _ -> false
            ) hprels
          in
          let (hp_lst_assume,(* hp_rest *)_) = List.partition (fun hp ->
              match hp.CF.hprel_kind with
              | CP.RelAssume _ -> true
              | _ -> false
            ) hp_rest
          in
          let oblgs = List.fold_left (fun r_ass lc -> r_ass@(Infer.collect_rel_list_context lc)) [] lcs in
          (*left*)
          let l_coers, rl, lshapes =
            if left = [] then left,[],[] else
               infer iprog cprog left hp_lst_assume oblgs
          in
          (*right*)
          (*shape*)
          let r_coers, rr,rshapes = match right with
            | [] -> right,[],[]
            | coer::_ ->
                  let r_coers, rr,rshapes = infer iprog cprog right hp_lst_assume [](* oblgs *) in
                  let post_rel_ids =  CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_head))) in
                  let rel_ids = List.filter (fun sv -> CP.is_rel_typ sv) coer.C.coercion_infer_vars in
            (*TO MERGE with left*)
            (* let post_hps, post_rel_ids, sel_hps, rel_ids = match right  with *)
            (*   | [] -> [],[],[],[] *)
            (*   | [coer] -> (CP.remove_dups_svl (CF.get_hp_rel_name_formula coer.C.coercion_head), *)
            (*     CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_head))), *)
            (*     List.filter (fun sv -> CP.is_hprel_typ sv) coer.C.coercion_infer_vars, *)
            (*     List.filter (fun sv -> CP.is_rel_typ sv) coer.C.coercion_infer_vars *)
            (*     ) *)
            (*   | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas 2" *)
            (* in *)
            (* let hp_defs = if sel_hps = [] || hp_lst_assume = [] then [] else *)
            (*   let _, hp_defs,_ = !infer_shapes iprog cprog "temp" hp_lst_assume sel_hps post_hps *)
            (*     [] [] [] true true !norm_flow_int in *)
            (*   hp_defs *)
            (* in *)
            (* (\* let () = print_endline ("\nxxxxxx " ^ ((pr_list_ln Cprinter.string_of_list_context) lcs)) in *\) *)
            (* (\*pure fixpoint*\) *)
            let right, rr = if rel_ids = [] || oblgs = [] then r_coers,[] else
              let pre_invs, pre_rel_oblgs, post_rel_oblgs = partition_pure_oblgs oblgs post_rel_ids in
              let pre_rel_ids = CP.diff_svl rel_ids post_rel_ids in
              let proc_spec = CF.mkETrue_nf no_pos in
              (*more invs*)
              let pre_inv_ext,pre_fmls,grp_post_rel_flag = match right with
                | [] -> [],[],0
                | [coer] ->
                      let _,bare = CF.split_quantifiers coer.C.coercion_body in
                      let pres,posts_wo_rel,all_posts,inf_vars,pre_fmls,grp_post_rel_flag =
                        CF.get_pre_post_vars [] xpure_fnc (CF.struc_formula_of_formula bare no_pos) cprog in
                      let () = Debug.ninfo_hprint (add_str "pre_fmls" (pr_list !CP.print_formula)) pre_fmls no_pos in
                      let pre_rel_fmls = List.concat (List.map CF.get_pre_rels pre_fmls) in
                      let pre_rel_fmls = List.filter (fun x -> CP.intersect (CP.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
                      let pre_vnodes = CF.get_views coer.C.coercion_body in
                      let ls_rel_args = CP.get_list_rel_args (CF.get_pure bare) in
                      let () = Debug.ninfo_hprint (add_str "coercion_body" !CF.print_formula) bare no_pos in
                      (* let () = Debug.info_hprint (add_str "pre_rel_ids" !CP.print_svl) pre_rel_ids no_pos in *)
                      let pre_rel_args = List.fold_left (fun r (rel_id,args)-> if CP.mem_svl rel_id pre_rel_ids then r@args
                                                          else r
                      ) [] ls_rel_args in
                      let invs = List.map (Fixpoint.get_inv cprog pre_rel_args) pre_vnodes in
                      let rel_fm = CP.filter_var (CF.get_pure bare) pre_rel_args in
                      let inv = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) rel_fm (pre_invs@invs)  in
                      [ inv],pre_fmls,grp_post_rel_flag
                | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas 3"
              in
              let r = Fixpoint.rel_fixpoint_wrapper pre_inv_ext pre_fmls pre_rel_oblgs post_rel_oblgs pre_rel_ids post_rel_ids proc_spec grp_post_rel_flag in
              (* let () = if r = [] then () else *)
              (*   Debug.info_hprint (add_str "fixpoint" *)
              (*       (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in *)
              (* let () = print_endline_quiet "" in *)
              let () = print_res r in
              let coers = List.map (fun inferred_coer -> plug_inferred_pure cprog inferred_coer r post_rel_ids (CP.diff_svl rel_ids post_rel_ids)) r_coers in
              coers, r
            in
            (*plug in res*)
            (right,rr,rshapes)
          in
          (* print shape inference result *)
          let () =  List.iter print_inferred_lemma (l_coers@r_coers) in
          let () = Lem_store.all_lemma # add_coercion l_coers r_coers  in
          (* let _=  print_endline "*************************************" in *)
          helper rest (rel_fixs@rl@rr) (hp_rels@lshapes@rshapes) (res_so_far@lcs)
          end
        | false -> helper rest rel_fixs hp_rels res_so_far
      end
  in
  let rec_fixs, hp_defs, ls_opt = helper repo [] [] [] in
  let rel_defs = List.fold_left (fun r (post_rel, post_f, pre_rel, pre_f) ->
      let r1 = if not (CP.isConstFalse post_f || CP.isConstTrue post_f) then
          r@[(post_rel, post_f)]
        else r
      in
      let r2 = if not (CP.isConstFalse pre_f || CP.isConstTrue pre_f) then
          r1@[(pre_rel, pre_f)]
        else r1
      in
      r2
    ) [] rec_fixs in
  (*update for Z3*)
  let todo_unk = List.map (fun (rel_name, rel_f) ->
      let rel_args_opt = CP.get_relargs_opt rel_name in
      match rel_args_opt with
      | Some (rel, args) ->
        let _= Smtsolver.add_relation (CP.name_of_spec_var rel) args rel_f in
        let _= Z3.add_relation (CP.name_of_spec_var rel) args rel_f in
        ()
      | None -> report_error no_pos "Lemma.manage_infer_pred_lemmas: should rel name"
    ) rel_defs in
  let n_hp_defs = List.map (fun hp_def -> Cfutil.subst_rel_def_4_hpdef hp_def rel_defs) hp_defs in
  (rec_fixs, n_hp_defs, ls_opt)

(* type: I.coercion_decl list -> *)
(*   Astsimp.I.prog_decl -> *)
(*   Astsimp.C.prog_decl -> *)
(*   (int -> *)
(*    Astsimp.C.prog_decl -> *)
(*    CF.h_formula -> CF.MCP.mix_formula -> int -> CF.MCP.mix_formula * 'a * 'b) -> *)
(*   (Cformula.CP.formula * Cformula.CP.formula * Cformula.CP.formula * *)
(*    Cformula.CP.formula) *)
(*   list * Cformula.hp_rel_def list * Lemproving.CF.list_context list option *)
let manage_infer_pred_lemmas repo iprog cprog xpure_fnc =
  let pr_c = Iprinter.string_of_coercion in
  Debug.no_1 "manage_infer_pred_lemmas" (pr_list pr_c)
    (fun (_,rel_defs,res) -> (pr_list Cprinter.string_of_hp_rel_def) rel_defs)
    (fun _ -> manage_infer_pred_lemmas repo iprog cprog xpure_fnc) repo


(* verify given repo in a fresh store. Revert the store back to it's state prior to this method call *)
(* let manage_test_new_lemmas repo iprog cprog ctx =  *)
(*   let left_lems = Lem_store.all_lemma # get_left_coercion in *)
(*   let right_lems = Lem_store.all_lemma # get_right_coercion in *)
(*   let () = Lem_store.all_lemma # set_coercion [] [] in *)
(*   let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog ctx in *)
(*   let () = Lem_store.all_lemma # set_left_coercion left_lems in *)
(*   let () = Lem_store.all_lemma # set_right_coercion right_lems in *)
(*   let () = match nctx with  *)
(*     | CF.FailCtx _ ->  *)
(*           let () = Log.last_cmd # dumping (invalid_lem) in *)
(*           print_endline ("\nFailed to prove "^ (invalid_lem) ^ " ==> invalid repo in fresh context.") *)
(*     | CF.SuccCtx _ -> *)
(*           print_endline ("\nTemp repo proved valid in fresh context.") in *)
(*   print_endline ("Removing temp repo ---> lemma store restored."); *)
(*   Some ctx *)

(* verify given repo in a fresh store. Revert the store back to it's state prior to this method call *)
let manage_test_new_lemmas repo iprog cprog =
  let left_lems = Lem_store.all_lemma # get_left_coercion in
  let right_lems = Lem_store.all_lemma # get_right_coercion in
  let () = Lem_store.all_lemma # set_coercion [] [] in
  let res = manage_test_lemmas repo iprog cprog in
  let () = Lem_store.all_lemma # set_left_coercion left_lems in
  let () = Lem_store.all_lemma # set_right_coercion right_lems in
  res

let manage_test_new_lemmas1 repo iprog cprog =
  let left_lems = Lem_store.all_lemma # get_left_coercion in
  let right_lems = Lem_store.all_lemma # get_right_coercion in
  let () = Lem_store.all_lemma # clear_left_coercion in
  let () = Lem_store.all_lemma # clear_right_coercion in
  let res = manage_test_lemmas1 repo iprog cprog in
  let () = Lem_store.all_lemma # set_left_coercion left_lems in
  let () = Lem_store.all_lemma # set_right_coercion right_lems in
  res

let sort_list_lemma iprog =
  let lems = iprog.Iast.prog_coercion_decls in
  let unsafe_lems, others = List.partition (fun lem ->
    match lem.Iast.coercion_list_kind with LEM_UNSAFE -> true | _ -> false) lems in
  iprog.Iast.prog_coercion_decls <- unsafe_lems @ others

(* ==================================== *)
let process_list_lemma_helper ldef_lst iprog cprog lem_infer_fnct =
  let lst = ldef_lst.Iast.coercion_list_elems in
  (* why do we check residue for ctx? do we really need a previous context? *)
  let enable_printing = (!Globals.dump_lem_proc) && ( List.length lst > 0 ) in
  (* let () = if enable_printing then Debug.ninfo_pprint "=============== Processing lemmas ===============" no_pos else () in *)
  let ctx = match !CF.residues with
    | None            ->  CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos]
    | Some (CF.SuccCtx ctx, _) -> CF.SuccCtx ctx
    | Some (CF.FailCtx ctx, _) -> CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in
  (* andreeac: to check if it should skip lemma proving *)
  let res =
    match ldef_lst.Iast.coercion_list_kind with
    | LEM            -> manage_lemmas ~force_pr:true lst iprog cprog
    | LEM_PROP       -> (manage_unsafe_lemmas ~force_pr:false lst iprog cprog )
    | LEM_SPLIT       -> (manage_unsafe_lemmas ~force_pr:false lst iprog cprog )
    | LEM_TEST       -> (manage_test_lemmas lst iprog cprog )
    | LEM_TEST_NEW   -> (manage_test_new_lemmas lst iprog cprog )
    | LEM_UNSAFE     -> manage_unsafe_lemmas ~force_pr:true lst iprog cprog
    | LEM_SAFE       -> manage_safe_lemmas ~force_pr:true  lst iprog cprog
    | LEM_INFER      -> snd (manage_infer_lemmas lst iprog cprog)
    | LEM_INFER_PRED      -> let r1,r2,r3 = manage_infer_pred_lemmas lst iprog cprog Cvutil.xpure_heap in
      let todo_unk = lem_infer_fnct r1 r2 in
      r3
    | RLEM           -> manage_unsafe_lemmas lst iprog cprog
  in
  (* let () = if enable_printing then Debug.ninfo_pprint "============ end - Processing lemmas ============\n" no_pos else () in *)
  match res with
  | None | Some [] -> CF.clear_residue ()
  | Some(c::_) ->
        CF.set_residue true c (* !Globals.disable_failure_explaining false false *)

let process_list_lemma_helper ldef_lst iprog cprog lem_infer_fnct  =
  Debug.no_1 "process_list_lemma_helper" !I.print_coerc_decl_list pr_none
    (fun _ -> process_list_lemma_helper ldef_lst iprog cprog lem_infer_fnct ) ldef_lst

(* ============================ END --- lemma translation and store update================================= *)


let do_unfold_view_hf cprog hf0 =
  let fold_fnc ls1 ls2 aux_fnc = List.fold_left (fun r (hf2, p2) ->
      let in_r = List.map (fun (hf1, p1) ->
          let nh = aux_fnc hf1 hf2 in
          let () = Debug.info_hprint (add_str "        p1:" !CP.print_formula) (MCP.pure_of_mix p1) no_pos in
          let () = Debug.info_hprint (add_str "        p2:" !CP.print_formula) (MCP.pure_of_mix p2) no_pos in
          let qvars1, bare1 = CP.split_ex_quantifiers (MCP.pure_of_mix p1) in
          let qvars2, bare2 = CP.split_ex_quantifiers (MCP.pure_of_mix p2) in
          let () = Debug.info_hprint (add_str "        bare1:" !CP.print_formula) bare1 no_pos in
          let () = Debug.info_hprint (add_str "        bare2:" !CP.print_formula) bare2 no_pos in
          let np = CP.mkAnd bare1 bare2 (CP.pos_of_formula bare1) in
          (nh, MCP.mix_of_pure (CP.add_quantifiers (CP.remove_dups_svl (qvars1@qvars2)) np))
        ) ls1 in
      r@in_r
    ) [] ls2 in
  let rec helper hf=
    match hf with
    | CF.Star { CF.h_formula_star_h1 = hf1;
                CF.h_formula_star_h2 = hf2;
                CF.h_formula_star_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let star_fnc h1 h2 =
        CF.Star {CF.h_formula_star_h1 = h1;
                 CF.h_formula_star_h2 = h2;
                 CF.h_formula_star_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 star_fnc
    | CF.StarMinus { h_formula_starminus_h1 = hf1;
                     CF.h_formula_starminus_h2 = hf2;
                     CF.h_formula_starminus_aliasing = al;
                     CF.h_formula_starminus_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let starminus_fnc h1 h2 =
        CF.StarMinus {CF.h_formula_starminus_h1 = h1;
                      CF.h_formula_starminus_h2 = h2;
                      CF.h_formula_starminus_aliasing = al;
                      CF.h_formula_starminus_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 starminus_fnc
    | CF.ConjStar  { CF.h_formula_conjstar_h1 = hf1;
                     CF.h_formula_conjstar_h2 = hf2;
                     CF.h_formula_conjstar_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjstar_fnc h1 h2 = CF.ConjStar { CF.h_formula_conjstar_h1 = h1;
                                             CF.h_formula_conjstar_h2 = h2;
                                             CF.h_formula_conjstar_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjstar_fnc
    | CF.ConjConj { CF.h_formula_conjconj_h1 = hf1;
                    CF.h_formula_conjconj_h2 = hf2;
                    CF.h_formula_conjconj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjconj_fnc h1 h2 = CF.ConjConj { CF.h_formula_conjconj_h1 = h1;
                                             CF.h_formula_conjconj_h2 = h2;
                                             CF.h_formula_conjconj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjconj_fnc
    | CF.Phase { h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let phase_fnc h1 h2 = CF.Phase { CF.h_formula_phase_rd = h1;
                                       CF.h_formula_phase_rw = h2;
                                       CF.h_formula_phase_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 phase_fnc
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conj_fnc h1 h2 = CF.Conj { CF.h_formula_conj_h1 = h1;
                                     CF.h_formula_conj_h2 = h2;
                                     CF.h_formula_conj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conj_fnc
    | CF.ViewNode hv -> begin
        try
          let vdcl = x_add C.look_up_view_def_raw x_loc cprog.C.prog_view_decls hv.CF.h_formula_view_name in
          let fs = List.map fst vdcl.C.view_un_struc_formula in
          let f_args = (CP.SpecVar (Named vdcl.C.view_name,self, Unprimed))::vdcl.C.view_vars in
          let a_args = hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments in
          let ss = List.combine f_args  a_args in
          let fs1 = List.map (x_add CF.subst ss) fs in
          List.map (fun f -> (List.hd (CF.heap_of f), MCP.mix_of_pure (CF.get_pure f))) fs1
        with _ -> let () = report_warning no_pos ("LEM.do_unfold_view_hf: can not find view " ^ hv.CF.h_formula_view_name) in
          [(CF.HTrue, MCP.mix_of_pure (CP.mkTrue no_pos))]
      end
    | CF.ThreadNode _
    | CF.DataNode _  | CF.HRel _ | CF.Hole _ | CF.FrmHole _
    | CF.HTrue  | CF.HFalse | CF.HEmp  | CF.HVar _-> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
  in
  helper hf0

let do_unfold_view_x cprog (f0: CF.formula) =
  let rec helper f=
    match f with
    | CF.Base fb ->
      let ls_hf_pure = do_unfold_view_hf cprog fb.CF.formula_base_heap in
      let fs = List.map (fun (hf, p) ->
          let () = Debug.ninfo_hprint (add_str "        p:" !CP.print_formula) (MCP.pure_of_mix p) no_pos in
          let qvars0, bare_f = CP.split_ex_quantifiers_ext (CP.elim_exists (MCP.pure_of_mix  p)) in
          let () = Debug.ninfo_hprint (add_str "        bare_f:" !CP.print_formula) bare_f no_pos in
          let f = CF.Base {fb with CF.formula_base_heap = hf;
                                   CF.formula_base_pure = MCP.merge_mems (MCP.mix_of_pure bare_f) fb.CF.formula_base_pure true;
                          }
          in CF.add_quantifiers qvars0 f
        ) ls_hf_pure in
      CF.disj_of_list fs fb.CF.formula_base_pos
    | CF.Exists _ ->
      let qvars, base1 = CF.split_quantifiers f in
      let nf = helper base1 in
      CF.add_quantifiers qvars nf
    | CF.Or orf  ->
      CF.Or { orf with CF.formula_or_f1 = helper orf.CF.formula_or_f1;
                       CF.formula_or_f2 = helper orf.CF.formula_or_f2 }
  in
  helper f0

let do_unfold_view cprog (f0: CF.formula) =
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_1 "LEM.do_unfold_view" pr1 pr1
    (fun _ -> do_unfold_view_x cprog f0) f0


(* (* Trung: need rename *)    *)
(* type lemma_param_property = *)
(*   | LemmaParamEqual         *)
(*   | LemmaParamDistributive  *)
(*   | LemmaParamUnknown       *)

(* let compute_lemma_params_property (vd: C.view_decl) (prog: C.prog_decl)                         *)
(*     : (CP.spec_var * lemma_param_property) list =                                               *)
(*   let pos = vd.C.view_pos in                                                                    *)
(*   (* find recursive view in each branch *)                                                      *)
(*   let rec collect_recursive_view hf = (match hf with                                            *)
(*     | CF.ViewNode vn ->                                                                         *)
(*         if (String.compare vn.CF.h_formula_view_name vd.C.view_name = 0) then                   *)
(*           [vn]                                                                                  *)
(*         else []                                                                                 *)
(*     | CF.Star sf ->                                                                             *)
(*         let h1 = sf.CF.h_formula_star_h1 in                                                     *)
(*         let h2 = sf.CF.h_formula_star_h2 in                                                     *)
(*         (collect_recursive_view h1) @ (collect_recursive_view h2)                               *)

(*     | CF.HTrue | CF.HFalse | CF.HEmp -> []                                                      *)
(*     | CF.DataNode _ -> []                                                                       *)
(*     | _ -> report_error pos "compute_lemma_params_property: unexpected formula"                 *)
(*   ) in                                                                                          *)
(*   (* find base branch and inductive branch *)                                                   *)
(*   let base_branches, inductive_branches = List.partition(fun (branch, _) ->                     *)
(*     let (hf,_,_,_,_) = CF.split_components branch in                                            *)
(*     let views = collect_recursive_view hf in                                                    *)
(*     (List.length views = 0)                                                                     *)
(*   ) vd.C.view_un_struc_formula in                                                               *)
(*   let param_branches = List.map2 (fun (branch,_) (aux_f,_) ->                                   *)
(*     let (hf,_,_,_,_) = CF.split_components branch in                                            *)
(*     let views = collect_recursive_view hf in                                                    *)
(*     match views with                                                                            *)
(*     | [] -> []                                                                                  *)
(*     | [vn] ->                                                                                   *)
(*         let (_,aux_mf,_,_,_) = CF.split_components aux_f in                                     *)
(*         let aux_pf = MCP.pure_of_mix aux_mf in                                                  *)
(*         List.map2 (fun sv1 sv2 ->                                                               *)
(*           let e1 = CP.mkVar sv1 pos in                                                          *)
(*           let e2 = CP.mkVar sv2 pos in                                                          *)
(*           let equal_cond = CP.mkEqExp e1 e2 pos in                                              *)
(*           if (TP.imply_raw aux_pf equal_cond) then                                              *)
(*             LemmaParamEqual                                                                     *)
(*           else match (CP.type_of_spec_var sv1) with                                             *)
(*           | BagT _ ->                                                                           *)
(*               let subset_cond = CP.mkBagSubExp e2 e1 pos in                                     *)
(*               if (TP.imply_raw aux_pf subset_cond) then                                         *)
(*                 LemmaParamDistributive                                                          *)
(*               else LemmaParamUnknown                                                            *)
(*           | Int ->                                                                              *)
(*               (* exists k: forall sv1, sv2: aux_pf implies (sv1 - sv2 = k) *)                   *)
(*               let distributive_cond = (                                                         *)
(*                 let diff_var = CP.SpecVar(Int, fresh_name (), Unprimed) in                      *)
(*                 let diff_exp = CP.mkVar diff_var pos in                                         *)
(*                 let imply_cond =                                                                *)
(*                   CP.mkOr (CP.mkNot aux_pf None pos)                                            *)
(*                           (CP.mkEqExp (CP.mkSubtract e1 e2 pos) diff_exp pos)                   *)
(*                           None pos                                                              *)
(*                 in                                                                              *)
(*                 CP.mkExists [diff_var] (CP.mkForall [sv1;sv2] imply_cond None pos) None pos     *)
(*               ) in                                                                              *)
(*               if not(TP.imply_raw distributive_cond (CP.mkFalse pos)) then                      *)
(*                 LemmaParamDistributive                                                          *)
(*               else LemmaParamUnknown                                                            *)
(*           | _ -> LemmaParamUnknown                                                              *)
(*         ) vd.C.view_vars vn.CF.h_formula_view_arguments                                         *)
(*     | _ -> report_error pos "compute_lemma_params_property: expect at most 1 view node"         *)
(*   ) vd.C.view_un_struc_formula vd.C.view_aux_formula in                                         *)
(*   let param_properties = List.fold_left (fun res param_branch ->                                *)
(*     match res with                                                                              *)
(*     | [] -> param_branch                                                                        *)
(*     | _ ->                                                                                      *)
(*         try List.map2 (fun x y -> if (x=y) then x else LemmaParamUnknown) res param_branch      *)
(*         with _ -> report_error pos "compute_lemma_params_property: expect 2 list has same size" *)
(*   ) [] param_branches in                                                                        *)
(*   List.map2 (fun sv p -> (sv,p)) vd.C.view_vars param_properties                                *)

(* let generate_lemma_sll (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)                    *)
(*     : (I.coercion_decl list) =                                                                        *)
(*   let dname = vd.C.view_data_name in                                                                  *)
(*   let ddecl = I.look_up_data_def_raw iprog.I.prog_data_decls dname in                                 *)
(*   (* generate lemmas for segmented predicates *)                                                      *)
(*   if (vd.C.view_is_segmented) then                                                                    *)
(*     (* self::lseg(y,P) <--> sefl::lseg(x,P1) * x::lseg(y,P2) *)                                       *)
(*     (*    2 posibilities about P:                            *)                                       *)
(*     (*       + P = P1  =  P2   unifying operation            *)                                       *)
(*     (*       + P = P1 (+) P2   combining operation           *)                                       *)
(*     let pos = vd.C.view_pos in                                                                        *)
(*     let llemma_name = "llem_" ^ vd.C.view_name in                                                     *)
(*     let rlemma_name = "rlem_" ^ vd.C.view_name in                                                     *)
(*     let ihead = (                                                                                     *)
(*       let view_params = (List.map (fun (CP.SpecVar (_,id,p)) ->                                       *)
(*         IP.Var ((id,p), pos)                                                                          *)
(*       ) vd.C.view_vars ) in                                                                           *)
(*       let head = (                                                                                    *)
(*         IF.mkHeapNode (self, Unprimed) (vd.C.view_name)                                               *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params [] None pos                                                                   *)
(*       ) in                                                                                            *)
(*       Iformula.mkBase head (Ipure.mkTrue pos) Iformula.top_flow []  pos                               *)
(*     ) in                                                                                              *)
(*     let (left_body, right_body) = (                                                                   *)
(*       let view_params1 = (List.map (fun (CP.SpecVar (_,id,p)) ->                                      *)
(*         let vp = id ^ "_1" in                                                                         *)
(*         IP.Var ((vp,p), pos)                                                                          *)
(*       ) vd.C.view_vars) in                                                                            *)
(*       let body1 = (                                                                                   *)
(*         IF.mkHeapNode (self, Unprimed) (vd.C.view_name)                                               *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params1 [] None pos                                                                  *)
(*       ) in                                                                                            *)
(*       let forward_ptr = match vd.C.view_forward_ptrs with                                             *)
(*         | [sv] -> CP.name_of_spec_var sv                                                              *)
(*         | _ ->                                                                                        *)
(*             let msg = "generate_lemma_sll: expect 1 forward pointer in view "                         *)
(*                       ^ vd.C.view_name in                                                             *)
(*             report_error pos msg                                                                      *)
(*       in                                                                                              *)
(*       let view_params2 = (List.map (fun (CP.SpecVar (_,id,p)) ->                                      *)
(*         let vp =                                                                                      *)
(*           if (String.compare id forward_ptr = 0) then forward_ptr                                     *)
(*           else id ^ "_2"                                                                              *)
(*         in                                                                                            *)
(*         IP.Var ((vp,p), pos)                                                                          *)
(*       ) vd.C.view_vars) in                                                                            *)
(*       let body2 = (                                                                                   *)
(*         IF.mkHeapNode (forward_ptr^"_1", Unprimed) (vd.C.view_name)                                   *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params2 [] None pos                                                                  *)
(*       ) in                                                                                            *)
(*       let left_hbody = Iformula.mkStar body1 body2 pos in                                             *)
(*       let right_hbody = (                                                                             *)
(*         if (vd.C.view_is_touching) then left_hbody                                                    *)
(*         else                                                                                          *)
(*           (* lemma for non-touching predicates also borrow a @L node *)                               *)
(*           let lending_node =                                                                          *)
(*             IF.mkHeapNode (forward_ptr, Unprimed) dname                                               *)
(*                 0 false  (IP.ConstAnn Lend) false false false None                                    *)
(*                 (List.map (fun _ -> Ipure_D.Var((fresh_name (), Unprimed), pos)) ddecl.I.data_fields) *)
(*                 [] None pos                                                                           *)
(*           in                                                                                          *)
(*           Iformula.mkStar left_hbody lending_node pos                                                 *)
(*       ) in                                                                                            *)
(*       let pure_constraint = (                                                                         *)
(*         let param_properties = compute_lemma_params_property vd cprog in                              *)
(*         let param_constraints = List.fold_left(                                                       *)
(*           fun res (CP.SpecVar (typ,id,p), param_prop) ->                                              *)
(*             let sv_cond = (match param_prop with                                                      *)
(*               | LemmaParamEqual ->                                                                    *)
(*                   let e = Ipure_D.Var ((id,p), pos) in                                                *)
(*                   let e1 = Ipure_D.Var ((id^"_1",p), pos) in                                          *)
(*                   let e2 =                                                                            *)
(*                     if (String.compare id forward_ptr = 0) then                                       *)
(*                       Ipure_D.Var ((forward_ptr,p), pos)                                              *)
(*                     else Ipure_D.Var ((id^"_2",p), pos) in                                            *)
(*                   IP.mkAnd (IP.mkEqExp e e1 pos) (IP.mkEqExp e1 e2 pos) pos                           *)
(*               | LemmaParamDistributive -> (                                                           *)
(*                   let e = Ipure_D.Var ((id,p), pos) in                                                *)
(*                   let e1 = Ipure_D.Var ((id^"_1",p), pos) in                                          *)
(*                   let e2 =                                                                            *)
(*                     if (String.compare id forward_ptr = 0) then                                       *)
(*                       Ipure_D.Var ((forward_ptr,p), pos)                                              *)
(*                     else Ipure_D.Var ((id^"_2",p), pos) in                                            *)
(*                   match typ with                                                                      *)
(*                   | Int -> IP.mkEqExp e (IP.mkAdd e1 e2 pos) pos                                      *)
(*                   | BagT _ -> IP.mkEqExp e (Ipure_D.BagUnion ([e1;e2],pos)) pos                       *)
(*                   | _ -> report_error pos "generate_lemma_sll: unexpect typ"                          *)
(*                 )                                                                                     *)
(*               | _ -> IP.mkTrue pos                                                                    *)
(*             ) in                                                                                      *)
(*             IP.mkAnd sv_cond res pos                                                                  *)
(*         ) (IP.mkTrue pos) param_properties in                                                         *)
(*         param_constraints                                                                             *)
(*       ) in                                                                                            *)
(*       let l_body = Iformula.mkBase left_hbody pure_constraint Iformula.top_flow [] pos in             *)
(*       let r_body = Iformula.mkBase right_hbody pure_constraint Iformula.top_flow [] pos in            *)
(*       (l_body, r_body)                                                                                *)
(*     ) in                                                                                              *)
(*     let left_coercion = Iast.mk_lemma llemma_name LEM_SAFE Iast.Left [] ihead left_body in            *)
(*     let right_coercion = Iast.mk_lemma rlemma_name LEM_SAFE Iast.Right [] ihead right_body in         *)
(*     if (!Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold) then                          *)
(*       [right_coercion]                                                                                *)
(*     else [left_coercion; right_coercion]                                                              *)
(*   (* no need to generate lemma for non-segmented predicates *)                                        *)
(*   else ([])                                                                                           *)

(* let generate_lemma_dll (vd: C.view_decl)  (iprog: I.prog_decl) (cprog: C.prog_decl)                   *)
(*     : (I.coercion_decl list) =                                                                        *)
(*   let dname = vd.C.view_data_name in                                                                  *)
(*   let ddecl = I.look_up_data_def_raw iprog.I.prog_data_decls dname in                                 *)
(*   (* generate lemmas for segmented dll *)                                                             *)
(*   if (vd.C.view_is_segmented) then                                                                    *)
(*     (* self::dll(pr,last,out) <--> sefl::dll(pr,last1,out1) * out1::dll(last1,last,out) *)            *)
(*     (*    2 posibilities about P:                            *)                                       *)
(*     (*       + P = P1  =  P2   unifying operation            *)                                       *)
(*     (*       + P = P1 (+) P2   combining operation           *)                                       *)
(*     let pos = vd.C.view_pos in                                                                        *)
(*     let llemma_name = "llem_" ^ vd.C.view_name in                                                     *)
(*     let rlemma_name = "rlem_" ^ vd.C.view_name in                                                     *)
(*     let ihead = (                                                                                     *)
(*       let view_params = (List.map (fun (CP.SpecVar (_,id,p)) ->                                       *)
(*         IP.Var ((id,p), pos)                                                                          *)
(*       ) vd.C.view_vars ) in                                                                           *)
(*       let head = (                                                                                    *)
(*         IF.mkHeapNode (self, Unprimed) (vd.C.view_name)                                               *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params [] None pos                                                                   *)
(*       ) in                                                                                            *)
(*       Iformula.mkBase head (Ipure.mkTrue pos) Iformula.top_flow []  pos                               *)
(*     ) in                                                                                              *)
(*     let (left_body, right_body) = (                                                                   *)
(*       let view_params1 = (List.map (fun (CP.SpecVar (_,id,p)) ->                                      *)
(*         let vp = id ^ "_1" in                                                                         *)
(*         IP.Var ((vp,p), pos)                                                                          *)
(*       ) vd.C.view_vars) in                                                                            *)
(*       let body1 = (                                                                                   *)
(*         IF.mkHeapNode (self, Unprimed) (vd.C.view_name)                                               *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params1 [] None pos                                                                  *)
(*       ) in                                                                                            *)
(*       let forward_ptr = match vd.C.view_forward_ptrs with                                             *)
(*         | [sv] -> CP.name_of_spec_var sv                                                              *)
(*         | _ ->                                                                                        *)
(*             let msg = "generate_lemma_sll: expect 1 forward pointer in view "                         *)
(*                       ^ vd.C.view_name in                                                             *)
(*             report_error pos msg                                                                      *)
(*       in                                                                                              *)
(*       let view_params2 = (List.map (fun (CP.SpecVar (_,id,p)) ->                                      *)
(*         let vp =                                                                                      *)
(*           if (String.compare id forward_ptr = 0) then forward_ptr                                     *)
(*           else id ^ "_2"                                                                              *)
(*         in                                                                                            *)
(*         IP.Var ((vp,p), pos)                                                                          *)
(*       ) vd.C.view_vars) in                                                                            *)
(*       let body2 = (                                                                                   *)
(*         IF.mkHeapNode (forward_ptr^"_1", Unprimed) (vd.C.view_name)                                   *)
(*             0 false  (IP.ConstAnn Mutable) false false false None                                     *)
(*             view_params2 [] None pos                                                                  *)
(*       ) in                                                                                            *)
(*       let left_hbody = Iformula.mkStar body1 body2 pos in                                             *)
(*       let right_hbody = (                                                                             *)
(*         if (vd.C.view_is_touching) then left_hbody                                                    *)
(*         else                                                                                          *)
(*           (* lemma for non-touching predicates also borrow a @L node *)                               *)
(*           let lending_node =                                                                          *)
(*             IF.mkHeapNode (forward_ptr, Unprimed) dname                                               *)
(*                 0 false  (IP.ConstAnn Lend) false false false None                                    *)
(*                 (List.map (fun _ -> Ipure_D.Var((fresh_name (), Unprimed), pos)) ddecl.I.data_fields) *)
(*                 [] None pos                                                                           *)
(*           in                                                                                          *)
(*           Iformula.mkStar left_hbody lending_node pos                                                 *)
(*       ) in                                                                                            *)
(*       let pure_constraint = (                                                                         *)
(*         let param_properties = compute_lemma_params_property vd cprog in                              *)
(*         let param_constraints = List.fold_left(                                                       *)
(*           fun res (CP.SpecVar (typ,id,p), param_prop) ->                                              *)
(*             let sv_cond = (match param_prop with                                                      *)
(*               | LemmaParamEqual ->                                                                    *)
(*                   let e = Ipure_D.Var ((id,p), pos) in                                                *)
(*                   let e1 = Ipure_D.Var ((id^"_1",p), pos) in                                          *)
(*                   let e2 =                                                                            *)
(*                     if (String.compare id forward_ptr = 0) then                                       *)
(*                       Ipure_D.Var ((forward_ptr,p), pos)                                              *)
(*                     else Ipure_D.Var ((id^"_2",p), pos) in                                            *)
(*                   IP.mkAnd (IP.mkEqExp e e1 pos) (IP.mkEqExp e1 e2 pos) pos                           *)
(*               | LemmaParamDistributive -> (                                                           *)
(*                   let e = Ipure_D.Var ((id,p), pos) in                                                *)
(*                   let e1 = Ipure_D.Var ((id^"_1",p), pos) in                                          *)
(*                   let e2 =                                                                            *)
(*                     if (String.compare id forward_ptr = 0) then                                       *)
(*                       Ipure_D.Var ((forward_ptr,p), pos)                                              *)
(*                     else Ipure_D.Var ((id^"_2",p), pos) in                                            *)
(*                   match typ with                                                                      *)
(*                   | Int -> IP.mkEqExp e (IP.mkAdd e1 e2 pos) pos                                      *)
(*                   | BagT _ -> IP.mkEqExp e (Ipure_D.BagUnion ([e1;e2],pos)) pos                       *)
(*                   | _ -> report_error pos "generate_lemma_sll: unexpect typ"                          *)
(*                 )                                                                                     *)
(*               | _ -> IP.mkTrue pos                                                                    *)
(*             ) in                                                                                      *)
(*             IP.mkAnd sv_cond res pos                                                                  *)
(*         ) (IP.mkTrue pos) param_properties in                                                         *)
(*         param_constraints                                                                             *)
(*       ) in                                                                                            *)
(*       let l_body = Iformula.mkBase left_hbody pure_constraint Iformula.top_flow [] pos in             *)
(*       let r_body = Iformula.mkBase right_hbody pure_constraint Iformula.top_flow [] pos in            *)
(*       (l_body, r_body)                                                                                *)
(*     ) in                                                                                              *)
(*     let left_coercion = Iast.mk_lemma llemma_name LEM_SAFE Iast.Left [] ihead left_body in            *)
(*     let right_coercion = Iast.mk_lemma rlemma_name LEM_SAFE Iast.Right [] ihead right_body in         *)
(*     if (!Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold) then                          *)
(*       [right_coercion]                                                                                *)
(*     else [left_coercion; right_coercion]                                                              *)
(*   (* no need to generate lemma for non-segmented predicates *)                                        *)
(*   else ([])                                                                                           *)

(* let generate_lemma_tree_simple (vd: C.view_decl)  (iprog: I.prog_decl) (cprog: C.prog_decl)           *)
(*     : (I.coercion_decl list) =                                                                        *)
(*   ([])                                                                                                *)

(* let generate_lemma_tree_pointer_back (vd: C.view_decl)  (iprog: I.prog_decl) (cprog: C.prog_decl)     *)
(*     : (I.coercion_decl list) =                                                                        *)
(*   ([])                                                                                                *)
(* (*                                                                                                    *)
   (*  * assume that the prerequisite information of view is computed                                       *)
   (*  * (touching, segmented, forward, backward, aux...)                                                   *)
   (*  *)                                                                                                   *)
(* let generate_lemma (vd: C.view_decl)  (iprog: I.prog_decl) (cprog: C.prog_decl)                       *)
(*     : (I.coercion_decl list) =                                                                        *)
(*   let forward_fields = vd.C.view_forward_fields in                                                    *)
(*   let backward_fields = vd.C.view_backward_fields in                                                  *)
(*   (* singly linked list *)                                                                            *)
(*   if ((List.length forward_fields = 1) && (List.length backward_fields = 0)) then                     *)
(*     generate_lemma_sll vd iprog cprog                                                                 *)
(*   (* doubly linked list *)                                                                            *)
(*   else if ((List.length forward_fields = 1) && (List.length backward_fields = 1)) then                *)
(*     generate_lemma_dll vd iprog cprog                                                                 *)
(*   (* simple tree *)                                                                                   *)
(*   else if ((List.length forward_fields = 2) && (List.length backward_fields = 0)) then                *)
(*     generate_lemma_tree_simple vd iprog cprog                                                         *)
(*   (* tree with pointer back *)                                                                        *)
(*   else if ((List.length forward_fields = 2) && (List.length backward_fields = 1)) then                *)
(*     generate_lemma_tree_pointer_back vd iprog cprog                                                   *)
(*   (* what else ? *)                                                                                   *)
(*   else                                                                                                *)
(*     ([])                                                                                              *)

let normalize_view_branch_x (branch: CF.formula) (vd: C.view_decl) : CF.formula =
  (* let sst = collect_eq_vars branch in *)
  (* CF.subst_one_by_one sst branch      *)
  CF.elim_exists branch

let normalize_view_branch (branch: CF.formula) (vd: C.view_decl) : CF.formula =
  let pr_f = !CF.print_formula in
  Debug.no_1 "normalize_view_branch" pr_f pr_f
    (fun _ -> normalize_view_branch_x branch vd) branch

let collect_inductive_view_nodes (hf: CF.h_formula) (vd: C.view_decl)
  : CF.h_formula_view list =
  let view_nodes = ref [] in
  let f_hf hf = (match hf with
      | CF.ViewNode vn ->
        let () = (
          if (String.compare vn.CF.h_formula_view_name vd.C.view_name = 0) then
            view_nodes := !view_nodes @ [vn];
        ) in
        Some hf
      | CF.HTrue | CF.HFalse | CF.HEmp | CF.DataNode _ -> Some hf
      | _ -> None
    ) in
  let todo_unk = CF.transform_h_formula f_hf hf in
  !view_nodes

let remove_view_node_from_formula (f: CF.formula) (vn: CF.h_formula_view) : CF.formula =
  let f_e_f _ = None in
  let f_f _ = None in
  let f_hf hf = (match hf with
      | CF.ViewNode { CF.h_formula_view_name = vname } ->
        if (String.compare vname vn.CF.h_formula_view_name = 0) then
          Some CF.HEmp
        else Some hf
      | CF.HTrue | CF.HFalse | CF.HEmp | CF.DataNode _ -> Some hf
      | _ -> None
    ) in
  let f_m mp = Some mp in
  let f_a a = Some a in
  let f_pf pf = Some pf in
  let f_b bf = Some bf in
  let f_e e = Some e in
  CF.transform_formula (f_e_f, f_f, f_hf, (f_m, f_a, f_pf, f_b, f_e)) f

(* generalize generated coercion *)
let refine_nontail_coerc_body_heap_x (hf: IF.h_formula) (vd: C.view_decl) : IF.h_formula =
  (* replace self in view_vars by a fresh var *)
  let rec refine_heap (hf: IF.h_formula) (fr_var: ident)
    : IF.h_formula = (
    let new_var = (fresh_name (), Unprimed) in
    let subs_list = [((self,Unprimed), new_var)] in
    let f_hf hf = (match hf with
        | IF.HeapNode hn ->
          let args = hn.IF.h_formula_heap_arguments in
          let new_args = List.map (fun e ->
              IP.subst_exp subs_list e
            ) args in
          let new_hf = IF.HeapNode { hn with IF.h_formula_heap_arguments = new_args } in
          Some new_hf
        | IF.HeapNode2 _ -> None (* Trung: check later *)
        | _ -> None
      ) in
    IF.transform_h_formula f_hf hf
  ) in
  let new_var = fresh_name () in
  let new_hf = refine_heap hf new_var in
  new_hf

let refine_nontail_coerc_body_heap (hf: IF.h_formula) (vd: C.view_decl) : IF.h_formula =
  let pr = !IF.print_h_formula in
  Debug.no_1 "refine_nontail_coerc_body_heap" pr pr
    (fun _ -> refine_nontail_coerc_body_heap_x hf vd) hf

(* generalize generated coercion *)
let refine_tail_coerc_body_heap_x (hf: IF.h_formula) (vd: C.view_decl) : IF.h_formula =
  (* replace a heap node which is a view var of a view_decl by a fresh var *)
  let rec refine_heap (hf: IF.h_formula)
    : IF.h_formula = (
    let subs_list = ref [] in
    let view_vars = List.map (fun v ->
        CP.name_of_spec_var v
      ) vd.C.view_vars in
    (* substitute heap node first *)
    let collect_subs_list hf = (match hf with
        | IF.HeapNode hn ->
          let (hnode,prim) = hn.IF.h_formula_heap_node in
          (* heap node is a view var, substitute this heap node *)
          let () = (
            if List.exists (fun v -> String.compare v hnode = 0) view_vars then (
              try
                let todo_unk = List.find (fun subs ->
                    let v = fst subs in IP.eq_var (hnode,prim) v
                  ) !subs_list in
                ()
              with Not_found -> (
                  let new_var = (fresh_name (), Unprimed) in
                  subs_list := ((hnode,prim),new_var) :: !subs_list;
                )
            )
            else ()
          ) in
          None
        | IF.HeapNode2 _ -> None (* Trung: check later *)
        | _ -> None
      ) in
    let todo_unk = IF.transform_h_formula collect_subs_list hf in
    let subs_heap_node hf = (match hf with
        | IF.HeapNode hn ->
          let (hnode,prim) = hn.IF.h_formula_heap_node in
          let view_vars = List.map (fun v ->
              CP.name_of_spec_var v
            ) vd.C.view_vars in
          (* heap node is a view var, substitute this heap node *)
          if List.exists (fun v -> String.compare v hnode = 0) view_vars then (
            let (subs_node, subs_prim) = (
              try
                let subs = List.find (fun subs ->
                    let v = fst subs in
                    IP.eq_var (hnode,prim) v
                  ) !subs_list in
                snd subs
              with Not_found -> (
                  let msg = "refine_tail_coerc_body_heap: subs_list must be computed before" in
                  report_error no_pos msg
                )
            ) in
            let new_hf = IF.HeapNode {hn with IF.h_formula_heap_node = (subs_node, subs_prim)} in
            Some new_hf
          )
          else (
            let subs_args = List.map (fun arg ->
                IP.subst_exp !subs_list arg
              ) hn.IF.h_formula_heap_arguments in
            let new_hf = IF.HeapNode {hn with IF.h_formula_heap_arguments = subs_args} in
            Some new_hf
          )
        | IF.HeapNode2 _ -> None (* Trung: check later *)
        | _ -> None
      ) in
    IF.transform_h_formula subs_heap_node hf
  ) in
  let new_hf = refine_heap hf in
  new_hf

let refine_tail_coerc_body_heap (hf: IF.h_formula) (vd: C.view_decl) : IF.h_formula =
  let pr = !IF.print_h_formula in
  Debug.no_1 "refine_tail_coerc_body_heap" pr pr
    (fun _ -> refine_tail_coerc_body_heap_x hf vd) hf

let generate_view_lemmas_x (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
  : (I.coercion_decl list) =
  (* find base branch and inductive branch *)
  let vpos = vd.C.view_pos in
  let vname = vd.C.view_name in
  let dname = vd.C.view_data_name in
  if (String.compare dname "" = 0) then [] else
    let () = Debug.ninfo_hprint (add_str "dname" pr_id) dname no_pos in
    let ddecl = x_add I.look_up_data_def_raw iprog.I.prog_data_decls dname in
    let processed_branches = List.map (fun (f, lbl) ->
        (* (* TRUNG: TODO remove it later *)                                                             *)
        (* let () = try                                                                                   *)
        (*   let self_sv = CP.SpecVar (Named vd.C.view_data_name, self, Unprimed) in                     *)
        (*   let heap_chains = Acc_fold.collect_heap_chains f self_sv vd cprog in                        *)
        (*   let hc = List.hd heap_chains in                                                             *)
        (*   let fold_seq = Acc_fold.detect_fold_sequence hc vd self_sv cprog in                         *)
        (*   Debug.ninfo_hprint (add_str "fold_seq" (pr_list Acc_fold.print_fold_type)) fold_seq no_pos; *)
        (* with _ -> () in                                                                               *)

        let new_f = CF.elim_exists f in
        (new_f, lbl)
      ) vd.C.view_un_struc_formula in
    let base_branches, inductive_branches = List.partition(fun (f, _) ->
        let (hf,_,_,_,_,_) = CF.split_components f in
        let views = collect_inductive_view_nodes hf vd in
        (List.length views = 0)
      ) processed_branches in
    (* consider only the view has 1 base case and 1 inductive case *)
    if ((List.length base_branches != 1) || (List.length inductive_branches != 1)) then (
      Debug.ninfo_pprint ("generate_view_lemmas: no lemma is generated! 1") no_pos;
      []
    )
    (* consider only the view has 1 forward pointer *)
    else if (List.length vd.C.view_forward_ptrs != 1) then (
      Debug.ninfo_pprint ("generate_view_lemmas: no lemma is generated! 2") no_pos;
      []
    )
    (* statisfying view *)
    else (
      let forward_ptr = List.hd vd.C.view_forward_ptrs in
      let base_f, base_lbl = List.hd base_branches in
      let induct_f, induct_lbl = List.hd inductive_branches in
      let (induct_hf, _, _, _, _, _) = CF.split_components induct_f in
      let view_nodes = collect_inductive_view_nodes induct_hf vd in
      let induct_vnodes = List.filter (fun vn ->
          String.compare vn.CF.h_formula_view_name vname = 0
        ) view_nodes in
      if (List.length induct_vnodes != 1) then (
        Debug.ninfo_pprint ("generate_view_lemmas: no lemma is generated! 3") no_pos;
        []
      )
      else (
        let vns = Cformula.get_views induct_f in
        let other_vnodes = List.filter (fun vn ->
            String.compare vn.CF.h_formula_view_name vname != 0
          ) vns in
        if (!Globals.seg_fold) && other_vnodes !=[] then [] else
          (* create distributive lemma like:
                  pred -> pred1 * pred2
                  pred <- pred1 * pred2          *)
          (* this part is applicable to non-tail recursive lemmas *)
          let lem_head = (
            let head_node = (self, Unprimed) in
            let head_params = List.map (fun (CP.SpecVar (_,id,p)) ->
                IP.Var ((id,p), vpos)
              ) vd.C.view_vars in
            let head = (
              IF.mkHeapNode head_node (vd.C.view_name) [] (* TODO:HO *)
                0 false SPLIT0 (IP.ConstAnn Mutable) false false false None
                head_params [] None vpos
            ) in
            Iformula.mkBase head (Ipure.mkTrue vpos) IvpermUtils.empty_vperm_sets Iformula.top_flow [] vpos
          ) in
          let lem_body_heap = (
            let induct_vnode = List.hd induct_vnodes in
            let v_subs = C.collect_subs_from_view_node induct_vnode vd in
            let new_base_f = CF.subst_one_by_one v_subs base_f in
            Debug.ninfo_hprint (add_str "new_base_f" (!CF.print_formula)) new_base_f vpos;
            let base_subs = C.collect_subs_from_view_formula new_base_f vd in
            let induct_subs = C.collect_subs_from_view_formula induct_f vd in

            (* compute pred2 *)
            let pred2_node = (
              let pred2_node_sv = CP.subs_one induct_subs induct_vnode.CF.h_formula_view_node in
              match pred2_node_sv with
              | CP.SpecVar (_,vname,vprim) -> (vname,vprim)
            ) in
            let pred2_params = List.map (fun sv ->
                let sv = CP.subs_one induct_subs sv in
                let vname, vprim = CP.name_of_spec_var sv, CP.primed_of_spec_var sv in
                IP.Var ((vname,vprim), vpos)
              ) induct_vnode.CF.h_formula_view_arguments in
            let pred2 = (
              (* this is the original hformula view *)
              IF.mkHeapNode pred2_node (vd.C.view_name) [] (* TODO:HO *)
                0 false SPLIT0 (IP.ConstAnn Mutable) false false false None
                pred2_params [] None vpos
            ) in

            (* compute pred1 *)
            let pred1_node = (
              if not (vd.C.view_is_tail_recursive) then (self, Unprimed)
              else (
                let subs_sv = CP.subs_one v_subs forward_ptr in
                let subs_sv = CP.subs_one induct_subs subs_sv in
                match subs_sv with
                | CP.SpecVar (_,name,prim) -> (name,prim)
              )
            ) in
            (* check if new_induct_f can imply a view node *)
            (* we can have the distributive lemma only when the new_induct_f can form a view node *)
            let is_pred1_ok = (
              true
              (* TRUNG TODO: below should be included, uncomment later *)
              (* let reduced_induct_f = remove_view_node_from_formula induct_f induct_vnode in             *)
              (* let new_induct_f = x_add CF.subst base_subs reduced_induct_f in                                 *)
              (* (* let (hf,mf,fl,t,a) = CF.split_components new_induct_f in *)                            *)
              (* (* let pos = CF.pos_of_formula new_induct_f in              *)                            *)
              (* (* let new_induct_f = CF.mkBase hf mf t fl a pos in         *)                            *)
              (* let tmp_nname, tmp_nprim = pred1_node in                                                  *)
              (* let tmp_vnode = CP.SpecVar (Named dname, tmp_nname, tmp_nprim) in                         *)
              (* let tmp_vars = List.map (fun sv ->                                                        *)
              (*   match sv with                                                                           *)
              (*   | CP.SpecVar (t,_,_) -> CP.SpecVar (t, fresh_name (), Unprimed)                         *)
              (* ) vd.C.view_vars in                                                                       *)
              (* let tmp_vnode = CF.mkViewNode tmp_vnode vname tmp_vars no_pos in                          *)
              (* let tmp_f = CF.mkExists tmp_vars tmp_vnode (MCP.mkMTrue vpos)                             *)
              (*     CF.TypeTrue (CF.mkTrueFlow ()) [] vpos in                                             *)
              (* let tmp_sf = CF.struc_formula_of_formula tmp_f vpos in                                    *)
              (* (* let tmp_f = CF.struc_formula_of_formula (CF.formula_of_heap tmp_vnode vpos) vpos in *) *)
              (* Debug.ninfo_hprint (add_str "new_induct_f" (!CF.print_formula)) new_induct_f vpos;        *)
              (* Debug.ninfo_hprint (add_str "tmp_sf" (!CF.print_struc_formula)) tmp_sf vpos;              *)
              (* let (r,_,_) = wrap_classic (Some true)                                                    *)
              (*     (x_add Sleekcore.sleek_entail_check 9 [] cprog [] new_induct_f) tmp_sf in                   *)
              (* Debug.ninfo_pprint ("new_induct_f |- tmp_sf: " ^ (string_of_bool r)) vpos;                *)
              (* r                                                                                         *)
            ) in
            if not (is_pred1_ok) then None
            else (
              let pred1_params = List.map (fun sv ->
                  if (not vd.C.view_is_tail_recursive) && (CP.eq_spec_var sv forward_ptr) then
                    let vname, vprim = pred2_node in
                    IP.Var ((vname,vprim), vpos)
                  else
                    let param = (
                      try
                        let svs = List.find (fun (x,_) -> CP.eq_spec_var sv x) base_subs in
                        snd svs
                      with _ -> sv
                    ) in
                    match param with
                    | CP.SpecVar (_,vname,vprim) -> IP.Var ((vname,vprim), vpos)
                ) vd.C.view_vars in
              let pred1 = (
                (* this is a derived hformula view *)
                IF.mkHeapNode pred1_node (vd.C.view_name) [] (* TODO:HO *)
                  0 false SPLIT0 (IP.ConstAnn Mutable) true false false None
                  pred1_params [] None vpos
              ) in
              Debug.ninfo_hprint (add_str "pred1" !IF.print_h_formula) pred1 vpos;
              Debug.ninfo_hprint (add_str "pred2" !IF.print_h_formula) pred2 vpos;
              let body_heap = (
                if vd.C.view_is_tail_recursive then IF.mkStar pred2 pred1 vpos
                else IF.mkStar pred1 pred2 vpos
              ) in
              (* now, refine the lemma body *)
              let refined_body_heap = (
                if (vd.C.view_is_tail_recursive) then
                  refine_tail_coerc_body_heap body_heap vd
                else
                  refine_nontail_coerc_body_heap body_heap vd
              ) in
              Some refined_body_heap
            )
          ) in
          match lem_body_heap with
          | None ->
            Debug.ninfo_pprint ("generate_view_lemmas: no lemma is generated! 4") no_pos;
            []
          | Some lem_body_hf -> (
              let llem_body_hf = lem_body_hf in
              let llemma_name = "llem_" ^ vd.C.view_name in
              let true_pf = IP.mkTrue vpos in
              let llem_body = Iformula.mkBase llem_body_hf true_pf IvpermUtils.empty_vperm_sets Iformula.top_flow [] vpos in
              let left_coerc = Iast.mk_lemma llemma_name LEM_SAFE LEM_GEN Iast.Left [] lem_head llem_body in
              let right_coercs = (
                if (vd.C.view_is_touching) then (
                  let rlemma_name = "rlem_" ^ vd.C.view_name in
                  let rlem_body_hf = lem_body_hf in
                  let rlem_body = Iformula.mkBase rlem_body_hf true_pf IvpermUtils.empty_vperm_sets Iformula.top_flow [] vpos in
                  [(Iast.mk_lemma rlemma_name LEM_SAFE LEM_GEN Iast.Right [] lem_head rlem_body)]
                )
                else  (
                  let fwp_name = CP.name_of_spec_var forward_ptr in
                  (* lemma for non-touching predicates also borrow a @L node *)
                  let lending_node =
                    let params = List.map (fun _ ->
                        Ipure_D.Var((fresh_name (), Unprimed), vpos)
                      ) ddecl.I.data_fields in
                    IF.mkHeapNode (fwp_name, Unprimed) dname [] (* TODO:HO *)
                      0 false SPLIT0 (IP.ConstAnn Lend) false false false None
                      params [] None vpos
                  in
                  let rlemma_name1 = "rlem1_" ^ vd.C.view_name in
                  let rlem_body_hf1 = Iformula.mkStar llem_body_hf lending_node vpos in
                  let rlem_body1 = Iformula.mkBase rlem_body_hf1 true_pf IvpermUtils.empty_vperm_sets Iformula.top_flow [] vpos in
                  let right_coerc1 = Iast.mk_lemma rlemma_name1 LEM_SAFE LEM_GEN Iast.Right [] lem_head rlem_body1 in
                  let rlemma_name2 = "rlem2_" ^ vd.C.view_name in
                  let rlem_body_hf2 = llem_body_hf in
                  let rlem_body_pf2 = IP.mkEqExp (Ipure_D.Var ((fwp_name,Unprimed), vpos)) (Ipure_D.Null vpos) vpos in
                  let rlem_body2 = Iformula.mkBase rlem_body_hf2 rlem_body_pf2 IvpermUtils.empty_vperm_sets Iformula.top_flow [] vpos in
                  let right_coerc2 = Iast.mk_lemma rlemma_name2 LEM_SAFE LEM_GEN Iast.Right [] lem_head rlem_body2 in
                  [right_coerc1;right_coerc2]
                )
              ) in
              if (!Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold) then
                right_coercs
              else [left_coerc] @ right_coercs
            )
      )
    )

let generate_view_lemmas (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
  : (I.coercion_decl list) =
  let pr_v = !C.print_view_decl_short in
  let pr_out = pr_list Iprinter.string_of_coerc_decl in
  Debug.no_1 "generate_view_lemmas" pr_v pr_out
    (fun _ -> generate_view_lemmas_x vd iprog cprog) vd

let generate_view_rev_rec_lemmas_x (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
  : (I.coercion_decl list) =
  let vpos = vd.C.view_pos in
  let vname = vd.C.view_name in
  let dname = vd.C.view_data_name in
  if (String.compare dname "" = 0) then [] else
    let () = Debug.ninfo_hprint (add_str "dname" pr_id) dname no_pos in
    (* let ddecl = I.look_up_data_def_raw iprog.I.prog_data_decls dname in *)
    (*********************************************)
    let str_cmp s1 s2 = String.compare s1 s2 = 0 in
    let rec get_dfield_pos ls n sv=
      match ls with
      | [] -> raise Not_found
      | ((_,sv1),_)::rest -> if str_cmp sv sv1 then n
        else get_dfield_pos rest (n+1) sv
    in
    let find_pos (view_fwd_para, (ddcl, data_fwd_fname) )=
      try
        let view_fwd_para_pos = Cfutil.get_pos vd.Cast.view_vars 0 view_fwd_para in
        let data_fwd_fname_pos =  get_dfield_pos ddcl.Cast.data_fields 0 data_fwd_fname in
        [(view_fwd_para, view_fwd_para_pos, (ddcl, data_fwd_fname),data_fwd_fname_pos )]
      with _ -> []
    in
    let rec look_up_fwd_ptr_pos pr_fwd_ptrs_pos fwd_dname=
      match pr_fwd_ptrs_pos with
      | (_, para_pos, (ddcl, _),fname_pos )::rest ->
        if str_cmp ddcl.Cast.data_name fwd_dname then (para_pos, fname_pos) else
          look_up_fwd_ptr_pos rest fwd_dname
      | [] -> raise Not_found
    in
    let gen_sst_4_exchange_sv (sv1,sv2)=
      let fr_sv = CP.fresh_spec_var sv1 in
      [(sv1,fr_sv);(sv2,sv1);(fr_sv,sv2)]
    in
    let subst_sv_one_seq sst sv0=
      List.fold_left (fun sv ss -> CP.subs_one [ss] sv) sv0 sst
    in
    let cp_subst_seq sst p0=
      List.fold_left (fun p ss -> CP.subst [ss] p) p0 sst
    in
    let subst_list_var_seq sst svl= List.map (subst_sv_one_seq sst) svl
    in
    let subst_h_root sst hf=
      match hf with
      | CF.DataNode hn ->
        CF.DataNode {hn with CF.h_formula_data_node = subst_sv_one_seq sst hn.CF.h_formula_data_node }
      | CF.ViewNode hv -> CF.ViewNode {hv with CF.h_formula_view_node = subst_sv_one_seq sst hv.CF.h_formula_view_node}
      | _ -> hf
    in
    let subst_h_args sst hf=
      match hf with
      | CF.DataNode hn -> CF.DataNode {hn with CF.h_formula_data_arguments = subst_list_var_seq sst hn.CF.h_formula_data_arguments}
      | CF.ViewNode hv -> CF.ViewNode {hv with CF.h_formula_view_arguments = subst_list_var_seq sst hv.CF.h_formula_view_arguments}
      | _ -> hf
    in
    let gen_view_formula vdcl=
      let self_sv = CP.SpecVar (Named vdcl.Cast.view_data_name ,self, Unprimed) in
      let vnode = CF.mkViewNode (self_sv ) vdcl.Cast.view_name (vdcl.Cast.view_vars) no_pos in
      CF.formula_of_heap vnode no_pos
    in
    let exchange_two r1 args1 r2 args2=
      (* exchange root and fwd ptrs of hd, hv *)
      let sst_root = gen_sst_4_exchange_sv (r2, r1) in
      let sst_args = List.fold_left (fun r pr_sv -> r@(gen_sst_4_exchange_sv pr_sv)) []
          ((List.combine args2 args1)) in
      (sst_root, sst_args)
    in
    let self_sv = CP.SpecVar (Named vd.Cast.view_data_name ,self, Unprimed) in
    let view_f =  gen_view_formula vd in
    let rev_order pr_fwd_ptrs_pos (f,p)=
      let () = Debug.ninfo_hprint (add_str "f" Cprinter.prtt_string_of_formula) f no_pos in
      let hds, hvs,_ = CF.get_hp_rel_formula f in
      (****support one view, one data node. to extend****)
      match hds, hvs with
      | [hd],[hv] -> begin
          if str_cmp hd.CF.h_formula_data_name dname && str_cmp hv.CF.h_formula_view_name vname then
            try
              let view_fwd_para_pos, data_fwd_f_pos = look_up_fwd_ptr_pos pr_fwd_ptrs_pos hd.CF.h_formula_data_name in
              (* get para sv from view_fwd_para_pos *)
              let view_fwd_ptrs = Cfutil.retrieve_args_from_locs hv.CF.h_formula_view_arguments [view_fwd_para_pos] in
              (* get field sv from data_fwd_f_pos *)
              let dfield_fwd_ptrs = Cfutil.retrieve_args_from_locs hd.CF.h_formula_data_arguments [data_fwd_f_pos] in
              (* exchange root and fwd ptrs of hd, hv *)
              let sst_root = gen_sst_4_exchange_sv (hv.CF.h_formula_view_node, hd.CF.h_formula_data_node) in
              let sst_args = List.fold_left (fun r pr_sv -> r@(gen_sst_4_exchange_sv pr_sv)) [] ((List.combine view_fwd_ptrs dfield_fwd_ptrs)) in
              let rev_f0 = CF.formula_trans_heap_node (subst_h_root sst_root) f in
              let () = Debug.ninfo_hprint (add_str "rev_f0" Cprinter.prtt_string_of_formula) rev_f0 no_pos in
              let rev_f1 = CF.formula_trans_heap_node (subst_h_args sst_args) rev_f0 in
              let () = Debug.ninfo_hprint (add_str "rev_f1" Cprinter.prtt_string_of_formula) rev_f1 no_pos in
              [(rev_f1,p)]
            with _ -> []
          else []
        end
      | [hd1;hd2],[hv] -> begin
          if str_cmp hd1.CF.h_formula_data_name dname && str_cmp hd2.CF.h_formula_data_name dname && str_cmp hv.CF.h_formula_view_name vname then
            try
              let view_fwd_para_pos, data_fwd_f_pos = look_up_fwd_ptr_pos pr_fwd_ptrs_pos hd1.CF.h_formula_data_name in
              (* get para sv from view_fwd_para_pos *)
              let view_fwd_ptrs = Cfutil.retrieve_args_from_locs hv.CF.h_formula_view_arguments [view_fwd_para_pos] in
              (* get field sv from data_fwd_f_pos *)
              let dfield_fwd_ptrs1 = Cfutil.retrieve_args_from_locs hd1.CF.h_formula_data_arguments [data_fwd_f_pos] in
              (* let dfield_fwd_ptrs2 = Cfutil.retrieve_args_from_locs hd2.CF.h_formula_data_arguments [data_fwd_f_pos] in *)
              (* exchange root and fwd ptrs of hd, hv *)
              (* let sst_root1 = gen_sst_4_exchange_sv (hv.CF.h_formula_view_node, hd1.CF.h_formula_data_node) in *)
              (* let sst_root2 = gen_sst_4_exchange_sv (hd1.CF.h_formula_data_node, hd2.CF.h_formula_data_node) in *)
              (* let sst_root = sst_root1@sst_root2 in *)
              (* let sst_args = List.fold_left (fun r pr_sv -> r@(gen_sst_4_exchange_sv pr_sv)) [] ((List.combine view_fwd_ptrs dfield_fwd_ptrs1)) in *)
              let sst_root, sst_args = exchange_two hd1.CF.h_formula_data_node dfield_fwd_ptrs1
                  hv.CF.h_formula_view_node  view_fwd_ptrs  in
              let rev_f0 = CF.formula_trans_heap_node (subst_h_root sst_root) f in
              let () = Debug.ninfo_hprint (add_str "rev_f0" Cprinter.prtt_string_of_formula) rev_f0 no_pos in
              let rev_f1 = CF.formula_trans_heap_node (subst_h_args sst_args) rev_f0 in
              let () = Debug.ninfo_hprint (add_str "rev_f1" Cprinter.prtt_string_of_formula) rev_f1 no_pos in
              (* let sst_root2, sst_args2 = exchange_two hd1.CF.h_formula_data_node dfield_fwd_ptrs1 *)
              (*   hd2.CF.h_formula_data_node view_fwd_ptrs  in *)
              (* let rev_f20 = CF.formula_trans_heap_node (subst_h_root sst_root2) rev_f1 in *)
              (* let () = Debug.info_hprint (add_str "rev_f20" Cprinter.prtt_string_of_formula) rev_f20 no_pos in *)
              (* let rev_f21 = CF.formula_trans_heap_node (subst_h_args sst_args2) rev_f20 in *)
              (* let () = Debug.info_hprint (add_str "rev_f21" Cprinter.prtt_string_of_formula) rev_f21 no_pos in *)
              [(rev_f1,p)]
            with _ -> []
          else []
        end
      | _ -> []
    in
    (********************************************)
    let view_args = self_sv::vd.Cast.view_vars in
    let processed_brs = List.map (fun (f, lbl) ->
        let f1 = CF.elim_exists f in
        let _,new_f = CF.split_quantifiers f1 in
        (* let p,_,_ = x_add Cvutil.xpure_symbolic 20 cprog new_f in *)
        let p = CF.get_pure new_f in
        let p1 = CP.filter_var  p view_args in
        (new_f, p1)
      ) vd.C.view_un_struc_formula in
    let base_brs, indc_brs = List.partition(fun (f,p) ->
        let views = CF.get_views f in
        List.for_all (fun vn -> String.compare vname vn.CF.h_formula_view_name != 0) views
      ) processed_brs in
    if  base_brs = [] || indc_brs = [] || not vd.Cast.view_is_segmented
        (* retrict for one fwd ptr. to extend *)
        || List.length vd.Cast.view_forward_fields != 1
        (* not support backward yet. to extend *)
        || vd.Cast.view_backward_fields != []
    then [] else begin
      let lemma_name = "rev_"^vname in
      let base_p = CP.conj_of_list (List.map snd base_brs) no_pos in
      let neg_base_p = CP.mkNot_s base_p in
      let pr_fwd_ptrs = List.combine vd.Cast.view_forward_ptrs vd.Cast.view_forward_fields in
      let pr_fwd_ptrs_pos = List.fold_left (fun r pr -> r@(find_pos pr)) [] pr_fwd_ptrs in
      let rev_indc_brs = List.fold_left (fun r (f,p) ->
          let p = if (CP.isConstTrue p) && not (CP.isConstFalse neg_base_p) then neg_base_p else p in
          let rev_fs = rev_order pr_fwd_ptrs_pos (f,p) in
          r@rev_fs
        ) [] indc_brs in
      let i_coers = List.fold_left (fun r (f,p) ->
          let () = Debug.ninfo_hprint (add_str "p" Cprinter.string_of_pure_formula) p no_pos in
          let ihd = Rev_ast.rev_trans_formula (CF.mkAnd_pure view_f (Mcpure.mix_of_pure p) vpos) in
          let ibody = Rev_ast.rev_trans_formula f in
          let l_coer = I.mk_lemma (fresh_any_name lemma_name) LEM_SAFE LEM_GEN I.Left [] ihd ibody in
          r@[l_coer]
        ) [] rev_indc_brs in
      i_coers
    end

let generate_view_rev_rec_lemmas (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
  : (I.coercion_decl list) =
  let pr_v = !C.print_view_decl_short in
  let pr_out = pr_list Iprinter.string_of_coerc_decl in
  Debug.no_1 "generate_view_rev_rec_lemmas" pr_v pr_out
    (fun _ -> generate_view_rev_rec_lemmas_x vd iprog cprog) vd

let generate_all_lemmas (iprog: I.prog_decl) (cprog: C.prog_decl)
  : unit =
  let lemmas = List.concat (List.map (fun vd ->
      (* generate_lemma vd iprog cprog *)
      x_add generate_view_lemmas vd iprog cprog
    ) cprog.C.prog_view_decls) in
  let rev_rec_lemmas = List.concat (List.map (fun vd ->
      x_add generate_view_rev_rec_lemmas vd iprog cprog
    ) cprog.C.prog_view_decls) in
  let gen_lemmas = lemmas@rev_rec_lemmas in
  if (!Globals.lemma_gen_unsafe) || (!Globals.lemma_gen_unsafe_fold) then
    let todo_unk = manage_unsafe_lemmas (gen_lemmas) iprog cprog in ()
  else if (!Globals.lemma_gen_safe) || (!Globals.lemma_gen_safe_fold) then
    let todo_unk = manage_safe_lemmas gen_lemmas iprog cprog in ()
  else if (!Globals.lemma_rev_unsafe) then
    let todo_unk = manage_unsafe_lemmas rev_rec_lemmas iprog cprog in ()
  else ();
  let pr_lemmas lemmas = String.concat "\n" (List.map (fun lem ->
      "    " ^ (Cprinter.string_of_coerc_med lem)
    ) lemmas) in
  (* let () = print_endline "gen lemmas" in *)
  let () = Debug.ninfo_hprint (add_str "gen_lemmas" pr_lemmas)
      (Lem_store.all_lemma#get_left_coercion @ Lem_store.all_lemma#get_right_coercion)
      no_pos in
  (
  )


let () = Sleekcore.generate_lemma := generate_lemma_helper;;
let () = Solver.manage_unsafe_lemmas := manage_unsafe_lemmas;;
let () = Solver.manage_infer_pred_lemmas := manage_infer_pred_lemmas;;
