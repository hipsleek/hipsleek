open Globals
open Wrapper
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
(* module SC = Sleekcore *)
(* module LP = Lemproving *)
(* module SAO = Saout *)
(* module FP = Fixpoint *)

let infer_shapes = ref (fun (iprog: I.prog_decl) (cprog: C.prog_decl) (proc_name: ident)
  (hp_constrs: CF.hprel list) (sel_hp_rels: CP.spec_var list) (sel_post_hp_rels: CP.spec_var list)
  (hp_rel_unkmap: ((CP.spec_var * int list) * CP.xpure_view) list)
  (unk_hpargs: (CP.spec_var * CP.spec_var list) list)
  (link_hpargs: (int list * (Cformula.CP.spec_var * Cformula.CP.spec_var list)) list)
  (need_preprocess: bool) (detect_dang: bool) -> let a = ([] : CF.hprel list) in
  let b = ([] : CF.hp_rel_def list) in
  let c = ([] : CP.spec_var list) in
  (a, b, c)
)

let generate_lemma_helper iprog lemma_name coer_type ihps ihead ibody=
  (*generate ilemma*)
    let ilemma = I.mk_lemma (fresh_any_name lemma_name) LEM_UNSAFE LEM_GEN coer_type ihps ihead ibody in
    (*transfrom ilemma to clemma*)
    let ldef = Astsimp.case_normalize_coerc iprog ilemma in
    let l2r, r2l = Astsimp.trans_one_coercion iprog ldef in
    l2r, r2l

let generate_lemma iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody=
  (*check entailment*)
  let (res,_,_) =  if coer_type = I.Left then
    Sleekcore.sleek_entail_check 4 [] cprog [(chead,cbody)] lhs (CF.struc_formula_of_formula rhs no_pos)
  else Sleekcore.sleek_entail_check 5 [] cprog [(cbody,chead)] rhs (CF.struc_formula_of_formula lhs no_pos)
  in
  if res then
    let l2r, r2l = generate_lemma_helper iprog lemma_n coer_type [] ihead ibody in
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
    (subst_helper ss f, IF.mkBase ihf ip IF.top_flow [] pos,
    CF.mkBase chf (MCP.mix_of_pure cp) CF.TypeTrue (CF.mkNormalFlow()) [] pos)
  else if self_hns <> [] then
    let _ = report_warning no_pos ("Lemma.subst_cont: to handle") in
    (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)
  else (f, IF.formula_of_heap_1 ihf pos, CF.formula_of_heap chf pos)

(*if two views are equiv (subsume), generate an equiv (left/right) lemma*)
let check_view_subsume iprog cprog view1 view2 need_cont_ana=
  let v_f1 = CF.formula_of_disjuncts (List.map fst view1.C.view_un_struc_formula) in
  let v_f2 = CF.formula_of_disjuncts (List.map fst view2.C.view_un_struc_formula) in
  let v_f11 = (* CF.formula_trans_heap_node (hn_c_trans (view1.C.view_name, view2.C.view_name)) *) v_f1 in
  let pos1 = (CF.pos_of_formula v_f1) in
  let pos2 = (CF.pos_of_formula v_f2) in
  let ihf1 = IF.mkHeapNode (self, Unprimed) (view1.C.view_name)
    0  false  (IP.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view1.C.view_vars) []  None pos1 in
  let chf1 = CF.mkViewNode (CP.SpecVar (Named view1.C.view_name,self, Unprimed)) view1.C.view_name
    view1.C.view_vars no_pos in
  let ihf2 = IF.mkHeapNode (self, Unprimed) (view2.C.view_name)
    0  false (IP.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view2.C.view_vars) [] None pos2 in
  let chf2 = CF.mkViewNode (CP.SpecVar (Named view2.C.view_name,self, Unprimed)) view2.C.view_name
    view2.C.view_vars no_pos in
  let v_f1, v_f2, iform_hf1, cform_hf1, iform_hf2, cform_hf2=
    if not need_cont_ana then
      (v_f11, v_f2, IF.formula_of_heap_1 ihf1 pos1, CF.formula_of_heap chf1 pos1,
      IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
    else
      if List.length view1.C.view_vars > List.length view2.C.view_vars && view1.C.view_cont_vars != [] then
        (* let _ = print_endline ("xxx1") in *)
        let self_hds, self_null = final_inst_analysis_view cprog view2 in
        let v_f12, ihf_12, cform_chf12 = subst_cont view1.C.view_name view1.C.view_cont_vars
          v_f11 ihf1 chf1 self_hds self_null pos1 in
        (v_f12, v_f2, ihf_12, cform_chf12, IF.formula_of_heap_1 ihf2 pos2, CF.formula_of_heap chf2 pos2)
      else if List.length view2.C.view_vars > List.length view1.C.view_vars && view2.C.view_cont_vars != [] then
        (* let _ = print_endline ("xxx2") in *)
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
                  (* let _ = report_warning no_pos ("cont paras + final inst analysis " ^ (v.C.view_name) ^ " ..." ^ *)
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
  (* let _ = cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions in *)
  (* let _ = cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions in *)
  (l2r,r2l)

let generate_lemma_4_views iprog cprog=
  let pr1 cp = (pr_list_ln Cprinter.string_of_view_decl_short) cp.C.prog_view_decls in
  let pr2 = pr_list_ln Cprinter.string_of_coerc_short in
  Debug.no_1 "generate_lemma_4_views" pr1 (pr_pair pr2 pr2)
      (fun _ -> generate_lemma_4_views_x iprog cprog)
      cprog

(* ============================ lemma translation and store update================================= *)
(* Below are methods used for lemma transformation (ilemma->lemma), lemma proving and lemma store update *)


(* ilemma  ----> (left coerc list, right coerc list) *)
let process_one_lemma iprog cprog ldef = 
  let ldef = Astsimp.case_normalize_coerc iprog ldef in
  let l2r, r2l = Astsimp.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> Astsimp.coerc_spec cprog c) l2r) in
  let r2l = List.concat (List.map (fun c-> Astsimp.coerc_spec cprog c) r2l) in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then 
    let _ = print_string (Iprinter.string_of_coerc_decl ldef) in 
    let _ = print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") in
    () else () in
  (l2r,r2l,ldef.I.coercion_type)


(* ilemma repo ----> (left coerc list, right coerc list) *)
let process_one_repo repo iprog cprog = 
  List.map (fun ldef -> 
      let l2r,r2l,typ = process_one_lemma iprog cprog ldef in
      (l2r,r2l,typ,(ldef.I.coercion_name))
  ) repo

let verify_one_repo lems cprog = 
  let res = List.fold_left (fun ((fail_ans,res_so_far) as res) (l2r,r2l,typ,name) ->
      match fail_ans with
        | None ->
            let res = Lemproving.verify_lemma 3 l2r r2l cprog name typ in 
            let chk_for_fail =  if !Globals.disable_failure_explaining then CF.isFailCtx else CF.isFailCtx_gen in
            let res_so_far = res::res_so_far in
            let fail = if chk_for_fail res then Some (name^":"^(Cprinter.string_of_coercion_type typ)) else None in
            (fail, res_so_far)
            (* ((if CF.isFailCtx res then Some (name^":"^(Cprinter.string_of_coercion_type typ)) else None), res_so_far) *)
        | Some n ->
              res
  ) (None,[]) lems in
  res



(* update the lemma store with the lemmas in repo and check for their validity *)
let update_store_with_repo_x repo iprog cprog =
  let lems = process_one_repo repo iprog cprog in
  let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in
  let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in
  let _ = Lem_store.all_lemma # add_coercion left right in
  let (invalid_lem, lctx) =  verify_one_repo lems cprog in
  (invalid_lem, lctx)

let update_store_with_repo repo iprog cprog =
  let pr1 = pr_list Iprinter.string_of_coerc_decl in
  let pr_out = pr_pair (pr_opt pr_id) (pr_list Cprinter.string_of_list_context) in 
  Debug.no_1 "update_store_with_repo"  pr1 pr_out (fun _ -> update_store_with_repo_x repo iprog cprog) repo

(* pop only if repo is invalid *)
(* return None if all succeed, and result of first failure otherwise *)
let manage_safe_lemmas repo iprog cprog = 
  let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog in
  match invalid_lem with
    | Some name -> 
          let _ = Log.last_cmd # dumping (name) in
          let _ = if !Globals.lemma_ep then
            print_endline ("\nFailed to prove "^ (name) ^ " in current context.")
          else ()
          in
          Lem_store.all_lemma # pop_coercion;
          let _ = if !Globals.lemma_ep then
            print_endline_quiet ("Removing invalid lemma ---> lemma store restored.")
          else ()
          in
          Some([List.hd(nctx)])
    | None ->
          let lem_str = pr_list pr_id (List.map (fun i -> 
              i.I.coercion_name^":"^(Cprinter.string_of_coercion_type i.I.coercion_type)) repo) in
          let _ = if !Globals.lemma_ep then
            print_endline_quiet ("\nValid Lemmas : "^lem_str^" added to lemma store.")
          else ()
          in
          None

(* update store with given repo without verifying the lemmas *)
let manage_unsafe_lemmas repo iprog cprog: (CF.list_context list option) =
  let (left,right, lnames) = List.fold_left (fun (left,right,names) ldef -> 
      let l2r,r2l,typ = process_one_lemma iprog cprog ldef in
      (l2r@left,r2l@right,((ldef.I.coercion_name)::names))
  ) ([],[], []) repo in
  let _ = Lem_store.all_lemma # add_coercion left right in
  let _ = (* if  (!Globals.dump_lem_proc) then   *)
    Debug.binfo_hprint (add_str "\nUpdated lemma store with unsafe repo:" ( pr_list pr_id)) lnames no_pos (* else () *) in
  let _ = Debug.info_ihprint (add_str "\nUpdated store with unsafe repo." pr_id) "" no_pos in
  None

let manage_lemmas repo iprog cprog =
  if !Globals.check_coercions then manage_safe_lemmas repo iprog cprog 
  else manage_unsafe_lemmas repo iprog cprog 

(* update store with given repo, but pop it out in the end regardless of the result of lemma verification *)
(* let manage_test_lemmas repo iprog cprog orig_ctx =  *)
(*   let new_ctx = CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in  *)
(*   (\* what is the purpose of new_ctx? *\) *)
(*   let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog new_ctx in *)
(*   Lem_store.all_lemma # pop_coercion; *)
(*   let _  = match nctx with *)
(*     | CF.FailCtx _ ->  *)
(*           let _ = Log.last_cmd # dumping (invalid_lem) in *)
(*           print_endline ("\nFailed to prove "^(invalid_lem) ^ " ==> invalid repo in current context.") *)
(*     | CF.SuccCtx _ -> *)
(*           print_endline ("\nTemp repo proved valid in current context.") in *)
(*   let _ = print_endline ("Removing temp repo ---> lemma store restored.") in *)
(*   Some nctx *)


(* update store with given repo, but pop it out in the end regardless of the result of lemma verification *)
(* return None if all succeed, return first failed ctx otherwise *)
let manage_infer_lemmas str repo iprog cprog = 
  let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog in
  Lem_store.all_lemma # pop_coercion;
  match invalid_lem with
    | Some name -> 
          let _ = Log.last_cmd # dumping (name) in
          let _ = if !Globals.lemma_ep then
            print_endline ("\nFailed to "^str^" for "^ (name) ^ " ==> invalid lemma encountered.")
          else ()
          in
          false,Some([List.hd(nctx)])
    | None ->
          let _ = if !Globals.lemma_ep then
            print_endline ("\n Temp Lemma(s) "^str^" as valid in current context.")
          else ()
          in
          true,Some nctx

(* verify  a list of lemmas *)
(* if one of them fails, return failure *)
(* otherwise, return a list of their successful contexts 
   which may contain inferred result *)
let sa_verify_one_repo cprog l2r r2l = 
  let res = List.fold_left (fun ((valid_ans,res_so_far) as res) coer ->
      match valid_ans with
        | true ->
              let (flag,lc) = Lemproving.sa_verify_lemma cprog coer in 
              (flag, lc::res_so_far)
        | false -> res
  ) (true,[]) (l2r@r2l) in
  res

(* update the lemma store with the lemmas in repo and check for their validity *)
let sa_update_store_with_repo cprog l2r r2l =
   let _ = Lem_store.all_lemma # add_coercion l2r r2l in
   let (invalid_lem, lctx) =  sa_verify_one_repo cprog l2r r2l in
   (invalid_lem, lctx)

(* l2r are left to right_lemmas *)
(* r2l are right to right_lemmas *)
(* return None if some failure; return list of contexts if all succeeded *)
let sa_infer_lemmas iprog cprog lemmas  = 
  (* let (l2r,others) = List.partition (fun c -> c.C.coercion_type==I.Left) lemmas in  *)
  (* let (r2l,equiv) = List.partition (fun c -> c.C.coercion_type==I.Right) others in  *)
  (* let l2r = l2r@(List.map (fun c -> {c with C.coercion_type = I.Left} ) equiv) in *)
  (* let r2l = r2l@(List.map (fun c -> {c with C.coercion_type = I.Right} ) equiv) in *)
  (* let (valid_lem, nctx) = sa_update_store_with_repo cprog l2r r2l in *)
  (* Lem_store.all_lemma # pop_coercion; *)
  (* match valid_lem with *)
  (*   | false ->  *)
  (*         (\* let _ = Log.last_cmd # dumping (name) in *\) *)
  (*         let _ = Debug.tinfo_pprint ("\nFailed to prove a lemma ==> during sa_infer_lemmas.") no_pos in *)
  (*         None *)
  (*   | true -> Some nctx *)
  let (invalid_lem, nctx) = update_store_with_repo lemmas iprog cprog in
  Lem_store.all_lemma # pop_coercion;
   match invalid_lem with
    | Some name -> 
          let _ = Debug.tinfo_pprint ("\nFailed to prove a lemma ==> during sa_infer_lemmas.") no_pos in
          None
    | None ->
          Some nctx

let sa_infer_lemmas iprog cprog lemmas  =
  let pr1 = pr_list pr_none in
  Debug.no_1 "sa_infer_lemmas" pr1 pr_none (fun _ -> sa_infer_lemmas iprog cprog lemmas) lemmas

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
  let _ = Debug.ninfo_hprint (add_str "pre_fmls" (pr_list !CP.print_formula)) pre_fmls no_pos in
  let pre_rel_fmls = List.concat (List.map CF.get_pre_rels pre_fmls) in
  let pre_rel_fmls = List.filter (fun x -> CP.intersect (CP.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
  let pre_vnodes = CF.get_views bare in
  let ls_rel_args = CP.get_list_rel_args (CF.get_pure bare) in
  let _ = Debug.ninfo_hprint (add_str "coercion_body" !CF.print_formula) bare no_pos in
  (* let _ = Debug.info_hprint (add_str "pre_rel_ids" !CP.print_svl) pre_rel_ids no_pos in *)
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

let manage_infer_pred_lemmas repo iprog cprog xpure_fnc=
  let rec helper coercs rel_fixs hp_rels res_so_far=
    match coercs with
      | [] -> (rel_fixs, hp_rels, Some res_so_far)
      | coer::rest -> begin
          let lems = process_one_repo [coer] iprog cprog in
          let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in
          let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in
          let _ = Lem_store.all_lemma # add_coercion left right in
          let (invalid_lem, lcs) =  verify_one_repo lems cprog in
          Lem_store.all_lemma # pop_coercion;
          match invalid_lem with
            | None ->
                  let hprels = List.fold_left (fun r_ass lc -> r_ass@(Infer.collect_hp_rel_list_context lc)) [] lcs in
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
                  let rl, lshapes =
                    if left = [] then [],[] else
                      (*shape*)
                      let post_hps, post_rel_ids, sel_hps, rel_ids = match left  with
                        | [] -> [],[],[],[]
                        | [coer] -> (CP.remove_dups_svl (CF.get_hp_rel_name_formula coer.C.coercion_body),
                          CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_body))),
                          List.filter (fun sv -> CP.is_hprel_typ sv) coer.C.coercion_infer_vars,
                          List.filter (fun sv -> CP.is_rel_typ sv) coer.C.coercion_infer_vars
                          )
                        | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas"
                      in
                      let lshape = if sel_hps = [] || hp_lst_assume = [] then [] else
                        let _, hp_defs, _ = !infer_shapes iprog cprog "temp" hp_lst_assume sel_hps post_hps
                          [] [] [] true true in
                        hp_defs
                      in
                      (*pure fixpoint*)
                      let rl = if rel_ids = [] || oblgs = [] then [] else
                        let pre_invs, pre_rel_oblgs, post_rel_oblgs = partition_pure_oblgs oblgs post_rel_ids in
                        let proc_spec = CF.mkETrue_nf no_pos in
                        let pre_rel_ids = CP.diff_svl rel_ids post_rel_ids in
                        let r = Fixpoint.rel_fixpoint_wrapper pre_invs [] pre_rel_oblgs post_rel_oblgs pre_rel_ids post_rel_ids proc_spec 1 in
                        let _ = Debug.info_hprint (add_str "fixpoint"
                            (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in
                        let _ = print_endline "" in
                        r
                      in
                      rl,lshape
                  in
                  (*right*)
                  (*shape*)
                  let rr,rshapes = if right = [] then [],[] else
                    let post_hps, post_rel_ids, sel_hps, rel_ids = match right  with
                      | [] -> [],[],[],[]
                      | [coer] -> (CP.remove_dups_svl (CF.get_hp_rel_name_formula coer.C.coercion_head),
                        CP.remove_dups_svl (List.map fst (CP.get_list_rel_args (CF.get_pure coer.C.coercion_head))),
                        List.filter (fun sv -> CP.is_hprel_typ sv) coer.C.coercion_infer_vars,
                        List.filter (fun sv -> CP.is_rel_typ sv) coer.C.coercion_infer_vars
                        )
                      | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas 2"
                    in
                    let hp_defs = if sel_hps = [] || hp_lst_assume = [] then [] else
                      let _, hp_defs,_ = !infer_shapes iprog cprog "temp" hp_lst_assume sel_hps post_hps
                        [] [] [] true true in
                      hp_defs
                    in
                    (* let _ = print_endline ("\nxxxxxx " ^ ((pr_list_ln Cprinter.string_of_list_context) lcs)) in *)
                    (*pure fixpoint*)
                    let rr = if rel_ids = [] || oblgs = [] then [] else
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
                              let _ = Debug.ninfo_hprint (add_str "pre_fmls" (pr_list !CP.print_formula)) pre_fmls no_pos in
                              let pre_rel_fmls = List.concat (List.map CF.get_pre_rels pre_fmls) in
                              let pre_rel_fmls = List.filter (fun x -> CP.intersect (CP.get_rel_id_list x) inf_vars != []) pre_rel_fmls in
                              let pre_vnodes = CF.get_views coer.C.coercion_body in
                              let ls_rel_args = CP.get_list_rel_args (CF.get_pure bare) in
                              let _ = Debug.ninfo_hprint (add_str "coercion_body" !CF.print_formula) bare no_pos in
                              (* let _ = Debug.info_hprint (add_str "pre_rel_ids" !CP.print_svl) pre_rel_ids no_pos in *)
                              let pre_rel_args = List.fold_left (fun r (rel_id,args)-> if CP.mem_svl rel_id pre_rel_ids then r@args
                              else r
                              ) [] ls_rel_args in
                              let invs = List.map (Fixpoint.get_inv cprog pre_rel_args) pre_vnodes in
                              let rel_fm = CP.filter_var (CF.get_pure bare) pre_rel_args in
                              let inv = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) rel_fm (pre_invs@invs) in
                              [inv],pre_fmls,grp_post_rel_flag
                        | _ -> report_error no_pos "LEMMA: manage_infer_pred_lemmas 3"
                      in
                      let r = Fixpoint.rel_fixpoint_wrapper pre_inv_ext pre_fmls pre_rel_oblgs post_rel_oblgs pre_rel_ids post_rel_ids proc_spec grp_post_rel_flag in
                      let _ = Debug.info_hprint (add_str "fixpoint"
                          (let pr1 = Cprinter.string_of_pure_formula in pr_list_ln (pr_quad pr1 pr1 pr1 pr1))) r no_pos in
                      let _ = print_endline "" in
                      r
                    in
                    (rr,hp_defs)
                  in
                  (* let _=  print_endline "*************************************" in *)
                   helper rest (rel_fixs@rl@rr) (hp_rels@lshapes@rshapes) (res_so_far@lcs)
            | Some _ -> (rel_fixs,hp_rels, None)
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
  let _ = List.map (fun (rel_name, rel_f) ->
      let rel_args_opt = CP.get_relargs_opt rel_name in
      match rel_args_opt with
        | Some (rel, args) ->
              let _= Smtsolver.add_relation (CP.name_of_spec_var rel) args rel_f in
              ()
        | None -> report_error no_pos "Lemma.manage_infer_pred_lemmas: should rel name"
  ) rel_defs in
  let n_hp_defs = List.map (fun hp_def -> Cfutil.subst_rel_def_4_hpdef hp_def rel_defs) hp_defs in
  (rec_fixs, n_hp_defs, ls_opt)

(* for lemma_test, we do not return outcome of lemma proving *)
let manage_test_lemmas repo iprog cprog = 
  manage_infer_lemmas "proved" repo iprog cprog; None (*Loc: while return None? instead full result*)

let manage_test_lemmas1 repo iprog cprog = 
  manage_infer_lemmas "proved" repo iprog cprog

let manage_infer_lemmas repo iprog cprog = 
   (manage_infer_lemmas "inferred" repo iprog cprog)

(* verify given repo in a fresh store. Revert the store back to it's state prior to this method call *)
(* let manage_test_new_lemmas repo iprog cprog ctx =  *)
(*   let left_lems = Lem_store.all_lemma # get_left_coercion in *)
(*   let right_lems = Lem_store.all_lemma # get_right_coercion in *)
(*   let _ = Lem_store.all_lemma # set_coercion [] [] in *)
(*   let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog ctx in *)
(*   let _ = Lem_store.all_lemma # set_left_coercion left_lems in *)
(*   let _ = Lem_store.all_lemma # set_right_coercion right_lems in *)
(*   let _ = match nctx with  *)
(*     | CF.FailCtx _ ->  *)
(*           let _ = Log.last_cmd # dumping (invalid_lem) in *)
(*           print_endline ("\nFailed to prove "^ (invalid_lem) ^ " ==> invalid repo in fresh context.") *)
(*     | CF.SuccCtx _ -> *)
(*           print_endline ("\nTemp repo proved valid in fresh context.") in *)
(*   print_endline ("Removing temp repo ---> lemma store restored."); *)
(*   Some ctx *)

(* verify given repo in a fresh store. Revert the store back to it's state prior to this method call *)
let manage_test_new_lemmas repo iprog cprog = 
   let left_lems = Lem_store.all_lemma # get_left_coercion in
   let right_lems = Lem_store.all_lemma # get_right_coercion in
   let _ = Lem_store.all_lemma # set_coercion [] [] in
   let res = manage_test_lemmas repo iprog cprog in
   let _ = Lem_store.all_lemma # set_left_coercion left_lems in
   let _ = Lem_store.all_lemma # set_right_coercion right_lems in
   res

let manage_test_new_lemmas1 repo iprog cprog = 
   let left_lems = Lem_store.all_lemma # get_left_coercion in
   let right_lems = Lem_store.all_lemma # get_right_coercion in
   let _ = Lem_store.all_lemma # clear_left_coercion in
   let _ = Lem_store.all_lemma # clear_right_coercion in
   let res = manage_test_lemmas1 repo iprog cprog in
   let _ = Lem_store.all_lemma # set_left_coercion left_lems in
   let _ = Lem_store.all_lemma # set_right_coercion right_lems in
   res

(* ==================================== *)
let process_list_lemma_helper_x ldef_lst iprog cprog lem_infer_fnct =
  let lst = ldef_lst.Iast.coercion_list_elems in
  (* why do we check residue for ctx? do we really need a previous context? *)
  let enable_printing = (!Globals.dump_lem_proc) && ( List.length lst > 0 ) in
  (* let _ = if enable_printing then Debug.binfo_pprint "=============== Processing lemmas ===============" no_pos else () in *)
  let ctx = match !CF.residues with
    | None            ->  CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos]
    | Some (CF.SuccCtx ctx, _) -> CF.SuccCtx ctx 
    | Some (CF.FailCtx ctx, _) -> CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in 
  (* andreeac: to check if it should skip lemma proving *)
  let res = 
    match ldef_lst.Iast.coercion_list_kind with
      | LEM            -> manage_lemmas lst iprog cprog 
      | LEM_TEST       -> (manage_test_lemmas lst iprog cprog )
      | LEM_TEST_NEW   -> (manage_test_new_lemmas lst iprog cprog )
      | LEM_UNSAFE     -> manage_unsafe_lemmas lst iprog cprog 
      | LEM_SAFE       -> manage_safe_lemmas lst iprog cprog 
      | LEM_INFER      -> snd (manage_infer_lemmas lst iprog cprog)
      | LEM_INFER_PRED      -> let r1,_,r2 = manage_infer_pred_lemmas lst iprog cprog Cvutil.xpure_heap in 
        let _ = lem_infer_fnct r1 r2 in
        r2
  in
  (* let _ = if enable_printing then Debug.binfo_pprint "============ end - Processing lemmas ============\n" no_pos else () in *)
  match res with
    | None | Some [] -> CF.clear_residue ()
    | Some(c::_) -> CF.set_residue true c

let process_list_lemma_helper ldef_lst iprog cprog lem_infer_fnct  =
  Debug.no_1 "process_list_lemma" pr_none pr_none (fun _ -> process_list_lemma_helper_x ldef_lst iprog cprog lem_infer_fnct )  ldef_lst

(* ============================ END --- lemma translation and store update================================= *)


let do_unfold_view_hf cprog hf0 =
  let fold_fnc ls1 ls2 aux_fnc = List.fold_left (fun r (hf2, p2) ->
      let in_r = List.map (fun (hf1, p1) ->
          let nh = aux_fnc hf1 hf2 in
          let _ = Debug.info_hprint (add_str "        p1:" !CP.print_formula) (MCP.pure_of_mix p1) no_pos in
          let _ = Debug.info_hprint (add_str "        p2:" !CP.print_formula) (MCP.pure_of_mix p2) no_pos in
          let qvars1, bare1 = CP.split_ex_quantifiers (MCP.pure_of_mix p1) in
          let qvars2, bare2 = CP.split_ex_quantifiers (MCP.pure_of_mix p2) in
          let _ = Debug.info_hprint (add_str "        bare1:" !CP.print_formula) bare1 no_pos in
          let _ = Debug.info_hprint (add_str "        bare2:" !CP.print_formula) bare2 no_pos in
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
              let vdcl = C.look_up_view_def_raw 40 cprog.C.prog_view_decls hv.CF.h_formula_view_name in
              let fs = List.map fst vdcl.C.view_un_struc_formula in
              let f_args = (CP.SpecVar (Named vdcl.C.view_name,self, Unprimed))::vdcl.C.view_vars in
              let a_args = hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments in
              let ss = List.combine f_args  a_args in
              let fs1 = List.map (CF.subst ss) fs in
              List.map (fun f -> (List.hd (CF.heap_of f), MCP.mix_of_pure (CF.get_pure f))) fs1
            with _ -> let _ = report_warning no_pos ("LEM.do_unfold_view_hf: can not find view " ^ hv.CF.h_formula_view_name) in
            [(CF.HTrue, MCP.mix_of_pure (CP.mkTrue no_pos))]
      end
      | CF.ThreadNode _
      | CF.DataNode _  | CF.HRel _ | CF.Hole _ | CF.FrmHole _
      | CF.HTrue  | CF.HFalse | CF.HEmp -> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
  in
  helper hf0

let do_unfold_view_x cprog (f0: CF.formula) =
  let rec helper f=
  match f with
    | CF.Base fb ->
          let ls_hf_pure = do_unfold_view_hf cprog fb.CF.formula_base_heap in
          let fs = List.map (fun (hf, p) ->
              let _ = Debug.ninfo_hprint (add_str "        p:" !CP.print_formula) (MCP.pure_of_mix p) no_pos in
              let qvars0, bare_f = CP.split_ex_quantifiers_ext (CP.elim_exists (MCP.pure_of_mix  p)) in
               let _ = Debug.ninfo_hprint (add_str "        bare_f:" !CP.print_formula) bare_f no_pos in
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


(* Trung: need rename *)
type lemma_param_property =
  | LemmaParamEqual
  | LemmaParamDistributive
  | LemmaParamUnknown

let compute_lemma_params_property (vd: C.view_decl) (prog: C.prog_decl)
    : (CP.spec_var * lemma_param_property) list =
  let pos = vd.C.view_pos in
  (* find recursive view in each branch *)
  let rec collect_recursive_view hf = (match hf with
    | CF.ViewNode vn ->
        if (String.compare vn.CF.h_formula_view_name vd.C.view_name = 0) then
          [vn]
        else []
    | CF.Star sf ->
        let h1 = sf.CF.h_formula_star_h1 in
        let h2 = sf.CF.h_formula_star_h2 in
        (collect_recursive_view h1) @ (collect_recursive_view h2)
    
    | CF.HTrue | CF.HFalse | CF.HEmp -> []
    | CF.DataNode _ -> []
    | _ -> report_error pos "compute_lemma_params_property: unexpected formula"
  ) in
  (* find base branch and inductive branch *)
  let base_branches, inductive_branches = List.partition(fun (branch, _) ->
    let (hf,_,_,_,_) = CF.split_components branch in
    let views = collect_recursive_view hf in
    (List.length views = 0)
  ) vd.C.view_un_struc_formula in
  let param_branches = List.map2 (fun (branch,_) (aux_f,_) ->
    let (hf,_,_,_,_) = CF.split_components branch in
    let views = collect_recursive_view hf in
    match views with
    | [] -> []
    | [vn] ->
        let (_,aux_mf,_,_,_) = CF.split_components aux_f in
        let aux_pf = MCP.pure_of_mix aux_mf in
        List.map2 (fun sv1 sv2 ->
          let e1 = CP.mkVar sv1 pos in
          let e2 = CP.mkVar sv2 pos in
          let equal_cond = CP.mkEqExp e1 e2 pos in
          if (Tpdispatcher.imply_raw aux_pf equal_cond) then
            LemmaParamEqual
          else match (CP.type_of_spec_var sv1) with
          | BagT _ ->
              let subset_cond = CP.mkBagSubExp e2 e1 pos in
              if (Tpdispatcher.imply_raw aux_pf subset_cond) then
                LemmaParamDistributive
              else LemmaParamUnknown
          | Int ->
              (* exists k: forall sv1, sv2: aux_pf implies (sv1 - sv2 = k) *)
              let distributive_cond = (
                let diff_var = CP.SpecVar(Int, fresh_name (), Unprimed) in
                let diff_exp = CP.mkVar diff_var pos in
                let imply_cond = 
                  CP.mkOr (CP.mkNot aux_pf None pos)
                          (CP.mkEqExp (CP.mkSubtract e1 e2 pos) diff_exp pos)
                          None pos
                in
                CP.mkExists [diff_var] (CP.mkForall [sv1;sv2] imply_cond None pos) None pos 
              ) in
              if not(Tpdispatcher.imply_raw distributive_cond (CP.mkFalse pos)) then
                LemmaParamDistributive
              else LemmaParamUnknown
          | _ -> LemmaParamUnknown
        ) vd.C.view_vars vn.CF.h_formula_view_arguments
    | _ -> report_error pos "compute_lemma_params_property: expect at most 1 view node"
  ) vd.C.view_un_struc_formula vd.C.view_aux_formula in
  let param_properties = List.fold_left (fun res param_branch ->
    match res with
    | [] -> param_branch
    | _ -> 
        try List.map2 (fun x y -> if (x=y) then x else LemmaParamUnknown) res param_branch
        with _ -> report_error pos "compute_lemma_params_property: expect 2 list has same size"
  ) [] param_branches in
  List.map2 (fun sv p -> (sv,p)) vd.C.view_vars param_properties 

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

let collect_subs_from_view_node_x (vn: CF.h_formula_view) (vd: C.view_decl)
    : (CP.spec_var * CP.spec_var) list =
  let view_type = Named vd.C.view_data_name in
  let self_var = CP.SpecVar (view_type, self, Unprimed) in
  let subs = [(self_var, vn.CF.h_formula_view_node)] in
  let subs = List.fold_left2 (fun subs sv1 sv2 ->
    subs @ [(sv1, sv2)]
  ) subs vd.C.view_vars vn.CF.h_formula_view_arguments in
  subs

let collect_subs_from_view_node (vn: CF.h_formula_view) (vd: C.view_decl)
    : (CP.spec_var * CP.spec_var) list =
  let pr_subs = pr_list (fun (x,y) -> 
    "(" ^ (CP.name_of_spec_var x) ^ "," ^ (CP.name_of_spec_var y) ^ ")"
  ) in
  let pr_vn vn = !CF.print_h_formula (CF.ViewNode vn) in
  Debug.no_1 "collect_subs_from_view_node" pr_vn pr_subs
    (fun _ -> collect_subs_from_view_node_x vn vd) vn

let collect_subs_from_view_base_case_x (f: CF.formula) (vd: C.view_decl)
    : (CP.spec_var * CP.spec_var) list =
  let is_view_var v = (
    List.exists (fun sv -> CP.eq_spec_var v sv) vd.C.view_vars
  ) in
  let is_self v = String.compare (CP.name_of_spec_var v) self = 0 in
  let subs_list = ref [] in
  let f_e_f _ = None in
  let f_f _ = None in
  let f_h_f _ = None in
  let f_m mp = Some mp in
  let f_a _ = None in
  let f_pf pf = None in
  let f_b bf= (
    let pf, a = bf in
    match pf with
    | CP.Eq (CP.Var (sv1, _), CP.Var(sv2, _), _) ->
        let new_subs = (
          (* in tail-recursive predicates, self must be substituted *)
          if (is_self sv1) then (
            if (vd.C.view_is_tail_recursive) then [(sv1,sv2)]
            else [(sv2,sv1)]
          )
          else if (is_self sv2) then (
            if (vd.C.view_is_tail_recursive) then [(sv2,sv1)]
            else [(sv1,sv2)]
          )
          (* otherwise only subs a view var by a non-view var *)
          else if (is_view_var sv1) && (not (is_view_var sv2)) then
            [(sv1,sv2)]
          else if (is_view_var sv2) && (not (is_view_var sv1)) then
            [(sv2,sv1)]
          else []
        ) in
        let _ = subs_list := !subs_list @ new_subs in
        (Some (pf,a))
    | _ -> None
  ) in
  let f_e _ = None in
  let _ = CF.transform_formula (f_e_f, f_f, f_h_f, (f_m, f_a, f_pf, f_b, f_e)) f in
  !subs_list

let collect_subs_from_view_base_case (f: CF.formula) (vd: C.view_decl)
    : (CP.spec_var * CP.spec_var) list =
  let pr_f = !CF.print_formula in
  let pr_out = pr_list (fun (x,y) -> 
    "(" ^ (CP.name_of_spec_var x) ^ "," ^ (CP.name_of_spec_var y) ^ ")"
  ) in
  Debug.no_1 "collect_subs_from_view_base_case" pr_f pr_out
      (fun _ -> collect_subs_from_view_base_case_x f vd) f

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
        let _ = (
          if (String.compare vn.CF.h_formula_view_name vd.C.view_name = 0) then
            view_nodes := !view_nodes @ [vn];
        ) in
        Some hf
    | CF.HTrue | CF.HFalse | CF.HEmp | CF.DataNode _ -> Some hf
    | _ -> None
  ) in
  let _ = CF.transform_h_formula f_hf hf in
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
          let _ = (
            if List.exists (fun v -> String.compare v hnode = 0) view_vars then (
              try 
                let _ = List.find (fun subs ->
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
    let _ = IF.transform_h_formula collect_subs_list hf in
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

(* let generate_distributive_lemmas (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl) = *)
  

let generate_view_lemmas_x (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
    : (I.coercion_decl list) =
  (* find base branch and inductive branch *)
  let vpos = vd.C.view_pos in
  let vname = vd.C.view_name in
  let dname = vd.C.view_data_name in
  let ddecl = I.look_up_data_def_raw iprog.I.prog_data_decls dname in
  let processed_branches = List.map (fun (f, lbl) ->
    let new_f = CF.elim_exists f in
    (new_f, lbl)
  ) vd.C.view_un_struc_formula in
  let base_branches, inductive_branches = List.partition(fun (f, _) ->
    let (hf,_,_,_,_) = CF.split_components f in
    let views = collect_inductive_view_nodes hf vd in
    (List.length views = 0)
  ) processed_branches in
  (* consider only the view has 1 base case and 1 inductive case *)
  if ((List.length base_branches != 1) || (List.length inductive_branches != 1)) then (
    Debug.binfo_pprint ("generate_view_lemmas: no lemma is generated! 1") no_pos;
    []
  )
  (* consider only the view has 1 forward pointer *)
  else if (List.length vd.C.view_forward_ptrs != 1) then (
    Debug.binfo_pprint ("generate_view_lemmas: no lemma is generated! 2") no_pos;
    []
  )
  (* statisfying view *)
  else (
    let forward_ptr = List.hd vd.C.view_forward_ptrs in
    let base_f, base_lbl = List.hd base_branches in
    let induct_f, induct_lbl = List.hd inductive_branches in
    let (induct_hf, _, _, _, _) = CF.split_components induct_f in
    let view_nodes = collect_inductive_view_nodes induct_hf vd in
    let induct_vnodes = List.filter (fun vn ->
      String.compare vn.CF.h_formula_view_name vname = 0
    ) view_nodes in
    if (List.length induct_vnodes != 1) then (
      Debug.binfo_pprint ("generate_view_lemmas: no lemma is generated! 3") no_pos;
      []
    )
    else (
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
          IF.mkHeapNode head_node (vd.C.view_name)
              0 false  (IP.ConstAnn Mutable) false false false None
              head_params [] None vpos
        ) in
        Iformula.mkBase head (Ipure.mkTrue vpos) Iformula.top_flow [] vpos
      ) in
      let lem_body_heap = (
        let induct_vnode = List.hd induct_vnodes in
        let v_subs = collect_subs_from_view_node induct_vnode vd in
        let new_base_f = CF.subst_one_by_one v_subs base_f in
        Debug.ninfo_hprint (add_str "new_base_f" (!CF.print_formula)) new_base_f vpos;
        let b_subs = collect_subs_from_view_base_case new_base_f vd in


        (* compute pred2 *)
        let pred2_node = (match induct_vnode.CF.h_formula_view_node with
          | CP.SpecVar (_,vname,vprim) -> (vname,vprim)
        ) in
        let pred2_params = List.map (fun sv ->
          let vname, vprim = CP.name_of_spec_var sv, CP.primed_of_spec_var sv in
          IP.Var ((vname,vprim), vpos)
        ) induct_vnode.CF.h_formula_view_arguments in
        let pred2 = (
          (* this is the original hformula view *)
          IF.mkHeapNode pred2_node (vd.C.view_name)
              0 false (IP.ConstAnn Mutable) false false false None
              pred2_params [] None vpos 
        ) in

        (* compute pred1 *)
        let pred1_node = (
          if not (vd.C.view_is_tail_recursive) then (self, Unprimed)
          else (
            let subs_sv = CF.subst_one_by_one_var v_subs forward_ptr in
            match subs_sv with
            | CP.SpecVar (_,name,prim) -> (name,prim)
          )
        ) in
        (* check if new_induct_f can imply a view node *)
        (* we can have the distributive lemma only when the new_induct_f can form a view node *)
        let is_pred1_ok = (
          let reduced_induct_f = remove_view_node_from_formula induct_f induct_vnode in
          let new_induct_f = CF.subst b_subs reduced_induct_f in
          (* let (hf,mf,fl,t,a) = CF.split_components new_induct_f in *)
          (* let pos = CF.pos_of_formula new_induct_f in              *)
          (* let new_induct_f = CF.mkBase hf mf t fl a pos in         *)
          let tmp_nname, tmp_nprim = pred1_node in
          let tmp_vnode = CP.SpecVar (Named dname, tmp_nname, tmp_nprim) in
          let tmp_vars = List.map (fun sv -> 
            match sv with
            | CP.SpecVar (t,_,_) -> CP.SpecVar (t, fresh_name (), Unprimed)
          ) vd.C.view_vars in
          let tmp_vnode = CF.mkViewNode tmp_vnode vname tmp_vars no_pos in
          let tmp_f = CF.mkExists tmp_vars tmp_vnode (MCP.mkMTrue vpos)
              CF.TypeTrue (CF.mkTrueFlow ()) [] vpos in 
          let tmp_sf = CF.struc_formula_of_formula tmp_f vpos in 
          (* let tmp_f = CF.struc_formula_of_formula (CF.formula_of_heap tmp_vnode vpos) vpos in *)
          Debug.ninfo_hprint (add_str "new_induct_f" (!CF.print_formula)) new_induct_f vpos;
          Debug.ninfo_hprint (add_str "tmp_sf" (!CF.print_struc_formula)) tmp_sf vpos;
          let (r,_,_) = wrap_classic (Some true) 
              (Sleekcore.sleek_entail_check 9 [] cprog [] new_induct_f) tmp_sf in
          Debug.ninfo_pprint ("new_induct_f |- tmp_sf: " ^ (string_of_bool r)) vpos;
          r
        ) in
        if not (is_pred1_ok) then None
        else (
          let pred1_params = List.map (fun sv ->
            if (CP.eq_spec_var sv forward_ptr) then 
              let vname, vprim = pred2_node in
              IP.Var ((vname,vprim), vpos)
            else
              let param = (
                try 
                  let svs = List.find (fun (x,_) -> CP.eq_spec_var sv x) b_subs in
                  snd svs
                with _ -> sv
              ) in
              match param with
              | CP.SpecVar (_,vname,vprim) -> IP.Var ((vname,vprim), vpos)
          ) vd.C.view_vars in
          let pred1 = (
            (* this is a derived hformula view *)
            IF.mkHeapNode pred1_node (vd.C.view_name)
                0 false (IP.ConstAnn Mutable) true false false None
                pred1_params [] None vpos 
          ) in
          
          let body_heap = (
            if vd.C.view_is_tail_recursive then Iformula.mkStar pred2 pred1 vpos
            else Iformula.mkStar pred1 pred2 vpos
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
          Debug.binfo_pprint ("generate_view_lemmas: no lemma is generated! 4") no_pos;
          []
      | Some lem_body_hf -> (
          let llem_body_hf = lem_body_hf in
          let rlem_body_hf = (
            if (vd.C.view_is_touching) then lem_body_hf
            else (
              let fwp_name = CP.name_of_spec_var forward_ptr in
              (* lemma for non-touching predicates also borrow a @L node *)
              let lending_node =
                let params = List.map (fun _ ->
                  Ipure_D.Var((fresh_name (), Unprimed), vpos)
                ) ddecl.I.data_fields in
                IF.mkHeapNode (fwp_name, Unprimed) dname
                    0 false  (IP.ConstAnn Lend) false false false None
                    params [] None vpos
              in
              Iformula.mkStar lem_body_hf lending_node vpos
            )
          ) in
          let llemma_name = "llem_" ^ vd.C.view_name in
          let rlemma_name = "rlem_" ^ vd.C.view_name in
          let true_pf = Ipure.mkTrue vpos in
          let llem_body = Iformula.mkBase llem_body_hf true_pf Iformula.top_flow [] vpos in
          let rlem_body = Iformula.mkBase rlem_body_hf true_pf Iformula.top_flow [] vpos in
          let left_coerc = Iast.mk_lemma llemma_name LEM_SAFE LEM_GEN Iast.Left [] lem_head llem_body in
          let right_coerc = Iast.mk_lemma rlemma_name LEM_SAFE LEM_GEN Iast.Right [] lem_head rlem_body in
          if (!Globals.lemma_gen_safe_fold || !Globals.lemma_gen_unsafe_fold) then
            [right_coerc]
          else [left_coerc; right_coerc]
        )
    )
  )

let generate_view_lemmas (vd: C.view_decl) (iprog: I.prog_decl) (cprog: C.prog_decl)
    : (I.coercion_decl list) =
  let pr_v = !C.print_view_decl in
  let pr_out = pr_list Iprinter.string_of_coerc_decl in
  Debug.no_1 "generate_view_lemmas" pr_v pr_out
      (fun _ -> generate_view_lemmas_x vd iprog cprog) vd

let generate_all_lemmas (iprog: I.prog_decl) (cprog: C.prog_decl)
    : unit =
  let lemmas = List.concat (List.map (fun vd ->
    (* generate_lemma vd iprog cprog *)
    generate_view_lemmas vd iprog cprog
  ) cprog.C.prog_view_decls) in
  if (!Globals.lemma_gen_unsafe) || (!Globals.lemma_gen_unsafe_fold) then
    let _ = manage_unsafe_lemmas lemmas iprog cprog in ()
  else if (!Globals.lemma_gen_safe) || (!Globals.lemma_gen_safe_fold) then
    let _ = manage_safe_lemmas lemmas iprog cprog in ()
  else ();
  let pr_lemmas lemmas = String.concat "\n" (List.map (fun lem ->
     "    " ^ (Cprinter.string_of_coerc_med lem)
  ) lemmas) in
  (* let _ = print_endline "gen lemmas" in *)
  let _ = Debug.ninfo_hprint (add_str "gen_lemmas" pr_lemmas)
      (Lem_store.all_lemma#get_left_coercion @ Lem_store.all_lemma#get_right_coercion)
      no_pos in
  ()

let _ = Sleekcore.generate_lemma := generate_lemma_helper;;
let _ = Solver.manage_unsafe_lemmas := manage_unsafe_lemmas;;
let _ = Solver.manage_infer_pred_lemmas := manage_infer_pred_lemmas;;
