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
module LP = Lemproving
module SAO = Saout


let generate_lemma_helper iprog lemma_name coer_type ihps ihead ibody=
  (*generate ilemma*)
    let ilemma = I.mk_lemma (fresh_any_name lemma_name) coer_type ihps ihead ibody in
    (*transfrom ilemma to clemma*)
    let ldef = AS.case_normalize_coerc iprog ilemma in
    let l2r, r2l = AS.trans_one_coercion iprog ldef in
    l2r, r2l

let generate_lemma iprog cprog lemma_n coer_type lhs rhs ihead chead ibody cbody=
  (*check entailment*)
  let (res,_,_) =  if coer_type = I.Left then
    SC.sleek_entail_check [] cprog [(chead,cbody)] lhs (CF.struc_formula_of_formula rhs no_pos)
  else SC.sleek_entail_check [] cprog [(cbody,chead)] rhs (CF.struc_formula_of_formula lhs no_pos)
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


(* Below are methods used for lemma transformation (ilemma->lemma), lemma proving and lemma store update *)


(* ilemma  ----> (left coerc list, right coerc list) *)
let process_one_lemma iprog cprog ldef = 
  let ldef = AS.case_normalize_coerc iprog ldef in
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
  let l2r = List.concat (List.map (fun c-> AS.coerc_spec cprog c) l2r) in
  let r2l = List.concat (List.map (fun c-> AS.coerc_spec cprog c) r2l) in
  let _ = if (!Globals.print_input || !Globals.print_input_all) then 
    let _ = print_string (Iprinter.string_of_coerc_decl ldef) in 
    let _ = print_string ("\nleft:\n " ^ (Cprinter.string_of_coerc_decl_list l2r) ^"\n right:\n"^ (Cprinter.string_of_coerc_decl_list r2l) ^"\n") in
    () else () in
  (l2r,r2l,ldef.I.coercion_type)


let lst_to_opt l = 
  match l with
    | [c] -> Some c
    | _   -> None

(* ilemma repo ----> (left coerc list, right coerc list) *)
let process_one_repo repo iprog cprog = 
  List.map (fun ldef -> 
      let l2r,r2l,typ = process_one_lemma iprog cprog ldef in
      (l2r,r2l,typ,(ldef.I.coercion_name))
  ) repo


(* verify all the lemmas in one repo *)
(* let verify_one_repo lems cprog ctx =  *)
(*   let nm = ref "" in *)
(*   let nlctx = ref ctx in *)
(*   let _ = List.exists (fun (l2r,r2l,typ,name) ->  *)
(*       let res = LP.verify_lemma 3 (lst_to_opt l2r) (lst_to_opt r2l) !nlctx cprog name typ in  *)
(*       nlctx := res; *)
(*       match res with *)
(*         | CF.FailCtx _  -> nm := name; true *)
(*         | CF.SuccCtx _  ->  false *)
(*   ) lems in *)
(*   (!nm, !nlctx) *)
let verify_one_repo lems cprog = 
  let res = List.fold_left (fun ((fail_ans,res_so_far) as res) (l2r,r2l,typ,name) ->
      match fail_ans with
        | None ->
              let res = LP.verify_lemma 3 (lst_to_opt l2r) (lst_to_opt r2l) cprog name typ in 
              ((if CF.isFailCtx res then Some (name^":"^(Cprinter.string_of_coercion_type typ)) else None), res::res_so_far)
        | Some n ->
              res
  ) (None,[]) lems in
  res


(* update the lemma store with the lemmas in repo and check for their validity *)
let update_store_with_repo repo iprog cprog =
  let lems = process_one_repo repo iprog cprog in
  let left  = List.concat (List.map (fun (a,_,_,_)-> a) lems) in
  let right = List.concat (List.map (fun (_,a,_,_)-> a) lems) in
  let _ = Lem_store.all_lemma # add_coercion left right in
  let (invalid_lem, lctx) =  verify_one_repo lems cprog in
  (invalid_lem, lctx)

(* pop only if repo is invalid *)
(* return None if all succeed, and result of first failure otherwise *)
let manage_safe_lemmas repo iprog cprog = 
  let (invalid_lem, nctx) = update_store_with_repo repo iprog cprog in
  match invalid_lem with
    | Some name -> 
          let _ = Log.last_cmd # dumping (name) in
          let _ = print_endline ("\nFailed to prove "^ (name) ^ " in current context.") in
          Lem_store.all_lemma # pop_coercion;
          let _ = print_endline ("Removing invalid lemma ---> lemma store restored.") in
          Some([List.hd(nctx)])
    | None ->
          let lem_str = pr_list pr_id (List.map (fun i -> 
              i.I.coercion_name^":"^(Cprinter.string_of_coercion_type i.I.coercion_type)) repo) in
          let _ = print_endline ("\nValid Lemmas : "^lem_str^" added to lemma store.") in
          None

(* update store with given repo without verifying the lemmas *)
let manage_unsafe_lemmas repo iprog cprog = 
  let (left,right) = List.fold_left (fun (left,right) ldef -> 
      let l2r,r2l,typ = process_one_lemma iprog cprog ldef in
      (l2r@left,r2l@right)
  ) ([],[]) repo in
  let _ = Lem_store.all_lemma # add_coercion left right in
  print_endline ("\nUpdated store with unsafe repo.");
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
          let _ = print_endline ("\nFailed to "^str^" for "^ (name) ^ " ==> invalid lemma encountered.") in
          Some([List.hd(nctx)])
    | None ->
          let _ = print_endline ("\n Temp Lemma(s) "^str^" as valid in current context.") in
          Some nctx

(* verify  a list of lemmas *)
(* if one of them fails, return failure *)
(* otherwise, return a list of their successful contexts 
   which may contain inferred result *)
let sa_verify_one_repo cprog l2r r2l = 
  let res = List.fold_left (fun ((valid_ans,res_so_far) as res) coer ->
      match valid_ans with
        | true ->
              let (flag,lc) = LP.sa_verify_lemma cprog coer in 
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


(* for lemma_test, we do not return outcome of lemma proving *)
let manage_test_lemmas repo iprog cprog = 
  manage_infer_lemmas "proved" repo iprog cprog; None

let manage_infer_lemmas repo iprog cprog = 
  manage_infer_lemmas "inferred" repo iprog cprog

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


let do_unfold_view_hf cprog hf0 =
  let fold_fnc ls1 ls2 aux_fnc = List.fold_left (fun r (hf2, p2) ->
      let in_r = List.map (fun (hf1, p1) ->
          let nh = aux_fnc hf1 hf2 in
          let np = MCP.merge_mems p1 p2 true in
          (nh, np)
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
            with _ -> report_error no_pos ("LEM.do_unfold_view_hf: can not find view " ^ hv.CF.h_formula_view_name)
        end
      | CF.DataNode _  | CF.HRel _ | CF.Hole _
      | CF.HTrue  | CF.HFalse | CF.HEmp -> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
  in
  helper hf0

let do_unfold_view_x cprog (f0: CF.formula) =
  let rec helper f=
  match f with
    | CF.Base fb ->
          let ls_hf_pure = do_unfold_view_hf cprog fb.CF.formula_base_heap in
          let fs = List.map (fun (hf, p) -> CF.Base {fb with CF.formula_base_heap = hf;
              CF.formula_base_pure = MCP.merge_mems p fb.CF.formula_base_pure true;
          }) ls_hf_pure in
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

let checkeq_sem_x iprog0 cprog0 f1 f2 hpdefs=
  (*************INTERNAL******************)
  let back_up_progs iprog cprog=
    (iprog.I.prog_view_decls, iprog.I.prog_hp_decls, cprog.C.prog_view_decls, cprog.C.prog_hp_decls,
    Lem_store.all_lemma # get_left_coercion, Lem_store.all_lemma # get_right_coercion)
  in
  let reset_progs (ivdecls, ihpdecls, cvdecls, chpdecls, left_coers, righ_coers)=
    let _ = iprog0.I.prog_view_decls <- ivdecls in
    let _ = iprog0.I.prog_hp_decls <- ihpdecls in
    let _ = cprog0.C.prog_view_decls <- cvdecls in
    let _ = cprog0.C.prog_hp_decls <- chpdecls in
    let _ = Lem_store.all_lemma # set_coercion left_coers righ_coers in
    ()
  in
  let rec look_up_hpdef rem_hpdefs (r_unk_hps, r_hpdefs) hp=
    match rem_hpdefs with
      | [] -> (r_unk_hps@[hp], r_hpdefs)
      | ((k, _,_,_) as hpdef)::rest -> begin
          match k with
            | CP.HPRelDefn (hp1,_,_) -> if CP.eq_spec_var hp hp1 then
                (r_unk_hps, r_hpdefs@[hpdef])
              else look_up_hpdef rest (r_unk_hps, r_hpdefs) hp
            | _ -> look_up_hpdef rest (r_unk_hps, r_hpdefs) hp
        end
  in
  let heap_remove_unk_hps unk_hps hn = match hn with
    | CF.HRel (hp,eargs, pos)-> begin
        if CP.mem_svl hp unk_hps then CF.HTrue else hn
      end
    | _ -> hn
  in
  (*************END INTERNAL******************)
  (*for each proving: generate lemma; cyclic proof*)
  let bc = back_up_progs iprog0 cprog0 in
  let hps = CP.remove_dups_svl ((CF.get_hp_rel_name_formula f1)@(CF.get_hp_rel_name_formula f2)) in
  let unk_hps, known_hpdefs = List.fold_left (look_up_hpdef hpdefs) ([],[]) hps in
  (*remove unk_hps*)
  let f11,f21 = if unk_hps = [] then (f1, f2) else
    (CF.formula_trans_heap_node (heap_remove_unk_hps unk_hps) f1,
    CF.formula_trans_heap_node (heap_remove_unk_hps unk_hps) f2)
  in
  (*transform hpdef to view;
    if preds are unknown -> HTRUE
  *)
  let proc_name = "eqproving" in
  let n_cview,chprels_decl = SAO.trans_hprel_2_cview iprog0 cprog0 proc_name known_hpdefs in
  (*trans_hp_view_formula*)
  let f12 = SAO.trans_formula_hp_2_view iprog0 cprog0 proc_name chprels_decl known_hpdefs f11 in
  let f22 = SAO.trans_formula_hp_2_view iprog0 cprog0 proc_name chprels_decl known_hpdefs f21 in
  (*iform*)
  let if12 = AS.rev_trans_formula f12 in
  let if22 = AS.rev_trans_formula f22 in
  (*unfold lhs - rhs*)
  let f13 = do_unfold_view cprog0 f12 in
  let f23 = do_unfold_view cprog0 f22 in
  let r=
    let lemma_name = "tmp" in
    let l_coer = I.mk_lemma (fresh_any_name lemma_name) I.Left [] if12 if22 in
    let _ = manage_unsafe_lemmas [l_coer] iprog0 cprog0 in
    let r1,_,_ = SC.sleek_entail_check [] cprog0 [(* (f12,f22) *)] f13 (CF.struc_formula_of_formula f23 no_pos) in
    if not r1 then false else
      let r_coer = I.mk_lemma (fresh_any_name lemma_name) I.Right [] if12 if22 in
      let _ = manage_unsafe_lemmas [r_coer] iprog0 cprog0 in
      let r2,_,_ = SC.sleek_entail_check [] cprog0 [(* (f22,f12) *)] f23 (CF.struc_formula_of_formula f13 no_pos) in
      r2
  in
  let _ = reset_progs bc in
  r

let checkeq_sem iprog cprog f1 f2 hpdefs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_3 "LEM.checkeq_sem" pr1 pr1 pr2 string_of_bool
      (fun _ _ _ ->  checkeq_sem_x iprog cprog f1 f2 hpdefs)
      f1 f2 hpdefs



let _ = Sleekcore.generate_lemma := generate_lemma_helper
