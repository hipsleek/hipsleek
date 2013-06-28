open Globals
open Gen

module DD = Debug
module Err = Error
module CA = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher
module SAC = Sacore
module SAU = Sautility

let step_change = new Gen.change_flag

(* outcome from shape_infer *)
let rel_def_stk : CF.hprel_def Gen.stack_pr = new Gen.stack_pr
  Cprinter.string_of_hprel_def_lib (==)


(***************************************************************)
             (*      APPLY TRANS IMPL     *)
(****************************************************************)
(*input in fb
 output: true,susbs: can subst
*)

(*
dn is current node, it is one node of ldns
ss: subst from ldns -> ldns
*)

let rec find_imply_subst_x prog constrs new_cs=
  let rec check_constr_duplicate (lhs,rhs) constrs=
    match constrs with
      | [] -> false
      | cs::ss -> if SAU.checkeq_pair_formula (lhs,rhs)
            (cs.CF.hprel_lhs,cs.CF.hprel_rhs) then
            true
          else check_constr_duplicate (lhs,rhs) ss
  in
  let find_imply_one cs1 cs2=
    let _ = Debug.ninfo_pprint ("    rhs: " ^ (Cprinter.string_of_hprel cs2)) no_pos in
    let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_lhs in
    let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_rhs in
    match f1,f2 with
      | CF.Base lhs1, CF.Base rhs2 ->
          let r = SAU.find_imply prog (List.map fst cs1.CF.unk_hps) (List.map fst cs2.CF.unk_hps) lhs1 cs1.CF.hprel_rhs cs2.CF.hprel_lhs rhs2 in
          begin
              match r with
                | Some (l,r,lhs_ss, rhs_ss) ->
                    (*check duplicate*)
                    if check_constr_duplicate (l,r) (constrs@new_cs) then []
                    else
                      begin
                          let new_cs = {cs2 with
                              CF.predef_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.CF.predef_svl)@
                                          (CP.subst_var_list rhs_ss cs2.CF.predef_svl));
                              CF.unk_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.CF.unk_svl)@
                                          (CP.subst_var_list rhs_ss cs2.CF.unk_svl));
                              CF.unk_hps = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq
                                  ((List.map (fun (hp,args) -> (hp,CP.subst_var_list lhs_ss args)) cs1.CF.unk_hps)@
                                          (List.map (fun (hp,args) -> (hp,CP.subst_var_list rhs_ss args)) cs2.CF.unk_hps));
                              CF.hprel_lhs = l;
                              CF.hprel_rhs = r;
                          }
                          in
                          let _ = Debug.ninfo_pprint ("    new cs: " ^ (Cprinter.string_of_hprel new_cs)) no_pos in
                          [new_cs]
                      end
                | None -> []
          end
      | _ -> report_error no_pos "sa2.find_imply_one"
  in
  (*new_cs: one x one*)
  (* let rec helper_new_only don rest res= *)
  (*   match rest with *)
  (*     | [] -> res *)
  (*     | cs1::rest -> *)
  (*         let _ = Debug.ninfo_pprint ("    lhs: " ^ (Cprinter.string_of_hprel cs1)) no_pos in *)
  (*         let r = List.concat (List.map (find_imply_one cs1) (don@rest@res)) in *)
  (*         (helper_new_only (don@[cs1]) rest (res@r)) *)
  (* in *)
  let rec helper_new_only don rest is_changed=
    match rest with
      | [] -> is_changed,don
      | cs1::rest ->
          let _ = Debug.ninfo_pprint ("    lhs: " ^ (Cprinter.string_of_hprel cs1)) no_pos in
          let is_changed1, new_rest = List.fold_left ( fun (b,res) cs2->
              match find_imply_one cs1 cs2 with
                | [n_cs2] -> true,res@[n_cs2]
                | _ -> b,res@[cs2]
          ) (is_changed, []) (rest)
          in
          let is_changed2,new_don = List.fold_left ( fun (b,res) cs2->
              match find_imply_one cs1 cs2 with
                | [n_cs2] -> true,res@[n_cs2]
                | _ -> b,res@[cs2]
          ) (is_changed1,[]) (don)
          in
          (helper_new_only (new_don@[cs1]) new_rest is_changed2)
  in
  (*new_cs x constr*)
  let rec helper_old_new rest res=
    match rest with
      | [] -> res
      | cs1::ss ->
          let r = List.fold_left ( fun ls cs2 -> ls@(find_imply_one cs1 cs2)) res constrs in
          helper_old_new ss r
  in
  let is_changed,new_cs1 = if List.length new_cs < 1 then (false, new_cs) else helper_new_only [] new_cs false in
  let new_cs2 = helper_old_new new_cs [] in
  (is_changed,new_cs1(* @new_cs2 *))

and find_imply_subst prog constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_2 "find_imply_subst" pr1 pr1 (pr_pair string_of_bool pr1)
      (fun _ _ -> find_imply_subst_x prog constrs new_cs) constrs new_cs

and is_trivial cs= (SAU.is_empty_f cs.CF.hprel_rhs) ||
  (SAU.is_empty_f cs.CF.hprel_lhs || SAU.is_empty_f cs.CF.hprel_rhs)

and is_non_recursive_non_post_cs post_hps dang_hps constr=
  let lhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_lhs in
  let rhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_rhs in
  (CP.intersect_svl rhrel_svl post_hps = []) && ((CP.intersect lhrel_svl rhrel_svl) = [])

and subst_cs_w_other_cs_x prog post_hps dang_hps constrs new_cs=
  (*remove recursive cs and post-preds based to preserve soundness*)
  let constrs1 = List.filter (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)) constrs in
  let new_cs1,rem = List.partition (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)) new_cs in
  let b,new_cs2 = find_imply_subst prog constrs1 new_cs1 in
  (b, new_cs2@rem)
(*=========END============*)

let rec subst_cs_w_other_cs prog post_hps dang_hps constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
   Debug.no_1 "subst_cs_w_other_cs" pr1 pr1
       (fun _ -> subst_cs_w_other_cs_x prog post_hps dang_hps constrs  new_cs) constrs

(* let subst_cs_x prog dang_hps constrs new_cs = *)
(*   (\*subst by constrs*\) *)
(*   DD.ninfo_pprint "\n subst with other assumptions" no_pos; *)
(*   let new_cs1 = subst_cs_w_other_cs prog dang_hps constrs new_cs in *)
(*   (constrs@new_cs, new_cs1,[]) *)

(* let subst_cs prog dang_hps hp_constrs new_cs= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hprel in *)
(*   Debug.no_1 "subst_cs" pr1 (pr_triple pr1 pr1 !CP.print_svl) *)
(*       (fun _ -> subst_cs_x prog dang_hps hp_constrs new_cs) new_cs *)

let subst_cs_x prog post_hps dang_hps constrs new_cs =
  (*subst by constrs*)
  DD.ninfo_pprint "\n subst with other assumptions" no_pos;
  let is_changed, new_cs1 = subst_cs_w_other_cs prog post_hps dang_hps constrs new_cs in
  (is_changed, new_cs1,[])

let subst_cs prog post_hps dang_hps hp_constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "subst_cs" pr1 (pr_triple string_of_bool  pr1 pr1)
      (fun _ -> subst_cs_x prog post_hps dang_hps hp_constrs new_cs) new_cs

(*===========fix point==============*)
let apply_transitive_impl_fix prog post_hps callee_hps hp_rel_unkmap unk_hps (constrs: CF.hprel list) =
  let dang_hps = (fst (List.split hp_rel_unkmap)) in
  let rec helper_x (constrs: CF.hprel list) new_cs =
    DD.binfo_pprint ">>>>>> step 3a: simplification <<<<<<" no_pos;
    let new_cs1 = (* simplify_constrs prog unk_hps *) new_cs in
     Debug.ninfo_hprint (add_str "apply_transitive_imp LOOP: " (pr_list_ln Cprinter.string_of_hprel)) constrs no_pos;
    begin
        DD.binfo_pprint ">>>>>> step 3b: do apply_transitive_imp <<<<<<" no_pos;
        (* let constrs2, new_cs2, new_non_unk_hps = subst_cs prog dang_hps constrs new_cs1 in *)
      let is_changed, constrs2,new_cs2 = subst_cs prog post_hps dang_hps constrs new_cs1 in
        (*for debugging*)
        let _ = DD.ninfo_pprint ("   new constrs:" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr constrs2)) no_pos in
        let helper (constrs: CF.hprel list) new_cs=
          let pr = pr_list_ln Cprinter.string_of_hprel in
          Debug.no_1 "apply_transitive_imp_fix" pr (fun (cs,_) -> pr cs)
              (fun _ -> helper_x constrs new_cs) new_cs
        in
        (*END for debugging*)
        let norm_constrs, non_unk_hps1 =
          if (* List.length new_cs2 = 0 *) not is_changed then (constrs2@new_cs2,[])
          else
            helper new_cs2 constrs2 in
        ( norm_constrs, [])
      end
  in
  helper_x [] constrs

(***************************************************************
                      END APPLY TRANS IMPL
****************************************************************)
(***************************************************************
                      CONSTR: ELIM UNUSED PREDS
****************************************************************)
(*split constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
let split_constr prog constrs post_hps prog_vars unk_map unk_hps link_hps=
  (*internal method*)
  let split_one cs total_unk_map=
    let _ = Debug.ninfo_pprint ("  cs: " ^ (Cprinter.string_of_hprel_short cs)) no_pos in
    let (_ ,mix_lf,_,_,_) = CF.split_components cs.CF.hprel_lhs in
    let l_qvars, lhs = CF.split_quantifiers cs.CF.hprel_lhs in
    let r_qvars, rhs = CF.split_quantifiers cs.CF.hprel_rhs in
    let l_hpargs = CF.get_HRels_f lhs in
    let r_hpargs = CF.get_HRels_f rhs in
    if (List.exists (fun (hp,_) -> CP.mem_svl hp post_hps) r_hpargs) &&
      (List.length l_hpargs > 0) then
        let leqs = (MCP.ptr_equations_without_null mix_lf) in
        let lhs_b = match lhs with
          | CF.Base fb -> fb
          | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
        in
        let rhs_b = match rhs with
          | CF.Base fb -> fb
          | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
        in
        (**smart subst**)
        let lhs_b1, rhs_b1, subst_prog_vars = SAU.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs)
          leqs [] [] prog_vars
        in
        (* let lfb = match lhs_b1 with *)
        (*   | CF.Base fb -> fb *)
        (*   | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula" *)
        (* in *)
        let lfb = lhs_b1 in
        let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
        let (_ ,mix_lf,_,_,_) = CF.split_components (CF.Base lfb) in
        let leqNulls = MCP.get_null_ptrs mix_lf in
        let leqs = (MCP.ptr_equations_without_null mix_lf) in
        let ls_rhp_args = CF.get_HRels_f (CF.Base rhs_b1) in
        let r_hps = List.map fst ls_rhp_args in
        let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds)
          @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in
        let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (leqs)) in
        let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
        let ls_lhp_args = (List.map helper lhrs) in
        (*generate linking*)
        let unk_svl, lfb1, unk_map1 = ([], lfb, total_unk_map)
          (* let unk_svl, unk_xpure, unk_map1 = SAC.generate_map ls_lhp_args ls_rhp_args total_unk_map no_pos in *)
          (* let lfb1 = CF.mkAnd_base_pure lfb (MCP.mix_of_pure unk_xpure) no_pos in *)
          (* ([], lfb1, unk_map1) *)
        in
        let unk_svl1 = CP.remove_dups_svl (cs.CF.unk_svl@unk_svl) in
        (*do not split unk_hps and link_hps*)
        let non_split_hps = unk_hps @ link_hps in
        let ls_lhp_args1 = List.filter (fun (hp,_) -> not(CP.mem_svl hp non_split_hps)) ls_lhp_args in
        (* let _ = Debug.info_pprint ("  ls_lhp_args1: " ^ *)
        (*     (let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr1 ls_lhp_args1)) no_pos in *)
        let lfb2, defined_preds,rems_hpargs,link_hps =
          List.fold_left (fun (lfb, r_defined_preds, r_rems, r_link_hps) hpargs ->
              let n_lfb,def_hps, rem_hps, ls_link_hps=
                SAU.find_well_defined_hp (* split_base *) prog lhds lhvs r_hps
                    prog_vars post_hps hpargs (l_def_vs@unk_svl1) lfb true no_pos
              in
              (n_lfb, r_defined_preds@def_hps, r_rems@rem_hps, r_link_hps@(snd (List.split ls_link_hps)))
          ) (lfb1, [], [], []) ls_lhp_args1
        in
        (* let defined_preds = List.concat ls_defined_hps in *)
        (* let _ = if defined_preds!=[] then step_change # i else () in *)
        let rf = CF.mkTrue (CF.mkTrueFlow()) no_pos in
        let defined_preds0 = List.fold_left (fun (defined_preds) hpargs ->
            let def_hps, _ = (SAU.find_well_eq_defined_hp prog lhds lhvs lfb2 leqs hpargs) in
            (defined_preds@(List.map (fun (a,b,c) -> (a,b,c,rf)) def_hps))
        ) (defined_preds) rems_hpargs in
        let new_cs = {cs with CF.hprel_lhs = CF.add_quantifiers l_qvars (CF.Base lfb2);
            CF.unk_svl = unk_svl1;
            CF.hprel_rhs = (CF.add_quantifiers r_qvars (CF.Base rhs_b1));
        } in
        let new_constrs = match defined_preds0 with
          | [] -> [new_cs]
          | _ ->
                let _ = Debug.ninfo_pprint (Cprinter.string_of_hprel_short cs) no_pos in
                let _ = Debug.ninfo_pprint ("  unused ptrs: " ^ (!CP.print_svl unk_svl)) no_pos in
                (*prune defined hps in lhs*)
                let new_lhs, _ = CF.drop_hrel_f new_cs.CF.hprel_lhs (List.map (fun (a, _, _,_) -> a) defined_preds0) in
                let new_lhs1 = CF.add_quantifiers l_qvars new_lhs in
                let new_lhs2 = CF.elim_unused_pure new_lhs1 new_cs.CF.hprel_rhs in
                let new_cs = {new_cs with CF.hprel_lhs = new_lhs2;} in
                let _ = Debug.ninfo_pprint ("  refined cs: " ^ (Cprinter.string_of_hprel_short new_cs)) no_pos in
                (* let rf = CF.mkTrue (CF.mkTrueFlow()) no_pos in *)
                let _ = Debug.ninfo_pprint ("  generate pre-preds-based constraints: " ) no_pos in
                let defined_hprels = List.map (SAU.generate_hp_ass unk_svl1) defined_preds0 in
                new_cs::defined_hprels
        in
        (new_constrs, unk_map1, link_hps)
    else
      (*detect link hps: move to outside of shape_infer??*)
      (*  let leqs = (MCP.ptr_equations_without_null mix_lf) in *)
      (*   let lhs_b = match lhs with *)
      (*     | CF.Base fb -> fb *)
      (*     | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula" *)
      (*   in *)
      (*   let rhs_b = match rhs with *)
      (*     | CF.Base fb -> fb *)
      (*     | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula" *)
      (*   in *)
      (*   (\**smart subst**\) *)
      (*   let lhs_b1, rhs_b1, subst_prog_vars = SAU.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs) *)
      (*     leqs [] [] prog_vars *)
      (*   in *)
      (*   let lfb = lhs_b1 in *)
      (*   let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in *)
      (*   let (_ ,mix_lf,_,_,_) = CF.split_components (CF.Base lfb) in *)
      (*   let leqNulls = MCP.get_null_ptrs mix_lf in *)
      (*   let leqs = (MCP.ptr_equations_without_null mix_lf) in *)
      (*   let ls_rhp_args = CF.get_HRels_f (CF.Base rhs_b1) in *)
      (*   let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds) *)
      (*     @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in *)
      (*   let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (leqs)) in *)
      (*   let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in *)
      (*   let ls_lhp_args = (List.map helper lhrs) in *)
      (*   let link_hpargs0 =  match ls_rhp_args with *)
      (*     | [(r_hp,r_args)] -> *)
      (*           if CP.mem_svl r_hp post_hps then *)
      (*             [] *)
      (*           else *)
      (*             SAU.detect_link_hp prog lhds lhvs r_hp r_args post_hps ls_lhp_args (l_def_vs) *)
      (*     | _ -> [] *)
      (* in *)
      ([cs],total_unk_map,[])
  in
  let split_one cs total_unk_map =
    let pr1 = Cprinter.string_of_hprel_short in
    (* let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in *)
    let res = split_one cs total_unk_map in
    let (new_cs,new_umap,link_hpargs) = res in
    if (List.length new_cs > 1) then
      begin
        step_change # inc;
        (* Debug.binfo_start "split_base"; *)
        (* Debug.binfo_hprint (add_str "BEFORE" pr1) cs no_pos; *)
        (* Debug.binfo_pprint "=============>>>>" no_pos; *)
        (* Debug.binfo_hprint (add_str "AFTER" (pr_list_ln pr1)) new_cs no_pos; *)
        (* Debug.binfo_end "split_base"; *)
        res
      end
    else res
  in
  let split_one cs total_unk_map =
    let pr1 = Cprinter.string_of_hprel in
    let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
    let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
    Debug.no_2 "split_one" pr1 pr2 (pr_triple (pr_list_ln pr1) pr2 pr3) split_one cs total_unk_map 
    in
  let new_constrs, new_map, link_hpargs = List.fold_left (fun (r_constrs,unk_map, r_link_hpargs) cs ->
      let new_constrs, new_map, new_link_hpargs = split_one cs unk_map in
      (r_constrs@new_constrs, new_map, r_link_hpargs@new_link_hpargs)
  ) ([], unk_map, []) constrs
  in
  (new_constrs, new_map, link_hpargs)

let split_constr prog constrs post_hps prog_vars unk_map unk_hps link_hps=
      let _ = step_change # reset in
      let s1 = (pr_list_num Cprinter.string_of_hprel_short) constrs in
      let (constrs2, unk_map2, link_hpargs2) as res = split_constr prog constrs post_hps prog_vars unk_map unk_hps link_hps in
      let s2 = (pr_list_num Cprinter.string_of_hprel_short) constrs2 in
      if step_change # no_change then 
        DD.binfo_pprint "*** NO SPLITTING DONE ***" no_pos
      else 
        begin
          let _ = DD.binfo_start "split_base" in
          let _ = DD.binfo_hprint (add_str "post_hps" Cprinter.string_of_spec_var_list) post_hps no_pos in
          let _ = DD.binfo_hprint (add_str "prog_vars" Cprinter.string_of_spec_var_list) prog_vars no_pos in
          let _ = DD.binfo_hprint (add_str "BEFORE" pr_id) s1 no_pos in
          let _ = DD.binfo_pprint "=============>>>>" no_pos in
          let _ = DD.binfo_hprint (add_str "AFTER" pr_id) s2 no_pos in
          let _ = DD.binfo_hprint (add_str "UNKNOWN added" (pr_list (fun (x,_) -> Cprinter.string_of_spec_var x)))  link_hpargs2 no_pos in
          let _ = DD.binfo_end "split_base" in
          ()
        end;
      res


let split_constr prog constrs post_hps prog_vars unk_map unk_hps link_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  (* let pr2 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_4 "split_constr" pr1 pr2 !CP.print_svl !CP.print_svl (pr_triple pr1 pr2 pr3)
      (fun _ _ _ _ -> split_constr prog constrs post_hps prog_vars unk_map
          unk_hps link_hps) constrs unk_map unk_hps post_hps

let get_preds (lhs_preds, lhs_heads, rhs_preds,rhs_heads) cs=
  (* let pr1 = Cprinter.string_of_hprel_short in *)
  (* let _ = print_endline ( "cs: " ^ (pr1 cs)) in *)
  let lhs_hps = List.map (fun (hp, eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) (CF.get_hprel cs.CF.hprel_lhs) in
  let rhs_hps = List.map (fun (hp, eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) (CF.get_hprel cs.CF.hprel_rhs) in
  (* let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in *)
  (*lhs pred should be one pred + heap + pure*)
  let n_lhs_heads = match List.length lhs_hps  with
    | 1 -> lhs_heads@lhs_hps
    | _ -> lhs_heads
  in
  (*rhs pred should be one pred + heap + pure*)
  let n_rhs_heads = match List.length rhs_hps  with
    | 1 -> rhs_heads@rhs_hps
    | _ -> rhs_heads
  in
  (lhs_preds@lhs_hps, n_lhs_heads, rhs_preds@rhs_hps,n_rhs_heads)

(* let do_elim_unused unused_hps cs map= *)
(*   let new_lhs, _ = CF.drop_hrel_f cs.CF.hprel_lhs unused_hps in *)
(*   let new_rhs, _ = CF.drop_hrel_f cs.CF.hprel_rhs unused_hps in *)
(*   ({cs with CF.hprel_lhs = new_lhs; CF.hprel_rhs = new_rhs}, map) *)

(* let do_elim_unused unused_hps cs map= *)
(*   let pr1 = !CP.print_svl in *)
(*   let pr2 = Cprinter.string_of_hprel in *)
(*   (\* let pr3= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *\) *)
(*   let pr3 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in *)
(*   Debug.no_3 "do_elim_unused" pr1 pr2 pr3 (pr_pair pr2 pr3) *)
(*       do_elim_unused unused_hps cs map *)

let cmp_hpargs_fn (hp1, _) (hp2, _) = CP.eq_spec_var hp1 hp2

let elim_unused_pre_preds post_hps constrs unk_map=
  let lhs_preds, lhs_heads, rhs_preds,rhs_heads = List.fold_left get_preds ([],[],[],[]) constrs in
  (* let lhs_preds1 = CP.remove_dups_svl lhs_preds in *)
  let rhs_preds1 = Gen.BList.remove_dups_eq cmp_hpargs_fn rhs_preds in
  (* let _ = print_endline ("lhs_preds1: " ^ (!CP.print_svl lhs_preds1)) in *)
  (* let _ = print_endline ("rhs_preds1: " ^ (!CP.print_svl rhs_preds1)) in *)
  (*unused pre preds are preds in rhs but do not appear in any lhs*)
  let unused_pre_preds = Gen.BList.difference_eq cmp_hpargs_fn rhs_preds1 lhs_heads in
  (*and they are NOT post*)
  let unused_pre_preds0 = List.filter (fun (hp,_) -> not (CP.mem_svl hp post_hps)) unused_pre_preds in
  let unused_pre = (List.map fst unused_pre_preds0) in
  let _ = DD.binfo_pprint ("pre-preds: "  ^ (!CP.print_svl unused_pre) ^" are removed") no_pos in
  let new_constrs,new_map = List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = SAC.do_elim_unused cs unused_pre map in
      (ls_cs@[new_cs], n_map)
  ) ([], unk_map) constrs in
  let _ = DD.dinfo_pprint ("   After removing, derived:\n" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr new_constrs)) no_pos in
  let _ = DD.dinfo_pprint ("   uu map:" ^ (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in pr new_map)) no_pos in
  (unused_pre_preds0, new_constrs, new_map)

let elim_unused_pre_preds post_hps constrs unk_map=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  (* let pr3= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr3 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  Debug.no_2 "elim_unused_pre_preds" pr1 pr3 (pr_triple pr2 pr1 pr3)
      (fun _ _ -> elim_unused_pre_preds post_hps constrs unk_map)
      constrs unk_map

let elim_unused_post_preds post_hps constrs unk_map=
  let lhs_preds, lhs_heads, rhs_preds,rhs_heads = List.fold_left get_preds ([],[],[],[]) constrs in
  let lhs_preds1 = Gen.BList.remove_dups_eq cmp_hpargs_fn lhs_preds in
  (* let rhs_preds1 = CP.remove_dups_svl rhs_preds in *)
  (* let _ = print_endline ("lhs_preds1: " ^ (!CP.print_svl lhs_preds1)) in *)
  (* let _ = print_endline ("rhs_preds1: " ^ (!CP.print_svl rhs_preds1)) in *)
  (*unused pre preds are preds in rhs but do not appear in any lhs*)
  (*post-preds*)
  (*unused post preds are preds in lhs but do not appear in any rhs*)
  let unused_post_preds = Gen.BList.difference_eq cmp_hpargs_fn lhs_preds1 rhs_heads in
  (*and they are NOT pre*)
  let unused_post_preds0 = unused_post_preds(* CP.diff_svl unused_post_preds lhs_heads *) in
  let unused_post = (List.map fst unused_post_preds0) in
  let _ = DD.binfo_pprint ("post-preds: "  ^ (!CP.print_svl unused_post) ^" are removed") no_pos in
  let new_constrs,new_map = List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = SAC.do_elim_unused cs unused_post map in
      (ls_cs@[new_cs], n_map)
  ) ([], unk_map) constrs in
  let _ = DD.dinfo_pprint ("   After removing, derived:\n" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr new_constrs)) no_pos in
  let _ = DD.dinfo_pprint ("   uu map:" ^ (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in pr new_map)) no_pos in
  ( unused_post_preds, new_constrs, new_map)

let elim_unused_post_preds post_hps constrs unk_map=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  (* let pr3= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr3 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  Debug.no_2 "elim_unused_post_preds" pr1 pr3 (pr_triple pr2 pr1 pr3)
      (fun _ _ -> elim_unused_post_preds post_hps constrs unk_map)
      constrs unk_map

(* let elim_unused_post_preds post_hps constrs= *)
(*   constrs *)

(* let elim_unused_pre_preds post_hps constrs= *)
(*   constrs *)

(***************************************************************
                      END. CONSTR: ELIM UNUSED PREDS
****************************************************************)

(***************************************************************
                      PARTIAL DEFS
****************************************************************)
let mk_pdef hp_sv args unk_svl imp_cond olhs orhs=
  (hp_sv, args,  unk_svl, imp_cond, olhs , orhs)

let cmp_formula_opt args of1 of2=
  match of1,of2 with
    | Some f1, Some f2 ->
          SAU.check_relaxeq_formula args f1 f2
    | None, None -> true
    | _ -> false

(*assume hp1 = hp2*)
let cmp_pdef_grp (hp1,args1,unk_svl1, cond1, olhs1, orhs1) (hp2,args2,unk_svl2, cond2, olhs2, orhs2)=
  (CP.equalFormula cond1 cond2) && (cmp_formula_opt args1 orhs1 orhs2)

let get_par_defs_post constrs0 =
  let mk_par_def cs=
    let hp, args = CF.extract_HRel_f cs.CF.hprel_rhs in
    mk_pdef hp args cs.CF.unk_svl (CP.mkTrue no_pos) (Some cs.CF.hprel_lhs) None
  in
  List.map mk_par_def constrs0

let get_par_defs_pre constrs0 =
  let mk_par_def cs=
    (* let _ = print_endline ("cs.CF.hprel_lhs: " ^ ( !CF.print_formula cs.CF.hprel_lhs)) in *)
    let op_res = CF.extract_hprel_pure cs.CF.hprel_lhs in
    match op_res with
      | Some (hp, args,p) ->
          (* let _ = print_endline ("p: " ^ ( !CP.print_formula p)) in *)
          ([(mk_pdef hp args cs.CF.unk_svl (CP.remove_redundant p) None (Some cs.CF.hprel_rhs), cs)], [])
      | None -> ([], [cs])
  in
  List.fold_left (fun (pdefs,rem_cs) cs ->
      let ls1, ls2 = mk_par_def cs in
      (pdefs@ls1, rem_cs@ls2)
  )
      ([], []) constrs0
      (*remove_dups*)

let combine_pdefs_pre_x prog unk_hps link_hps pr_pdefs=
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
      | [] -> parts
      | ((a1,a2,a3,a4,a5,a6),cs)::xs ->
          let part,remains= List.partition (fun ((hp_name,_,_,_,_,_),_) ->
              CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[((a1,a2,a3,a4,a5,a6),cs)]@part])
  in
  let do_combine (hp,args,unk_svl, cond, lhs, orhs)=
    match orhs with
      | Some rhs ->
            let n_cond = CP.remove_redundant cond in
            let nf = (CF.mkAnd_pure rhs (MCP.mix_of_pure n_cond) (CF.pos_of_formula rhs)) in
            if SAU.is_unsat nf then [] else
            [(hp,args,unk_svl, n_cond, lhs, Some nf)]
      | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None 1"
  in
  let mkAnd_w_opt args (* ss *) of1 of2=
    match of1,of2 with
      | Some f1, Some f2 ->
            let pos = CF.pos_of_formula f1 in
            let new_f2 = (*CF.subst ss*) f2 in
            let f = SAU.mkConjH_and_norm prog args unk_hps [] f1 new_f2 pos in
            (* let f = (CF.mkConj_combine f1 new_f2 CF.Flow_combine no_pos) in *)
        if CF.isAnyConstFalse f || SAU.is_unsat f then
          false, Some f
        else true, Some f
      | None, None -> true, None
      | None, Some f2 -> true, (Some ( (*CF.subst ss*) f2))
      | Some f1, None -> true, of1
  in
  (*nav code. to improve*)
  let combine_helper2_x (hp1,args1,unk_svl1, cond1, olhs1, orhs1) (hp2,args2,unk_svl2, cond2, olhs2, orhs2)=
    let cond_disj1 = CP.mkAnd cond1 (CP.mkNot (CP.remove_redundant cond2) None no_pos) no_pos in
    let pdef1 = if (TP.is_sat_raw (MCP.mix_of_pure cond_disj1)) then
      (* let _ = DD.info_pprint ("      cond_disj1: " ^ (!CP.print_formula  cond_disj1) ) no_pos in *)
      let cond21 = CF.remove_neqNull_redundant_andNOT_opt orhs1 cond2 in
      let n_cond = CP.mkAnd cond1 (CP.mkNot cond21 None no_pos) no_pos in
      let npdef1 = do_combine (hp1,args1,unk_svl1, CP.remove_redundant n_cond , olhs1, orhs1) in
      npdef1
    else []
    in
    let cond_disj2 = CP.mkAnd cond2 (CP.mkNot cond1 None no_pos) no_pos in
    let pdef2 = if (TP.is_sat_raw (MCP.mix_of_pure cond_disj2)) then
      (* let _ = DD.info_pprint ("      cond_disj2: " ^ (!CP.print_formula  cond_disj2) ) no_pos in *)
      let cond11 = CF.remove_neqNull_redundant_andNOT_opt orhs2 cond1 in
      let n_cond = (CP.mkAnd cond2 (CP.mkNot cond11 None no_pos) no_pos) in
      let npdef2 = do_combine (hp2,args2,unk_svl2, CP.remove_redundant n_cond, olhs2, orhs2) in
      npdef2
    else []
    in
    let cond_disj3 = CP.mkAnd cond2 cond1 no_pos in
    (* let _ = DD.info_pprint ("      cond_disj3: " ^ (!CP.print_formula  cond_disj3) ) no_pos in *)
    let pdef3 = if (TP.is_sat_raw (MCP.mix_of_pure cond_disj3)) then
      let n_cond = CP.remove_redundant (CP.mkAnd cond1 cond2 no_pos) in
      let is_sat1, n_orhs = mkAnd_w_opt args1 orhs1 orhs2 in
      let is_sat2, n_olhs = mkAnd_w_opt args1 olhs1 olhs2 in
      let npdef3 = if is_sat1 && is_sat2 then
        do_combine (hp1,args1,unk_svl1, n_cond, n_olhs, n_orhs)
      else [(hp1,args1,unk_svl1,  n_cond, olhs1, Some (CF.mkFalse_nf no_pos))]
      in
      npdef3
    else []
    in
    pdef1@pdef2@pdef3
  in
  let combine_helper2 pdef1 pdef2=
    let pr1 = !CP.print_svl in
    let pr2 = !CP.print_formula in
    let pr3 oform= match oform with
      | None -> "None"
      | Some f -> Cprinter.prtt_string_of_formula f
    in
    let pr4 = pr_hexa !CP.print_sv pr1 pr1 pr2 pr3 pr3 in
    Debug.no_2 " combine_helper2" pr4 pr4 (pr_list_ln pr4)
        (fun _ _ -> combine_helper2_x pdef1 pdef2)
        pdef1 pdef2
  in
  let rec combine_helper_list rem res=
    match rem with
      | [] -> res
      | pdef::rest ->
            let n = List.fold_left (fun res_pdefs pdef1 ->
                res_pdefs@(combine_helper2 pdef pdef1)
            ) [] rest in
             combine_helper_list rest (res@n)
  in
  let filter_trivial_pardef (res_pr, res_depen_cs) ((hp,args,unk_svl, cond, olhs, orhs), cs) =
     match orhs with
       | Some rhs -> let b = CP.isConstTrue cond && SAU.is_empty_f rhs in
                     if not b then
                       (res_pr@[((hp,args,unk_svl, cond, olhs, orhs), cs)], res_depen_cs)
                     else (res_pr, res_depen_cs@[cs])
       | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None 2"
  in
  let obtain_and_norm_def args0 ((hp,args,unk_svl, cond, olhs, orhs), cs)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let cond1 = (CP.subst subst cond) in
    let norhs = match orhs with
      | Some f -> Some (CF.subst subst f)
      | None -> None
    in
    let nolhs = match olhs with
      | None -> None
      | Some f -> Some (CF.subst subst f)
    in
    ((hp,args0,CP.subst_var_list subst unk_svl, cond1, nolhs, norhs), (*TODO: subst*)cs)
  in
  let combine_grp pr_pdefs equivs=
    match pr_pdefs with
      | [] -> ([],[], equivs)
      | [(hp,args,unk_svl, cond, lhs, orhs), _] ->
          let new_pdef = do_combine (hp,args,unk_svl, cond, lhs, orhs) in
          (new_pdef,[], equivs)
      | _ -> begin
          (*each group, filter depended constraints*)
          let rem_pr_defs, depend_cs = List.fold_left filter_trivial_pardef ([],[]) pr_pdefs in
          (* let rem_pr_defs = pr_pdefs in *)
          (* let depend_cs = [] in *)
          (*do norm args first, apply for cond only, other parts will be done later*)
          let cs,rem_pr_defs1 , n_equivs=
            match rem_pr_defs with
              | [] -> [],[],equivs
              | [x] -> [x],[],equivs
              | ((hp,args0,unk_svl0, cond0, olhs0, orhs0),cs0)::rest ->
                  let new_rest = List.map (obtain_and_norm_def args0) rest in
                  let pdefs = ((hp,args0,unk_svl0, cond0, olhs0, orhs0),cs0)::new_rest in
                  let pdefs1 = Gen.BList.remove_dups_eq (fun (pdef1,_) (pdef2,_) -> cmp_pdef_grp pdef1 pdef2) pdefs in
                  let pdefs2,n_equivs = SAC.unify_consj_pre prog unk_hps link_hps equivs pdefs1 in
                  ([], pdefs2,n_equivs)
          in
          let pdefs,rem_constrs0 = begin
            match cs,rem_pr_defs1 with
              | [],[] -> [],[]
              | [((hp,args,unk_svl, cond, lhs, orhs), _)],[] -> (do_combine (hp, args, unk_svl, cond, lhs, orhs)),[]
              | [],[(pr1,_);(pr2,_)] -> let npdefs = combine_helper2 pr1 pr2 in
                npdefs,[]
              | _ ->
                    (* let pdefs, rem_constrs = *)
                    (*   combine_helper rem_pr_defs1 [] [] [] in *)
                    (* (pdefs,rem_constrs) *)
                    let fst_ls = List.map fst rem_pr_defs1 in
                    let pdefs = (* combine_helper_list fst_ls [] *)
                      List.fold_left (fun res_pdefs pdef ->
                        res_pdefs@(List.fold_left (fun res pdef1 -> res@(combine_helper2 pdef pdef1)) [] res_pdefs)
                      ) [List.hd fst_ls] (List.tl fst_ls)
                    in
                    (pdefs,[])
          end
          in
          (pdefs, depend_cs@rem_constrs0, n_equivs)
      end
  in
  let subst_equiv equivs ((hp,args1,unk_svl1, cond1, olhs1, orhs1) as pdef)=
    match orhs1 with
      | None -> pdef
      | Some f ->
            let rele_equivs = List.fold_left (fun ls (hp1,hp2) ->
                if CP.eq_spec_var hp1 hp then (ls@[hp2]) else ls)
              [] equivs
            in
            let from_hps = CP.remove_dups_svl rele_equivs in
            let nf = CF.subst_hprel f from_hps hp in
            (hp,args1,unk_svl1, cond1, olhs1, Some nf)
  in
  (*group*)
  let ls_pr_pdefs = partition_pdefs_by_hp_name pr_pdefs [] in
  (*combine rhs with condition for each group*)
  let pdefs, rem_constr,equivs = List.fold_left (fun (r_pdefs, r_constrs, equivs) grp ->
      let pdefs, cs, new_equivs = combine_grp grp equivs in
      (r_pdefs@pdefs, r_constrs@cs, new_equivs)
  ) ([],[],[]) ls_pr_pdefs
  in
  let pdefs1 = (* List.map (fun (a,b,c,d,e,f,g) -> (a,b,c,d,f,g)) *) pdefs in
  (*subst equivs*)
  let pdefs2 = List.map (subst_equiv equivs) pdefs1 in
  (pdefs2,rem_constr,equivs)
(*retain depended constraints*)

let combine_pdefs_pre prog unk_hps link_hps pr_pdefs=
  let pr1= pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = SAU.string_of_par_def_w_name in
  let pr3 (pdef, _) = pr2 pdef in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_1 "combine_pdefs_pre" (pr_list_ln pr3) (pr_triple (pr_list_ln pr2) pr1 pr4)
      (fun _ -> combine_pdefs_pre_x prog unk_hps link_hps pr_pdefs) pr_pdefs
(***************************************************************
                      END PARTIAL DEFS
****************************************************************)
(***************************************************************
                      GENERALIZATION
****************************************************************)
(*remove neqNUll redundant*)
let remove_neqNull_helper (hp,args,f,unk_svl)=
  let f1 = CF.remove_neqNulls_f f in
  if SAU.is_empty_f f1 then [] else [(hp,args,f1,unk_svl)]

let remove_neqNull_grp_helper grp=
    List.fold_left (fun r pdef-> let new_pdef = remove_neqNull_helper pdef in
                                 r@new_pdef) [] grp

let get_null_quans f=
  let qvars, base_f = CF.split_quantifiers f in
   let (_ ,mix_lf,_,_,_) = CF.split_components base_f in
   let eqNulls = MCP.get_null_ptrs mix_lf in
   (CP.intersect_svl eqNulls qvars, base_f)

(*for par_defs*)
let generalize_one_hp_x prog is_pre hpdefs non_ptr_unk_hps unk_hps link_hps par_defs=
  let skip_hps = unk_hps@link_hps in
  (*collect definition for each partial definition*)
  let obtain_and_norm_def hp args0 quan_null_svl0 (a1,args,f,unk_args)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let f1 = (CF.subst subst f) in
    (* let f2 = *)
    (*   if !Globals.sa_dangling then *)
    (*     CF.annotate_dl f1 (List.filter (fun hp1 -> not (CP.eq_spec_var hp hp1)) unk_hps) *)
    (*     (\* fst (CF.drop_hrel_f f1 unk_hps) *\) *)
    (*   else f1 *)
    (* in *)
    let f2 = (* CF.split_quantifiers *) f1 in
    let quan_null_svl, base_f2 = get_null_quans f2 in
    let f3=
      if List.length quan_null_svl = List.length quan_null_svl0 then
        let ss = List.combine quan_null_svl quan_null_svl0 in
        CF.add_quantifiers quan_null_svl0 (CF.subst ss base_f2)
      else f2
    in
    let unk_args1 = List.map (CP.subs_one subst) unk_args in
    (* (\*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *\) *)
    (f3,unk_args1)
  in
  DD.tinfo_pprint ">>>>>> generalize_one_hp: <<<<<<" no_pos;
  if par_defs = [] then ([],[]) else
    begin
        let hp, args, f0,_ = (List.hd par_defs) in
        if CP.mem_svl hp skip_hps then
          let fs = List.map (fun (a1,args,f,unk_args) -> fst (CF.drop_hrel_f f [hp]) ) par_defs in
          let fs1 = Gen.BList.remove_dups_eq (fun f1 f2 -> SAU.check_relaxeq_formula args f1 f2) fs in
          (SAU.mk_unk_hprel_def hp args fs1 no_pos,[])
        else
          (*find the root: ins2,ins3: root is the second, not the first*)
          let args0 = List.map (CP.fresh_spec_var) args in
          (* DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")") no_pos; *)
          let quan_null_svl,_ = get_null_quans f0 in
          let quan_null_svl0 = List.map (CP.fresh_spec_var) quan_null_svl in
          let defs,ls_unk_args = List.split (List.map (obtain_and_norm_def hp args0 quan_null_svl0) par_defs) in
          let r,non_r_args = SAU.find_root prog skip_hps args0 defs in
          (*make explicit root*)
          let defs0 = List.map (SAU.mk_expl_root r) defs in
          let unk_svl = CP.remove_dups_svl (List.concat (ls_unk_args)) in
          (*normalize linked ptrs*)
          let defs1 = SAU.norm_hnodes args0 defs0 in
          (*remove unkhp of non-node*)
          let defs2 = (* List.map remove_non_ptr_unk_hp *) defs1 in
          (*remove duplicate*)
          let defs3 = SAU.equiv_unify args0 defs2 in
          let defs4 = SAU.remove_equiv_wo_unkhps hp skip_hps defs3 in
          let defs5 = SAU.find_closure_eq hp args0 defs4 in
          (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
          (* let _ = DD.info_pprint ("defs4: " ^ (pr1 defs4)) no_pos in *)
          (*remove duplicate with self-recursive*)
          (* let base_case_exist,defs4 = SAU.remove_dups_recursive hp args0 unk_hps defs3 in *)
          (*find longest hnodes common for more than 2 formulas*)
          (*each hds of hdss is def of a next_root*)
          (* let defs5 = List.filter (fun f -> have_roots args0 f) defs4 in *)
          let old_disj = !Globals.pred_disj_unify in
          let disj_opt = !Globals.pred_elim_useless || !Globals.pred_disj_unify in
          let defs,elim_ss = if disj_opt then
            SAU.get_longest_common_hnodes_list prog is_pre hpdefs (skip_hps) unk_svl hp r non_r_args args0 defs5
          else
            let defs = SAU.mk_hprel_def prog is_pre hpdefs skip_hps unk_svl hp args0 defs5 no_pos in
          (defs,[])
          in
          let _ = Globals.pred_disj_unify := old_disj in
          if defs <> [] then (defs,elim_ss) else
            report_error no_pos "shape analysis: FAIL"
    end

let generalize_one_hp prog is_pre defs non_ptr_unk_hps unk_hps link_hps par_defs=
  let pr1 = pr_list_ln SAU.string_of_par_def_w_name_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  let pr3 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  Debug.no_2 "generalize_one_hp" pr1 !CP.print_svl (pr_pair pr2 pr3)
      (fun _ _ -> generalize_one_hp_x prog is_pre defs non_ptr_unk_hps
          unk_hps link_hps par_defs) par_defs unk_hps

let get_pdef_body_x unk_hps post_hps (a1,args,unk_args,a3,olf,orf)=
  let exchane_unk_post hp1 args f unk_args=
    let hpargs2 = CF.get_HRels_f f in
    match hpargs2 with
      | [(hp2,args2)] ->
          if CP.mem_svl hp2 unk_hps && (CP.mem_svl hp2 post_hps) &&
            SAU.eq_spec_var_order_list args args2 then
            let new_f = SAU.mkHRel_f hp1 args (CF.pos_of_formula f) in
            [(hp2,args,new_f,unk_args)]
          else [(hp1,args,f,unk_args)]
      | _ -> [(hp1,args,f,unk_args)]
  in
  match olf,orf with
    | Some f, None -> [(a1,args,f,unk_args)]
    | None, Some f -> if CP.mem_svl a1 unk_hps && not (CP.mem_svl a1 post_hps) then
          exchane_unk_post a1 args f unk_args
        else
          [(a1,args,f,unk_args)]
    | Some f1, Some f2 ->
        let f_body=
          let hps1 = CF.get_hp_rel_name_formula f1 in
          let hps2 = CF.get_hp_rel_name_formula f2 in
          if CP.intersect_svl hps1 hps2 <> [] then
            (*recurive case*)
            if CF.is_HRel_f f1 then f2 else f1
          else SAU.compose_subs f2 f1 (CF.pos_of_formula f2)
        in
        if SAU.is_trivial f_body (a1,args) then [] else
          [(a1,args,f_body,unk_args)]
    | None, None -> report_error no_pos "sa.obtain_def: can't happen 2"

let get_pdef_body unk_hps post_hps (a1,args,unk_args,a3,olf,orf)=
  let pr1 = SAU.string_of_par_def_w_name in
  let pr2 = pr_list (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl) in
  Debug.no_1 "get_pdef_body" pr1 pr2
      (fun _ -> get_pdef_body_x unk_hps post_hps (a1,args,unk_args,a3,olf,orf) )(a1,args,unk_args,a3,olf,orf)

(*=========SUBST DEF and PARDEF FIX==========*)
(*
  divide hp into three groups:
  - independent - ready for genalizing
  - dependent:
      - depend on non-recursive groups: susbst
      - depend on recusive groups: wait
*)
let pardef_subst_fix_x prog unk_hps groups=
  (* let get_hp_from_grp grp= *)
  (*   match grp with *)
  (*     | (hp,_,_,_)::_ -> hp *)
  (*     | [] -> report_error no_pos "sa.pardef_subst_fix_x: 1" *)
  (* in *)
  let is_rec_pardef (hp,_,f,_)=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_pardef (hp,_,f,_) =
    let hps = CF.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_pprint ("       rec hp: " ^ (!CP.print_sv hp)) no_pos; *)
    let dep_hps = List.filter (fun hp1 -> not ((CP.eq_spec_var hp hp1) (* || *)
    (* (CP.mem_svl hp1 unk_hps) *))) hps in
    (* DD.ninfo_pprint ("       rec rems: " ^ (!CP.print_svl rems)) no_pos; *)
    (dep_hps = [])
  in
  let is_rec_group grp=
    List.exists is_rec_pardef grp
  in
  let is_independ_group grp =
    List.for_all is_independ_pardef grp
  in
  (* let get_succ_hps_pardef (_,_,f,_)= *)
  (*   (CF.get_HRels_f f) *)
  (* in *)
  let process_dep_group grp rec_hps nrec_grps=
    (*not depends on any recursive hps, susbt it*)
    let ters,fss = List.split (List.map (SAU.succ_susbt prog nrec_grps unk_hps false) grp) in
    (*check all is false*)
    (* let pr = pr_list string_of_bool in *)
    (* DD.ninfo_pprint ("       bool: " ^ (pr ters)) no_pos; *)
    let new_grp_ls = List.concat fss in
    let ter = List.for_all (fun b -> not b) ters in
    (not ter, new_grp_ls)
  in
  let subst_dep_groups_x deps rec_hps nrec_grps=
    (*local_helper deps []*)
    let bs, new_deps = List.split (List.map (fun grp -> process_dep_group grp rec_hps nrec_grps) deps) in
    let new_deps1 = List.filter (fun l -> List.length l > 0) new_deps in
    (List.fold_left (fun b1 b2 -> b1 || b2) false bs, new_deps1)
  in
  (*for debugging*)
  let subst_dep_groups deps rec_hps nrec_grps=
    let pr0 = (pr_list_ln SAU.string_of_par_def_w_name_short) in
    let pr1 =  pr_list_ln pr0 in
    let pr2 = pr_pair string_of_bool pr1 in
    Debug.no_2 "subst_dep_groups" pr1 pr1 pr2
        (fun _ _ -> subst_dep_groups_x deps rec_hps nrec_grps) deps nrec_grps
  in
  (*END for debugging*)
  (*sort order of nrec_grps to subst*)
  let topo_sort_x dep_grps nrec_grps=
    (*get name of n_rec_hps, intial its number with 0*)
    let ini_order_from_grp grp=
      let (hp,_,_,_) = List.hd grp in
      (grp,hp,0) (*called one topo*)
    in
    let update_order_from_grp updated_hps incr (grp,hp, old_n)=
      if CP.mem_svl hp updated_hps then
        (grp,hp,old_n+incr)
      else (grp,hp,old_n)
    in
  (*each grp, find succ_hp, add number of each succ hp + 1*)
    let process_one_dep_grp topo dep_grp=
      let (hp,_,_,_) = List.hd dep_grp in
      let succ_hps = List.concat (List.map (fun (_,_,f,_) -> CF.get_hp_rel_name_formula f) dep_grp) in
    (*remove dups*)
      let succ_hps1 = Gen.BList.remove_dups_eq CP.eq_spec_var succ_hps in
    (* DD.ninfo_pprint ("       process_dep_group succ_hps: " ^ (!CP.print_svl succ_hps)) no_pos; *)
    (*remove itself hp and unk_hps*)
      let succ_hps2 = List.filter (fun hp1 -> not (CP.eq_spec_var hp1 hp) &&
          not (CP.mem_svl hp1 unk_hps)) succ_hps1
      in
      List.map (update_order_from_grp succ_hps2 1) topo
    in
    let topo0 = List.map ini_order_from_grp nrec_grps in
    let dep_grps = List.filter (fun grp -> List.length grp > 0) dep_grps in
    let topo1 = List.fold_left process_one_dep_grp topo0 dep_grps in
    (*sort decreasing and return the topo list*)
    let topo2 = List.sort (fun (_,_,n1) (_,_,n2) -> n2-n1) topo1 in
    topo2
  in
  (*for debugging*)
  let topo_sort dep_grps nrec_grps=
    let pr0 = (pr_list_ln SAU.string_of_par_def_w_name_short) in
    let pr1 =  pr_list_ln pr0 in
    let pr2 =  pr_list_ln (pr_triple pr0 !CP.print_sv string_of_int) in
    Debug.no_2 "topo_sort" pr1 pr1 pr2
        (fun _ _ -> topo_sort_x dep_grps nrec_grps) dep_grps nrec_grps
  in
  (*END for debugging*)
  let helper_x grps rec_inds nrec_inds=
    let indeps,deps = List.partition is_independ_group grps in
    (*classify indeps into rec and non_rec*)
    let lrec_inds,lnrec_inds = List.partition is_rec_group indeps in
    (*for return*)
    let res_rec_inds = rec_inds@lrec_inds in
    let res_nrec_inds = nrec_inds@lnrec_inds in
    (* let lrec_deps,l_nrec_deps = comp_rec_grps_fix res_rec_inds  deps in *)
    let lrec_deps,l_nrec_deps = List.partition is_rec_group deps in
    (*find deps on non_recs*)
    let rec_hps = List.map
      (fun grp -> let (hp,_,_,_) = List.hd grp in hp)
      (res_rec_inds@lrec_deps)
    in
    (*deps may have mutual rec*)
    let mutrec_term_grps,mutrec_nonterm_grps, deps_0,mutrec_hps = SAU.succ_subst_with_mutrec prog deps unk_hps in
    (*add rec grp*)
    let l_nrec_deps1 = List.filter
      (fun grp -> let (hp,_,_,_) = List.hd grp in not(CP.mem_svl hp mutrec_hps))
      l_nrec_deps
    in
    (*topo deps*)
    let deps_1 = mutrec_term_grps@mutrec_nonterm_grps @ deps_0 in
    let topo_nrec_grps = topo_sort deps_1 (res_nrec_inds@l_nrec_deps1) in
    (*remove order number*)
    let topo_nrec_grps1 = List.map (fun (grp,hp,_) -> (grp,hp)) topo_nrec_grps in
    let rec loop_helper deps0 nrec_grps=
      let rec look_up_newer_nrec ls (cur_grp,hp)=
        match ls with
          | [] -> cur_grp
          | dep_grp::gss ->
              begin
                  match dep_grp with
                    | [] ->  look_up_newer_nrec gss (cur_grp,hp)
                    | _ ->
                        let hp1,_,_,_ = List.hd dep_grp in
                        if CP.eq_spec_var hp1 hp then dep_grp
                        else look_up_newer_nrec gss (cur_grp,hp)
              end
      in
      match nrec_grps with
        | [] -> deps0
        | (nrec_grp,nrec_hp)::ss ->
            (*find the latest in deps0, if applicable*)
            let nrec_grp1 = look_up_newer_nrec deps0 (nrec_grp,nrec_hp) in
            let _, deps1 = subst_dep_groups deps0 rec_hps [nrec_grp1] in
            loop_helper deps1 ss
    in
    let deps1 = loop_helper deps_1 topo_nrec_grps1
    in
    (* let r, deps1 = subst_dep_groups deps rec_hps (res_nrec_inds@l_nrec_deps) in *)
    (* ((List.length indeps>0 || r), deps1, res_rec_inds,res_nrec_inds) *)
    (*re-classify rec_ndep*)
    let indeps2,deps2 = List.partition is_independ_group deps1 in
    (*classify indeps into rec and non_rec*)
    let rec_inds2, nrec_indeps2 = List.partition is_rec_group indeps2 in
    (false, deps2, res_rec_inds@rec_inds2,res_nrec_inds@nrec_indeps2)
  in
  (*for debugging*)
   let helper grps rec_inds nrec_inds=
     let pr1 = pr_list_ln (pr_list_ln SAU.string_of_par_def_w_name_short) in
     let pr2= pr_quad string_of_bool pr1 pr1 pr1 in
     Debug.no_3 "pardef_subst_fix:helper" pr1 pr1 pr1 pr2
         (fun _ _ _ -> helper_x grps rec_inds nrec_inds) grps rec_inds nrec_inds
   in
  (*END for debugging*)
  let rec helper_fix cur rec_indps nrec_indps=
    let r,new_cur,new_rec_indps,new_nrec_indps = helper cur rec_indps nrec_indps in
    if r then helper_fix new_cur new_rec_indps new_nrec_indps
    else
      (* let pr1 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl)) in *)
      (* let _ = DD.info_pprint ("      new_cur: " ^ (pr1 new_cur)) no_pos in *)
      (*subs new_cur with new_rec_indps (new_nrec_indps is substed already)*)
      let new_cur1 = List.map SAU.remove_dups_pardefs new_cur in
      let new_cur2 = SAU.succ_subst_with_rec_indp prog new_rec_indps unk_hps new_cur1 in
      (new_cur2@new_rec_indps@new_nrec_indps)
  in
  helper_fix groups [] []

(*this subst is for a nice matching between inferred HP
and lib based predicates*)
let pardef_subst_fix prog unk_hps groups=
  let pr1 = pr_list_ln (pr_list_ln SAU.string_of_par_def_w_name_short) in
  Debug.no_1 "pardef_subst_fix" pr1 pr1
      (fun _ -> pardef_subst_fix_x prog unk_hps groups) groups

let is_valid_pardef (_,args,f,_)=
  let ls_succ_args = snd (List.split (CF.get_HRels_f f)) in
  let succ_args = List.concat ls_succ_args in
  let ptrs = CF.get_ptrs_f f in
  let dups = (CP.intersect_svl ptrs succ_args) in
  let root_arg=
    match args with
      | [] -> report_error no_pos "sa.is_valid_pardef: hp must have at least one arguments"
      | a::_ -> a
  in
  let b1 = not (CP.mem_svl root_arg dups) in
  (b1 (* && (not (check_unsat f)) *))

let rec partition_pdefs_by_hp_name pdefs parts=
  match pdefs with
    | [] -> parts
    | (a1,a2,a3,a4)::xs ->
          let part,remains= List.partition (fun (hp_name,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[(a1,a2,a3,a4)]@part])

let generalize_hps_par_def_x prog is_pre non_ptr_unk_hps unk_hpargs link_hps post_hps
      pre_def_grps predef_hps par_defs=
  (*partition the set by hp_name*)
  let pr1 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl)) in
  let unk_hps = (List.map fst unk_hpargs) in
  let par_defs1 = List.concat (List.map (get_pdef_body unk_hps post_hps) par_defs) in
  let par_defs2 = (* List.filter is_valid_pardef *) par_defs1 in
  let groups = partition_pdefs_by_hp_name par_defs2 [] in
  (*do not generate anyting for LINK preds*)
  let groups1 = List.filter (fun grp ->
      match grp with
        | [] -> false
        | ((hp,_,_,_)::_) -> not (CP.mem_svl hp link_hps)
  ) groups
  in
  (*
    subst such that each partial def does not contain other hps
    dont subst recursively search_largest_matching between two formulas
  *)
  let _ = DD.tinfo_pprint ("      groups1: " ^ (pr1 groups)) no_pos in
  let groups20 = pardef_subst_fix prog unk_hps (groups1@pre_def_grps) in
  (*filter out groups of pre-preds which defined already*)
  let groups2 =  List.filter (fun grp ->
      match grp with
        | [] -> false
        | ((hp,_,_,_)::_) -> not (CP.mem_svl hp predef_hps)
  ) groups20
  in
  (* let _ = Debug.info_pprint ("     END: " ) no_pos in *)
  (*remove empty*)
  let _ = DD.tinfo_pprint ("      groups2: " ^ (pr1 groups2)) no_pos in
  let groups3 = List.filter (fun grp -> grp <> []) groups2 in
  let _ = DD.binfo_hprint (add_str "before remove redundant" pr1) groups2 no_pos in
  (*each group, do union partial definition*)
  let hpdefs,elim_ss = List.fold_left (fun (hpdefs,elim_ss) pdefs->
      let new_defs,ss = generalize_one_hp prog is_pre hpdefs non_ptr_unk_hps unk_hps link_hps pdefs in
      ((hpdefs@new_defs), elim_ss@ss)
  ) ([],[]) groups3
  in
  let prh = Cprinter.string_of_h_formula in
  let _ = DD.binfo_hprint (add_str "elim_ss" (pr_list (pr_pair prh prh))) elim_ss no_pos in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr_hpd = pr_list (fun (_,a)-> pr2 a) in
  let _ = DD.binfo_hprint (add_str "after remove redundant" pr_hpd) hpdefs no_pos in
  let hpdefs1 =
    if !Globals.pred_elim_useless then
      List.map (fun (hp,(a,b,def)) ->
          (hp, (a,b,CF.subst_hrel_f def elim_ss))) hpdefs
    else
      hpdefs
  in
  hpdefs1

let generalize_hps_par_def prog is_pre non_ptr_unk_hps unk_hpargs link_hps post_hps pre_defs predef_hps par_defs=
 let pr1 = pr_list_ln SAU.string_of_par_def_w_name in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr3 = fun (_,a)-> pr2 a in
  Debug.no_3 "generalize_hps_par_def" !CP.print_svl !CP.print_svl pr1 (pr_list_ln pr3)
      (fun _ _ _ -> generalize_hps_par_def_x prog is_pre non_ptr_unk_hps unk_hpargs
          link_hps post_hps pre_defs predef_hps par_defs)
      post_hps link_hps par_defs

(**********get more definition from cs once, by right should loop************)
(* let generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs= *)
(*   let generalize_hps_one_cs constr= *)
(*     let lhs,rhs = constr.CF.hprel_lhs,constr.CF.hprel_rhs in *)
(*     let lhds, lhvs,l_hp = CF.get_hp_rel_formula lhs in *)
(*     let rhds, rhvs,r_hp = CF.get_hp_rel_formula rhs in *)
(*     let hp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (l_hp@r_hp) in *)
(*     (\*filer def hp out*\) *)
(*     let diff = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 (hpdefs@callee_hps))) hp_args in *)
(*     match diff with *)
(*       | [] -> ([],[],[]) (\*drop constraint, no new definition*\) *)
(*       | [(hp,args)] -> begin *)
(*           if CP.mem_svl hp hpdefs then (\*defined already drop constraint, no new definition*\) *)
(*             let _ = DD.binfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*             let _ = DD.binfo_pprint ("         " ^ (!CP.print_sv hp) ^ " is defined already: drop the constraint") no_pos in *)
(*             ([constr],[],[]) *)
(*           else if CP.mem_svl hp unk_hps then *)
(*             let _ = DD.binfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*             let _ = DD.binfo_pprint ("         " ^ (!CP.print_sv hp) ^ " is unknown. pass to next step") no_pos in *)
(*             ([constr],[],[]) *)
(*           else *)
(*             let keep_ptrs = SAU.look_up_closed_ptr_args prog (lhds@rhds) (lhvs@rhvs) args in *)
(*             let p = CF.pos_of_formula lhs in *)
(*             let nlhs = CF.mkStar lhs rhs  CF.Flow_combine p in *)
(*             let hpargs = CF.get_HRels_f nlhs in *)
(*             let hpdefs1 = *)
(*               let lhps = CF.get_hp_rel_name_formula lhs in *)
(*               let rhps = CF.get_hp_rel_name_formula rhs in *)
(*               if (CP.intersect_svl lhps rhps) = [] then hpdefs else hpdefs@[hp] *)
(*             in *)
(*             let hpargs1 = List.filter (fun (hp1,_) -> CP.mem_svl hp1 hpdefs1) hpargs in *)
(*             let keep_def_hps = List.concat (List.map (SAU.get_intersect_hps keep_ptrs) hpargs1) in *)
(*             let r = CF.drop_data_view_hrel_nodes nlhs SAU.check_nbelongsto_dnode SAU.check_nbelongsto_vnode SAU.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in *)
(*             if (not (SAU.is_empty_f r)) then *)
(*               let _ = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*               let _ = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")=" ^ *)
(*                   (Cprinter.prtt_string_of_formula r) ) no_pos in *)
(*                   ([],[((CP.HPRelDefn hp, (\*CF.formula_of_heap*\) *)
(*                   (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, p)) , r))], [hp]) *)
(*             else *)
(*               ([constr],[], []) *)
(*         end *)
(*       | _ -> ([constr],[], []) (\*keep constraint, no new definition*\) *)
(*   in *)
(*   let cs1, hp_defs, hp_names = List.fold_left (fun (ls1,ls2,ls3) c -> *)
(*       let r1,r2,r3 = generalize_hps_one_cs c in *)
(*   (ls1@r1, ls2@r2, ls3@r3) *)
(*   ) ([],[],[]) cs *)
(*   in *)
(*   (\*combine hp_defs*\) *)
(*   let hpdefs = SAU.combine_hpdefs hp_defs in *)
(*   (cs1, hpdefs, hp_names) *)

(* let generalize_hps_cs prog callee_hps hpdefs unk_hps cs= *)
(*    let pr1 = pr_list_ln Cprinter.string_of_hprel in *)
(*    let pr3  = pr_list Cprinter.string_of_hp_rel_def in *)
(*    let pr4 (_,b,c) = let pr = pr_pair pr3 !CP.print_svl in pr (b,c) in *)
(*   Debug.no_3 "generalize_hps_cs" pr1 !CP.print_svl !CP.print_svl pr4 *)
(*       (fun _ _ _ -> generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs) cs  callee_hps hpdefs *)

(*for tupled defs*)
let generalize_hps_cs_new_x prog callee_hps hpdefs unk_hps link_hps cs=
  let generalize_hps_one_cs constr=
    let lhs,rhs = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
    let lhds, lhvs,l_hp = CF.get_hp_rel_formula lhs in
    let rhds, rhvs,r_hp = CF.get_hp_rel_formula rhs in
    let lhp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (l_hp) in
    let rhp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (r_hp) in
    (*filer def hp out*)
    let dfs = (hpdefs@callee_hps@unk_hps) in
    let diff = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 dfs)) lhp_args in
    let diff1 = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 link_hps)) diff in
    match diff1 with
      | [] -> ([],[],[]) (*drop constraint, no new definition*)
      | _ -> begin
          let _ = DD.binfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
          if lhvs <> [] || lhds <> [] then
            ([constr],[],[])
          else
            let lhps, ls_largs = List.split lhp_args in
            let rhps, ls_rargs = List.split rhp_args in
            let largs = CP.remove_dups_svl (List.concat ls_largs) in
            let rargs = CP.remove_dups_svl (List.concat ls_rargs) in
            let keep_ptrs = SAU.look_up_closed_ptr_args prog (lhds@rhds) (lhvs@rhvs) (largs@rargs) in
            let pos = CF.pos_of_formula lhs in
            let nrhs = CF.mkAnd_pure rhs (MCP.mix_of_pure (CF.get_pure lhs)) pos in
            let keep_def_hps = lhps@rhps@unk_hps@hpdefs in
            let r = CF.drop_data_view_hrel_nodes nrhs SAU.check_nbelongsto_dnode SAU.check_nbelongsto_vnode SAU.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in
            if (not (SAU.is_empty_f r)) then
              let hps = List.map fst diff in
              let hfs = List.map (fun (hp,args) -> (CF.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos))) diff in
              let hf = CF.join_star_conjunctions hfs in
              let def_tit = match hps with
                | [hp] -> CP.HPRelDefn hp
                | _ -> CP.HPRelLDefn hps
              in
              let _ = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" pos in
              let _ = DD.ninfo_pprint ((let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr diff) ^ "::=" ^
                  (Cprinter.prtt_string_of_formula r) ) pos in
                  ([],[((def_tit, hf , r))], hps)
            else
              ([constr],[], [])
        end
  in
  let cs1, hp_defs, hp_names = List.fold_left (fun (ls1,ls2,ls3) c ->
      let r1,r2,r3 = generalize_hps_one_cs c in
  (ls1@r1, ls2@r2, ls3@r3)
  ) ([],[],[]) cs
  in
  (*combine hp_defs*)
  let hpdefs = SAU.combine_hpdefs hp_defs in
  (cs1, hpdefs, hp_names)

let generalize_hps_cs_new prog callee_hps hpdefs unk_hps link_hps cs=
   let pr1 = pr_list_ln Cprinter.string_of_hprel in
   let pr3  = pr_list Cprinter.string_of_hp_rel_def in
   let pr4 (_,b,c) = let pr = pr_pair pr3 !CP.print_svl in pr (b,c) in
  Debug.no_4 "generalize_hps_cs_new" pr1 !CP.print_svl !CP.print_svl !CP.print_svl pr4
      (fun _ _ _ _ -> generalize_hps_cs_new_x prog callee_hps hpdefs unk_hps link_hps cs)
      cs callee_hps hpdefs unk_hps

let generalize_hps_x prog is_pre callee_hps unk_hps link_hps sel_post_hps pre_defs predef_hps cs par_defs=
  DD.binfo_pprint ">>>>>> step 6: generalization <<<<<<" no_pos;
(*general par_defs*)
  let non_ptr_unk_hps = List.concat (List.map (fun (hp,args) ->
      if List.exists (fun a ->
          not ( CP.is_node_typ a))
        args then [hp]
      else []) unk_hps) in
  let pair_names_defs = generalize_hps_par_def prog is_pre non_ptr_unk_hps unk_hps link_hps
    sel_post_hps pre_defs predef_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
(*for each constraints, we may pick more definitions*)
  let remain_constr, hp_def1, hp_names2 = generalize_hps_cs_new prog callee_hps hp_names (List.map fst unk_hps) link_hps cs in
  (*room for unk predicates processing*)
  (remain_constr, (hp_defs@hp_def1), hp_names@hp_names2)

let generalize_hps prog is_pre callee_hps unk_hps link_hps sel_post_hps pre_defs predef_hps cs par_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln SAU.string_of_par_def_w_name in
  let pr3 = pr_list Cprinter.string_of_hp_rel_def in
  Debug.no_4 "generalize_hp" !CP.print_svl !CP.print_svl pr1 pr2 (pr_triple pr1 pr3 !CP.print_svl)
      (fun _ _ _ _ -> generalize_hps_x prog is_pre callee_hps unk_hps link_hps sel_post_hps
          pre_defs predef_hps cs par_defs)
      callee_hps link_hps cs par_defs

(***************************************************************
                     END GENERALIZATION
****************************************************************)

(***************************************************************
                      LIB MATCHING
****************************************************************)
let collect_sel_hp_def_x defs sel_hps unk_hps m=
  (*currently, use the first lib matched*)
  let m = List.map (fun (hp, l) -> (hp, List.hd l)) m in
  let mlib = List.map (fun (hp, _) -> hp) m in
  let rec look_up_lib hp ms=
    match ms with
      | [] -> None
      | (hp1,hf1)::ss -> if CP.eq_spec_var hp hp1 then
            Some (CF.formula_of_heap hf1 no_pos)
          else look_up_lib hp ss
  in
  let mk_hprel_def kind hprel opf opflib=
    {
        CF.hprel_def_kind = kind;
        CF.hprel_def_hrel = hprel;
        CF.hprel_def_body = opf;
        CF.hprel_def_body_lib = opflib;
    }
  in
  let compute_def_w_lib (hp,(a,hprel,f))=
    let olib = look_up_lib hp m in
    (* if CP.mem_svl hp unk_hps then *)
    (*   (mk_hprel_def a hprel None None) *)
    (* else *)
    begin
        let f1 =
          match olib with
            | None ->
            (*subs lib form inside f if applicable*)
                let f_subst = CF.subst_hrel_hview_f f m in
                f_subst
            | Some lib_f -> lib_f
        in
        (mk_hprel_def a hprel (Some f) (Some f1))
    end
  in
  let look_up_depend cur_hp_sel f=
    let hps = CF.get_hp_rel_name_formula f in
    let dep_hp = Gen.BList.difference_eq CP.eq_spec_var hps (cur_hp_sel(* @unk_hps *)) in
    (CP.remove_dups_svl dep_hp)
  in
  let look_up_hp_def new_sel_hps non_sel_hp_def=
    List.partition (fun (hp,_) -> CP.mem_svl hp new_sel_hps) non_sel_hp_def
  in
  let rec find_closed_sel cur_sel cur_sel_hpdef non_sel_hp_def incr=
    let rec helper1 ls res=
      match ls with
        | [] -> res
        | (hp,(a,hf,f))::lss ->
            let incr =
              if CP.mem_svl hp (cur_sel(* @unk_hps *)) then
                []
              else
                [hp]
            in
            let new_hp_dep = look_up_depend cur_sel f in
            helper1 lss (CP.remove_dups_svl (res@incr@new_hp_dep))
    in
    let incr_sel_hps = helper1 incr [] in
    (*nothing new*)
    if incr_sel_hps = [] then cur_sel_hpdef else
      let incr_sel_hp_def,remain_hp_defs = look_up_hp_def incr_sel_hps non_sel_hp_def in
      find_closed_sel (cur_sel@incr_sel_hps) (cur_sel_hpdef@incr_sel_hp_def) remain_hp_defs incr_sel_hp_def
  in
  let defsw = List.map (fun (a,hf,f) ->
      (List.hd (CF.get_hp_rel_name_h_formula hf), (a,hf,f))) defs in
  let sel_defw,remain_hp_defs = List.partition (fun (hp,_) -> CP.mem_svl hp sel_hps) defsw in
  (* let sel_defw1 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) sel_defw in *)
  let closed_sel_defw = find_closed_sel sel_hps sel_defw remain_hp_defs sel_defw in
  let all_sel_defw = List.map compute_def_w_lib closed_sel_defw in
  (*remove hp not in orig but == lib*)
  let inter_lib = Gen.BList.difference_eq CP.eq_spec_var mlib sel_hps in
  List.filter (fun hdef ->
      let a1 = hdef.CF.hprel_def_kind in
      let hp = SAU.get_hpdef_name a1 in
      not (CP.mem_svl hp inter_lib))
      all_sel_defw

let collect_sel_hp_def defs sel_hps unk_hps m=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_svl in
  let pr3b = pr_list_ln Cprinter.prtt_string_of_h_formula in
  let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^
      (* ( String.concat " OR " view_names) *) (pr3b vns) in
  let pr3 = pr_list_ln pr3a in
  let pr4 = (pr_list_ln Cprinter.string_of_hprel_def) in
  Debug.no_3 "collect_sel_hp_def" pr1 pr2 pr3 pr4
      (fun _ _ _ -> collect_sel_hp_def_x defs sel_hps unk_hps m) defs sel_hps m

let match_hps_views_x (hp_defs: CF.hp_rel_def list) (vdcls: CA.view_decl list):
(CP.spec_var* CF.h_formula list) list=
  let hp_defs1 = List.filter (fun (def,_,_) -> match def with
    | CP.RelDefn _ -> true
    | _ -> false
  ) hp_defs in
  let m = List.map (SAU.match_one_hp_views vdcls) hp_defs1 in
    (List.filter (fun (_,l) -> l<>[]) m)

let match_hps_views (hp_defs: CF.hp_rel_def list) (vdcls: CA.view_decl list):
(CP.spec_var* CF.h_formula list) list=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln  Cprinter.prtt_string_of_h_formula  in
  let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^
      (* ( String.concat " OR " view_names) *) (pr2 vns) in
  let pr3 = pr_list_ln pr3a in
  let pr4 = pr_list_ln (Cprinter.string_of_view_decl) in
  Debug.no_2 "match_hps_views" pr1 pr4 pr3
      (fun _ _ -> match_hps_views_x hp_defs vdcls) hp_defs vdcls


(***************************************************************
                     END LIB MATCHING
****************************************************************)

let infer_shapes_init_pre_x prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
 hp_rel_unkmap detect_dang (* :(CP.spec_var list * CF.hp_rel_def list* (CP.spec_var * CP.spec_var list) list) *) =
  let _ = DD.binfo_pprint ">>>>>> step pre-4: remove unused predicates<<<<<<" no_pos in
  let constrs01 = (* SAU.remove_dups_constr *) constrs0 in
  let constrs02 = List.map SAU.weaken_trivial_constr_pre constrs01 in
  let unused_pre_hps, constrs0, unk_map1 =
    if detect_dang then elim_unused_pre_preds (sel_post_hps@link_hps) constrs02 hp_rel_unkmap
    else ([], constrs02, hp_rel_unkmap)
  in
  let unk_hpargs1 = Gen.BList.remove_dups_eq cmp_hpargs_fn (unk_hps@unused_pre_hps) in
  let unk_hps1 = (List.map fst unk_hpargs1) in
  let _ = DD.binfo_pprint ">>>>>> pre-predicates: step pre-5: group & simpl impl<<<<<<" no_pos in
  let pr_par_defs,rem_constr1 = get_par_defs_pre constrs0 in
  let _ = DD.binfo_pprint ">>>>>> pre-predicates: step pre-6: combine<<<<<<" no_pos in
  let par_defs, rem_constrs2, hconj_unify_cond = combine_pdefs_pre prog unk_hps1 link_hps pr_par_defs in
  let _ = DD.binfo_pprint ">>>>>> pre-predicates: step pre-7: remove redundant x!=null: not implemented yet<<<<<<" no_pos in
  let _ = DD.binfo_pprint ">>>>>> pre-predicates: step pre-8: strengthen<<<<<<" no_pos in
  let rem_constrs3, hp_defs, defined_hps = generalize_hps prog true callee_hps unk_hpargs1 link_hps sel_post_hps [] []
    constrs0 par_defs in
  (* check hconj_unify_cond*)
  let hp_defs1, new_equivs, unk_equivs = if hconj_unify_cond = [] then (hp_defs,[], []) else
    let is_sat, new_hpdefs, equivs, unk_equivs = SAC.reverify_cond prog unk_hps1 link_hps hp_defs hconj_unify_cond in
    if not is_sat then report_error no_pos "SA.infer_shapes_init_pre: HEAP CONJS do not SAT"
    else (new_hpdefs, equivs,  unk_equivs)
  in
 (* generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in *)
  (* let hp_names,hp_defs = List.split pair_names_defs in *)
  (*TODO: check consistency of the solution against rem_constraints: LOOP*)
  (defined_hps,hp_defs1,unk_hpargs1, unk_map1, new_equivs, unk_equivs)

let infer_shapes_init_pre prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
      hp_rel_unkmap detect_dang (* :(CP.spec_var list * CF.hp_rel_def list * (CP.spec_var * CP.spec_var list) list) *) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_,_,_) = (pr_triple pr2 pr3 pr4) (a,b,c) in
  Debug.no_1 "infer_shapes_init_pre" pr1 pr5
      (fun _ -> infer_shapes_init_pre_x prog constrs0 callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
          hp_rel_unkmap detect_dang) constrs0

let infer_shapes_init_post_x prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps
      hp_rel_unkmap detect_dang pre_defs (* :(CP.spec_var list * CF.hp_rel_def list * (CP.spec_var * CP.spec_var list) list * ) *) =
  let constrs0a = (* SAU.remove_dups_constr *) constrs0 in
  let _ = DD.binfo_pprint ">>>>>> step post-4: step remove unused predicates<<<<<<" no_pos in
  let unused_post_hps,constrs0,unk_map1 =
    if detect_dang then elim_unused_post_preds (sel_post_hps@link_hps) constrs0a hp_rel_unkmap
    else ([], constrs0a, hp_rel_unkmap)
  in
  let unk_hps1 = Gen.BList.remove_dups_eq cmp_hpargs_fn (unk_hps@unused_post_hps) in
  let par_defs = get_par_defs_post constrs0 in
  let _ = DD.binfo_pprint ">>>>>> post-predicates: step post-5: remove redundant x!=null : not implemented yet<<<<<<" no_pos in

  let _ = DD.binfo_pprint ">>>>>> post-predicates: step post-61: weaken<<<<<<" no_pos in
  (*subst pre-preds into if they are not recursive -do with care*)
  let pre_defs, pre_hps = SAU.extract_fwd_pre_defs [] pre_defs in
  let pair_names_defs = generalize_hps_par_def prog false non_ptr_unk_hps unk_hps1 link_hps sel_post_hps pre_defs pre_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
  (hp_names,hp_defs,unk_hps1,unk_map1)

let infer_shapes_init_post prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap
      detect_dang pre_defs
      (* :(CP.spec_var list * CF.hp_rel_def list * (CP.spec_var * CP.spec_var list) list ) *) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_) = (pr_triple pr2 pr3 pr4) (a,b,c) in
  Debug.no_1 "infer_shapes_init_post" pr1 pr5
      (fun _ -> infer_shapes_init_post_x prog constrs0 non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap
      detect_dang pre_defs ) constrs0

let partition_constrs_x constrs post_hps=
  let classify (pre_cs,post_cs,rem) cs =
    let is_post =
      try
        let ohp = CF.extract_hrel_head cs.CF.hprel_rhs in
        match ohp with
          | Some hp -> (CP.mem_svl hp post_hps)
          | None -> false
      with _ -> false
    in
    if is_post then (pre_cs,post_cs@[cs],rem) else
      let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
      if CP.intersect_svl post_hps lhs_hps = [] then
        (pre_cs@[cs],post_cs,rem)
      else (pre_cs,post_cs,rem@[cs])
  in
  List.fold_left classify ([],[],[]) constrs

let partition_constrs constrs post_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  Debug.no_2 "partition_constrs" pr1 pr2 (pr_triple pr1 pr1 pr1)
      (fun _ _ -> partition_constrs_x constrs post_hps) constrs post_hps


let infer_shapes_from_obligation_x prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap detect_dang pre_defs post_defs=
  let constrs1 = SAU.remove_dups_constr constrs0 in
  (*for each oblg, subst + simplify + generate new constrs with new hp post in rhs*)

  (*call to infer_shape? proper? or post?*)
  ([],[],[],[])

let infer_shapes_from_obligation prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap detect_dang pre_defs post_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_) = (pr_triple pr2 pr3 pr4) (a,b,c) in
  Debug.no_1 "infer_shapes_from_obligation" pr1 pr5
      (fun _ -> infer_shapes_from_obligation_x prog constrs0 non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap detect_dang pre_defs post_defs)
      constrs0

let infer_shapes_proper prog proc_name (constrs2: CF.hprel list) callee_hps sel_hp_rels sel_post_hps
      (unk_map2: ((CP.spec_var * int list) * CP.xpure_view) list)
      prog_vars unk_hpargs link_hpargs detect_dang: (CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list * (CP.spec_var * CP.spec_var list) list *  (CP.spec_var *CP.spec_var list) list * (CP.spec_var *CP.spec_var) list)=
  let unk_hps = List.map fst unk_hpargs in
  let link_hps = List.map fst link_hpargs in
  let _ = DD.binfo_pprint ">>>>>> step 3: apply transitive implication<<<<<<" no_pos in
  let constrs3a,_ = apply_transitive_impl_fix prog sel_post_hps callee_hps unk_map2
     unk_hps constrs2 in
  let constrs3 = List.map (SAU.simp_match_unknown unk_hps link_hps) constrs3a in
  (*partition constraints into 2 groups: pre-predicates, post-predicates*)
  let pre_constrs,post_constrs, oblg_constrs = partition_constrs constrs3 sel_post_hps in
  (*find inital sol*)
  let _ = DD.binfo_pprint ">>>>>> pre-predicates<<<<<<" no_pos in
  let pre_hps, pre_defs, unk_hpargs1,unk_map3, pre_equivs, unk_equivs = infer_shapes_init_pre prog pre_constrs callee_hps []
    sel_post_hps unk_hpargs link_hps unk_map2 detect_dang in
  let pre_defs1, unify_equiv_map1 = if (* !Globals.sa_conj_unify *) true then
    SAC.do_unify prog unk_hps link_hps pre_defs
  else
    (pre_defs, [])
  in
  let pre_defs2, unify_equiv_map11 =
    if !Globals.pred_equiv then (*TODO: should move it to normalization*)
      SAC.unify_pred prog unk_hps link_hps pre_defs1 unify_equiv_map1
    else (pre_defs1, unify_equiv_map1)
  in
  let _ = DD.binfo_pprint ">>>>>> post-predicates<<<<<<" no_pos in
  let post_constrs1 = SAU.subst_equiv_hprel unify_equiv_map11 post_constrs in
  let post_hps, post_defs,unk_hpargs2,unk_map4  = infer_shapes_init_post prog post_constrs1 []
    sel_post_hps unk_hpargs1 link_hps unk_map3 detect_dang pre_defs2 in
  let post_defs1,unify_equiv_map2 = if false then (*this just for pre-preds*)
    SAC.do_unify prog unk_hps link_hps post_defs
  else
    (post_defs,unify_equiv_map11)
  in
  let oblg_hps, oblg_defs,unk_hpargs3,unk_map5  = infer_shapes_from_obligation prog oblg_constrs []
    sel_post_hps unk_hpargs2 link_hps unk_map4 detect_dang pre_defs2 post_defs1 in
  let defs1 = (pre_defs2@post_defs1) in
  (*normalization*)
  let defs2a, unify_equiv_map3 =
    if !Globals.pred_equiv then (*TODO: should move it to normalization*)
      SAC.unify_pred prog unk_hps link_hps defs1 (pre_equivs@unify_equiv_map2@unk_equivs)
    else (defs1, unify_equiv_map2)
  in
  let defs2 = SAC.generate_hp_def_from_unk_hps defs2a unk_hpargs2 (pre_hps@post_hps) sel_post_hps unk_map4 unify_equiv_map3 in
  let defs3 = if !Globals.sa_inlining then
    (* SAU.transform_unk_hps_to_pure (defs3b) unk_hp_frargs *)
    let defs3a = SAC.transform_xpure_to_pure defs2 unk_map4 in
    defs3a
  else defs2
  in
  (constrs2, defs3,[], unk_hpargs2, link_hpargs,(pre_equivs@unify_equiv_map2@unk_equivs))

let infer_shapes_core prog proc_name (constrs0: CF.hprel list) callee_hps sel_hp_rels sel_post_hps hp_rel_unkmap
      unk_hpargs0a link_hpargs need_preprocess detect_dang:
      (CF.hprel list * CF.hp_rel_def list * (CP.spec_var*CP.exp list * CP.exp list) list *
          (CP.spec_var * CP.spec_var list) list * (CP.spec_var *CP.spec_var list) list * (CP.spec_var * CP.spec_var) list)=
  (*move to outer func*)
  let prog_vars = [] in (*TODO: improve for hip*)
  (********************************)
  let unk_hpargs0b = List.fold_left (fun ls ((hp,_),xpure) ->
      let args = match xpure.CP.xpure_view_node with
        | None -> xpure.CP.xpure_view_arguments
        | Some r -> r::xpure.CP.xpure_view_arguments
      in
      ls@[(hp,args)]
  ) [] hp_rel_unkmap
  in
  let unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (unk_hpargs0a@unk_hpargs0b) in
  (* let constrs, unk_map0, unk_hpargs = SAC.syn_unk constrs0 hp_rel_unkmap sel_post_hps no_pos in *)
  let constrs1,unk_map,unk_hpargs, link_hpargs3 =
    if need_preprocess then
       (*unk analysis*)
      let _ = DD.binfo_pprint ">>>>>> step 1: find dangling ptrs, link pre and post-preds dangling preds<<<<<<" no_pos in
      (* let constrs3, unk_map1, unk_hpargs = SAC.detect_dangling_pred constrs2 sel_hp_rels unk_map in *)
      let constrs1, unk_hpargs1, unk_map1, link_hpargs1 =
        if detect_dang then
          SAC.analize_unk prog sel_post_hps constrs0 hp_rel_unkmap unk_hpargs link_hpargs
        else (constrs0, unk_hpargs,hp_rel_unkmap,link_hpargs)
      in
      let _ = DD.binfo_pprint ">>>>>> step 2: split constraints based on pre and post-preds<<<<<<" no_pos in
      (*split constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
      let unk_hps1 = List.map fst unk_hpargs1 in
      let link_hps1 = List.map fst link_hpargs1 in
      let constrs2, unk_map2, link_hpargs2 = split_constr prog constrs1 sel_post_hps prog_vars unk_map1 unk_hps1 link_hps1 in
      let link_hpargs3= link_hpargs1@link_hpargs2 in
       (constrs2, unk_map2,unk_hpargs1, link_hpargs3)
    else
      (constrs0, hp_rel_unkmap, unk_hpargs, link_hpargs)
  in
  (* let unk_hps = (List.map fst unk_hpargs) in *)
  (*TODO: remove detect dangling at pre/post process*)
  (*TEMP*)
  let user_detect_dang =  false (* detect_dang && !Globals.sa_elim_unused_preds  *)in
  (* let _ = Debug.info_pprint ("  link_hpargs3: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                             in pr link_hpargs3)) no_pos *)
  (*  in *)
  infer_shapes_proper prog proc_name constrs1 callee_hps sel_hp_rels sel_post_hps unk_map prog_vars
      unk_hpargs link_hpargs3 user_detect_dang

let infer_shapes_x prog proc_name (constrs0: CF.hprel list) sel_hps sel_post_hps hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang:
      (CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list ) =
  (*move to outer func*)
  (* let callee_hpdefs = *)
  (*   try *)
  (*       Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name *)
  (*   with _ -> [] *)
  (* in *)
  (* let callee_hps = List.map (fun (hpname,_,_) -> SAU.get_hpdef_name hpname) callee_hpdefs in *)
  let callee_hps = [] in
  (* let _ = DD.info_pprint ("  sel_hps:" ^ !CP.print_svl sel_hps) no_pos in *)
  (*remove hp(x) --> hp(x)*)
  (* let constrs1 = List.filter (fun cs -> not(SAU.is_trivial_constr cs)) constrs0 in *)
  let constr, hp_defs, c, unk_hpargs2, link_hpargs2, equivs = infer_shapes_core prog proc_name constrs0 callee_hps sel_hps
    sel_post_hps hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang in
  let link_hp_defs = SAC.generate_hp_def_from_link_hps prog equivs link_hpargs2 in
  let hp_defs1,tupled_defs = SAU.partition_tupled hp_defs in
  (*decide what to show: DO NOT SHOW hps relating to tupled defs*)
  let m = match_hps_views hp_defs1 prog.CA.prog_view_decls in
  let sel_hp_defs = collect_sel_hp_def hp_defs1 sel_hps unk_hpargs2 m in
  let tupled_defs1 = List.map (fun (a, hf, f) -> {
      CF.hprel_def_kind = a;
      CF.hprel_def_hrel = hf;
      CF.hprel_def_body = Some f;
      CF.hprel_def_body_lib = Some f;
  }
  ) tupled_defs in
  let shown_defs = if !Globals.sa_elim_unused_preds then sel_hp_defs@link_hp_defs else
    sel_hp_defs@tupled_defs1@link_hp_defs
  in
  let _ = List.iter (fun hp_def -> rel_def_stk # push hp_def) shown_defs in
  (constr, hp_defs, c)

let infer_shapes prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
      need_preprocess detect_dang:
 (CF.hprel list * CF.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) =
  let pr0 = pr_list !CP.print_exp in
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in
  (* let pr4 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in *)
  let pr4 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_6 "infer_shapes" pr_id pr1 !CP.print_svl pr4 pr5 pr5 (pr_triple pr1 pr2 pr3)
      (fun _ _ _ _ _ _ -> infer_shapes_x prog proc_name hp_constrs sel_hp_rels
          sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
          need_preprocess detect_dang)
      proc_name hp_constrs sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
