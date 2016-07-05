#include "xdebug.cppo"
open VarGen
open Globals
open Others
open Gen

module DD = Debug
module Err = Error
module CA = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
(* module TP = Tpdispatcher *)
(* module SAC = Sacore *)
(* module SAU = Sautility *)
module IC = Icontext
let step_change = new Gen.change_flag

(* outcome from shape_infer *)
let rel_def_stk : CF.hprel_def Gen.stack_pr = new Gen.stack_pr "rel-def-stk"
  Cprinter.string_of_hprel_def_short (==)


(***************************************************************)
(*      APPLY TRANS IMPL     *)
(****************************************************************)
let collect_ho_ass iprog cprog is_pre def_hps (acc_constrs, post_no_def) cs=
  let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
  let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in
  let linfer_hps = CP.remove_dups_svl (CP.diff_svl (lhs_hps) def_hps) in
  let rinfer_hps =  (CP.diff_svl (rhs_hps) def_hps) in
  let infer_hps = CP.remove_dups_svl (linfer_hps@rinfer_hps) in
  (* if infer_hps = [] then (acc_constrs, post_no_def) else *)
  let log_str = if is_pre then PK_Pre_Oblg else PK_Post_Oblg in
  let  _ = DD.info_zprint (lazy (((string_of_proving_kind log_str) ^ ":\n" ^ (Cprinter.string_of_hprel_short cs)))) no_pos in
  (* let tmp = (check_is_classic ()) in *)
  (* let () = Wrapper.set_classic  true in *)
  let f = wrap_proving_kind log_str (Sacore.do_entail_check infer_hps iprog cprog) in
  let new_constrs = Wrapper.wrap_classic x_loc (Some true) f cs in
  (* let () = Wrapper.set_classic  tmp in *)
  (acc_constrs@new_constrs, post_no_def@linfer_hps)

(*input in fb
  output: true,susbs: can subst
*)

(*
dn is current node, it is one node of ldns
ss: subst from ldns -> ldns
*)
(*
equal_hps: are preds that are going to be generalized. DO NOT subst them
*)
let rec find_imply_subst_x prog unk_hps link_hps frozen_hps complex_hps constrs new_cs=
  let rec check_constr_duplicate (lhs,rhs) constrs=
    match constrs with
    | [] -> false
    | cs::ss -> if Sautil.checkeq_pair_formula (lhs,rhs)
        (cs.CF.hprel_lhs,cs.CF.hprel_rhs) then
        true
      else check_constr_duplicate (lhs,rhs) ss
  in
  let find_imply_one cs1 cs2=
    let () = Debug.ninfo_zprint (lazy (("    rhs: " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
    (*if this assumption is going to be equal generalized. do not subst*)
    let lhps = CF.get_hp_rel_name_formula cs2.CF.hprel_lhs in
    if List.length lhps<2 && CP.diff_svl lhps frozen_hps = [] then ([],[]) else
      let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_lhs in
      let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_rhs in
      match f1,f2 with
      | CF.Base lhs1, CF.Base rhs2 ->
        let r = Sautil.find_imply prog (List.map fst cs1.CF.unk_hps) (List.map fst cs2.CF.unk_hps)
            lhs1 cs1.CF.hprel_rhs cs2.CF.hprel_lhs rhs2 cs1.CF.hprel_guard frozen_hps complex_hps in
        begin
          match r with
          | Some (l,r,lhs_ss, rhs_ss,_) ->
            (*check duplicate*)
            if check_constr_duplicate (l,r) (constrs@new_cs) then ([],[])
            else
              begin
                let n_cs_hprel_guard =
                  match cs2.CF.hprel_guard with
                  | None -> None
                  | Some hf -> Some (x_add CF.subst lhs_ss hf)
                in
                let new_cs = {cs2 with
                              CF.predef_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.CF.predef_svl)@
                                   (CP.subst_var_list rhs_ss cs2.CF.predef_svl));
                              CF.unk_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.CF.unk_svl)@
                                   (CP.subst_var_list rhs_ss cs2.CF.unk_svl));
                              CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq
                                  ((List.map (fun (hp,args) -> (hp,CP.subst_var_list lhs_ss args)) cs1.CF.unk_hps)@
                                   (List.map (fun (hp,args) -> (hp,CP.subst_var_list rhs_ss args)) cs2.CF.unk_hps));
                              CF.hprel_lhs = l;
                              CF.hprel_guard = n_cs_hprel_guard;
                              CF.hprel_rhs = r;
                             }
                in
                let () = Debug.ninfo_zprint (lazy (("    new rhs: " ^ (Cprinter.string_of_hprel_short new_cs)))) no_pos in
                (*moved after pre-preds synthesized*)
                (* let l_hds, l_hvs,lhrels =CF.get_hp_rel_formula new_cs.CF.hprel_lhs in *)
                (* let r_hds, r_hvs,rhrels =CF.get_hp_rel_formula new_cs.CF.hprel_rhs in *)
                (* if (List.length l_hds > 0 || List.length l_hvs > 0) && List.length lhrels > 0 && *)
                (*    (\* (List.length r_hds > 0 || List.length r_hvs > 0) && *\) List.length rhrels > 0 *)
                (* then *)
                (*   let ho_constrs, _ = collect_ho_ass prog true [] ([], []) new_cs in *)
                (*   let ho_constrs1 = Sautil.remove_dups_constr ho_constrs in *)
                (*   if ho_constrs1==[] || *)
                (*     check_constr_duplicate (new_cs.CF.hprel_lhs,new_cs.CF.hprel_rhs) ho_constrs1 then *)
                (*       let new_cs1 = Sautil.simp_match_hp_w_unknown prog unk_hps link_hps new_cs in *)
                (*       ([new_cs1],[]) *)
                (*   else *)
                (*     (\***************  PRINTING*********************\) *)
                (*     let () = *)
                (*       begin *)
                (*         let pr = pr_list_ln Cprinter.string_of_hprel_short in *)
                (*         print_endline ""; *)
                (*         print_endline "\n*************************************************"; *)
                (*         print_endline "*******relational assumptions (obligation)********"; *)
                (*         print_endline "****************************************************"; *)
                (*         print_endline (pr ho_constrs1); *)
                (*         print_endline "*************************************" *)
                (*       end *)
                (*     in *)
                (*     (ho_constrs1, List.map fst3 lhrels) *)
                (*   (\***************  END PRINTING*********************\) *)
                (* else *)
                let new_cs1 = Sautil.simp_match_hp_w_unknown prog unk_hps link_hps new_cs in
                ([new_cs1],[])
              end
          | None -> ([],[])
        end
      | _ -> report_error no_pos "sa2.find_imply_one"
  in
  (*new_cs: one x one*)
  (* let rec helper_new_only don rest res= *)
  (*   match rest with *)
  (*     | [] -> res *)
  (*     | cs1::rest -> *)
  (*         let () = Debug.ninfo_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel cs1)))) no_pos in *)
  (*         let r = List.concat (List.map (find_imply_one cs1) (don@rest@res)) in *)
  (*         (helper_new_only (don@[cs1]) rest (res@r)) *)
  (* in *)
  let rec helper_new_only don rest is_changed unfrozen_hps=
    match rest with
    | [] -> is_changed,don,unfrozen_hps
    | cs1::rest ->
      let () = Debug.ninfo_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in
      if Sacore.cs_rhs_is_only_neqNull cs1 then
        (helper_new_only (don@[cs1]) rest is_changed unfrozen_hps)
      else
        let is_changed1, new_rest, n_unfrozen_hps1 = List.fold_left ( fun (b,res, r_unfroz_hps) cs2->
            let new_constrs, unfroz_hps = find_imply_one cs1 cs2 in
            if List.length new_constrs > 0 then
              (true,res@new_constrs, r_unfroz_hps@unfroz_hps)
            else (b,res@[cs2], r_unfroz_hps)
          ) (is_changed, [], []) (rest)
        in
        let is_changed2,new_don, n_unfrozen_hps2 = List.fold_left ( fun (b,res, r_unfroz_hps) cs2->
            let new_constrs, unfroz_hps = find_imply_one cs1 cs2 in
            if List.length new_constrs > 0 then
              (true,res@new_constrs,  r_unfroz_hps@unfroz_hps)
            else
              (b,res@[cs2], r_unfroz_hps)
          ) (is_changed1,[], []) (don)
        in
        (helper_new_only (new_don@[cs1]) new_rest is_changed2 (unfrozen_hps@n_unfrozen_hps1@n_unfrozen_hps2))
  in
  (*new_cs x constr*)
  (* let rec helper_old_new rest res= *)
  (*   match rest with *)
  (*     | [] -> res *)
  (*     | cs1::ss -> *)
  (*         let r = List.fold_left ( fun ls cs2 -> ls@(find_imply_one cs1 cs2)) res constrs in *)
  (*         helper_old_new ss r *)
  (* in *)
  let is_changed,new_cs1,unfrozen_hps =
    if List.length new_cs < 1 then (false, new_cs, []) else
      helper_new_only [] new_cs false []
  in
  (* let new_cs2 = helper_old_new new_cs [] in *)
  (is_changed,new_cs1(* @new_cs2 *),unfrozen_hps)

and find_imply_subst prog unk_hps link_hps equal_hps complex_hps constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_2 "find_imply_subst" pr1 pr1 (pr_triple string_of_bool pr1 !CP.print_svl)
    (fun _ _ -> find_imply_subst_x prog unk_hps link_hps equal_hps complex_hps constrs new_cs) constrs new_cs

and is_trivial cs= (Sautil.is_empty_f cs.CF.hprel_rhs) ||
                   (Sautil.is_empty_f cs.CF.hprel_lhs || Sautil.is_empty_f cs.CF.hprel_rhs)

and is_non_recursive_non_post_cs post_hps dang_hps constr=
  let lhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_lhs in
  let rhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_rhs in
  (CP.intersect_svl rhrel_svl post_hps = []) && ((CP.intersect lhrel_svl rhrel_svl) = [])

and subst_cs_w_other_cs_x prog post_hps dang_hps link_hps equal_hps complex_hps constrs new_cs=
  (*remove recursive cs and post-preds based to preserve soundness*)
  let constrs1 = List.filter (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)) constrs in
  let new_cs1,rem = List.partition (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)) new_cs in
  let b,new_cs2, unfrozen_hps = find_imply_subst prog dang_hps link_hps equal_hps complex_hps constrs1 new_cs1 in
  (b, new_cs2@rem,unfrozen_hps)
(*=========END============*)

let rec subst_cs_w_other_cs prog post_hps dang_hps link_hps equal_hps complex_hps constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "subst_cs_w_other_cs" pr1 (pr_triple string_of_bool pr1 !CP.print_svl)
    (fun _ -> subst_cs_w_other_cs_x prog post_hps dang_hps link_hps equal_hps complex_hps constrs  new_cs) constrs

(* let subst_cs_x prog dang_hps constrs new_cs = *)
(*   (\*subst by constrs*\) *)
(*   DD.ninfo_pprint "\n subst with other assumptions" no_pos; *)
(*   let new_cs1 = subst_cs_w_other_cs prog dang_hps constrs new_cs in *)
(*   (constrs@new_cs, new_cs1,[]) *)

(* let subst_cs prog dang_hps hp_constrs new_cs= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hprel in *)
(*   Debug.no_1 "subst_cs" pr1 (pr_triple pr1 pr1 !CP.print_svl) *)
(*       (fun _ -> subst_cs_x prog dang_hps hp_constrs new_cs) new_cs *)

let subst_cs_x prog post_hps dang_hps link_hps equal_hps complex_hps constrs new_cs =
  (*subst by constrs*)
  DD.ninfo_pprint "\n subst with other assumptions" no_pos;
  let is_changed, new_cs1,unfrozen_hps = subst_cs_w_other_cs prog post_hps dang_hps link_hps equal_hps complex_hps constrs new_cs in
  (is_changed, new_cs1,[], unfrozen_hps)

let subst_cs prog post_hps dang_hps link_hps equal_hps complex_hps hp_constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_1 "subst_cs" pr1 (pr_quad string_of_bool  pr1 pr1 !CP.print_svl)
    (fun _ -> subst_cs_x prog post_hps dang_hps link_hps equal_hps complex_hps hp_constrs new_cs) new_cs

(*===========fix point==============*)
let apply_transitive_impl_fix prog post_hps callee_hps (* hp_rel_unkmap *) dang_hps link_hps (constrs: CF.hprel list) =
  (* let dang_hps = (fst (List.split hp_rel_unkmap)) in *)
  (*find equal pre-preds: has one assumption.
    in the new algo, those will be generalized as equiv. do not need to substed
  *)
  (*frozen_hps: it is synthesized already*)
  let rec helper (constrs: CF.hprel list) new_cs frozen_hps =
    x_binfo_pp ">>>>>> step 3a: simplification <<<<<<" no_pos;
    let new_cs1 = (* Sautil.simplify_constrs prog unk_hps *) new_cs in
    (*  Debug.ninfo_hprint (add_str "apply_transitive_imp LOOP: " (pr_list_ln Cprinter.string_of_hprel)) constrs no_pos; *)
    begin
      let equal_cands, complex_hps,_ = Icontext.icompute_action_pre new_cs1 post_hps frozen_hps [] in
      let equal_hps = List.map fst equal_cands in
      let () = if equal_hps <> [] then
          x_binfo_pp (" freeze: " ^ (!CP.print_svl equal_hps) )no_pos
        else ()
      in
      let frozen_hps0 = frozen_hps@equal_hps in
      x_binfo_pp ">>>>>> step 3b: do apply_transitive_imp <<<<<<" no_pos;
      (* let constrs2, new_cs2, new_non_unk_hps = subst_cs prog dang_hps constrs new_cs1 in *)
      if equal_hps = [] then
        (*stop*)
        let () =  if complex_hps <> [] then x_binfo_zp (lazy ((" freeze: " ^ (!CP.print_svl complex_hps) ))) no_pos
          else ()
        in
        (constrs@new_cs1,[])
      else
        let is_changed, constrs2,new_cs2,unfrozen_hps  = subst_cs prog post_hps dang_hps link_hps (frozen_hps@equal_hps)
            complex_hps constrs new_cs1 in
        let unfrozen_hps1 = CP.remove_dups_svl (CP.intersect_svl unfrozen_hps frozen_hps0) in
        let frozen_hps1 = CP.diff_svl  frozen_hps0 unfrozen_hps1 in
        let () = if unfrozen_hps1 <> [] then
            x_binfo_pp (" unfreeze: " ^ (!CP.print_svl unfrozen_hps) )no_pos
          else ()
        in
        (*for debugging*)
        let () = DD.ninfo_zprint (lazy (("   new constrs:" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr constrs2)))) no_pos in
        (* let helper (constrs: CF.hprel list) new_cs= *)
        (*   let pr = pr_list_ln Cprinter.string_of_hprel_short in *)
        (*   Debug.no_1 "apply_transitive_imp_fix" pr (fun (cs,_) -> pr cs) *)
        (*       (fun _ -> helper_x constrs new_cs) new_cs *)
        (* in *)
        (*END for debugging*)
        let norm_constrs, non_unk_hps1 =
          let constrs, new_constrs = if is_changed then (new_cs2, constrs2) else (constrs, new_cs1) in
          (* helper new_cs2 constrs2 (frozen_hps@equal_hps) in *)
          helper constrs new_constrs frozen_hps1
        in
        (norm_constrs, [])
    end
  in
  let () = DD.ninfo_zprint (lazy (("   constrs:" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr constrs)))) no_pos in
  helper [] constrs []

(***************************************************************
                      END APPLY TRANS IMPL
 ****************************************************************)
(***************************************************************
                      CONSTR: ELIM UNUSED PREDS
 ****************************************************************)
(*split constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
let split_constr prog cond_path constrs post_hps prog_vars unk_map unk_hps link_hps=
  (*internal method*)
  let split_one cs total_unk_map=
    let () = Debug.ninfo_zprint (lazy (("  cs: " ^ (Cprinter.string_of_hprel_short cs)))) no_pos in
    let (_ ,mix_lf,_,_,_,_) = CF.split_components cs.CF.hprel_lhs in
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
      let lhs_b1, rhs_b1, subst_prog_vars = Sautil.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs)
          leqs [] [] prog_vars
      in
      (* let lfb = match lhs_b1 with *)
      (*   | CF.Base fb -> fb *)
      (*   | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula" *)
      (* in *)
      let lfb = lhs_b1 in
      let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
      let (_ ,mix_lf,_,_,_,_) = CF.split_components (CF.Base lfb) in
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
      (* let unk_svl, unk_xpure, unk_map1 = Sacore.generate_map ls_lhp_args ls_rhp_args total_unk_map no_pos in *)
      (* let lfb1 = CF.mkAnd_base_pure lfb (MCP.mix_of_pure unk_xpure) no_pos in *)
      (* ([], lfb1, unk_map1) *)
      in
      let unk_svl1 = CP.remove_dups_svl (cs.CF.unk_svl@unk_svl) in
      (*do not split unk_hps and link_hps, all non-ptrs args*)
      let non_split_hps = unk_hps @ link_hps in
      let ls_lhp_args1, ls_lhs_non_node_hpargs = List.fold_left (fun (r1,r2) (hp,args) ->
          let arg_i,_ = Sautil.partition_hp_args prog hp args in
          if ((List.filter (fun (sv,_) -> CP.is_node_typ sv) arg_i) = []) then
            (r1, r2@[(hp,args)])
          else if not (CP.mem_svl hp non_split_hps) then
            (r1@[(hp,args)],r2)
          else (r1,r2)
        ) ([],[]) ls_lhp_args in
      (* let () = Debug.info_pprint ("  ls_lhp_args1: " ^ *)
      (* (let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr1 ls_lhp_args1)) no_pos in *)
      (* let () = Debug.info_pprint ("  ls_lhs_non_node_hpargs: " ^ *)
      (* (let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr1 ls_lhs_non_node_hpargs)) no_pos in *)
      let lfb2, defined_preds,rems_hpargs,link_hps =
        List.fold_left (fun (lfb, r_defined_preds, r_rems, r_link_hps) hpargs ->
            let n_lfb,def_hps, rem_hps, ls_link_hps=
              Sautil.find_well_defined_hp (* split_base *) prog lhds lhvs r_hps
                prog_vars post_hps hpargs (l_def_vs@unk_svl1) lfb true no_pos
            in
            (n_lfb, r_defined_preds@def_hps, r_rems@rem_hps, r_link_hps@(snd (List.split ls_link_hps)))
          ) (lfb1, [], [], []) ls_lhp_args1
      in
      (* let defined_preds = List.concat ls_defined_hps in *)
      (* let () = if defined_preds!=[] then step_change # i else () in *)
      let rf = CF.mkTrue (CF.mkTrueFlow()) no_pos in
      let defined_preds0 = List.fold_left (fun (defined_preds) hpargs ->
          let def_hps, _ = (Sautil.find_well_eq_defined_hp prog lhds lhvs lfb2 leqs hpargs) in
          (defined_preds@(List.map (fun (a,b,c) -> (a,b,c,rf)) def_hps))
        ) (defined_preds) (rems_hpargs@ls_lhs_non_node_hpargs) in
      let new_cs = {cs with CF.hprel_lhs = CF.add_quantifiers l_qvars (CF.Base lfb2);
                            CF.unk_svl = unk_svl1;
                            CF.hprel_rhs = (CF.add_quantifiers r_qvars (CF.Base rhs_b1));
                   } in
      let new_constrs = match defined_preds0 with
        | [] -> [new_cs]
        | _ ->
          let () = Debug.ninfo_zprint (lazy ((Cprinter.string_of_hprel_short cs))) no_pos in
          let () = Debug.ninfo_zprint (lazy (("  unused ptrs: " ^ (!CP.print_svl unk_svl)))) no_pos in
          (*prune defined hps in lhs*)
          let new_lhs, _ = CF.drop_hrel_f new_cs.CF.hprel_lhs (List.map (fun (a, _, _,_) -> a) defined_preds0) in
          let new_lhs1 = CF.add_quantifiers l_qvars new_lhs in
          let new_lhs2 = CF.elim_unused_pure new_lhs1 new_cs.CF.hprel_rhs in
          let new_cs = {new_cs with CF.hprel_lhs = new_lhs2;} in
          let () = Debug.ninfo_zprint (lazy (("  refined cs: " ^ (Cprinter.string_of_hprel_short new_cs)))) no_pos in
          (* let rf = CF.mkTrue (CF.mkTrueFlow()) no_pos in *)
          let () = Debug.ninfo_pprint ("  generate pre-preds-based constraints: " ) no_pos in
          let defined_hprels = List.map (x_add Sautil.generate_hp_ass 2 unk_svl1 cond_path) defined_preds0 in
          new_cs::defined_hprels
      in
      (new_constrs, unk_map1, link_hps)
    else
      (*do subst: sa/demo/mcf-3a1.slk*)
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let lhs_b = match lhs with
        | CF.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      let rhs_b = match rhs with
        | CF.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      (*smart subst*)
      let lhs_b1, rhs_b1, _ = Sautil.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs)
          leqs [] [] prog_vars
      in
      let n_cs = {cs with CF.hprel_lhs = (CF.Base lhs_b1);
                          CF.hprel_rhs = (CF.Base rhs_b1);
                 } in
      ([n_cs],total_unk_map,[])
  in
  let split_one cs total_unk_map =
    (* let pr1 = Cprinter.string_of_hprel_short in *)
    (* let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in *)
    let res = split_one cs total_unk_map in
    let (new_cs,new_umap,link_hpargs) = res in
    if (List.length new_cs > 1) then
      begin
        step_change # inc;
        (* Debug.binfo_start "split_base"; *)
        (* x_binfo_hp (add_str "BEFORE" pr1) cs no_pos; *)
        (* x_binfo_pp "=============>>>>" no_pos; *)
        (* x_binfo_hp (add_str "AFTER" (pr_list_ln pr1)) new_cs no_pos; *)
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

let split_constr prog cond_path constrs post_hps prog_vars unk_map unk_hps link_hps=
  let () = step_change # reset in
  let s1 = (pr_list_num Cprinter.string_of_hprel_short) constrs in
  let (constrs2, unk_map2, link_hpargs2) as res = split_constr prog cond_path constrs post_hps prog_vars unk_map unk_hps link_hps in
  let s2 = (pr_list_num Cprinter.string_of_hprel_short) constrs2 in
  if step_change # no_change then 
    x_binfo_pp "*** NO SPLITTING DONE ***" no_pos
  else 
    begin
      let () = DD.binfo_start "split_base" in
      let () = x_binfo_hp (add_str "post_hps" Cprinter.string_of_spec_var_list) post_hps no_pos in
      let () = x_binfo_hp (add_str "prog_vars" Cprinter.string_of_spec_var_list) prog_vars no_pos in
      let () = x_binfo_hp (add_str "BEFORE" pr_id) s1 no_pos in
      let () = x_binfo_pp "=============>>>>" no_pos in
      let () = x_binfo_hp (add_str "AFTER" pr_id) s2 no_pos in
      let () = x_binfo_hp (add_str "UNKNOWN added" (pr_list (fun (x,_) -> Cprinter.string_of_spec_var x)))  link_hpargs2 no_pos in
      let () = DD.binfo_end "split_base" in
      ()
    end;
  res


let split_constr prog cond_path constrs post_hps prog_vars unk_map unk_hps link_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  (* let pr2 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_4 "split_constr" pr1 pr2 !CP.print_svl !CP.print_svl (pr_triple pr1 pr2 pr3)
    (fun _ _ _ _ -> split_constr prog cond_path constrs post_hps prog_vars unk_map
        unk_hps link_hps) constrs unk_map unk_hps post_hps

let get_preds (lhs_preds, lhs_heads, rhs_preds,rhs_heads) cs=
  (* let pr1 = Cprinter.string_of_hprel_short in *)
  (* let () = print_endline ( "cs: " ^ (pr1 cs)) in *)
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

let cmp_hpargs_fn (hp1, _) (hp2, _) = CP.eq_spec_var hp1 hp2

let elim_unused_pre_preds post_hps constrs unk_map=
  let lhs_preds, lhs_heads, rhs_preds,rhs_heads = List.fold_left get_preds ([],[],[],[]) constrs in
  (* let lhs_preds1 = CP.remove_dups_svl lhs_preds in *)
  let rhs_preds1 = Gen.BList.remove_dups_eq cmp_hpargs_fn rhs_preds in
  (* let () = print_endline ("lhs_preds1: " ^ (!CP.print_svl lhs_preds1)) in *)
  (* let () = print_endline ("rhs_preds1: " ^ (!CP.print_svl rhs_preds1)) in *)
  (*unused pre preds are preds in rhs but do not appear in any lhs*)
  let unused_pre_preds = Gen.BList.difference_eq cmp_hpargs_fn rhs_preds1 lhs_heads in
  (*and they are NOT post*)
  let unused_pre_preds0 = List.filter (fun (hp,_) -> not (CP.mem_svl hp post_hps)) unused_pre_preds in
  let unused_pre = (List.map fst unused_pre_preds0) in
  let () = x_binfo_zp (lazy (("pre-preds: "  ^ (!CP.print_svl unused_pre) ^" are removed"))) no_pos in
  let new_constrs,new_map = List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = Sacore.do_elim_unused cs unused_pre map in
      (ls_cs@[new_cs], n_map)
    ) ([], unk_map) constrs in
  let () = x_dinfo_zp (lazy (("   After removing, derived:\n" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr new_constrs)))) no_pos in
  let () = x_dinfo_zp (lazy (("   uu map:" ^ (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in pr new_map)))) no_pos in
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
  (* let () = print_endline ("lhs_preds1: " ^ (!CP.print_svl lhs_preds1)) in *)
  (* let () = print_endline ("rhs_preds1: " ^ (!CP.print_svl rhs_preds1)) in *)
  (*unused pre preds are preds in rhs but do not appear in any lhs*)
  (*post-preds*)
  (*unused post preds are preds in lhs but do not appear in any rhs*)
  let unused_post_preds = Gen.BList.difference_eq cmp_hpargs_fn lhs_preds1 rhs_heads in
  (*and they are NOT pre*)
  let unused_post_preds0 = unused_post_preds(* CP.diff_svl unused_post_preds lhs_heads *) in
  let unused_post = (List.map fst unused_post_preds0) in
  let () = x_binfo_zp (lazy (("post-preds: "  ^ (!CP.print_svl unused_post) ^" are removed"))) no_pos in
  let new_constrs,new_map = List.fold_left (fun (ls_cs,map) cs ->
      let new_cs, n_map,_ = Sacore.do_elim_unused cs unused_post map in
      (ls_cs@[new_cs], n_map)
    ) ([], unk_map) constrs in
  let () = x_dinfo_zp (lazy (("   After removing, derived:\n" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr new_constrs)))) no_pos in
  let () = x_dinfo_zp (lazy (("   uu map:" ^ (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in pr new_map)))) no_pos in
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
let mk_pdef hp_sv args unk_svl imp_cond olhs og orhs=
  (hp_sv, args,  unk_svl, imp_cond, olhs , og, orhs)

let cmp_formula_opt args of1 of2=
  match of1,of2 with
  | Some f1, Some f2 ->
    Sautil.check_relaxeq_formula args f1 f2
  | None, None -> true
  | _ -> false

(*assume hp1 = hp2*)
let cmp_pdef_grp (hp1,args1,unk_svl1, cond1, olhs1,og1, orhs1) (hp2,args2,unk_svl2, cond2, olhs2, og2, orhs2)=
  (CP.equalFormula cond1 cond2) && (cmp_formula_opt args1 orhs1 orhs2)

let get_par_defs_post constrs0 =
  let mk_par_def cs=
    let hp, args = CF.extract_HRel_f cs.CF.hprel_rhs in
    mk_pdef hp args cs.CF.unk_svl (CP.mkTrue no_pos) (Some cs.CF.hprel_lhs) None None
  in
  List.map mk_par_def constrs0

let get_par_defs_pre constrs0 =
  let mk_par_def cs=
    (* let () = print_endline ("cs.CF.hprel_lhs: " ^ ( !CF.print_formula cs.CF.hprel_lhs)) in *)
    let op_res = CF.extract_hprel_pure cs.CF.hprel_lhs in
    match op_res with
    | Some (hp, args,p) ->
      (* let () = print_endline ("p: " ^ ( !CP.print_formula p)) in *)
      ([(mk_pdef hp args cs.CF.unk_svl (CP.remove_redundant p) None cs.CF.hprel_guard (Some cs.CF.hprel_rhs), cs)], [])
    | None -> ([], [cs])
  in
  List.fold_left (fun (pdefs,rem_cs) cs ->
      let ls1, ls2 = mk_par_def cs in
      (pdefs@ls1, rem_cs@ls2)
    )
    ([], []) constrs0
(*remove_dups*)

let combine_pdefs_pre_x prog unk_hps link_hps pr_pdefs=
  (*Now unk_hps (dangling) is similar to link_hps (unknown).
    in future, it may different. Thus, we keep both, now.
  *)
  let link_hps = unk_hps@link_hps in
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
    | [] -> parts
    | ((a1,a2,a3,a4,a5,a5g,a6),cs)::xs ->
      let part,remains= List.partition (fun ((hp_name,_,_,_,_,_,_),_) ->
          CP.eq_spec_var a1 hp_name) xs in
      partition_pdefs_by_hp_name remains (parts@[[((a1,a2,a3,a4,a5,a5g,a6),cs)]@part])
  in
  let do_combine (hp,args,unk_svl, cond, lhs,og, orhs)=
    match orhs with
    | Some rhs ->
      let n_cond = CP.remove_redundant cond in
      let nf = (CF.mkAnd_pure rhs (MCP.mix_of_pure n_cond) (CF.pos_of_formula rhs)) in
      if Sautil.is_unsat nf then [] else
        [(hp,args,unk_svl, n_cond, lhs, og, Some (x_add_1 CF.simplify_pure_f_old nf))]
    | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None 1"
  in
  let mkAnd_w_opt hp args (* ss *) of1 of2=
    match of1,of2 with
    | Some f1, Some f2 ->
      let pos = CF.pos_of_formula f1 in
      let new_f2 = (*x_add CF.subst ss*) f2 in
      let f = Sautil.mkConjH_and_norm prog hp args unk_hps [] f1 new_f2 pos in
      (* let f = (CF.mkConj_combine f1 new_f2 CF.Flow_combine no_pos) in *)
      if CF.isAnyConstFalse f || Sautil.is_unsat f then
        false, Some f
      else true, Some f
    | None, None -> true, None
    | None, Some f2 -> true, (Some ( (*x_add CF.subst ss*) f2))
    | Some f1, None -> true, of1
  in
  (*nav code. to improve*)
  let combine_helper2_x (hp1,args1,unk_svl1, cond1, olhs1,og1, orhs1) (hp2,args2,unk_svl2, cond2, olhs2,og2, orhs2)=
    let cond_disj1 = CP.mkAnd cond1 (CP.mkNot (CP.remove_redundant cond2) None no_pos) no_pos in
    let pdef1 = if (Tpdispatcher.is_sat_raw (MCP.mix_of_pure cond_disj1)) then
        (* let () = DD.info_zprint (lazy (("      cond_disj1: " ^ (!CP.print_formula  cond_disj1) ))) no_pos in *)
        let cond21 = CF.remove_neqNull_redundant_andNOT_opt orhs1 cond2 in
        let n_cond = CP.mkAnd cond1 (CP.mkNot cond21 None no_pos) no_pos in
        let npdef1 = do_combine (hp1,args1,unk_svl1, CP.remove_redundant n_cond , olhs1,og1, orhs1) in
        npdef1
      else []
    in
    let cond_disj2 = CP.mkAnd cond2 (CP.mkNot cond1 None no_pos) no_pos in
    let pdef2 = if (Tpdispatcher.is_sat_raw (MCP.mix_of_pure cond_disj2)) then
        (* let () = DD.info_zprint (lazy (("      cond_disj2: " ^ (!CP.print_formula  cond_disj2) ))) no_pos in *)
        let cond11 = CF.remove_neqNull_redundant_andNOT_opt orhs2 cond1 in
        let n_cond = (CP.mkAnd cond2 (CP.mkNot cond11 None no_pos) no_pos) in
        let npdef2 = do_combine (hp2,args2,unk_svl2, CP.remove_redundant n_cond, olhs2,og2, orhs2) in
        npdef2
      else []
    in
    let cond_disj3 = CP.mkAnd cond2 cond1 no_pos in
    (* let () = DD.info_zprint (lazy (("      cond_disj3: " ^ (!CP.print_formula  cond_disj3) ))) no_pos in *)
    let pdef3 = if (Tpdispatcher.is_sat_raw (MCP.mix_of_pure cond_disj3)) then
        let n_cond = CP.remove_redundant (CP.mkAnd cond1 cond2 no_pos) in
        let is_sat1, n_orhs = mkAnd_w_opt hp1 args1 orhs1 orhs2 in
        let is_sat2, n_olhs = mkAnd_w_opt hp1 args1 olhs1 olhs2 in
        let npdef3 = if is_sat1 && is_sat2 then
            do_combine (hp1,args1,unk_svl1, n_cond, n_olhs,og1, n_orhs)
          else [(hp1,args1,unk_svl1,  n_cond, olhs1, og1, Some (CF.mkFalse_nf no_pos))]
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
    (* let pr3a oform= match oform with *)
    (*   | None -> "None" *)
    (*   | Some hf -> Cprinter.prtt_string_of_h_formula hf *)
    (* in *)
    let pr4 = pr_hepta !CP.print_sv pr1 pr1 pr2 pr3 pr3 pr3 in
    Debug.no_2 " combine_helper2" pr4 pr4 (pr_list_ln pr4)
      (fun _ _ -> combine_helper2_x pdef1 pdef2)
      pdef1 pdef2
  in
  (* let rec combine_helper_list rem res= *)
  (*   match rem with *)
  (*     | [] -> res *)
  (*     | pdef::rest -> *)
  (*           let n = List.fold_left (fun res_pdefs pdef1 -> *)
  (*               res_pdefs@(combine_helper2 pdef pdef1) *)
  (*           ) [] rest in *)
  (*            combine_helper_list rest (res@n) *)
  (* in *)
  let filter_trivial_pardef (res_pr, res_depen_cs) ((hp,args,unk_svl, cond, olhs,og, orhs), cs) =
    match orhs with
    | Some rhs -> let b = CP.isConstTrue cond && Sautil.is_empty_f rhs in
      if not b then
        (res_pr@[((hp,args,unk_svl, cond, olhs, og, orhs), cs)], res_depen_cs)
      else (res_pr, res_depen_cs@[cs])
    | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None 2"
  in
  let obtain_and_norm_def_x args0 ((hp,args,unk_svl, cond, olhs, og, orhs), cs)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let cond1 = (CP.subst subst cond) in
    let norhs, cond1 = match orhs with
      | Some f -> let nf = (x_add CF.subst subst f) in
        let cond2 =
          (* if Sautil.is_empty_heap_f nf then *)
          (*   CP.mkAnd cond1 (CF.get_pure nf) (CP.pos_of_formula cond1) *)
          (* else cond1 *)
          cond1
        in
        (Some (CF.mkAnd_pure nf (MCP.mix_of_pure cond2) (CF.pos_of_formula nf)), cond2)
      | None -> None, cond1
    in
    let nolhs = match olhs with
      | None -> None
      | Some f -> Some (x_add CF.subst subst f)
    in
    let nog = match og with
      | None -> None
      | Some f -> Some (x_add CF.subst subst f)
    in
    ((hp,args0,CP.subst_var_list subst unk_svl, cond1, nolhs,nog, norhs), (*TODO: subst*)cs)
  in
  let obtain_and_norm_def args0 ((hp,args,unk_svl, cond, olhs, og, orhs), cs)=
    let pr1 = !CP.print_svl in
    let pr2 = !CP.print_formula in
    let pr3 oform= match oform with
      | None -> "None"
      | Some f -> Cprinter.prtt_string_of_formula f
    in
    (* let pr3a oform= match oform with *)
    (*   | None -> "None" *)
    (*   | Some f -> Cprinter.prtt_string_of_h_formula f *)
    (* in *)
    let pr4 = pr_hepta !CP.print_sv pr1 pr1 pr2 pr3 pr3 pr3 in
    let pr5 (a,_) = pr4 a in
    Debug.no_2 "obtain_and_norm_def" pr1 pr4 pr5
      (fun _ _ -> obtain_and_norm_def_x args0 ((hp,args,unk_svl, cond, olhs,og, orhs), cs))
      args0 (hp,args,unk_svl, cond, olhs,og, orhs)
  in
  let combine_grp pr_pdefs equivs=
    match pr_pdefs with
    | [] -> ([],[], equivs)
    | [(hp,args,unk_svl, cond, lhs, og, orhs), _] ->
      let new_pdef = do_combine (hp,args,unk_svl, cond, lhs,og, orhs) in
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
          | ((hp,args0,unk_svl0, cond0, olhs0, og0, orhs0),cs0)::rest ->
            (* let pr_pdef0 = obtain_and_norm_def args0 ((hp,args0,unk_svl0, cond0, olhs0, orhs0),cs0) in *)
            let pdefs = List.map (obtain_and_norm_def args0) rem_pr_defs in
            (* let pdefs = pr_pdef0::new_rest in *)
            let pdefs1 = Gen.BList.remove_dups_eq (fun (pdef1,_) (pdef2,_) -> cmp_pdef_grp pdef1 pdef2) pdefs in
            let pdefs2,n_equivs = Sacore.unify_consj_pre prog unk_hps link_hps equivs pdefs1 in
            ([], pdefs2,n_equivs)
        in
        let pdefs,rem_constrs0 = begin
          match cs,rem_pr_defs1 with
          | [],[] -> [],[]
          | [((hp,args,unk_svl, cond, lhs,og, orhs), _)],[] -> (do_combine (hp, args, unk_svl, cond, lhs,og, orhs)),[]
          | [],[(pr1,_);(pr2,_)] -> let npdefs = combine_helper2 pr1 pr2 in
            npdefs,[]
          | _ ->
            (* let pdefs, rem_constrs = *)
            (*   combine_helper rem_pr_defs1 [] [] [] in *)
            (* (pdefs,rem_constrs) *)
            let fst_ls = List.map fst rem_pr_defs1 in
            let pdefs = (* combine_helper_list fst_ls [] *)
              List.fold_left (fun res_pdefs pdef ->
                  let pdefs = res_pdefs@(List.fold_left (fun res pdef1 ->
                      let pdefs = res@(combine_helper2 pdef pdef1) in
                      pdefs
                    ) [] res_pdefs) in
                  let pdefs2 = Gen.BList.remove_dups_eq cmp_pdef_grp pdefs in
                  pdefs2
                ) [List.hd fst_ls] (List.tl fst_ls)
            in
            (pdefs,[])
        end
        in
        (pdefs, depend_cs@rem_constrs0, n_equivs)
      end
  in
  let subst_equiv equivs ((hp,args1,unk_svl1, cond1, olhs1,og1, orhs1) as pdef)=
    match orhs1 with
    | None -> pdef
    | Some f ->
      let rele_equivs = List.fold_left (fun ls (hp1,hp2) ->
          if CP.eq_spec_var hp1 hp then (ls@[hp2]) else ls)
          [] equivs
      in
      let from_hps = CP.remove_dups_svl rele_equivs in
      let nf = CF.subst_hprel f from_hps hp in
      (hp,args1,unk_svl1, cond1, olhs1,og1, Some nf)
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
  let pr2 = Sautil.string_of_par_def_w_name in
  let pr3 (pdef, _) = pr2 pdef in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "combine_pdefs_pre" (pr_list_ln pr3) !CP.print_svl !CP.print_svl
    (pr_triple (pr_list_ln pr2) pr1 pr4)
    (fun _ _ _ -> combine_pdefs_pre_x prog unk_hps link_hps pr_pdefs)
    pr_pdefs unk_hps link_hps
(***************************************************************
                      END PARTIAL DEFS
 ****************************************************************)
(***************************************************************
                      GENERALIZATION
 ****************************************************************)
(*remove neqNUll redundant*)
let remove_neqNull_helper (hp,args,f,unk_svl)=
  let f1 = CF.remove_neqNulls_f f in
  if Sautil.is_empty_f f1 then [] else [(hp,args,f1,unk_svl)]

let remove_neqNull_grp_helper grp=
  List.fold_left (fun r pdef-> let new_pdef = remove_neqNull_helper pdef in
                   r@new_pdef) [] grp

let get_null_quans f=
  let qvars, base_f = CF.split_quantifiers f in
  let (_ ,mix_lf,_,_,_,_) = CF.split_components base_f in
  let eqNulls = MCP.get_null_ptrs mix_lf in
  (CP.intersect_svl eqNulls qvars, base_f)

(*for par_defs*)
let generalize_one_hp_x prog is_pre (hpdefs: (CP.spec_var *CF.hp_rel_def) list) non_ptr_unk_hps unk_hps link_hps par_defs=
  let skip_hps = unk_hps@link_hps in
  (*collect definition for each partial definition*)
  let obtain_and_norm_def hp args0 quan_null_svl0 (a1,args,og,f,unk_args)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let f1 = (x_add CF.subst subst f) in
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
        CF.add_quantifiers quan_null_svl0 (x_add CF.subst ss base_f2)
      else f2
    in
    let unk_args1 = List.map (CP.subs_one subst) unk_args in
    (* (\*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *\) *)
    (f3,CF.subst_opt subst og, unk_args1)
  in
  x_tinfo_pp ">>>>>> generalize_one_hp: <<<<<<" no_pos;
  if par_defs = [] then ([],[]) else
    begin
      let hp, args, _, f0,_ = (List.hd par_defs) in
      let () = Debug.info_zprint (lazy (("    synthesize: " ^ (!CP.print_sv hp) ))) no_pos in
      let hpdefs,subst_useless=
        if CP.mem_svl hp skip_hps then
          let fs = List.map (fun (a1,args,og,f,unk_args) -> fst (CF.drop_hrel_f f [hp]) ) par_defs in
          let fs1 = Gen.BList.remove_dups_eq (fun f1 f2 -> Sautil.check_relaxeq_formula args f1 f2) fs in
          (Sautil.mk_unk_hprel_def hp args fs1 no_pos,[])
        else
          (*find the root: ins2,ins3: root is the second, not the first*)
          let args0 = List.map (CP.fresh_spec_var) args in
          (* DD.ninfo_zprint (lazy (((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")"))) no_pos; *)
          let quan_null_svl,_ = get_null_quans f0 in
          let quan_null_svl0 = List.map (CP.fresh_spec_var) quan_null_svl in
          let defs,defs_wg, ogs, unk_svl = List.fold_left (fun (r1,r2,r3,r4) pdef->
              let (f, og, unk_args) = obtain_and_norm_def hp args0 quan_null_svl0 pdef in
              (r1@[f], r2@[(f,og)],r3@[og],r4@unk_args)
            ) ([],[],[],[]) par_defs in
          (* let defs,ogs, ls_unk_args = split3 (List.map (obtain_and_norm_def hp args0 quan_null_svl0) par_defs) in *)
          let r,non_r_args = Sautil.find_root prog (hp::skip_hps) args0 defs in
          (*make explicit root*)
          (* let defs0 = List.map (Sautil.mk_expl_root r) defs in *)
          let defs0_wg = List.map (fun (f,og) -> (Sautil.mk_expl_root r f, og)) defs_wg in
          (* let unk_svl = CP.remove_dups_svl (List.concat (ls_unk_args)) in *)
          (*normalize linked ptrs*)
          (* let defs1,_ = List.split (Sautil.norm_hnodes_wg args0 (List.map (fun f -> (f, None)) defs0)) in *)
          let defs1_wg = Sautil.norm_hnodes_wg args0 defs0_wg in
          (* let defs1 = Sautil.norm_hnodes args0 defs0 in *)
          (*remove unkhp of non-node*)
          let defs2_wg = if is_pre then (* List.map remove_non_ptr_unk_hp *) defs1_wg
            else Sautil.elim_useless_rec_preds prog hp args0 defs1_wg
          in
          (*remove duplicate*)
          let defs3_wg = Sautil.equiv_unify_wg args0 defs2_wg in
          let defs4_wg = Sautil.remove_equiv_wo_unkhps_wg hp args0 skip_hps defs3_wg in
          let defs5a_wg = Sautil.find_closure_eq_wg hp args0 defs4_wg in
          (*Perform Conjunctive Unification (without loss) for post-preds. pre-preds are performed separately*)
          let defs5_wg =  if is_pre then defs5a_wg else
              Sautil.perform_conj_unify_post_wg prog hp args0 (unk_hps@link_hps) unk_svl defs5a_wg no_pos
          in
          let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
          let () = DD.ninfo_zprint (lazy (("defs1: " ^ (pr1 defs1_wg)))) no_pos in
          (*remove duplicate with self-recursive*)
          (* let base_case_exist,defs4 = Sautil.remove_dups_recursive hp args0 unk_hps defs3 in *)
          (*find longest hnodes common for more than 2 formulas*)
          (*each hds of hdss is def of a next_root*)
          (* let defs5 = List.filter (fun f -> have_roots args0 f) defs4 in *)
          let old_disj = !Globals.pred_disj_unify in
          let disj_opt = !Globals.pred_elim_useless || !Globals.pred_disj_unify in
          (* let defs5,_ = List.split defs5_wg in *)
          let defs,elim_ss = if disj_opt then
              Sautil.get_longest_common_hnodes_list prog is_pre hpdefs (skip_hps) unk_svl hp r non_r_args args0 defs5_wg
            else
              let defs = Sautil.mk_hprel_def_wprocess prog is_pre hpdefs skip_hps unk_svl hp (args0,r,non_r_args) defs5_wg no_pos in
              (defs,[])
          in
          let () = Globals.pred_disj_unify := old_disj in
          if defs <> [] then
            (defs,elim_ss)
          else
            (* report_error no_pos "shape analysis: FAIL" *)
            let body = if is_pre then
                CF.mkHTrue_nf no_pos
              else
                CF.mkFalse_nf no_pos
            in
            let def = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, non_r_args))
                (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args0, no_pos)) [(body,None)] None in
            ([(hp, def)],[])
      in
      (********PRINTING***********)
      let () = List.iter (fun (_, def) ->
          Debug.info_zprint (lazy (((Cprinter.string_of_hp_rel_def_short def)))) no_pos)
          hpdefs
      in
      (********END PRINTING***********)
      (hpdefs, subst_useless)
    end

let generalize_one_hp prog is_pre (defs:(CP.spec_var *CF.hp_rel_def) list) non_ptr_unk_hps unk_hps link_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  let pr3 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  Debug.no_2 "generalize_one_hp" pr1 !CP.print_svl (pr_pair pr2 pr3)
    (fun _ _ -> generalize_one_hp_x prog is_pre defs non_ptr_unk_hps
        unk_hps link_hps par_defs) par_defs unk_hps

let get_pdef_body_x unk_hps post_hps (a1,args,unk_args,a3,olf,og, orf)=
  let exchane_unk_post hp1 args f unk_args=
    let hpargs2 = CF.get_HRels_f f in
    match hpargs2 with
    | [(hp2,args2)] ->
      if CP.mem_svl hp2 unk_hps && (CP.mem_svl hp2 post_hps) &&
         Sautil.eq_spec_var_order_list args args2 then
        let new_f = Sautil.mkHRel_f hp1 args (CF.pos_of_formula f) in
        [(hp2,args,og,new_f,unk_args)]
      else [(hp1,args,og,f,unk_args)]
    | _ -> [(hp1,args,og,f,unk_args)]
  in
  match olf,orf with
  | Some f, None -> [(a1,args,og,f,unk_args)]
  | None, Some f -> if CP.mem_svl a1 unk_hps && not (CP.mem_svl a1 post_hps) then
      exchane_unk_post a1 args f unk_args
    else
      [(a1,args,og,f,unk_args)]
  | Some f1, Some f2 ->
    let f_body=
      let hps1 = CF.get_hp_rel_name_formula f1 in
      let hps2 = CF.get_hp_rel_name_formula f2 in
      if CP.intersect_svl hps1 hps2 <> [] then
        (*recurive case*)
        if CF.is_HRel_f f1 then f2 else f1
      else Sautil.compose_subs f2 f1 (CF.pos_of_formula f2)
    in
    if Sautil.is_trivial f_body (a1,args) then [] else
      [(a1,args,og,f_body,unk_args)]
  | None, None -> report_error no_pos "sa.obtain_def: can't happen 2"

let get_pdef_body unk_hps post_hps (a1,args,unk_args,a3,olf,og,orf)=
  let pr1 = Sautil.string_of_par_def_w_name in
  let pr1a og = match og with
    | None -> ""
    | Some f -> Cprinter.prtt_string_of_formula f
  in
  let pr2 = pr_list (pr_penta !CP.print_sv !CP.print_svl pr1a Cprinter.prtt_string_of_formula !CP.print_svl) in
  Debug.no_1 "get_pdef_body" pr1 pr2
    (fun _ -> get_pdef_body_x unk_hps post_hps (a1,args,unk_args,a3,olf,og,orf) )(a1,args,unk_args,a3,olf,og,orf)

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
  let is_rec_pardef (hp,_,_,f,_)=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_pardef (hp,_,_,f,_) =
    let hps = CF.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       rec hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let dep_hps = List.filter (fun hp1 -> not ((CP.eq_spec_var hp hp1) (* || *)
    (* (CP.mem_svl hp1 unk_hps) *))) hps in
    (* DD.ninfo_zprint (lazy (("       rec rems: " ^ (!CP.print_svl rems)))) no_pos; *)
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
    let ters,fss = List.split (List.map (Sautil.succ_subst prog nrec_grps unk_hps false) grp) in
    (*check all is false*)
    (* let pr = pr_list string_of_bool in *)
    (* DD.ninfo_zprint (lazy (("       bool: " ^ (pr ters)))) no_pos; *)
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
    let pr0 = (pr_list_ln Sautil.string_of_par_def_w_name_short) in
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
      let (hp,_,_,_,_) = List.hd grp in
      (grp,hp,0) (*called one topo*)
    in
    let update_order_from_grp updated_hps incr (grp,hp, old_n)=
      if CP.mem_svl hp updated_hps then
        (grp,hp,old_n+incr)
      else (grp,hp,old_n)
    in
    (*each grp, find succ_hp, add number of each succ hp + 1*)
    let process_one_dep_grp topo dep_grp=
      let (hp,_,_,_,_) = List.hd dep_grp in
      let succ_hps = List.concat (List.map (fun (_,_,_,f,_) -> CF.get_hp_rel_name_formula f) dep_grp) in
      (*remove dups*)
      let succ_hps1 = Gen.BList.remove_dups_eq CP.eq_spec_var succ_hps in
      (* DD.ninfo_zprint (lazy (("       process_dep_group succ_hps: " ^ (!CP.print_svl succ_hps)))) no_pos; *)
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
    let pr0 = (pr_list_ln Sautil.string_of_par_def_w_name_short) in
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
        (fun grp -> let (hp,_,_,_,_) = List.hd grp in hp)
        (res_rec_inds@lrec_deps)
    in
    (*deps may have mutual rec*)
    let mutrec_term_grps,mutrec_nonterm_grps, deps_0,mutrec_hps = Sautil.succ_subst_with_mutrec prog deps unk_hps in
    (*add rec grp*)
    let l_nrec_deps1 = List.filter
        (fun grp -> let (hp,_,_,_,_) = List.hd grp in not(CP.mem_svl hp mutrec_hps))
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
              let hp1,_,_,_,_ = List.hd dep_grp in
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
    let pr1 = pr_list_ln (pr_list_ln Sautil.string_of_par_def_w_name_short) in
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
      (* let () = DD.info_zprint (lazy (("      new_cur: " ^ (pr1 new_cur)))) no_pos in *)
      (*subs new_cur with new_rec_indps (new_nrec_indps is substed already)*)
      let new_cur1 = List.map Sautil.remove_dups_pardefs new_cur in
      let new_cur2 = Sautil.succ_subst_with_rec_indp prog new_rec_indps unk_hps new_cur1 in
      (new_cur2@new_rec_indps@new_nrec_indps)
  in
  helper_fix groups [] []

(*this subst is for a nice matching between inferred HP
  and lib based predicates*)
let pardef_subst_fix prog unk_hps groups=
  let pr1 = pr_list_ln (pr_list_ln Sautil.string_of_par_def_w_name_short) in
  Debug.no_1 "pardef_subst_fix" pr1 pr1
    (fun _ -> pardef_subst_fix_x prog unk_hps groups) groups

let is_valid_pardef (_,args,_,_,f,_)=
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
  | (a1,a2,og, a3,a4)::xs ->
    let part,remains= List.partition (fun (hp_name,_,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
    partition_pdefs_by_hp_name remains (parts@[[(a1,a2,og,a3,a4)]@part])

let generalize_hps_par_def_x prog is_pre non_ptr_unk_hps unk_hpargs link_hps post_hps
    pre_def_grps predef_hps par_defs=
  (*partition the set by hp_name*)
  let pr1 = pr_list_ln (pr_list_ln (pr_penta !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula_opt Cprinter.prtt_string_of_formula !CP.print_svl)) in
  let unk_hps = (List.map fst unk_hpargs) in
  let par_defs1 = List.concat (List.map (get_pdef_body unk_hps post_hps) par_defs) in
  let par_defs2 = (* List.filter is_valid_pardef *) par_defs1 in
  let groups = partition_pdefs_by_hp_name par_defs2 [] in
  (*do not generate anyting for LINK preds*)
  let groups1 = List.filter (fun grp ->
      match grp with
      | [] -> false
      | ((hp,_,_,_,_)::_) -> not (CP.mem_svl hp link_hps)
    ) groups
  in
  (*
    subst such that each partial def does not contain other hps
    dont subst recursively search_largest_matching between two formulas
  *)
  let () = DD.ninfo_zprint (lazy (("      groups1: " ^ (pr1 groups)))) no_pos in
  let groups20 =
    if predef_hps <> [] then pardef_subst_fix prog unk_hps (groups1@pre_def_grps)
    else
      groups1
  in
  (*filter out groups of pre-preds which defined already*)
  let groups2 =  List.filter (fun grp ->
      match grp with
      | [] -> false
      | ((hp,_,_,_,_)::_) -> not (CP.mem_svl hp predef_hps)
    ) groups20
  in
  (* let () = Debug.info_pprint ("     END: " ) no_pos in *)
  (*remove empty*)
  let () = DD.ninfo_zprint (lazy (("      groups2: " ^ (pr1 groups2)))) no_pos in
  let groups3 = List.filter (fun grp -> grp <> []) groups2 in
  let () = x_tinfo_hp (add_str "before remove redundant" pr1) groups2 no_pos in
  (*each group, do union partial definition*)
  let hpdefs,elim_ss = List.fold_left (fun (hpdefs,elim_ss) pdefs->
      let new_defs,ss = generalize_one_hp prog is_pre hpdefs non_ptr_unk_hps unk_hps link_hps pdefs in
      ((hpdefs@new_defs), elim_ss@ss)
    ) ([],[]) groups3
  in
  let prh = Cprinter.string_of_h_formula in
  let () = x_tinfo_hp (add_str "elim_ss" (pr_list (pr_pair prh prh))) elim_ss no_pos in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr_hpd = pr_list (fun (_,a)-> pr2 a) in
  let () = x_tinfo_hp (add_str "after remove redundant" pr_hpd) hpdefs no_pos in
  let hpdefs1 =
    if !Globals.pred_elim_useless then
      List.map (fun (hp,def) ->
          (hp, {def with CF.def_rhs = List.map (fun (f,og) -> (CF.subst_hrel_f f elim_ss,og)) def.CF.def_rhs})) hpdefs
    else
      hpdefs
  in
  hpdefs1

let generalize_hps_par_def prog is_pre non_ptr_unk_hps unk_hpargs link_hps post_hps pre_defs predef_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr3 = fun (_,a)-> pr2 a in
  Debug.no_4 "generalize_hps_par_def" !CP.print_svl !CP.print_svl pr1
    !CP.print_svl (pr_list_ln pr3)
    (fun _ _ _ _ -> generalize_hps_par_def_x prog is_pre non_ptr_unk_hps unk_hpargs
        link_hps post_hps pre_defs predef_hps par_defs)
    post_hps link_hps par_defs predef_hps

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
(*             let () = x_binfo_pp ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*             let () = x_binfo_zp (lazy (("         " ^ (!CP.print_sv hp) ^ " is defined already: drop the constraint"))) no_pos in *)
(*             ([constr],[],[]) *)
(*           else if CP.mem_svl hp unk_hps then *)
(*             let () = x_binfo_pp ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*             let () = x_binfo_zp (lazy (("         " ^ (!CP.print_sv hp) ^ " is unknown. pass to next step"))) no_pos in *)
(*             ([constr],[],[]) *)
(*           else *)
(*             let keep_ptrs = CF.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) args in *)
(*             let p = CF.pos_of_formula lhs in *)
(*             let nlhs = CF.mkStar lhs rhs  CF.Flow_combine p in *)
(*             let hpargs = CF.get_HRels_f nlhs in *)
(*             let hpdefs1 = *)
(*               let lhps = CF.get_hp_rel_name_formula lhs in *)
(*               let rhps = CF.get_hp_rel_name_formula rhs in *)
(*               if (CP.intersect_svl lhps rhps) = [] then hpdefs else hpdefs@[hp] *)
(*             in *)
(*             let hpargs1 = List.filter (fun (hp1,_) -> CP.mem_svl hp1 hpdefs1) hpargs in *)
(*             let keep_def_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) hpargs1) in *)
(*             let r = CF.drop_data_view_hrel_nodes nlhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in *)
(*             if (not (Sautil.is_empty_f r)) then *)
(*               let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in *)
(*               let () = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")=" ^ *)
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
(*   let hpdefs = Sautil.combine_hpdefs hp_defs in *)
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
        let () = x_binfo_pp ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
        if lhvs <> [] || lhds <> [] then
          ([constr],[],[])
        else
          let lhps, ls_largs = List.split lhp_args in
          let rhps, ls_rargs = List.split rhp_args in
          let largs = CP.remove_dups_svl (List.concat ls_largs) in
          let rargs = CP.remove_dups_svl (List.concat ls_rargs) in
          let keep_ptrs = CF.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) (largs@rargs) in
          let pos = CF.pos_of_formula lhs in
          let nrhs = CF.mkAnd_pure rhs (MCP.mix_of_pure (CF.get_pure lhs)) pos in
          let keep_def_hps = lhps@rhps@unk_hps@hpdefs in
          let r = CF.drop_data_view_hrel_nodes nrhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in
          if (not (Sautil.is_empty_f r)) then
            let hps = List.map fst diff in
            let hfs = List.map (fun (hp,args) -> (CF.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos))) diff in
            let hf = CF.join_star_conjunctions hfs in
            let def_tit = match diff with
              | [(hp,args)] -> CP.HPRelDefn (hp, List.hd args, List.tl args)
              | _ -> CP.HPRelLDefn hps
            in
            let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" pos in
            let () = DD.ninfo_pprint ((let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr diff) ^ "::=" ^
                                      (Cprinter.prtt_string_of_formula r) ) pos in
            let ndef = {CF.def_cat=def_tit; CF.def_lhs=hf;CF.def_rhs=[(r,None)]; CF.def_flow=None;} in
            ([],[(ndef)], hps)
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
  let hpdefs = Sautil.combine_hpdefs hp_defs in
  (cs1, hpdefs, hp_names)

let generalize_hps_cs_new prog callee_hps hpdefs unk_hps link_hps cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr3  = pr_list Cprinter.string_of_hp_rel_def in
  let pr4 (_,b,c) = let pr = pr_pair pr3 !CP.print_svl in pr (b,c) in
  Debug.no_4 "generalize_hps_cs_new" pr1 !CP.print_svl !CP.print_svl !CP.print_svl pr4
    (fun _ _ _ _ -> generalize_hps_cs_new_x prog callee_hps hpdefs unk_hps link_hps cs)
    cs callee_hps hpdefs unk_hps

let generalize_hps_x prog is_pre callee_hps unk_hps link_hps sel_post_hps pre_defs predef_hps cs par_defs=
  x_binfo_pp ">>>>>> step 6: generalization <<<<<<" no_pos;
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
  let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in
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
let collect_sel_hp_def cond_path defs sel_hps unk_hps m=
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
  let mk_hprel_def kind hprel og opf opflib=
    let libs = match opflib with
      | None -> []
      | Some f -> [(f, None)]
    in
    {
      CF.hprel_def_kind = kind;
      CF.hprel_def_hrel = hprel;
      CF.hprel_def_guard = og;
      CF.hprel_def_body = [(cond_path,opf,None)];
      CF.hprel_def_body_lib = libs;
      CF.hprel_def_flow = None;
    }
  in
  let compute_def_w_lib (hp,d)=
    let olib = look_up_lib hp m in
    (* if CP.mem_svl hp unk_hps then *)
    (*   (mk_hprel_def a hprel None None) *)
    (* else *)
    begin
      let fs,ogs = List.split d.CF.def_rhs in
      let f = CF.disj_of_list fs no_pos in
      let og = CF.combine_guard ogs in
      let f1 =
        match olib with
        | None ->
          (*subs lib form inside f if applicable*)
          let f_subst = CF.subst_hrel_hview_f f m in
          f_subst
        | Some lib_f -> lib_f
      in
      (mk_hprel_def d.CF.def_cat d.CF.def_lhs og (Some f) (Some f1))
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
      | (hp,d)::lss ->
        let f = CF.disj_of_list (List.map fst d.CF.def_rhs) no_pos in
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
  let defsw = List.map (fun def ->
      (List.hd (CF.get_hp_rel_name_h_formula def.CF.def_lhs), def)) defs in
  let sel_defw,remain_hp_defs = List.partition (fun (hp,_) -> CP.mem_svl hp sel_hps) defsw in
  (* let sel_defw1 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) sel_defw in *)
  let closed_sel_defw = find_closed_sel sel_hps sel_defw remain_hp_defs sel_defw in
  let all_sel_defw = List.map compute_def_w_lib closed_sel_defw in
  (*remove hp not in orig but == lib*)
  let inter_lib = Gen.BList.difference_eq CP.eq_spec_var mlib sel_hps in
  List.filter (fun hdef ->
      let a1 = hdef.CF.hprel_def_kind in
      let hp = CF.get_hpdef_name a1 in
      not (CP.mem_svl hp inter_lib))
    all_sel_defw

(* let collect_sel_hp_def defs sel_hps unk_hps m= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in *)
(*   let pr2 = !CP.print_svl in *)
(*   let pr3b = pr_list_ln Cprinter.prtt_string_of_h_formula in *)
(*   let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^ *)
(*       (\* ( String.concat " OR " view_names) *\) (pr3b vns) in *)
(*   let pr3 = pr_list_ln pr3a in *)
(*   let pr4 = (pr_list_ln Cprinter.string_of_hprel_def) in *)
(*   Debug.no_3 "collect_sel_hp_def" pr1 pr2 pr3 pr4 *)
(*       (fun _ _ _ -> collect_sel_hp_def defs sel_hps unk_hps m) defs sel_hps m *)

let match_hps_views_x iprog prog (hp_defs: CF.hp_rel_def list) (vdcls: CA.view_decl list):
  (CP.spec_var* CF.h_formula list) list=
  let hp_defs1 = List.filter (fun def -> match def.CF.def_cat with
      | CP.HPRelDefn _ -> true
      | _ -> false
    ) hp_defs in
  let m = List.map (Sautil.match_one_hp_views iprog prog [] vdcls) (hp_defs1) in
  (List.filter (fun (_,l) -> l<>[]) m)

let match_hps_views iprog prog (hp_defs: CF.hp_rel_def list) (vdcls: CA.view_decl list):
  (CP.spec_var* CF.h_formula list) list=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln  Cprinter.prtt_string_of_h_formula  in
  let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^
                             (* ( String.concat " OR " view_names) *) (pr2 vns) in
  let pr3 = pr_list_ln pr3a in
  let pr4 = pr_list_ln (Cprinter.string_of_view_decl) in
  Debug.no_2 "match_hps_views" pr1 pr4 pr3
    (fun _ _ -> match_hps_views_x iprog prog hp_defs vdcls) hp_defs vdcls


(***************************************************************
                     END LIB MATCHING
 ****************************************************************)
let partition_constrs_x constrs post_hps0=
  (* let get_post_hp post_hps cs= *)
  (*   let ohp = CF.extract_hrel_head cs.CF.hprel_rhs in *)
  (*       match ohp with *)
  (*         | Some hp -> if (CP.mem_svl hp post_hps) then post_hps else *)
  (*             let lhps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in *)
  (*             if CP.mem_svl hp lhps then *)
  (*               ( post_hps@[hp]) *)
  (*             else post_hps *)
  (*         | None -> post_hps *)
  (* in *)
  let classify new_post_hps (pre_cs,post_cs,pre_oblg,tupled_hps, post_oblg) cs =
    let is_post =
      try
        let ohp = CF.extract_hrel_head cs.CF.hprel_rhs in
        match ohp with
        | Some (hp) -> (CP.mem_svl hp new_post_hps)
        | None -> false
      with _ -> false
    in
    if is_post then (pre_cs,post_cs@[cs],pre_oblg,tupled_hps,post_oblg) else
      let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
      if CP.intersect_svl (new_post_hps) lhs_hps = [] then
        (*identify pre-oblg*)
        let l_hds, l_hvs,lhrels =CF.get_hp_rel_formula cs.CF.hprel_lhs in
        let r_hds, r_hvs,rhrels =CF.get_hp_rel_formula cs.CF.hprel_rhs in
        if (List.length l_hds > 0 || List.length l_hvs > 0) && List.length lhrels > 0 &&
           (* (List.length r_hds > 0 || List.length r_hvs > 0) && *) List.length rhrels > 0
        then
          (pre_cs,post_cs,pre_oblg@[cs],tupled_hps@(CP.diff_svl (List.map (fun (a,_,_) -> a) rhrels) lhs_hps),post_oblg)
        else
          (pre_cs@[cs],post_cs,pre_oblg,tupled_hps,post_oblg)
      else (pre_cs,post_cs,pre_oblg,tupled_hps,post_oblg@[cs])
  in
  let new_post_hps = (* List.fold_left get_post_hp [] constrs *) [] in
  let pre_constrs,post_constrs,pre_oblg, tupled_dep_on_hps, post_oblg_constrs = List.fold_left (classify (post_hps0@new_post_hps)) ([],[],[],[],[]) constrs in
  (*partition pre-constrs, filter ones in pre-obligation*)
  let pre_constrs1, pre_oblg_ext = List.partition (fun cs ->
      let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
      CP.intersect_svl lhs_hps tupled_dep_on_hps = []
    ) pre_constrs in
  (pre_constrs1,post_constrs, pre_oblg@pre_oblg_ext, post_oblg_constrs, new_post_hps)
(* (pre_constrs,post_constrs, pre_oblg, post_oblg_constrs, new_post_hps) *)

let partition_constrs constrs post_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  Debug.no_2 "partition_constrs" pr1 pr2 (pr_penta pr1 pr1 pr1 pr1 pr2)
    (fun _ _ -> partition_constrs_x constrs post_hps) constrs post_hps

let rec infer_shapes_init_pre_x prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
    hp_rel_unkmap detect_dang (* :(CP.spec_var list * CF.hp_rel_def list* (CP.spec_var * CP.spec_var list) list) *) =
  let () = x_binfo_pp ">>>>>> step pre-4: remove unused predicates<<<<<<" no_pos in
  let constrs01 = (* Sautil.remove_dups_constr *) constrs0 in
  let constrs02 = List.map (Sautil.weaken_strengthen_special_constr_pre true) constrs01 in
  let unused_pre_hps, constrs0, unk_map1 =
    if detect_dang then elim_unused_pre_preds (sel_post_hps@link_hps) constrs02 hp_rel_unkmap
    else ([], constrs02, hp_rel_unkmap)
  in
  let unk_hpargs1 = Gen.BList.remove_dups_eq cmp_hpargs_fn (unk_hps@unused_pre_hps) in
  let unk_hps1 = (List.map fst unk_hpargs1) in
  let () = x_binfo_pp ">>>>>> pre-predicates: step pre-5: group & simpl impl<<<<<<" no_pos in
  let pr_par_defs,rem_constr1 = get_par_defs_pre constrs0 in
  (* let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in *)
  (* if rem_constr1 !=[] then *)
  (*   x_binfo_zp (lazy (("pre-obligation:\n" ^ (pr1 rem_constr1)))) no_pos; *)
  (* let () = x_binfo_pp ">>>>>> pre-predicates: step pre-6: combine<<<<<<" no_pos in *)
  let par_defs, rem_constrs2, hconj_unify_cond = combine_pdefs_pre prog unk_hps1 link_hps pr_par_defs in
  let () = x_binfo_pp ">>>>>> pre-predicates: step pre-7: remove redundant x!=null<<<<<<" no_pos in
  let () = x_binfo_pp ">>>>>> pre-predicates: step pre-8: strengthen<<<<<<" no_pos in
  let rem_constrs3, hp_defs, defined_hps = generalize_hps prog true callee_hps unk_hpargs1 link_hps sel_post_hps [] []
      constrs0 par_defs in
  (* check hconj_unify_cond*)
  let hp_defs1, new_equivs, unk_equivs = if hconj_unify_cond = [] then (hp_defs,[], []) else
      let is_sat, new_hpdefs, equivs, unk_equivs,punk_equivs = Sacore.reverify_cond prog unk_hps1 link_hps hp_defs hconj_unify_cond in
      if not is_sat then report_error no_pos "SA.infer_shapes_init_pre: HEAP CONJS do not SAT"
      else (new_hpdefs, equivs,  unk_equivs)
  in
  (* generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in *)
  (* let hp_names,hp_defs = List.split pair_names_defs in *)
  (*TODO: check consistency of the solution against rem_constraints: LOOP*)
  (defined_hps,hp_defs1,unk_hpargs1, unk_map1, new_equivs, unk_equivs,rem_constr1)

and infer_shapes_init_pre prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
    hp_rel_unkmap detect_dang (* :(CP.spec_var list * CF.hp_rel_def list * (CP.spec_var * CP.spec_var list) list) *) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_,_,_,pre_oblg) = (pr_quad pr2 pr3 pr4 pr1) (a,b,c,pre_oblg) in
  Debug.no_1 "infer_shapes_init_pre" pr1 pr5
    (fun _ -> infer_shapes_init_pre_x prog constrs0 callee_hps non_ptr_unk_hps sel_post_hps unk_hps link_hps
        hp_rel_unkmap detect_dang) constrs0

and infer_shapes_init_post_x prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps
    hp_rel_unkmap detect_dang pre_defs (* :(CP.spec_var list * CF.hp_rel_def list * (CP.spec_var * CP.spec_var list) list * ) *) =
  let constrs0a = (* Sautil.remove_dups_constr *) constrs0 in
  let constrs0b = List.map (Sautil.weaken_strengthen_special_constr_pre false) constrs0a in
  let () = x_binfo_pp ">>>>>> step post-4: step remove unused predicates<<<<<<" no_pos in
  let unused_post_hps,constrs1,unk_map1 =
    if detect_dang then elim_unused_post_preds (sel_post_hps@link_hps) constrs0b hp_rel_unkmap
    else ([], constrs0b, hp_rel_unkmap)
  in
  let unk_hps1 = Gen.BList.remove_dups_eq cmp_hpargs_fn (unk_hps@unused_post_hps) in
  let par_defs = get_par_defs_post constrs1 in
  let () = x_binfo_pp ">>>>>> post-predicates: step post-5: remove redundant x!=null : not implemented yet<<<<<<" no_pos in

  let () = x_binfo_pp ">>>>>> post-predicates: step post-61: weaken<<<<<<" no_pos in
  (*subst pre-preds into if they are not recursive -do with care*)
  let pre_hps_need_fwd= Sautil.get_pre_fwd sel_post_hps par_defs in
  let pre_defs, pre_hps = Sautil.extract_fwd_pre_defs pre_hps_need_fwd pre_defs in
  let pair_names_defs = generalize_hps_par_def prog false non_ptr_unk_hps unk_hps1 link_hps sel_post_hps pre_defs pre_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
  (* let () = if hp_names = [] then () else *)
  (*   x_binfo_pp (" synthesize: " ^ (!CP.print_svl hp_names) )no_pos *)
  (* in *)
  (hp_names,hp_defs,unk_hps1,unk_map1)

and infer_shapes_init_post prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps unk_hps link_hps hp_rel_unkmap
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

(*for each oblg generate new constrs with new hp post in rhs*)
(*call to infer_shape? proper? or post?*)
and infer_shapes_from_fresh_obligation_x iprog cprog proc_name is_pre cond_path (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_lhps sel_rhps sel_post_hps
    unk_hpargs link_hpargs need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps=
  (*if rhs is emp heap, should retain the constraint*)
  let pre_constrs, pre_oblg = List.partition (fun cs -> Cfutil.is_empty_heap_f cs.CF.hprel_rhs) constrs0 in
  let ho_constrs0, nondef_post_hps = List.fold_left (collect_ho_ass iprog cprog is_pre def_hps) ([],[]) pre_oblg in
  let ho_constrs = ho_constrs0@pre_constrs in
  if ho_constrs = [] then ([],[],unk_hpargs,hp_rel_unkmap) else
    (***************  PRINTING*********************)
    let _ =
      begin
        let pr = pr_list_ln Cprinter.string_of_hprel_short in
        print_endline_quiet "";
        print_endline_quiet "\n*************************************************";
        print_endline_quiet "*******relational assumptions (obligation)********";
        print_endline_quiet "****************************************************";
        print_endline_quiet (pr ho_constrs0);
        print_endline_quiet "*************************************"
      end
    in
    let _ =
      begin
        let pr = pr_list_ln Cprinter.string_of_hprel_short in
        print_endline_quiet "";
        print_endline_quiet "\n*************************************************";
        print_endline_quiet "*******relational assumptions (pre-assumptions)********";
        print_endline_quiet "****************************************************";
        print_endline_quiet (pr pre_constrs);
        print_endline_quiet "*************************************"
      end
    in
    (***************  END PRINTING*********************)
    let constr, hp_defs, unk_hpargs2, link_hpargs2, equivs = infer_shapes_core iprog cprog proc_name cond_path
        ho_constrs callee_hps (sel_lhps@sel_rhps)
        (*post-preds in lhs which dont have ad definition should be considered as pre-preds*)
        (CP.diff_svl (sel_post_hps@sel_rhps) nondef_post_hps)
        hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang in
    let hp_names = List.fold_left ( fun ls hpdef->
        let new_hps =  match hpdef.CF.def_cat with
          | CP.HPRelDefn (hp,_,_) -> [hp]
          | CP.HPRelLDefn hps -> hps
          | _ -> []
        in
        ls@new_hps
      ) [] hp_defs in
    (hp_names,hp_defs,unk_hpargs2,[])

and infer_shapes_from_fresh_obligation iprog cprog proc_name is_pre cond_path (constrs0: CF.hprel list)
    callee_hps non_ptr_unk_hps sel_lhps sel_rhps sel_post_hps
    unk_hps link_hps need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_) = (pr_triple pr2 pr3 pr4) (a,b,c) in
  Debug.no_1 "infer_shapes_from_fresh_obligation" pr1 pr5
    (fun _ -> infer_shapes_from_fresh_obligation_x iprog cprog proc_name is_pre cond_path constrs0
        callee_hps non_ptr_unk_hps sel_lhps sel_rhps sel_post_hps unk_hps
        link_hps need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps)
    constrs0


and infer_shapes_from_obligation_x iprog prog proc_name is_pre cond_path (constrs0: CF.hprel list)
    callee_hps non_ptr_unk_hps sel_post_hps unk_hpargs link_hpargs need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps=
  (*TODO: tupled preds should be infer after the obligation (from the below rem_constrs)*)
  (* let def_hps_w_tupled = List.fold_left (fun ls (hp_kind, _,_,_) -> *)
  (*     match hp_kind with *)
  (*         |  CP.HPRelDefn (hp,_,_) -> ls@[hp] *)
  (*         | _ -> ls *)
  (* ) [] (pre_defs@post_defs) in *)
  let classify_hps (r_lhs, r_rhs, dep_def_hps, r_oblg_constrs,r_rem_constrs) cs=
    let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
    let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in
    let dep_define_hps1, rem_lhs = List.partition (fun hp -> CP.mem_svl hp def_hps) lhs_hps in
    let dep_define_hps2, rem_rhs = List.partition (fun hp -> CP.mem_svl hp def_hps) rhs_hps in
    if (* (rem_lhs = [] && rem_rhs=[]) || *)(is_pre && rem_rhs = [] && rem_lhs = []) ||
                                            ((not is_pre) && (rem_lhs <> [])) then
      (r_lhs, r_rhs, dep_def_hps, r_oblg_constrs, r_rem_constrs@[cs])
    else
      (r_lhs@rem_lhs, r_rhs@rem_rhs, dep_def_hps@dep_define_hps1@dep_define_hps2,r_oblg_constrs@[cs], r_rem_constrs)
  in
  if constrs0 = [] then ([],[],unk_hpargs,hp_rel_unkmap) else
    let constrs1 = Sautil.remove_dups_constr constrs0 in
    (*the remain contraints will be treated as tupled ones.*)
    let sel_lhs_hps, sel_rhs_hps, dep_def_hps, oblg_constrs, rem_constr = List.fold_left classify_hps ([],[],[],[],[]) constrs1 in
    if oblg_constrs = [] then
      let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in
      x_binfo_zp (lazy (("proving:\n" ^ (pr1 rem_constr)))) no_pos;
      (* let () = if rem_constr = [] then () else *)
      (* (\*prove rem_constr*\) *)
      (* (\*transform defs to cviews*\) *)
      (* let need_trans_hprels = List.filter (fun (hp_kind, _,_,_) -> *)
      (*     match hp_kind with *)
      (*       |  CP.HPRelDefn (hp,_,_) -> CP.mem_svl hp dep_def_hps *)
      (*       | _ -> false *)
      (* ) (pre_defs@post_defs) in *)
      (* let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog prog proc_name need_trans_hprels in *)
      (* let in_hp_names = List.map CP.name_of_spec_var dep_def_hps in *)
      (* (\*for each oblg, subst + simplify*\) *)
      (* let rem_constr2 = Sacore.trans_constr_hp_2_view_x iprog prog proc_name (pre_defs@post_defs) *)
      (*   in_hp_names chprels_decl rem_constr in *)
      (* let () = List.fold_left (collect_ho_ass prog is_pre def_hps) ([],[]) rem_constr2 in *)
      (* () *)
      (* in *)
      ([],[],unk_hpargs,hp_rel_unkmap)
    else
      (* let () = DD.info_zprint (lazy (("dep_def_hps: " ^ (!CP.print_svl dep_def_hps)))) no_pos in *)
      let need_trans_hprels = List.filter (fun d ->
          match d.CF.def_cat with
          |  CP.HPRelDefn (hp,_,_) -> CP.mem_svl hp dep_def_hps
          | _ -> false
        ) (pre_defs@post_defs) in
      (*transform defs to cviews*)
      let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog prog proc_name need_trans_hprels in
      let in_hp_names = List.map CP.name_of_spec_var dep_def_hps in
      (*for each oblg, subst + simplify*)
      let constrs2 = Sacore.trans_constr_hp_2_view iprog prog proc_name (pre_defs@post_defs)
          in_hp_names chprels_decl oblg_constrs in
      (*for each oblg generate new constrs with new hp post in rhs*)
      (*call to infer_shape? proper? or post?*)
      let  oblg_hps1, oblg_defs1, unk_hpargs1,unk_map1=
        infer_shapes_from_fresh_obligation iprog prog proc_name is_pre cond_path constrs2
          callee_hps non_ptr_unk_hps sel_lhs_hps sel_rhs_hps sel_post_hps unk_hpargs link_hpargs
          need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps
      in
      let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in
      x_binfo_zp (lazy (("rem_constr:\n" ^ (pr1 rem_constr)))) no_pos;
      if rem_constr = [] then
        (*return*)
        (oblg_hps1, oblg_defs1, unk_hpargs1,unk_map1)
      else
        (*loop*)
        let pre_defs1,post_defs1 = if is_pre then (pre_defs@oblg_defs1,post_defs)
          else (pre_defs,post_defs@oblg_defs1)
        in
        let oblg_hps2, oblg_defs2, unk_hpargs2,unk_map2= infer_shapes_from_obligation iprog prog proc_name is_pre cond_path rem_constr callee_hps [] sel_post_hps unk_hpargs1
            link_hpargs need_preprocess unk_map1 detect_dang (pre_defs1) post_defs1 (def_hps(* @oblg_hps1 *)) in
        (oblg_hps1@oblg_hps2, oblg_defs1@oblg_defs2,unk_hpargs2,unk_map2)

and infer_shapes_from_obligation iprog prog proc_name is_pre cond_path (constrs0: CF.hprel list)
    callee_hps non_ptr_unk_hps sel_post_hps
    unk_hps link_hps need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list (pr_pair !CP.print_sv pr2) in
  let pr5 (a,b,c,_) = (pr_triple pr2 pr3 pr4) (a,b,c) in
  Debug.no_2 "infer_shapes_from_obligation" pr1 pr2 pr5
    (fun _ _ -> infer_shapes_from_obligation_x iprog prog proc_name is_pre cond_path constrs0
        callee_hps non_ptr_unk_hps sel_post_hps unk_hps
        link_hps need_preprocess hp_rel_unkmap detect_dang pre_defs post_defs def_hps)
    constrs0 def_hps

and infer_shapes_proper iprog prog proc_name cond_path (constrs2: CF.hprel list) callee_hps sel_hp_rels sel_post_hps
    (unk_map2: ((CP.spec_var * int list) * CP.xpure_view) list)
    prog_vars unk_hpargs link_hpargs need_preprocess detect_dang: (CF.hprel list * CF.hp_rel_def list *
                                                                   (CP.spec_var * CP.spec_var list) list *  (CP.spec_var *CP.spec_var list) list * (CP.spec_var *CP.spec_var) list)=
  let unk_hps = List.map fst unk_hpargs in
  let link_hps = List.map fst link_hpargs in
  let () = x_binfo_pp ">>>>>> step 3: apply transitive implication<<<<<<" no_pos in
  let constrs3,_ = apply_transitive_impl_fix prog sel_post_hps callee_hps unk_hps
      link_hps constrs2 in
  (*partition constraints into 2 groups: pre-predicates, post-predicates*)
  let pre_constrs,post_constrs, pre_oblg_constrs, post_oblg_constrs, new_post_hps = partition_constrs constrs3 sel_post_hps in
  let sel_post_hps1 = sel_post_hps@new_post_hps in
  let pre_constrs1 = List.map (Sautil.simp_match_unknown unk_hps link_hps) pre_constrs in
  (*find inital sol*)
  let () = x_binfo_pp ">>>>>> pre-predicates<<<<<<" no_pos in
  let pre_hps, pre_defs, unk_hpargs1,unk_map3, pre_equivs, unk_equivs, _ (*pre_oblg_constrs*) = infer_shapes_init_pre prog pre_constrs1 callee_hps []
      (sel_post_hps1) unk_hpargs link_hps unk_map2 detect_dang in
  let pre_defs1, unify_equiv_map1 = if !Globals.pred_conj_unify then
      Sacore.do_unify prog true unk_hps link_hps sel_post_hps1 pre_defs
    else
      (pre_defs, [])
  in
  let pre_defs2, unify_equiv_map11=
    if !Globals.pred_equiv then (*TODO: should move it to normalization*)
      Sacore.unify_pred prog unk_hps link_hps pre_defs1 unify_equiv_map1
    else (pre_defs1, unify_equiv_map1)
  in
  (*********PRE-OBLG ********)
  let pre_oblg_hps, pre_oblg_defs,unk_hpargs2,unk_map4  = if !Globals.pred_en_oblg then
      infer_shapes_from_obligation iprog prog proc_name true cond_path (pre_oblg_constrs) callee_hps []
        (sel_post_hps1) unk_hpargs1
                                         (* link_hpargs *)[] need_preprocess unk_map3 detect_dang pre_defs2 [] (pre_hps)
    else ([],[],unk_hpargs1,  unk_map3)
  in
  let () = x_binfo_pp ">>>>>> post-predicates<<<<<<" no_pos in
  let post_constrs1 = Sautil.subst_equiv_hprel unify_equiv_map11 post_constrs in
  let post_hps, post_defs,unk_hpargs3,unk_map5  = infer_shapes_init_post prog post_constrs1 []
      (sel_post_hps1) unk_hpargs2 link_hps unk_map4 detect_dang pre_defs2 in
  let post_defs1,unify_equiv_map2 = if !Globals.pred_unify_post then
      Sacore.do_unify prog false unk_hps link_hps post_hps post_defs
    else
      (post_defs,unify_equiv_map11)
  in
  (*********POST-OBLG ********)
  let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in
  if post_oblg_constrs !=[] then
    x_binfo_zp (lazy (("post-obligation:\n" ^ (pr1 post_oblg_constrs)))) no_pos;
  let post_oblg_hps, post_oblg_defs,unk_hpargs4,unk_map6  = if !Globals.pred_en_oblg then
      infer_shapes_from_obligation iprog prog proc_name false cond_path (post_oblg_constrs) callee_hps []
        (sel_post_hps1) unk_hpargs3
                                         (* link_hpargs *)[] need_preprocess unk_map5 detect_dang (pre_defs2@pre_oblg_defs) post_defs1 (pre_hps@post_hps@pre_oblg_hps)
    else ([],[],unk_hpargs3,  unk_map5 )
  in
  (*********END POST-OBLG************)
  let defs1 = (pre_defs2@post_defs1@pre_oblg_defs@post_oblg_defs) in
  (*normalization*)
  let def_oblg_hps = pre_oblg_hps@post_oblg_hps in
  let link_hpargs2 = List.filter (fun (hp,_) -> not(CP.mem hp def_oblg_hps)) link_hpargs in
  let link_hps1 = List.map fst link_hpargs2 in
  let defs2a, unify_equiv_map3 =
    if !Globals.pred_equiv then (*TODO: should move it to normalization*)
      Sacore.unify_pred prog unk_hps link_hps1 defs1 (pre_equivs@unify_equiv_map2@unk_equivs)
    else (defs1, unify_equiv_map2)
  in
  let htrue_hpargs, defs2b = Sautil.convert_HTrue_2_None defs2a in
  let defs2 = Sacore.generate_hp_def_from_unk_hps defs2b unk_hpargs4 (pre_hps@post_hps@post_oblg_hps@pre_oblg_hps)
      sel_post_hps1 unk_map6 unify_equiv_map3 in
  let defs3,link_hpargs3 = if !Globals.pred_elim_dangling then
      (* Sautil.transform_unk_hps_to_pure (defs3b) unk_hp_frargs *)
      let defs3a,remain_links = Sacore.transform_xpure_to_pure prog defs2 unk_map4 (link_hpargs2@htrue_hpargs) in
      (*we have already transformed link/unk preds into pure form.
        Now return [] so that we do not need generate another unk preds*)
      (defs3a, remain_links)
    else (defs2,link_hpargs2@htrue_hpargs)
  in
  (constrs2, defs3, unk_hpargs4, link_hpargs3,(pre_equivs@unify_equiv_map2@unk_equivs))

and infer_shapes_core iprog prog proc_name cond_path (constrs0: CF.hprel list) callee_hps sel_hp_rels sel_post_hps hp_rel_unkmap
    unk_hpargs0a link_hpargs need_preprocess detect_dang:
  (CF.hprel list * CF.hp_rel_def list  *
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
  (* let constrs, unk_map0, unk_hpargs = Sacore.syn_unk constrs0 hp_rel_unkmap sel_post_hps no_pos in *)
  let constrs1,unk_map,unk_hpargs, link_hpargs3,_ =
    if need_preprocess then
      (*unk analysis*)
      let () = x_binfo_pp ">>>>>> step 1: find dangling ptrs, link pre and post-preds dangling preds<<<<<<" no_pos in
      (* let constrs3, unk_map1, unk_hpargs = Sacore.detect_dangling_pred constrs2 sel_hp_rels unk_map in *)
      let constrs1, unk_hpargs1, unk_map1, link_hpargs1, punk_map0 =
        if detect_dang then
          x_add Sacore.analize_unk prog sel_post_hps constrs0 hp_rel_unkmap unk_hpargs link_hpargs
        else
          (*if dangling is not analized, find partial dangling/unknown*)
          let punk_map =  [] in
          (constrs0, unk_hpargs,hp_rel_unkmap,link_hpargs, punk_map)
      in
      let () = x_binfo_pp ">>>>>> step 2: split constraints based on pre and post-preds<<<<<<" no_pos in
      (*split constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
      let unk_hps1 = List.map fst unk_hpargs1 in
      let link_hps1 = List.map fst link_hpargs1 in
      let constrs2, unk_map2, link_hpargs2 =
        if !Globals.sa_sp_split_base || !Globals.sa_infer_split_base then
          split_constr prog cond_path constrs1 sel_post_hps prog_vars unk_map1 unk_hps1 link_hps1
        else
          (constrs1, unk_map1, [] (*extra preds from spec split*))
      in
      let link_hpargs3= link_hpargs1@link_hpargs2 in
      (constrs2, unk_map2,unk_hpargs1, link_hpargs3, punk_map0)
    else
      let punk_map0 = [] in
      (constrs0, hp_rel_unkmap, unk_hpargs, link_hpargs, punk_map0)
  in
  (* let unk_hps = (List.map fst unk_hpargs) in *)
  (*TODO: remove detect dangling at pre/post process*)
  (*TEMP*)
  let user_detect_dang =  false (* detect_dang && !Globals.pred_elim_unused_preds  *)in
  (* let () = Debug.info_pprint ("  link_hpargs3: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                             in pr link_hpargs3)) no_pos *)
  (*  in *)
  let () = DD.ninfo_zprint (lazy (("   constrs1:" ^ (let pr = pr_list_ln Cprinter.string_of_hprel_short in pr constrs1)))) no_pos in
  infer_shapes_proper iprog prog proc_name cond_path constrs1 callee_hps sel_hp_rels sel_post_hps unk_map prog_vars
    unk_hpargs link_hpargs3 need_preprocess user_detect_dang

and infer_shapes_divide iprog prog proc_name (constrs0: CF.hprel list) callee_hps sel_hps sel_post_hps
    hp_rel_unkmap unk_hpargs0 link_hpargs0 need_preprocess detect_dang:
  ((CF.cond_path_type * CF.hp_rel_def list *
    (CP.spec_var * CP.spec_var list) list * (CP.spec_var * CP.spec_var list) list * (CP.spec_var * CP.spec_var) list ) list) =
  let process_one_path (cond_path, link_hpargs, constrs1)=
    let constr, hp_defs, unk_hpargs2, link_hpargs2, equivs = infer_shapes_core iprog prog proc_name cond_path constrs1
        callee_hps sel_hps sel_post_hps hp_rel_unkmap unk_hpargs0 link_hpargs need_preprocess detect_dang
    in
    (cond_path, hp_defs, unk_hpargs2, link_hpargs2, equivs)
  in
  (* let ls_link_hpargs = Sautil.dang_partition link_hpargs0 in *)
  (* let ls_constrs_path = Sautil.assumption_partition constrs0 in *)
  (* (\* matching constrs_path with dang_path*\) *)
  (* let ls_cond_danghps_constrs = Sautil.pair_dang_constr_path ls_constrs_path ls_link_hpargs (pr_list_ln Cprinter.string_of_hprel_short) in *)
  let ls_cond_danghps_constrs = Sacore.partition_constrs_4_paths link_hpargs0 constrs0 in
  (*synthesize for each path*)
  let ls_res = List.map process_one_path ls_cond_danghps_constrs in
  ls_res


and infer_shapes_conquer iprog prog proc_name ls_path_defs_setting sel_hps iflow=
  let process_path_defs_setting (cond_path, hp_defs, unk_hpargs0, link_hpargs0, equivs)=
    let hp_defs1,tupled_defs = Sautil.partition_tupled hp_defs in
    let cl_sel_hps, defs, tupled_defs2=
      if !Globals.pred_elim_unused_preds then
        let cl_sel_hps, hp_defs2 = Sautil.find_closed_sel_hp_def hp_defs1 sel_hps
            (List.map fst link_hpargs0) equivs in
        (cl_sel_hps, hp_defs2, [])
      else
        let tupled_defs1 = List.map (fun d ->
            let fs, ogs = List.split d.CF.def_rhs in
            let f = (CF.disj_of_list fs no_pos) in
            {
              CF.hprel_def_kind = d.CF.def_cat;
              CF.hprel_def_hrel = d.CF.def_lhs;
              CF.hprel_def_guard = CF.combine_guard ogs;
              CF.hprel_def_body = [(cond_path, Some f,Some iflow)];
              CF.hprel_def_body_lib = [(f, Some iflow)];
              CF.hprel_def_flow = Some iflow;
            }
          ) tupled_defs
        in
        let cl_sel_hps = (List.map fst link_hpargs0)@
                         (List.fold_left (fun ls d -> ls@(CF.get_hp_rel_name_h_formula d.CF.def_lhs)) [] hp_defs1)
        in
        (cl_sel_hps, hp_defs1,tupled_defs1)
    in
    let hpdefs = List.map (fun d ->
        let fs,ogs = List.split d.CF.def_rhs in
        let og = CF.combine_guard ogs in
        let f = CF.disj_of_list fs no_pos in
        CF.mk_hprel_def d.CF.def_cat d.CF.def_lhs og [(cond_path, Some f)] (Some f) (Some iflow)
      ) defs
    in
    let link_hp_defs = Sacore.generate_hp_def_from_link_hps prog iflow cond_path equivs link_hpargs0 in
    (cl_sel_hps@(List.map fst link_hpargs0), hpdefs@link_hp_defs, tupled_defs2)
  in
  let cl_sel_hps, path_defs, tupled_defs = List.fold_left (fun (ls1, ls2,ls3) path_setting ->
      let r1,r2,r3 = process_path_defs_setting path_setting in
      (ls1@r1, ls2@[r2], ls3@r3)
    ) ([],[],[]) ls_path_defs_setting
  in
  let cl_sel_hps1 = CP.remove_dups_svl cl_sel_hps in
  let cmb_defs = Sautil.combine_path_defs cl_sel_hps1 path_defs iflow in
  let () = List.iter (fun hp_def -> rel_def_stk # push hp_def) (cmb_defs@tupled_defs) in
  cmb_defs

and infer_shapes_new_x iprog prog proc_name (constrs0: CF.hprel list) sel_hps sel_post_hps hp_rel_unkmap unk_hpargs
    link_hpargs_w_path need_preprocess detect_dang iflow=
  (* (CF.cond_path_type * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list ) = *)
  (*move to outer func*)
  (* let callee_hpdefs = *)
  (*   try *)
  (*       Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name *)
  (*   with _ -> [] *)
  (* in *)
  (* let callee_hps = List.map (fun (hpname,_,_) -> CF.get_hpdef_name hpname) callee_hpdefs in *)
  let callee_hps = [] in
  let () = x_binfo_zp (lazy (("  sel_hps:" ^ !CP.print_svl sel_hps))) no_pos in
  let () = x_binfo_zp (lazy (("  sel post_hps:" ^ !CP.print_svl sel_post_hps))) no_pos in
  let all_post_hps = CP.remove_dups_svl (sel_post_hps@(Sautil.collect_post_preds prog constrs0)) in
  let () = x_binfo_zp (lazy (("  all post_hps:" ^ !CP.print_svl all_post_hps))) no_pos in
  let ls_path_res = infer_shapes_divide iprog prog proc_name constrs0
      callee_hps sel_hps all_post_hps hp_rel_unkmap unk_hpargs link_hpargs_w_path need_preprocess detect_dang
  in
  let r =
    match ls_path_res with
    |[] -> ([])
    | (* (cond_path, hp_defs, c, unk_hpargs2, link_hpargs2, equivs)::_ *) _ -> (*conquer HERE*)
      infer_shapes_conquer iprog prog proc_name ls_path_res sel_hps iflow
      (* let link_hp_defs = Sacore.generate_hp_def_from_link_hps prog cond_path equivs link_hpargs2 in *)
      (* let hp_defs1,tupled_defs = Sautil.partition_tupled hp_defs in *)
      (* (\*decide what to show: DO NOT SHOW hps relating to tupled defs*\) *)
      (* let m = match_hps_views hp_defs1 prog.CA.prog_view_decls in *)
      (* let sel_hps1 = if !Globals.pred_elim_unused_preds then sel_hps else *)
      (*   CP.remove_dups_svl ((List.map (fun (a,_,_) -> CF.get_hpdef_name a) hp_defs1)@sel_hps) *)
      (* in *)
      (* let sel_hp_defs = collect_sel_hp_def cond_path hp_defs1 sel_hps1 unk_hpargs2 m in *)
      (* let tupled_defs1 = List.map (fun (a, hf, f) -> { *)
      (*     CF.hprel_def_kind = a; *)
      (*     CF.hprel_def_hrel = hf; *)
      (*     CF.hprel_def_body = [(cond_path, Some f)]; *)
      (*     CF.hprel_def_body_lib = Some f; *)
      (* } *)
      (* ) tupled_defs in *)
      (* let shown_defs = if !Globals.pred_elim_unused_preds then sel_hp_defs@link_hp_defs else *)
      (*   sel_hp_defs@tupled_defs1@link_hp_defs *)
      (* in *)
      (* let () = List.iter (fun hp_def -> rel_def_stk # push hp_def) shown_defs in *)
      (* (cond_path, hp_defs, c) *)
  in
  r

and infer_shapes_x iprog prog proc_name (constrs0: CF.hprel list) sel_hps post_hps hp_rel_unkmap unk_hpargs link_hpargs0 need_preprocess detect_dang flow_int:
  (CF.hprel list * CF.hp_rel_def list * CP.spec_var list) =
  (*move to outer func*)
  (* let callee_hpdefs = *)
  (*   try *)
  (*       Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name *)
  (*   with _ -> [] *)
  (* in *)
  (* let callee_hps = List.map (fun (hpname,_,_) -> CF.get_hpdef_name hpname) callee_hpdefs in *)
  let callee_hps = [] in
  let () = x_binfo_zp (lazy (("  sel_hps:" ^ !CP.print_svl sel_hps))) no_pos in
  let () = x_binfo_zp (lazy (("  sel post_hps:" ^ !CP.print_svl post_hps))) no_pos in
  let all_post_hps = CP.remove_dups_svl (post_hps@(Sautil.collect_post_preds prog constrs0)) in
  let () = x_binfo_zp (lazy (("  all post_hps:" ^ !CP.print_svl all_post_hps))) no_pos in
  (*remove hp(x) --> hp(x)*)
  (* let constrs1 = List.filter (fun cs -> not(Sautil.is_trivial_constr cs)) constrs0 in *)
  let grp_link_hpargs = Sautil.dang_partition link_hpargs0 in
  (*TODO: LOC: find a group of rel ass with the same cond_path.
    Now, assume = []
  *)
  let cond_path = [] in
  (*for temporal*)
  let link_hpargs = match grp_link_hpargs with
    | [] -> []
    | (_, a)::_ -> a
  in
  let constr, hp_defs, unk_hpargs2, link_hpargs2, equivs = infer_shapes_core iprog prog proc_name cond_path constrs0
      callee_hps sel_hps
      all_post_hps hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang in
  let link_hp_defs = Sacore.generate_hp_def_from_link_hps prog flow_int cond_path equivs link_hpargs2 in
  let hp_defs1,tupled_defs = Sautil.partition_tupled hp_defs in
  (* decide what to show: DO NOT SHOW hps relating to tupled defs *)
  let m = match_hps_views iprog prog hp_defs1 prog.CA.prog_view_decls in
  let sel_hps1 = if !Globals.pred_elim_unused_preds then sel_hps else
      CP.remove_dups_svl ((List.map (fun d -> CF.get_hpdef_name d.CF.def_cat) hp_defs1)@sel_hps)
  in
  let sel_hp_defs = collect_sel_hp_def cond_path hp_defs1 sel_hps1 unk_hpargs2 m in
  let tupled_defs1 = List.map (fun d ->
      let fs,ogs = List.split d.CF.def_rhs in
      let f = CF.disj_of_list fs no_pos in
      let og = CF.combine_guard ogs in
      {
        CF.hprel_def_kind = d.CF.def_cat;
        CF.hprel_def_hrel = d.CF.def_lhs;
        CF.hprel_def_guard = og;
        CF.hprel_def_body = [(cond_path, Some f, None)];
        CF.hprel_def_body_lib = [(f, None)];
        CF.hprel_def_flow = None;
      }
    ) tupled_defs in
  let shown_defs = if !Globals.pred_elim_unused_preds then sel_hp_defs@link_hp_defs else
      sel_hp_defs@tupled_defs1@link_hp_defs
  in
  let () = List.iter (fun hp_def -> rel_def_stk # push hp_def) shown_defs in
  (constr, hp_defs, CP.remove_dups_svl (List.map fst (unk_hpargs2@link_hpargs2)))


let infer_shapes iprog prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hp_rels
    hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang flow_int:
  (* (CF.cond_path_type * CF.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) = *)
  (CF.hprel list * CF.hp_rel_def list * CP.spec_var list) =
  (* let pr0 = pr_list !CP.print_exp in *)
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  (* let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in *)
  (* let pr4 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in *)
  let pr4 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5a = pr_list (pr_pair CF.string_of_cond_path (pr_pair !CP.print_sv !CP.print_svl)) in
  let () = if !Globals.print_heap_pred_decl then
      let all_hps = CF.get_hp_rel_name_assumption_set hp_constrs in
      let all_hp_decls = List.fold_left (fun ls hp ->
          try
            let hp_decl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
            ls@[hp_decl]
          with _ -> ls
        ) [] all_hps
      in
      if !Globals.sleek_flag then () 
      else
        let () = print_endline_quiet "\nHeap Predicate Declarations" in
        let () = print_endline_quiet "===========================" in
        let () = List.iter (fun hpdcl -> print_string (Cprinter.string_of_hp_decl hpdcl)) all_hp_decls in
        ()
    else ()
  in
  Debug.no_6 "infer_shapes" pr_id pr1 !CP.print_svl pr4 pr5 pr5a (pr_triple pr1 pr2 !CP.print_svl)
    (fun _ _ _ _ _ _ -> infer_shapes_x iprog prog proc_name hp_constrs sel_hp_rels
        sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
        need_preprocess detect_dang flow_int)
    proc_name hp_constrs sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs

let infer_shapes_new iprog prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hp_rels
    hp_rel_unkmap unk_hpargs link_hpargs need_preprocess detect_dang iflow: CF.hprel_def list=
  (* (CF.cond_path_type * CF.hp_reldef list*(CP.spec_var*CP.exp list * CP.exp list) list) = *)
  (* (CF.hprel list * CF.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) = *)
  (* let pr0 = pr_list !CP.print_exp in *)
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def_short in
  (* let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in *)
  (* let pr4 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in *)
  let pr4 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  (* let pr6 = (pr_triple CF.string_of_cond_path pr2 pr3) in *)
  let () = if !Globals.print_heap_pred_decl then
      let all_hps = CF.get_hp_rel_name_assumption_set hp_constrs in
      let all_hp_decls = List.map (fun hp ->
          Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp)) all_hps in
      let () = List.iter (fun hpdcl -> print_string (Cprinter.string_of_hp_decl hpdcl)) all_hp_decls in
      ()
    else ()
  in
  Debug.no_6 "infer_shapes_new" pr_id pr1 !CP.print_svl pr4 pr5 pr_none pr2
    (fun _ _ _ _ _ _ -> infer_shapes_new_x iprog prog proc_name hp_constrs sel_hp_rels
        sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
        need_preprocess detect_dang iflow)
    proc_name hp_constrs sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
