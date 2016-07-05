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
(* module CFU = Cfutil *)
module MCP = Mcpure
module CEQ = Checkeq
(* module TP = Tpdispatcher *)
(* module SAC = Sacore *)
(* module SAU = Sautility *)
module IC = Icontext
(* module LEM = Lemma *)
let step_change = new Gen.change_flag

(***************************************************************)
(*      APPLY TRANS IMPL     *)
(****************************************************************)
let collect_ho_ass iprog cprog is_pre def_hps unk_hps (acc_constrs, post_no_def) cs=
  let lhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
  let rhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_rhs in
  (* let () = Debug.info_zprint (lazy (("    rhs_hps: " ^ (!CP.print_svl rhs_hps)))) no_pos in *)
  let linfer_hps = CP.remove_dups_svl (CP.diff_svl (lhs_hps) def_hps) in
  let rinfer_hps =  (CP.diff_svl (rhs_hps) def_hps) in
  let infer_hps = CP.remove_dups_svl (linfer_hps@rinfer_hps) in
  (* if infer_hps = [] then (acc_constrs, post_no_def) else *)
  let log_str = if is_pre then PK_Pre_Oblg else PK_Post_Oblg in
  let  _ =
    if !VarGen.sap then
      DD.info_zprint (lazy (((string_of_proving_kind log_str) ^ ":\n" ^ (Cprinter.string_of_hprel_short cs)))) no_pos
    else ()
  in
  (* let tmp = Wrapper.check_is_classic in *)
  (* let () = Wrapper.set_classic  true in *)
  let f = wrap_proving_kind log_str (Sacore.do_entail_check (infer_hps@unk_hps) iprog cprog) in
  let new_constrs = Wrapper.wrap_classic x_loc (Some true) f cs in
  (* let () = Wrapper.set_classic  tmp in *)
  (acc_constrs@new_constrs, post_no_def@linfer_hps)


(*input in fb
  output: true,subst: can subst
*)

(*
dn is current node, it is one node of ldns
ss: subst from ldns -> ldns
*)
(*
equal_hps: are preds that are going to be generalized. DO NOT subst them
*)

let rec find_imply_subst_x prog sel_hps unk_hps link_hps frozen_hps frozen_constrs complex_hps constrs=
  let rec check_constr_duplicate (lhs,rhs) constrs=
    match constrs with
    | [] -> false
    | cs::ss -> if Sautil.checkeq_pair_formula (lhs,rhs)
        (cs.Cformula.hprel_lhs,cs.Cformula.hprel_rhs) then
        true
      else check_constr_duplicate (lhs,rhs) ss
  in
  let find_imply_one cs1 cs2=
    let () = Debug.ninfo_zprint (lazy (("    rhs: " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
    (*if this assumption is going to be equal generalized. do not subst*)
    let lhps = Cformula.get_hp_rel_name_formula cs2.Cformula.hprel_lhs in
    if List.length lhps<2 && CP.diff_svl lhps frozen_hps = [] then ([],[]) else
      let qvars1, f1 = Cformula.split_quantifiers cs1.Cformula.hprel_lhs in
      let qvars2, f2 = Cformula.split_quantifiers cs2.Cformula.hprel_rhs in
      match f1,f2 with
      | Cformula.Base lhs1, Cformula.Base rhs2 ->
        let r = Sautil.find_imply prog (List.map fst cs1.CF.unk_hps) (List.map fst cs2.CF.unk_hps)
            lhs1 cs1.Cformula.hprel_rhs cs2.Cformula.hprel_lhs rhs2 cs1.Cformula.hprel_guard frozen_hps complex_hps in
        begin
          match r with
          | Some (l,r,lhs_ss, rhs_ss, n_cs1_guard) ->
            (*check duplicate*)
            if check_constr_duplicate (l,r) (constrs) then ([],[])
            else
              begin
                let n_cs_hprel_guard0 =
                  match cs2.Cformula.hprel_guard with
                  | None -> begin
                      match n_cs1_guard with
                      | Some f -> (Some (x_add Cformula.subst rhs_ss  f))
                      | None -> None
                    end
                  | Some f2 -> begin
                      let nf2 = (x_add Cformula.subst rhs_ss f2) in
                      match n_cs1_guard with
                      | Some f1 ->
                        let nf1= (x_add Cformula.subst rhs_ss f1) in
                        Some (Cformula.mkConj_combine nf2 nf1 Cformula.Flow_combine no_pos)
                      | None -> Some nf2
                    end
                in
                (*to drop the matching guard*)
                let n_cs_hprel_guard= Sautil.drop_dups_guard l r n_cs_hprel_guard0 in
                let new_cs = {cs2 with
                              Cformula.predef_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.Cformula.predef_svl)@
                                   (CP.subst_var_list rhs_ss cs2.Cformula.predef_svl));
                              Cformula.unk_svl = CP.remove_dups_svl
                                  ((CP.subst_var_list lhs_ss cs1.Cformula.unk_svl)@
                                   (CP.subst_var_list rhs_ss cs2.Cformula.unk_svl));
                              CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq
                                  ((List.map (fun (hp,args) -> (hp,CP.subst_var_list lhs_ss args)) cs1.Cformula.unk_hps)@
                                   (List.map (fun (hp,args) -> (hp,CP.subst_var_list rhs_ss args)) cs2.Cformula.unk_hps));
                              Cformula.hprel_lhs = l;
                              Cformula.hprel_guard = n_cs_hprel_guard;
                              Cformula.hprel_rhs = r;
                             }
                in
                let () = Debug.ninfo_zprint (lazy (("    new rhs: " ^ (Cprinter.string_of_hprel_short new_cs)))) no_pos in
                let new_cs1 = Sautil.simp_match_hp_w_unknown prog unk_hps link_hps new_cs in
                let nlhs,nrhs = Sautil.do_simpl_nodes_match new_cs1.CF.hprel_lhs new_cs1.CF.hprel_rhs in
                let new_cs2 = {new_cs1 with Cformula.hprel_lhs = nlhs;
                                            Cformula.hprel_rhs = nrhs } in
                ([new_cs2],[])
              end
          | None -> ([],[])
        end
      | _ -> report_error no_pos "sa2.find_imply_one"
  in
  (*we should subst nonfrozen constrs for sel_hps.
    it may longer in conv, it presever the ordering*)
  let rec helper_new_only don rest is_changed unfrozen_hps=
    match rest with
    | [] -> is_changed,don,unfrozen_hps
    | cs1::rest ->
      let () = Debug.ninfo_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in
      (* let b2 = let hp_opt = Cformula.extract_hrel_head cs1.Cformula.hprel_lhs in *)
      (*   match hp_opt with *)
      (*     | None -> false *)
      (*     | Some hp -> CP.mem_svl hp sel_hps *)
      (* in *)
      if Sacore.cs_rhs_is_only_neqNull cs1 (* || b2 *) then
        (helper_new_only (don@[cs1]) rest is_changed unfrozen_hps)
      else
        let is_changed1, new_rest, n_unfrozen_hps1 = List.fold_left ( fun (b,res, r_unfroz_hps) cs2->
            let is_sel_tupled =
              let hp_opt = Cformula.extract_hrel_head cs2.Cformula.hprel_rhs in
              match hp_opt with
              | None -> false
              | Some (hp) -> if (CP.mem_svl hp sel_hps) then
                  let lhps = Cformula.get_hp_rel_name_formula cs2.Cformula.hprel_lhs in
                  List.length lhps > 1
                else false
            in
            if not is_sel_tupled then (b,res@[cs2], r_unfroz_hps)
            else
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
  (* let rec subst_w_frozen_old frozen_constrs non_frozen is_changed unfrozen_hps= *)
  (*   match frozen_constrs with *)
  (*     | [] -> is_changed,non_frozen,unfrozen_hps *)
  (*     | cs1::rest -> *)
  (*           let () = Debug.info_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in *)
  (*           if Sacore.cs_rhs_is_only_neqNull cs1 then *)
  (*             (subst_w_frozen_old rest non_frozen is_changed unfrozen_hps) *)
  (*           else *)
  (*             let is_changed1, n_non_frozen, n_unfrozen_hps1 = *)
  (*               List.fold_left ( fun (b,res, r_unfroz_hps) cs2-> *)
  (*                   let new_constrs, unfroz_hps = find_imply_one cs1 cs2 in *)
  (*                   if List.length new_constrs > 0 then *)
  (*                     (true,res@new_constrs, r_unfroz_hps@unfroz_hps) *)
  (*                   else (b,res@[cs2], r_unfroz_hps) *)
  (*               ) (is_changed, [], []) non_frozen *)
  (*             in *)
  (*             subst_w_frozen_old rest n_non_frozen is_changed1 n_unfrozen_hps1 *)
  (* in *)
  let neg_pure f0=
    let rec helper f=
      match f with
      | Cformula.Base fb ->
        let np = MCP.mix_of_pure (CP.neg_eq_neq (MCP.pure_of_mix fb.Cformula.formula_base_pure)) in
        Cformula.Base {fb with Cformula.formula_base_pure = np}
      | Cformula.Exists _ -> let qvars, base_f = Cformula.split_quantifiers f in
        let n_base_f = helper base_f in
        Cformula.add_quantifiers qvars n_base_f
      | _ -> report_error no_pos "SA3.neg_pure"
    in
    helper f0
  in
  let add_path_sensitive_guard cs_poss_g cs2=
    begin
      match cs_poss_g.Cformula.hprel_guard with
      | None -> false,[]
      | Some n_gf -> begin
          match cs2.Cformula.hprel_guard with
          | None ->
            (*generate the remain: the simplest scenario*)
            let p = Cformula.get_pure n_gf in
            let () = Debug.ninfo_zprint (lazy (("    p: " ^ (!CP.print_formula p)))) no_pos in
            if CP.isConstTrue p then (false, []) else
              let neg_g = neg_pure n_gf in
              (*do simple normalize*)
              let n_neg_g =
                try
                  let hp0, args0 = Cformula.extract_HRel_f  cs_poss_g.Cformula.hprel_lhs in
                  let hp1, args1 = Cformula.extract_HRel_f  cs2.Cformula.hprel_lhs in
                  if CP.eq_spec_var hp0 hp1 then
                    let ss = List.combine args1 args0 in
                    let n_cs2_rhs = x_add Cformula.subst ss cs2.Cformula.hprel_rhs in
                    Sautil.norm_guard args0 n_cs2_rhs cs_poss_g.CF.hprel_rhs neg_g
                  else (neg_g)
                with _ ->  neg_g
              in
              (true, [{cs2 with Cformula.hprel_guard = Some n_neg_g;
                      }])
          | Some _ -> (*to find the remain*) (false, [])
        end
    end
  in
  (*if cs is full paths and new_constrs is not, generate the missing*)
  let check_full_path_sensitive_x cs new_constrs=
    match new_constrs with
    | [] -> (false,new_constrs)
    | [n_cs] -> let b, ncs = add_path_sensitive_guard n_cs cs in
      if b then (b, new_constrs@ncs)
      else (b, new_constrs)
    | [n_cs1;n_cs2] -> if n_cs1.Cformula.hprel_guard != None then
        let b1, cs22 = add_path_sensitive_guard n_cs1 n_cs2 in
        if b1 then
          true,[n_cs1]@cs22
        else (false,  new_constrs)
      else
        let b2,cs12 = add_path_sensitive_guard n_cs2 n_cs1 in
        if b2 then (true, cs12@[n_cs2]) else (false,  new_constrs)
    | _ -> (*to implement*) (false,new_constrs)
  in
  let check_full_path_sensitive cs new_constrs=
    let pr1 = Cprinter.string_of_hprel_short in
    Debug.no_2 "check_full_path_sensitive" pr1 (pr_list_ln pr1) (pr_pair string_of_bool (pr_list_ln pr1))
      (fun _ _ -> check_full_path_sensitive_x cs new_constrs)
      cs new_constrs
  in

  let rec subst_w_frozen frozen_constrs non_frozen is_changed unfrozen_hps=
    let frozen_constrs0 = List.filter (fun cs -> not (Sacore.cs_rhs_is_only_neqNull cs)) frozen_constrs in
    if frozen_constrs = [] then is_changed,non_frozen,unfrozen_hps else
      let is_changed1, n_non_frozen1, n_unfrozen_hps1 =
        List.fold_left ( fun (b2,res2, r_unfroz_hps2) cs2->
            let b, res_constrs, unfroz_hps=    List.fold_left ( fun (b1,res1, r_unfroz_hps1) cs1 ->
                let () = Debug.ninfo_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in
                let new_constrs, unfroz_hps = find_imply_one cs1 cs2 in
                if List.length new_constrs > 0 then
                  (true, res1@new_constrs, r_unfroz_hps1@ unfroz_hps)
                else (b1, res1, r_unfroz_hps1)
              ) (false,[],[]) frozen_constrs0
            in
            if b then
              let rem_path_constrs=
                let b1, rem_path_constrs = check_full_path_sensitive cs2 res_constrs in
                if b1 then rem_path_constrs else res_constrs
              in
              (true,res2@rem_path_constrs, r_unfroz_hps2@unfroz_hps)
            else (b2,res2@[cs2], r_unfroz_hps2)
          ) (is_changed, [], []) non_frozen
      in
      (is_changed1, n_non_frozen1, n_unfrozen_hps1)
  in
  (*we should subst nonfrozen constrs for sel_hps.
    it may longer in conv, it presever the ordering*)
  let is_changed0,constrs0,unfrozen_hps0 =
    if List.length constrs < 2 then (false, constrs, []) else
      helper_new_only [] constrs false []
  in
  let is_changed1,constrs1,unfrozen_hps1 = subst_w_frozen frozen_constrs constrs0 is_changed0 unfrozen_hps0 in
  (is_changed1,constrs1,unfrozen_hps1)

and find_imply_subst prog sel_hps unk_hps link_hps frozen_hps frozen_constrs complex_hps constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_2 "find_imply_subst" pr1 pr1 (pr_triple string_of_bool pr1 !CP.print_svl)
    (fun _ _ -> find_imply_subst_x prog sel_hps unk_hps link_hps frozen_hps frozen_constrs complex_hps constrs) frozen_constrs constrs

and is_trivial cs= (Sautil.is_empty_f cs.CF.hprel_rhs) ||
                   (Sautil.is_empty_f cs.CF.hprel_lhs || Sautil.is_empty_f cs.CF.hprel_rhs)

(* and get_top_guard link_hps cs = *)
(*   if *)
(*     Cformula.is_top_guard cs.Cformula.hprel_rhs link_hps cs.Cformula.hprel_guard *)
(*     (\* Cformula.isStrictConstHTrue cs.Cformula.hprel_rhs && (match cs.Cformula.hprel_guard with | None -> false | Some _ -> true) *\) *)
(*   then *)
(*     match Cformula.extract_hrel_head cs.Cformula.hprel_lhs with *)
(*       | Some hp -> [hp] *)
(*       | None -> report_error no_pos "SA3.get_top_guard" *)
(*   else [] *)

(* and is_top_guard top_guard_hps cs= *)
(*   match Cformula.extract_hrel_head cs.Cformula.hprel_lhs with *)
(*       | Some hp -> CP.mem_svl hp top_guard_hps *)
(*       | None -> false *)

and is_non_recursive_non_post_cs post_hps dang_hps constr=
  let lhrel_svl = Cformula.get_hp_rel_name_formula constr.Cformula.hprel_lhs in
  let rhrel_svl = Cformula.get_hp_rel_name_formula constr.Cformula.hprel_rhs in
  (CP.intersect_svl rhrel_svl post_hps = []) && ((CP.intersect lhrel_svl rhrel_svl) = [])

and subst_cs_w_other_cs_x prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs0 complex_hps constrs=
  (*remove recursive cs and post-preds based to preserve soundness*)
  (* let constrs1 = List.filter (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)) constrs in *)
  (* let ignore_hps = dang_hps@link_hps in *)
  let constrs1,rem = List.partition (fun cs -> (is_non_recursive_non_post_cs post_hps dang_hps cs) && not (is_trivial cs)
                                    ) constrs in
  (* let top_guard_hps = List.fold_left (fun r cs -> r@(get_top_guard ignore_hps cs)) [] frozen_constrs0 in *)
  let frozen_constrs1 = (* List.filter (fun cs -> not (is_top_guard top_guard_hps cs) ) *) frozen_constrs0 in
  let b,new_cs2, unfrozen_hps=
    find_imply_subst prog sel_hps dang_hps link_hps frozen_hps (* (CP.diff_svl frozen_hps top_guard_hps) *) frozen_constrs1 complex_hps constrs1 in
  (b, new_cs2@rem,unfrozen_hps)
(*=========END============*)

let rec subst_cs_w_other_cs prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_2 "subst_cs_w_other_cs" pr1 pr1 (pr_triple string_of_bool pr1 !CP.print_svl)
    (fun _ _ -> subst_cs_w_other_cs_x prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs) frozen_constrs constrs

let subst_cs_x prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs =
  (*subst by constrs*)
  (* DD.ninfo_pprint "\n subst with other assumptions" no_pos; *)
  let is_changed, new_cs1,unfrozen_hps = subst_cs_w_other_cs prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs
      complex_hps constrs in
  (is_changed, new_cs1, unfrozen_hps)

let subst_cs prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs =
  let (is_changed, new_cs1, unfrozen_hps) as res = subst_cs_x prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs in
  if !VarGen.sap then
    if not is_changed then x_binfo_pp "*** NO NORM-CONSEQ DONE ***" no_pos
    else
      begin
        let pr1 = pr_list_num Cprinter.string_of_hprel_short in
        let s1 = pr1 constrs in
        let s2 = pr1 new_cs1 in
        let () = x_binfo_hp (add_str "BEFORE" pr_id) s1 no_pos in
        let () = x_binfo_pp "=============>>>>" no_pos in
        let () = x_binfo_hp (add_str "AFTER" pr_id) s2 no_pos in
        let () = DD.binfo_end "Syn-Norm-Conseq" in
        ()
      end;
  res
let subst_cs prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs =
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_4 "subst_cs" pr1 !CP.print_svl pr1 !CP.print_svl (pr_triple string_of_bool  pr1 !CP.print_svl)
    (fun _ _ _ _ -> subst_cs prog sel_hps post_hps dang_hps link_hps frozen_hps frozen_constrs complex_hps constrs)
    constrs  frozen_hps frozen_constrs complex_hps

let unfold_def_LHS_x prog link_hps constrs to_unfold_hps hp_defs=
  let () = if !VarGen.sap then DD.info_ihprint (add_str ">>>>>> Syn-Norm-Ante (UNFOLD IN LHS)<<<<<<" pr_id) "" no_pos else () in
  (* let pr_hp_defs = List.fold_left (fun r def -> match def.CF.def_cat with *)
  (*   | CP.HPRelDefn (hp, root, args) -> r@[(hp, def, root::args, Sautil.is_top_guard_hp_def link_hps def)] *)
  (*   | _ -> r *)
  (* ) [] hp_defs in *)
  let unfold_lhs_one (b, r) cs=
    let lhps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
    let rhps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_rhs in
    let l_inter = CP.intersect_svl lhps to_unfold_hps in
    let r_inter = CP.intersect_svl rhps to_unfold_hps in
    if l_inter == [] && r_inter == [] then (b, r@[cs]) else
      (* let pr_hp_defs0, rhs_pr_hp_defs0 = List.fold_left (fun (r1,r2) (hp,def,args,is_top) -> *)
      (*     let nr1 = if CP.mem_svl hp l_inter then (r1@[(hp,def,args)]) else r1 in *)
      (*     let nr2 = if CP.mem_svl hp r_inter && not is_top then r2@[(hp,def,args)] else r2 in *)
      (*     (nr1,nr2) *)
      (* ) ([],[]) pr_hp_defs in *)
      (*tll does not allow do unfold*)
      let nlhs = (* Cformula.do_unfold_hp_def prog pr_hp_defs0 *) cs.Cformula.hprel_lhs in
      let nrhs = (* Cformula.do_unfold_hp_def prog rhs_pr_hp_defs0 *) cs.Cformula.hprel_rhs in
      (true, r@[{cs with Cformula.hprel_lhs = nlhs; Cformula.hprel_rhs = nrhs;
                }])
  in
  (*****temporal remove it*****)
  (* let b,n_constrs = List.fold_left unfold_lhs_one (false,[]) constrs in *)
  (* b,n_constrs *)
  (false, constrs)

let unfold_def_LHS prog link_hps constrs to_unfold_hps hp_defs=
  let (is_changed, new_cs1) as res = unfold_def_LHS_x prog link_hps constrs to_unfold_hps hp_defs in
  if !VarGen.sap then
    if not is_changed then x_binfo_pp "*** NO NORM-ANTE DONE ***" no_pos
    else
      begin
        let pr1 = pr_list_num Cprinter.string_of_hprel_short in
        let s1 = pr1 constrs in
        let s2 = pr1 new_cs1 in
        let () = x_binfo_hp (add_str "BEFORE" pr_id) s1 no_pos in
        let () = x_binfo_pp "=============>>>>" no_pos in
        let () = x_binfo_hp (add_str "AFTER" pr_id) s2 no_pos in
        let () = DD.binfo_end "Syn-Norm-Ante" in
        ()
      end;
  res

let unfold_def_LHS prog link_hps constrs hps hp_defs=
  let pr1 = pr_list_num Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  Debug.no_2 "unfold_def_LHS" pr1 pr2 (pr_pair string_of_bool pr1)
    (fun _ _ -> unfold_def_LHS prog link_hps constrs hps hp_defs)
    constrs hps

(*split constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
let split_base_constr prog cond_path constrs post_hps sel_hps prog_vars unk_map unk_hps link_hps=
  (*internal method*)
  let split_one cs total_unk_map=
    let () = Debug.ninfo_zprint (lazy (("  cs: " ^ (Cprinter.string_of_hprel_short cs)))) no_pos in
    let (_ ,mix_lf,_,_,_,_) = Cformula.split_components cs.Cformula.hprel_lhs in
    let l_qvars, lhs = Cformula.split_quantifiers cs.Cformula.hprel_lhs in
    let r_qvars, rhs = Cformula.split_quantifiers cs.Cformula.hprel_rhs in
    let l_hpargs = Cformula.get_HRels_f lhs in
    let r_hpargs = Cformula.get_HRels_f rhs in
    if (* (List.exists (fun (hp,_) -> CP.mem_svl hp post_hps) r_hpargs) && *)
      (List.length l_hpargs > 0 && r_hpargs != []) then
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let lhs_b = match lhs with
        | Cformula.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      let rhs_b = match rhs with
        | Cformula.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      (**smart subst**)
      let lhs_b1, rhs_b1, subst_prog_vars = Sautil.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs)
          leqs [] [] prog_vars
      in
      (* let lfb = match lhs_b1 with *)
      (*   | Cformula.Base fb -> fb *)
      (*   | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula" *)
      (* in *)
      let lfb = lhs_b1 in
      let lhds, lhvs, lhrs = Cformula.get_hp_rel_bformula lfb in
      let (_ ,mix_lf,_,_,_,_) = Cformula.split_components (Cformula.Base lfb) in
      let leqNulls = MCP.get_null_ptrs mix_lf in
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let ls_rhp_args = Cformula.get_HRels_f (Cformula.Base rhs_b1) in
      let r_hps = List.map fst ls_rhp_args in
      let l_def_vs = leqNulls @ (List.map (fun hd -> hd.Cformula.h_formula_data_node) lhds)
                     @ (List.map (fun hv -> hv.Cformula.h_formula_view_node) lhvs) in
      let l_def_vs = CP.remove_dups_svl (Cformula.find_close l_def_vs (leqs)) in
      let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
      let ls_lhp_args = (List.map helper lhrs) in
      (*generate linking*)
      let unk_svl, lfb1, unk_map1 = ([], lfb, total_unk_map)
      (* let unk_svl, unk_xpure, unk_map1 = Sacore.generate_map ls_lhp_args ls_rhp_args total_unk_map no_pos in *)
      (* let lfb1 = Cformula.mkAnd_base_pure lfb (MCP.mix_of_pure unk_xpure) no_pos in *)
      (* ([], lfb1, unk_map1) *)
      in
      let unk_svl1 = CP.remove_dups_svl (cs.Cformula.unk_svl@unk_svl) in
      (*do not split unk_hps and link_hps, all non-ptrs args*)
      let non_split_hps = unk_hps @ link_hps in
      let ls_lhp_args1, ls_lhs_non_node_hpargs = List.fold_left (fun (r1,r2) (hp,args) ->
          let arg_i,_ = x_add Sautil.partition_hp_args prog hp args in
          if ((List.filter (fun (sv,_) -> CP.is_node_typ sv) arg_i) = []) then
            (r1, r2@[(hp,args)])
          else if not (CP.mem_svl hp non_split_hps) then
            (r1@[(hp,args)],r2)
          else (r1,r2)
        ) ([],[]) ls_lhp_args in
      (* let () = Debug.info_zprint (lazy (("   non_split_hps: " ^ (!CP.print_svl  non_split_hps)))) no_pos in *)
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
      let rf = Cformula.mkTrue (Cformula.mkTrueFlow()) no_pos in
      let defined_preds0, rem_hpargs1 = List.fold_left (fun (defined_preds, r) hpargs ->
          let def_hps, rem = (Sautil.find_well_eq_defined_hp prog lhds lhvs lfb2 leqs hpargs) in
          (defined_preds@(List.map (fun (a,b,c) -> (a,b,c,rf)) def_hps), r@rem)
        ) (defined_preds,[]) (rems_hpargs@ls_lhs_non_node_hpargs) in
      let () = Debug.ninfo_zprint (lazy (("   rem_hpargs1: " ^ ((pr_list (pr_pair !CP.print_sv !CP.print_svl))  rem_hpargs1)))) no_pos in
      let lfb2, guarded_preds0, link_hps2 = List.fold_left (fun (lfb, r1,r2) (hp,args) ->
          if CP.mem_svl hp r_hps || CP.mem_svl hp post_hps then (lfb, r1,r2) else
            let pr_lhs_g = Sautil.split_guard_constrs prog (cs.CF.hprel_guard!=None) lhds lhvs post_hps ls_rhp_args (hp,args) lfb no_pos in
            match pr_lhs_g with
            | None -> (lfb, r1, r2)
            | Some (lfb1, g_cs,link_hp) -> (lfb1, r1@[g_cs],r2@[(link_hp, args)])
        ) (lfb2, [],[]) rem_hpargs1 in
      (* let rhs_h = Cformula.mkHTrue_nf no_pos in *)
      let new_g_constrs = List.map (fun (hp, lhs, rhs, og) ->
          let knd = CP.RelAssume [hp] in
          let new_cs =  Cformula.mkHprel knd unk_svl1 [] [] lhs (og) rhs cs.Cformula.hprel_path in
          new_cs
        ) guarded_preds0 in
      let new_cs = {cs with Cformula.hprel_lhs = Cformula.add_quantifiers l_qvars (Cformula.Base lfb2);
                            Cformula.unk_svl = unk_svl1;
                            Cformula.hprel_rhs = (Cformula.add_quantifiers r_qvars (Cformula.Base rhs_b1));
                   } in
      let new_constrs = match defined_preds0 with
        | [] -> [new_cs]
        | _ ->
          let () = Debug.ninfo_zprint (lazy ((Cprinter.string_of_hprel_short cs))) no_pos in
          let () = Debug.ninfo_zprint (lazy (("  unused ptrs: " ^ (!CP.print_svl unk_svl)))) no_pos in
          (*prune defined hps in lhs*)
          let new_lhs, _ = Cformula.drop_hrel_f new_cs.Cformula.hprel_lhs (List.map (fun (a, _, _,_) -> a) defined_preds0) in
          let new_lhs1 = Cformula.add_quantifiers l_qvars new_lhs in
          let new_lhs2 = Cformula.elim_unused_pure new_lhs1 new_cs.Cformula.hprel_rhs in
          let new_cs = {new_cs with Cformula.hprel_lhs = new_lhs2;} in
          let () = Debug.ninfo_zprint (lazy (("  refined cs: " ^ (Cprinter.string_of_hprel_short new_cs)))) no_pos in
          (* let rf = Cformula.mkTrue (Cformula.mkTrueFlow()) no_pos in *)
          let () = Debug.ninfo_pprint ("  generate pre-preds-based constraints: " ) no_pos in
          let defined_hprels = List.map (x_add Sautil.generate_hp_ass 2 unk_svl1 new_cs.CF.hprel_path) defined_preds0 in
          if Sautil.is_empty_f new_cs.CF.hprel_lhs && Sautil.is_empty_f new_cs.CF.hprel_rhs then
            defined_hprels
          else
            new_cs::defined_hprels
      in
      (new_constrs@new_g_constrs, unk_map1, link_hps@link_hps2)
    else
      (*do subst: sa/demo/mcf-3a1.slk*)
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let lhs_b = match lhs with
        | Cformula.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      let rhs_b = match rhs with
        | Cformula.Base fb -> fb
        | _ -> report_error no_pos "sa2.split_constr: lhs should be a Base Formula"
      in
      (*smart subst*)
      let lhs_b1, rhs_b1, _ = Sautil.smart_subst lhs_b rhs_b (l_hpargs@r_hpargs)
          leqs [] [] prog_vars
      in
      let n_cs = {cs with Cformula.hprel_lhs = (Cformula.Base lhs_b1);
                          Cformula.hprel_rhs = (Cformula.Base rhs_b1);
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
        (* Debug.ninfo_start "split_base"; *)
        (* Debug.ninfo_hprint (add_str "BEFORE" pr1) cs no_pos; *)
        (* Debug.ninfo_pprint "=============>>>>" no_pos; *)
        (* Debug.ninfo_hprint (add_str "AFTER" (pr_list_ln pr1)) new_cs no_pos; *)
        (* Debug.ninfo_end "split_base"; *)
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

let split_base_constr_a prog cond_path constrs post_hps sel_hps prog_vars unk_map unk_hps link_hps=
  let () = if !Globals.sa_gen_slk then
      try
        Sautil.gen_slk_file false prog (List.hd !Globals.source_files)
          (CP.diff_svl sel_hps post_hps) post_hps constrs link_hps
      with _ -> ()
    else ()
  in
  let () = step_change # reset in
  let s1 = (pr_list_num Cprinter.string_of_hprel_short) constrs in
  let (constrs2, unk_map2, link_hpargs2) as res = split_base_constr prog cond_path constrs post_hps sel_hps  prog_vars unk_map unk_hps link_hps in
  let s2 = (pr_list_num Cprinter.string_of_hprel_short) constrs2 in
  if !VarGen.sap then
    if step_change # no_change then 
      x_binfo_pp "*** NO SPLITTING DONE ***" no_pos
    else 
      begin
        (* let () = DD.binfo_start "split_base" in *)
        let () = DD.ninfo_hprint (add_str "post_hps" Cprinter.string_of_spec_var_list) post_hps no_pos in
        let () = DD.ninfo_hprint (add_str "prog_vars" Cprinter.string_of_spec_var_list) prog_vars no_pos in
        let () = x_binfo_hp (add_str "BEFORE" pr_id) s1 no_pos in
        let () = x_binfo_pp "=============>>>>" no_pos in
        let () = x_binfo_hp (add_str "AFTER" pr_id) s2 no_pos in
        let () = x_binfo_hp (add_str "UNKNOWN added" (pr_list (fun (x,_) -> Cprinter.string_of_spec_var x)))  link_hpargs2 no_pos in
        let () = DD.binfo_end "split_base" in
        ()
      end;
  (* let () = if !Globals.sa_gen_slk then *)
  (*   try *)
  (*     Sautil.gen_slk_file true prog (List.hd !Globals.source_files) *)
  (*         (CP.diff_svl sel_hps post_hps) post_hps constrs2 (List.map fst link_hpargs2) *)
  (*   with _ -> () *)
  (* else () *)
  (* in *)
  res


let split_base_constr prog cond_path constrs post_hps sel_hps prog_vars unk_map unk_hps link_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  (* let pr2 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_4 "split_base_constr" pr1 pr2 !CP.print_svl !CP.print_svl (pr_triple pr1 pr2 pr3)
    (fun _ _ _ _ -> split_base_constr_a prog cond_path constrs post_hps sel_hps prog_vars unk_map
        unk_hps link_hps) constrs unk_map unk_hps post_hps

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
  (CP.equalFormula cond1 cond2) && (cmp_formula_opt args1 orhs1 orhs2) (* && (cmp_formula_opt args1 og1 og2) *)

let get_par_defs_pre_fix_x pre_fix_hps post_hps constrs0 =
  let mk_par_def (r1,r2) cs=
    try
      let hp, args= Cformula.extract_HRel_f cs.Cformula.hprel_rhs in
      let pre_pos_fix_hps = post_hps@pre_fix_hps in
      if CP.mem_svl hp pre_pos_fix_hps then
        (r1@[(hp, args, cs.CF.hprel_lhs)],r2)
      else
        let hpargs = CF.get_HRels_f cs.CF.hprel_lhs in
        match hpargs with
        | [hp,args] -> if CP.mem_svl hp pre_fix_hps then
            (r1,r2@[(hp, args, cs.CF.hprel_rhs)])
          else (r1@[(hp, args, cs.CF.hprel_rhs)],r2)
        | _ -> (r1,r2)
    with _ ->
      let hp, args=CF.extract_HRel_f cs.CF.hprel_lhs in
      (r1@[(hp, args, cs.CF.hprel_rhs)],r2)
  in
  List.fold_left mk_par_def ([],[]) constrs0

let get_par_defs_pre_fix pre_fix_hps post_hps constrs0 =
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln (pr_triple !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula) in
  Debug.no_1 "get_par_defs_pre_fix" pr1 (pr_pair pr2 pr2)
    (fun _ -> get_par_defs_pre_fix_x pre_fix_hps post_hps constrs0) constrs0

let get_par_defs_post_x constrs0 =
  let mk_par_def cs=
    let hp, args = Cformula.extract_HRel_f cs.Cformula.hprel_rhs in
    mk_pdef hp args cs.Cformula.unk_svl (CP.mkTrue no_pos) (Some cs.Cformula.hprel_lhs) None None
  in
  List.map mk_par_def constrs0

let get_par_defs_post constrs0 =
  let pr0 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr1 = !CP.print_svl in
  let pr2 = !CP.print_formula in
  let pr3 oform= match oform with
    | None -> "None"
    | Some f -> Cprinter.prtt_string_of_formula f
  in
  let pr4 = pr_hepta !CP.print_sv pr1 pr1 pr2 pr3 pr3 pr3 in
  Debug.no_1 "get_par_defs_post" pr0 (pr_list_ln pr4)
      (fun _ -> get_par_defs_post_x constrs0) constrs0

let get_par_defs_pre constrs0 =
  let mk_par_def cs=
    (* let () = print_endline ("cs.Cformula.hprel_lhs: " ^ ( !Cformula.print_formula cs.Cformula.hprel_lhs)) in *)
    let op_res = Cformula.extract_hprel_pure cs.Cformula.hprel_lhs in
    match op_res with
    | Some (hp, args,p) ->
      (* let () = print_endline ("p: " ^ ( !CP.print_formula p)) in *)
      let p1 = (CP.remove_redundant p) in
      let ps1, ps2 = List.partition (fun p -> CP.intersect_svl (CP.fv p) args != []) (CP.split_conjunctions p1) in
      let n_rhs = if ps1 = [] then cs.Cformula.hprel_rhs else
          Cformula.mkAnd_pure cs.Cformula.hprel_rhs (MCP.mix_of_pure (CP.join_conjunctions ps2)) no_pos
      in
      ([(mk_pdef hp args cs.Cformula.unk_svl (CP.join_conjunctions ps1)
           None cs.Cformula.hprel_guard (Some n_rhs), cs)], [])
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
  let do_combine b_acc_unsat (hp,args,unk_svl, cond, lhs,og, orhs)=
    match orhs with
    | Some rhs ->
      let n_cond = CP.remove_redundant cond in
      let nf = (Cformula.mkAnd_pure rhs (MCP.mix_of_pure n_cond) (Cformula.pos_of_formula rhs)) in
      if not b_acc_unsat && Sautil.is_unsat nf then [] else
        [(hp,args,unk_svl, n_cond, lhs, og, Some (x_add_1 Cformula.simplify_pure_f_old nf))]
    | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None 1"
  in
  let mkAnd_w_opt hp args (* ss *) of1 of2=
    match of1,of2 with
    | Some f1, Some f2 ->
      let pos = Cformula.pos_of_formula f1 in
      let new_f2 = (*x_add Cformula.subst ss*) f2 in
      let f = Sautil.mkConjH_and_norm prog hp args (unk_hps@link_hps) [] f1 new_f2 pos in
      (* let f = (Cformula.mkConj_combine f1 new_f2 Cformula.Flow_combine no_pos) in *)
      if CF.isAnyConstFalse f || Sautil.is_unsat f then
        false, Some f
      else true, Some f
    | None, None -> true, None
    | None, Some f2 -> true, (Some ( (*x_add Cformula.subst ss*) f2))
    | Some f1, None -> true, of1
  in
  (*nav code. to improve*)
  let combine_helper2_x (hp1,args1,unk_svl1, cond1, olhs1,og1, orhs1) (hp2,args2,unk_svl2, cond2, olhs2,og2, orhs2)=
    if og1 <> None && og2 <> None then
      (*to improve: check pure (conditional stmt)*)
      [(hp1,args1,unk_svl1, cond1, olhs1,og1, orhs1);(hp2,args2,unk_svl2, cond2, olhs2,og2, orhs2)]
    else
      let cond_disj1 = CP.mkAnd cond1 (CP.mkNot (CP.remove_redundant cond2) None no_pos) no_pos in
      let pdef1 = if (Tpdispatcher.is_sat_raw (MCP.mix_of_pure cond_disj1)) then
          (* let () = DD.info_zprint (lazy (("      cond_disj1: " ^ (!CP.print_formula  cond_disj1) ))) no_pos in *)
          let cond21 = Cformula.remove_neqNull_redundant_andNOT_opt orhs1 cond2 in
          let n_cond = CP.mkAnd cond1 (CP.mkNot cond21 None no_pos) no_pos in
          let npdef1 = do_combine false (hp1,args1,unk_svl1, CP.remove_redundant n_cond , olhs1,og1, orhs1) in
          npdef1
        else []
      in
      let cond_disj2 = CP.mkAnd cond2 (CP.mkNot cond1 None no_pos) no_pos in
      let pdef2 = if (Tpdispatcher.is_sat_raw (MCP.mix_of_pure cond_disj2)) then
          (* let () = DD.info_zprint (lazy (("      cond_disj2: " ^ (!CP.print_formula  cond_disj2) ))) no_pos in *)
          let cond11 = Cformula.remove_neqNull_redundant_andNOT_opt orhs2 cond1 in
          let n_cond = (CP.mkAnd cond2 (CP.mkNot cond11 None no_pos) no_pos) in
          let npdef2 = do_combine false (hp2,args2,unk_svl2, CP.remove_redundant n_cond, olhs2,og2, orhs2) in
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
              do_combine false (hp1,args1,unk_svl1, n_cond, n_olhs,og1, n_orhs)
            else [(hp1,args1,unk_svl1,  n_cond, olhs1, og1, Some (Cformula.mkFalse_nf no_pos))]
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
    Debug.no_2 "combine_helper2" pr4 pr4 (pr_list_ln pr4)
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
    | None -> report_error no_pos "sa3.combine_pdefs_pre: should not None 2"
  in
  let obtain_and_norm_def_x args0 ((hp,args,unk_svl, cond, olhs, og, orhs), cs)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let cond1 = (CP.subst subst cond) in
    let norhs, cond1 = match orhs with
      | Some f -> let nf = (x_add Cformula.subst subst f) in
        let cond2 =
          (* if Sautil.is_empty_heap_f nf then *)
          (*   CP.mkAnd cond1 (Cformula.get_pure nf) (CP.pos_of_formula cond1) *)
          (* else cond1 *)
          cond1
        in
        (Some (Cformula.mkAnd_pure nf (MCP.mix_of_pure cond2) (Cformula.pos_of_formula nf)), cond2)
      | None -> None, cond1
    in
    let nolhs = match olhs with
      | None -> None
      | Some f -> Some (x_add Cformula.subst subst f)
    in
    let nog = match og with
      | None -> None
      | Some f -> Some (x_add Cformula.subst subst f)
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
      let new_pdef = do_combine true (hp,args,unk_svl, cond, lhs,og, orhs) in
      (new_pdef,[], equivs)
    | _ -> begin
        (*each group, filter depended constraints*)
        let rem_pr_defs, depend_cs = List.fold_left filter_trivial_pardef ([],[]) pr_pdefs in
        let () = DD.ninfo_hprint (add_str "   depend_cs:" (pr_list_ln (Cprinter.string_of_hprel_short))) depend_cs no_pos in
        (* let rem_pr_defs = pr_pdefs in *)
        (* let depend_cs = [] in *)
        (*do norm args first, apply for cond only, other parts will be done later*)
        let cs,rem_pr_defs1 , n_equivs=
          match rem_pr_defs with
          | [] -> [],[],equivs
          | [x] -> [x],[],equivs
          | ((hp,args0,unk_svl0, cond0, olhs0, og0, orhs0),cs0)::rest ->
            (* let pr_pdef0 = obtain_and_norm_def args0 ((hp,args0,unk_svl0, cond0, olhs0, orhs0),cs0) in *)
            let pdefs0 = List.map (obtain_and_norm_def args0) rem_pr_defs in
            (* let pdefs = pr_pdef0::new_rest in *)
            let pdefs1 = Gen.BList.remove_dups_eq (fun (pdef1,_) (pdef2,_) -> cmp_pdef_grp pdef1 pdef2) pdefs0 in
            let () = DD.ninfo_hprint (add_str "   pdefs1:" (pr_list_ln (pr_pair pr_none Cprinter.string_of_hprel_short))) pdefs1 no_pos in
            let pdefs2,n_equivs = Sacore.unify_consj_pre prog unk_hps link_hps equivs pdefs1 in
            let () = DD.ninfo_hprint (add_str "   pdefs2:" (pr_list_ln (pr_pair pr_none Cprinter.string_of_hprel_short))) pdefs2 no_pos in
            ([], pdefs2,n_equivs)
        in
        let pdefs,rem_constrs0 = begin
          match cs,rem_pr_defs1 with
          | [],[] -> [],[]
          | [((hp,args,unk_svl, cond, lhs,og, orhs), _)],[] -> (do_combine true (hp, args, unk_svl, cond, lhs,og, orhs)),[]
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
      let nf = Cformula.subst_hprel f from_hps hp in
      (hp,args1,unk_svl1, cond1, olhs1,og1, Some nf)
  in
  (***********distinguish guarded top assumptions***********)
  let guarded_top_pdefs, pr_pdefs0 = List.partition ( fun (_,cs) ->
      let hp_opt = Cformula.extract_hrel_head cs.Cformula.hprel_rhs in
      match hp_opt with
      | None -> false
      | Some hp -> CP.mem_svl hp link_hps (* Cformula.isStrictConstHTrue cs.Cformula.hprel_rhs *)
                   && (cs.Cformula.hprel_guard != None)
    ) pr_pdefs in
  (*group*)
  let () = DD.ninfo_hprint (add_str "  guarded_top_pdefs:" (pr_list_ln (pr_pair pr_none Cprinter.string_of_hprel_short))) guarded_top_pdefs no_pos in
  let ls_pr_pdefs = partition_pdefs_by_hp_name pr_pdefs0 [] in
  (*combine rhs with condition for each group*)
  let pdefs, rem_constr,equivs = List.fold_left (fun (r_pdefs, r_constrs, equivs) grp ->
      let pdefs, cs, new_equivs = combine_grp grp equivs in
      (r_pdefs@pdefs, r_constrs@cs, new_equivs)
    ) ([],[],[]) ls_pr_pdefs
  in
  let pdefs1 = (* List.map (fun (a,b,c,d,e,f,g) -> (a,b,c,d,f,g)) *) pdefs in
  (*subst equivs*)
  let pdefs2 = List.map (subst_equiv equivs) pdefs1 in
  (pdefs2@(List.map fst guarded_top_pdefs),rem_constr,equivs)
(*retain depended constraints*)

let combine_pdefs_pre prog unk_hps link_hps pr_pdefs=
  let (pdefs2,rem_constr,equivs) as res = combine_pdefs_pre_x prog unk_hps link_hps pr_pdefs in
  if !VarGen.sap then
    begin
      let pr1 = pr_list_num (fun (pdef, _) -> Sautil.string_of_par_def_w_name pdef) in
      let s1 = pr1 pr_pdefs in
      let s2 = (pr_list_num Sautil.string_of_par_def_w_name) pdefs2 in
      let () = x_binfo_hp (add_str "BEFORE" pr_id) s1 no_pos in
      let () = x_binfo_pp "=============>>>>" no_pos in
      let () = x_binfo_hp (add_str "AFTER" pr_id) s2 no_pos in
      let () = DD.binfo_end "Syn-Case" in
      ()
    end;
  res

let combine_pdefs_pre prog unk_hps link_hps pr_pdefs=
  let pr1= pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = Sautil.string_of_par_def_w_name in
  let pr3 (pdef, _) = pr2 pdef in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "combine_pdefs_pre" (pr_list_ln pr3) !CP.print_svl !CP.print_svl
    (pr_triple (pr_list_ln pr2) pr1 pr4)
    (fun _ _ _ -> combine_pdefs_pre prog unk_hps link_hps pr_pdefs)
    pr_pdefs unk_hps link_hps
(***************************************************************
                      END PARTIAL DEFS
 ****************************************************************)

(***************************************************************
                      GENERALIZATION
 ****************************************************************)
(*remove neqNUll redundant*)
let remove_neqNull_helper (hp,args,f,unk_svl)=
  let f1 = Cformula.remove_neqNulls_f f in
  if Sautil.is_empty_f f1 then [] else [(hp,args,f1,unk_svl)]

let remove_neqNull_grp_helper grp=
  List.fold_left (fun r pdef-> let new_pdef = remove_neqNull_helper pdef in
                   r@new_pdef) [] grp

let get_null_quans f=
  let qvars, base_f = Cformula.split_quantifiers f in
  let (_ ,mix_lf,_,_,_,_) = Cformula.split_components base_f in
  let eqNulls = MCP.get_null_ptrs mix_lf in
  (CP.intersect_svl eqNulls qvars, base_f)

(*for par_defs*)
let generalize_one_hp_x prog is_pre (hpdefs: (CP.spec_var *Cformula.hp_rel_def) list) non_ptr_unk_hps unk_hps link_hps par_defs=
  let skip_hps = unk_hps@link_hps in
  (*collect definition for each partial definition*)
  let obtain_and_norm_def hp args0 quan_null_svl0 (a1,args,og,f,unk_args)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let f1 = (x_add Cformula.subst subst f) in
    (* let f2 = *)
    (*   if !Globals.sa_dangling then *)
    (*     Cformula.annotate_dl f1 (List.filter (fun hp1 -> not (CP.eq_spec_var hp hp1)) unk_hps) *)
    (*     (\* fst (Cformula.drop_hrel_f f1 unk_hps) *\) *)
    (*   else f1 *)
    (* in *)
    let f2 = (* Cformula.split_quantifiers *) f1 in
    let quan_null_svl, base_f2 = get_null_quans f2 in
    let f3=
      if List.length quan_null_svl = List.length quan_null_svl0 then
        let ss = List.combine quan_null_svl quan_null_svl0 in
        Cformula.add_quantifiers quan_null_svl0 (x_add Cformula.subst ss base_f2)
      else f2
    in
    (* fresh non-shape values *)
    let f4 = Cfutil.fresh_data_v_no_change f3 in
    let unk_args1 = List.map (CP.subs_one subst) unk_args in
    (* (\*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *\) *)
    (f4,Cformula.subst_opt subst og, unk_args1)
  in
  x_tinfo_pp ">>>>>> generalize_one_hp: <<<<<<" no_pos;
  if par_defs = [] then ([],[]) else
    begin
      let hp, args, _, f0,_ = (List.hd par_defs) in
      let () = if !VarGen.sap then Debug.info_zprint (lazy (("    synthesize: " ^ (!CP.print_sv hp) ))) no_pos
        else ()
      in
      let guarded_top_par_defs, par_defs = List.partition (fun (a1,args,og,f,unk_args) ->
          Cformula.is_top_guard f skip_hps og
          (* Cformula.isStrictConstHTrue f && og != None *)
        ) par_defs in
      let is_put_top_guarded, hpdefs,subst_useless=
        if CP.mem_svl hp skip_hps then
          let fs = List.map (fun (a1,args,og,f,unk_args) -> fst (Cformula.drop_hrel_f f [hp]) ) par_defs in
          let fs1 = Gen.BList.remove_dups_eq (fun f1 f2 -> Sautil.check_stricteq_formula args f1 f2) fs in
          (* let fs2 = try *)
          (*   let res_sv = List.find (fun sv -> String.compare res_name (CP.name_of_spec_var sv) =0) args in *)
          (*   let fr_res = CP.fresh_spec_var res_sv in *)
          (*   let ss = [(res_sv,fr_res)] in *)
          (*   List.map (fun f -> CF.subst ss f) fs1 *)
          (* with _ -> fs1 *)
          (* in *)
          (true, Sautil.mk_unk_hprel_def hp args fs1 no_pos,[])
        else
          (*find the root: ins2,ins3: root is the second, not the first*)
          let args0 = List.map (CP.fresh_spec_var) args in
          (* DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")") no_pos; *)
          let quan_null_svl,_ = get_null_quans f0 in
          let quan_null_svl0 = List.map (CP.fresh_spec_var) quan_null_svl in
          let defs0 (*not in used*),defs0_wg, ogs, unk_svl = List.fold_left (fun (r1,r2,r3,r4) pdef->
              let (f, og, unk_args) = obtain_and_norm_def hp args0 quan_null_svl0 pdef in
              (r1@[f], r2@[(f,og)],r3@[og],r4@unk_args)
            ) ([],[],[],[]) par_defs in
          let pr1 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula (pr_option Cprinter.prtt_string_of_formula)) in
          (* let defs = Gen.BList.remove_dups_eq (fun f1 f2 -> Sautil.check_relaxeq_formula args0 f1 f2) defs0 in *)
          let defs0a_wg = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) -> Sautil.check_stricteq_formula args0 f1 f2) defs0_wg in
          let defs_wg = if is_pre && List.length defs0a_wg > 1 then defs0a_wg else
              List.filter (fun (f,_) -> not (CF.isAnyConstFalse f)) defs0a_wg
          in
          let defs = List.map fst defs_wg in
          let () = DD.ninfo_hprint (add_str "defs0: " pr1) defs0_wg no_pos in
          let () = DD.ninfo_hprint (add_str "defs0a: " pr1) defs0a_wg no_pos in
          let () = DD.ninfo_hprint (add_str "defs: " pr1) defs_wg no_pos in
          let r,non_r_args = Sautil.find_root prog (hp::skip_hps) args0 defs in
          (*make explicit root*)
          (* (\*for temporal*\) *)
          (* let defs0 = List.map (Sautil.mk_expl_root r) defs in *)
          let defs0_wg = List.map (fun (f,og) -> (Sautil.mk_expl_root r f, og)) defs_wg in
          (* let unk_svl = CP.remove_dups_svl (List.concat (ls_unk_args)) in *)
          (*normalize linked ptrs*)
          let defs1_wg = Sautil.norm_hnodes_wg args0 defs0_wg in
          (* (\*for temporal*\) *)
          (* let defs1,_ = List.split defs1_wg in *)
          (*remove unkhp of non-node*)
          let defs2_wg = if is_pre then (* List.map remove_non_ptr_unk_hp *) defs1_wg
            else Sautil.elim_useless_rec_preds prog hp args0 defs1_wg
          in
          (*remove duplicate*)
          let defs3_wg = if is_pre then Sautil.equiv_unify_wg args0 defs2_wg else defs2_wg in
          let defs4a_wg = Sautil.remove_equiv_wo_unkhps_wg hp args0 skip_hps defs3_wg in
          let defs4_wg = Sautil.remove_pure_or_redundant_wg defs4a_wg in
          let defs5a_wg = Sautil.find_closure_eq_wg hp args0 defs4_wg in
          (*Perform Conjunctive Unification (without loss) for post-preds. pre-preds are performed separately*)
          let defs5_wg =  if is_pre then defs5a_wg else
              Sautil.perform_conj_unify_post_wg prog hp args0 (unk_hps@link_hps) unk_svl defs5a_wg no_pos
          in
          let () = DD.ninfo_hprint (add_str "defs5a: " pr1) defs5a_wg no_pos in
          let () = DD.ninfo_hprint (add_str "defs5: " pr1) defs5_wg no_pos in
          (*remove duplicate with self-recursive*)
          (* let base_case_exist,defs4 = Sautil.remove_dups_recursive hp args0 unk_hps defs3 in *)
          (*find longest hnodes common for more than 2 formulas*)
          (*each hds of hdss is def of a next_root*)
          (* let defs5 = List.filter (fun f -> have_roots args0 f) defs4 in *)
          (*to do: move elim useless + post-unify after the synthesis*)
          let old_disj = !Globals.pred_disj_unify in
          let disj_opt = (* !Globals.pred_elim_useless || *) !Globals.pred_disj_unify in
          let defs,elim_ss = if disj_opt then
              Sautil.get_longest_common_hnodes_list prog is_pre hpdefs (skip_hps) unk_svl hp r non_r_args args0 defs5_wg
            else
              let defs = Sautil.mk_hprel_def_wprocess prog is_pre hpdefs skip_hps unk_svl hp (args0,r,non_r_args) defs5_wg no_pos in
              (defs,[])
          in
          let () = Globals.pred_disj_unify := old_disj in
          if defs <> [] then
            (false, defs,elim_ss)
          else
            (* report_error no_pos "shape analysis: FAIL" *)
          if guarded_top_par_defs = [] then
            let body =
              if is_pre then
                Cformula.mkHTrue_nf no_pos
              else
                Cformula.mkFalse_nf no_pos
            in
            let def = Cformula.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, non_r_args))
                (Cformula.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args0, no_pos)) [(body,None)] None in
            (true, [(hp, def)],[])
          else
            let def = Cformula.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, non_r_args))
                (Cformula.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args0, no_pos))
                (List.map (fun (a1,args,og,f,_) -> (f,og)) guarded_top_par_defs) None in
            (true, [(hp, def)],[])
      in
      let hpdefs = if is_put_top_guarded then hpdefs else
          List.map (fun (hp,def) ->
              let _, args0= Cformula.extract_HRel def.Cformula.def_lhs in
              let f_pdefs = List.fold_left (fun r (a1,args,og,f,_) ->
                  if CP.eq_spec_var a1 hp then
                    let ss = List.combine args args0 in
                    let n_og = Cformula.subst_opt ss og in
                    r@[(f,n_og)]
                  else r
                ) [] guarded_top_par_defs in
              (hp, {def with Cformula.def_rhs = def.Cformula.def_rhs@f_pdefs})
            ) hpdefs in
      (********PRINTING***********)
      let () = if !VarGen.sap then
          List.iter (fun (_, def) ->
              Debug.info_pprint ((Cprinter.string_of_hp_rel_def_short def)) no_pos)
            hpdefs
        else ()
      in
      (********END PRINTING***********)
      (hpdefs, subst_useless)
    end

let generalize_one_hp prog is_pre (defs:(CP.spec_var *Cformula.hp_rel_def) list) non_ptr_unk_hps unk_hps link_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  let pr3 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  Debug.no_2 "generalize_one_hp" pr1 !CP.print_svl (pr_pair pr2 pr3)
    (fun _ _ -> generalize_one_hp_x prog is_pre defs non_ptr_unk_hps
        unk_hps link_hps par_defs) par_defs unk_hps

let get_pdef_body_x unk_hps post_hps (a1,args,unk_args,a3,olf,og, orf)=
  let exchane_unk_post hp1 args f unk_args=
    let hpargs2 = Cformula.get_HRels_f f in
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
      let hps1 = Cformula.get_hp_rel_name_formula f1 in
      let hps2 = Cformula.get_hp_rel_name_formula f2 in
      if CP.intersect_svl hps1 hps2 <> [] then
        (*recurive case*)
        if Cformula.is_HRel_f f1 then f2 else f1
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
    let hps = Cformula.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_pardef (hp,_,_,f,_) =
    let hps = Cformula.get_hp_rel_name_formula f in
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
  (*   (Cformula.get_HRels_f f) *)
  (* in *)
  let process_dep_group grp rec_hps nrec_grps=
    (*not depends on any recursive hps, susbt it*)
    let ters,fss = List.split (List.map (Sautil.succ_subst prog nrec_grps unk_hps false) grp) in
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
      let succ_hps = List.concat (List.map (fun (_,_,_,f,_) -> Cformula.get_hp_rel_name_formula f) dep_grp) in
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
      (* let () = DD.info_pprint ("      new_cur: " ^ (pr1 new_cur)) no_pos in *)
      (*subs new_cur with new_rec_indps (new_nrec_indps is substed already)*)
      let new_cur1 =  List.map Sautil.remove_dups_pardefs new_cur in
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

(*
  divide hp into three groups:
  - independent - ready for genalizing
  - dependent:
      - depend on non-recursive groups: susbst
      - depend on recusive groups: wait
*)
let def_subst_fix_x prog post_hps unk_hps prefix_hps hpdefs=
  (*remove dups*)
  (* let unk_hps = CP.remove_dups_svl unk_hps in *)
  let is_rec_hpdef d=
    let hp = Cformula.get_hpdef_name d.Cformula.def_cat in
    let hps = Cformula.get_hp_rel_name_formula (Cformula.disj_of_list (List.map fst d.Cformula.def_rhs) no_pos) in
    (CP.mem_svl hp hps)
  in
  let is_independ_hpdef d=
    let hp = Cformula.get_hpdef_name d.Cformula.def_cat in
    let f = Cformula.disj_of_list (List.map fst d.Cformula.def_rhs) no_pos in
    let hps = Cformula.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       rec hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let _,rems = List.partition (fun hp1 -> CP.eq_spec_var hp hp1) hps in
    (* DD.ninfo_zprint (lazy (("       rec rems: " ^ (!CP.print_svl rems)))) no_pos; *)
    (rems = [])
  in
  let process_dep_hpdef hpdef rec_hps nrec_hpdefs=
    let (a1,hprel,g,f) = Cformula.flatten_hp_rel_def hpdef in
    let hp = Cformula.get_hpdef_name a1 in
    let fs = Cformula.list_of_disjs f in
    (* DD.ninfo_zprint (lazy (("       process_dep_group hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let succ_hp_args =  List.concat (List.map Cformula.get_HRels_f fs) in
    (*remove dups*)
    let succ_hp_args = Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq succ_hp_args in
    (*get succ hp names only*)
    let succ_hps = fst (List.split succ_hp_args) in
    (* DD.ninfo_zprint (lazy (("       process_dep_group succ_hps: " ^ (!CP.print_svl succ_hps)))) no_pos; *)
    (*remove itself hp and unk_hps*)
    let succ_hps1 = List.filter (fun hp1 -> not (CP.eq_spec_var hp1 hp) &&
                                            not (CP.mem_svl hp1 unk_hps) && not (CP.mem_svl hp1 rec_hps) ) succ_hps in
    (* DD.info_zprint (lazy (("       process_dep_group succ_hps1: " ^ (!CP.print_svl succ_hps1)))) no_pos; *)
    if (CP.diff_svl succ_hps1 rec_hps) <> [] then
      (*not depends on any recursive hps, susbt it*)
      let args = Sautil.get_ptrs hprel in
      let ters,new_fs_wg = List.split (List.concat (List.map (fun (f0,g1) ->
          List.map (fun f1 ->
              Sautil.succ_subst_hpdef prog unk_hps nrec_hpdefs succ_hps1 (hp,args,g1,f1)
            ) (CF.list_of_disjs f0)
        ) hpdef.CF.def_rhs)) in
      (*check all is false*)
      (* let pr = pr_list string_of_bool in *)
      (* DD.ninfo_zprint (lazy (("       bool: " ^ (pr ters)))) no_pos; *)
      let ter = List.for_all (fun b -> not b) ters in

      let fs1_wg  = Sautil.remove_longer_common_prefix_w_unk_g unk_hps (List.concat new_fs_wg) in

      (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
      (* let () = DD.info_zprint (lazy (("       fs1: " ^ (pr1 fs1)))) no_pos in *)
      let b =
        if not ter then
          let fs1 = List.map fst fs1_wg in
          not (Sautil.checkeq_formula_list fs fs1)
        else false
      in
      (* let fs2 = Sautil.remove_subset new_fs1 in *)
      (*may be wrong: should reevauate root*)
      if b then
        let r, others = Sautil.find_root prog (hp::unk_hps) args (List.map fst fs1_wg) in
        let todo_unk = CA.set_proot_hp_def_raw (Sautil.get_pos args 0 r) prog.CA.prog_hp_decls (CP.name_of_spec_var hp) in
        (b , Cformula.mk_hp_rel_def1 (* hpdef.Cformula.def_cat *) (CP.HPRelDefn (hp, r, others )) hprel (* [(Cformula.disj_of_list fs1 no_pos, g)] *) fs1_wg None)
      else (false, hpdef)
    else
      (*return*)
      (false,hpdef)
  in
  let is_pure_guard hp_def =
    let fs, ogs = List.split hp_def.Cformula.def_rhs in
    if List.exists (fun og ->
        match og with
        | None -> false
        | Some f -> not (CP.isConstTrue (Cformula.get_pure f))
      ) ogs then
      let hps = List.fold_left (fun r f -> r@(Cformula.get_hp_rel_name_formula f)) [] fs in
      let hp0 = Cformula.get_hpdef_name hp_def.Cformula.def_cat in
      CP.diff_svl hps [hp0] <> []
    else false
  in
  let subst_first_dep_hpdef deps rec_hps nrec_hpdefs0=
    (*move guard with pure to the end*)
    let pure_guard_nrec_hpdefs, rem = List.partition is_pure_guard nrec_hpdefs0 in
    let nrec_hpdefs = rem@pure_guard_nrec_hpdefs in
    let rec local_helper deps res r=
      match deps with
      | [] -> (r,res)
      | hpdef::gs -> let r1,hpdef1 = process_dep_hpdef hpdef rec_hps nrec_hpdefs in
        (* if r then (true,(res@[hpdef1]@gs)) *)
        (* else local_helper gs (res@[hpdef]) *)
        local_helper gs (res@[hpdef1]) (r1||r)
    in
    (* if nrec_grps = [] then (false, deps) else *)
    local_helper deps [] false
  in
  let helper_x hpdefs rec_inds nrec_inds=
    let indeps,deps = List.partition is_independ_hpdef hpdefs in
    (*classify indeps into rec and non_rec*)
    let lrec_inds,lnrec_inds = List.partition is_rec_hpdef indeps in
    (*for return*)
    let res_rec_inds = rec_inds@lrec_inds in
    let res_nrec_inds = nrec_inds@lnrec_inds in
    let lrec_deps,l_nrec_deps = List.partition is_rec_hpdef deps in
    (*find deps on non_recs*)
    let rec_hps = List.map
        (fun d -> Cformula.get_hpdef_name d.Cformula.def_cat)
        (res_rec_inds@lrec_deps) in
    (*find the first depend grp in deps to subst,
      if can not find, return false for terminating*)
    let r, deps1 = subst_first_dep_hpdef deps rec_hps (res_nrec_inds@l_nrec_deps) in
    (( (*List.length indeps>0 || *) r), deps1, res_rec_inds,res_nrec_inds)
  in
  (*for debugging*)
  let helper hpdefs rec_inds nrec_inds=
    let pr1 = (pr_list_ln Sautil.string_of_hp_rel_def) in
    let pr2= pr_quad string_of_bool pr1 pr1 pr1 in
    Debug.no_3 "def_subst_fix:helper" pr1 pr1 pr1 pr2
      (fun _ _ _ -> helper_x hpdefs rec_inds nrec_inds) hpdefs rec_inds nrec_inds
  in
  (*END for debugging*)
  let rec helper_fix cur rec_indps nrec_indps=
    let r,new_cur,new_rec_indps,new_nrec_indps = helper cur rec_indps nrec_indps in
    if r then
      (*rearrange cur for terminating*)
      (* let new_cur1 = (List.tl new_cur)@[List.hd new_cur] in *)
      helper_fix new_cur new_rec_indps new_nrec_indps
    else
      (new_cur@new_rec_indps@new_nrec_indps)
  in
  let prefix_defs, hpdefs1 = List.partition (fun def ->
      let hp,_ = CF.extract_HRel def.CF.def_lhs in
      CP.mem_svl hp prefix_hps
    ) hpdefs in
  let hpdefs2 = if List.length hpdefs1 <=1 then hpdefs1 else
      helper_fix hpdefs1 [] []
  in
  hpdefs2@prefix_defs

let def_subst_fix prog post_hps unk_hps prefix_hps hpdefs=
  let pr1 = (pr_list_ln Sautil.string_of_hp_rel_def) in
  Debug.no_1 "def_subst_fix" pr1 pr1
    (fun _ -> def_subst_fix_x prog post_hps unk_hps prefix_hps hpdefs) hpdefs


let is_valid_pardef (_,args,_,_,f,_)=
  let ls_succ_args = snd (List.split (Cformula.get_HRels_f f)) in
  let succ_args = List.concat ls_succ_args in
  let ptrs = Cformula.get_ptrs_f f in
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
  (*do not generate anything for LINK preds*)
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
  let () = DD.ninfo_pprint ("      groups1: " ^ (pr1 groups)) no_pos in
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
  let () = DD.ninfo_pprint ("      groups2: " ^ (pr1 groups2)) no_pos in
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
          (hp, {def with Cformula.def_rhs = List.map (fun (f,og) ->( Cformula.subst_hrel_f f elim_ss, og)) def.Cformula.def_rhs})) hpdefs
    else
      hpdefs
  in
  hpdefs1

(*todo: remove non_ptr_unk_hps*)
let generalize_hps_par_def prog is_pre non_ptr_unk_hps unk_hpargs link_hps post_hps pre_defs predef_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr3 = fun (_,a)-> pr2 a in
  Debug.no_4 "generalize_hps_par_def" !CP.print_svl !CP.print_svl pr1
    !CP.print_svl (pr_list_ln pr3)
    (fun _ _ _ _ -> generalize_hps_par_def_x prog is_pre non_ptr_unk_hps unk_hpargs
        link_hps post_hps pre_defs predef_hps par_defs)
    post_hps link_hps par_defs predef_hps

(*for tupled defs*)
let generalize_hps_cs_new_x prog callee_hps hpdefs unk_hps link_hps cs=
  let generalize_hps_one_cs constr=
    let lhs,rhs = constr.Cformula.hprel_lhs,constr.Cformula.hprel_rhs in
    let lhds, lhvs,l_hp = Cformula.get_hp_rel_formula lhs in
    let rhds, rhvs,r_hp = Cformula.get_hp_rel_formula rhs in
    let lhp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (l_hp) in
    let rhp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (r_hp) in
    (*filer def hp out*)
    let dfs = (hpdefs@callee_hps@unk_hps) in
    let diff = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 dfs)) lhp_args in
    let diff1 = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 link_hps)) diff in
    match diff1 with
    | [] -> ([],[],[]) (*drop constraint, no new definition*)
    | _ -> begin
        let () = DD.info_ihprint (add_str ">>>>>> generalize_one_cs_hp: <<<<<<"pr_id) "" no_pos in
        if lhvs <> [] || lhds <> [] then
          ([constr],[],[])
        else
          let lhps, ls_largs = List.split lhp_args in
          let rhps, ls_rargs = List.split rhp_args in
          let largs = CP.remove_dups_svl (List.concat ls_largs) in
          let rargs = CP.remove_dups_svl (List.concat ls_rargs) in
          let keep_ptrs = Cformula.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) (largs@rargs) in
          let pos = Cformula.pos_of_formula lhs in
          let nrhs = Cformula.mkAnd_pure rhs (MCP.mix_of_pure (Cformula.get_pure lhs)) pos in
          let keep_def_hps = lhps@rhps@unk_hps@hpdefs in
          let r = CF.drop_data_view_hrel_nodes nrhs Sautil.check_nbelongsto_dnode CF.check_nbelongsto_vnode CF.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in
          if (not (Sautil.is_empty_f r)) then
            let hps = List.map fst diff in
            let hfs = List.map (fun (hp,args) -> (Cformula.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos))) diff in
            let hf = Cformula.join_star_conjunctions hfs in
            let def_tit = match diff with
              | [(hp,args)] -> CP.HPRelDefn (hp, List.hd args, List.tl args)
              | _ -> CP.HPRelLDefn hps
            in
            let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" pos in
            let () = DD.ninfo_pprint ((let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr diff) ^ "::=" ^
                                      (Cprinter.prtt_string_of_formula r) ) pos in
            ([],[( Cformula.mk_hp_rel_def1 def_tit hf [(r,None)] None)], hps)
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
  (* x_binfo_pp ">>>>>> step 6: generalization <<<<<<" no_pos; *)
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
let collect_sel_hpdef_x defs sel_hps unk_hps m=
  let lib_hps = List.map fst m in
  (*currently, use the first lib matched*)
  let m = List.map (fun (hp, l) -> (hp, List.hd l)) m in
  let mlib = List.map (fun (hp, _) -> hp) m in
  let rec look_up_lib hp ms=
    match ms with
    | [] -> None
    | (hp1,hf1)::ss -> if CP.eq_spec_var hp hp1 then
        Some (Cformula.formula_of_heap hf1 no_pos)
      else look_up_lib hp ss
  in
  let extract_body hpdef=
    let fs = List.fold_left (fun r (_, f_opt,_) ->  match f_opt with
        | Some f -> r@[f]
        | None -> r
      ) [] hpdef.Cformula.hprel_def_body in
    let f = Cformula.disj_of_list fs no_pos in
    f
  in
  let compute_def_w_lib (hp,hpdef)=
    let olib = look_up_lib hp m in
    begin
      let f1_opt =
        match olib with
        | None ->
          (*subs lib form inside f if applicable*)
          let f =  extract_body hpdef in
          let hps = Cformula.get_hp_rel_name_formula f in
          if CP.intersect_svl hps lib_hps = [] then [] else
            let f_subst = Cformula.subst_hrel_hview_f f m in
            [(f_subst,hpdef.Cformula.hprel_def_flow)]
        | Some lib_f -> [(lib_f,hpdef.Cformula.hprel_def_flow)]
      in
      {hpdef with Cformula.hprel_def_body_lib = f1_opt}
    end
  in
  let look_up_depend cur_hp_sel f=
    let hps = Cformula.get_hp_rel_name_formula f in
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
      | (hp,(* (a,hf,og,f) *) hpdef)::lss ->
        let incr =
          if CP.mem_svl hp (cur_sel(* @unk_hps *)) then
            []
          else
            [hp]
        in
        let f =  extract_body hpdef in
        let new_hp_dep = look_up_depend cur_sel f in
        helper1 lss (CP.remove_dups_svl (res@incr@new_hp_dep))
    in
    let incr_sel_hps = helper1 incr [] in
    (*nothing new*)
    if incr_sel_hps = [] then cur_sel_hpdef else
      let incr_sel_hp_def,remain_hp_defs = look_up_hp_def incr_sel_hps non_sel_hp_def in
      find_closed_sel (cur_sel@incr_sel_hps) (cur_sel_hpdef@incr_sel_hp_def) remain_hp_defs incr_sel_hp_def
  in
  let defsw = List.map (fun hpdef ->
      (List.hd (Cformula.get_hp_rel_name_h_formula hpdef.Cformula.hprel_def_hrel), hpdef)) defs in
  let sel_defw,remain_hp_defs = List.partition (fun (hp,_) -> CP.mem_svl hp sel_hps) defsw in
  let closed_sel_defw = find_closed_sel sel_hps sel_defw remain_hp_defs sel_defw in
  let all_sel_defw = List.map compute_def_w_lib closed_sel_defw in
  (*remove hp not in orig but == lib*)
  let inter_lib = Gen.BList.difference_eq CP.eq_spec_var mlib sel_hps in
  List.filter (fun hdef ->
      let a1 = hdef.Cformula.hprel_def_kind in
      let hp = Cformula.get_hpdef_name a1 in
      not (CP.mem_svl hp inter_lib))
    all_sel_defw

let collect_sel_hpdef hpdefs sel_hps unk_hps m=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_def in
  let pr2 = !CP.print_svl in
  let pr3b = pr_list_ln Cprinter.prtt_string_of_h_formula in
  let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^
                             (* ( String.concat " OR " view_names) *) (pr3b vns) in
  let pr3 = pr_list_ln pr3a in
  (* let pr4 = (pr_list_ln Cprinter.string_of_hprel_def) in *)
  Debug.no_3 "sa3.collect_sel_hpdef" pr1 pr2 pr3 pr1
    (fun _ _ _ -> collect_sel_hpdef_x hpdefs sel_hps unk_hps m) hpdefs sel_hps m

let match_one_hp_views_x iprog prog cur_m (vdcls: CA.view_decl list) def:(CP.spec_var* CF.h_formula list)=
  let helper args r paras vdcl=
    let () = DD.ninfo_hprint (add_str "        vdcl.Cast.view_name:" pr_id) vdcl.Cast.view_name no_pos in
    let self_t = CP.type_of_spec_var r in
    if (List.length args) = ((List.length vdcl.Cast.view_vars) + 1) &&
       self_t = (Named vdcl.Cast.view_data_name)
    then
      let () = DD.ninfo_hprint (add_str "        vdcl.Cast.view_name:" pr_id) vdcl.Cast.view_name no_pos in
      let f1 = Cformula.formula_of_heap def.Cformula.def_lhs no_pos in
      let self_sv = CP.SpecVar (self_t ,self, Unprimed) in
      let sst = List.combine (r::paras) (self_sv::vdcl.Cast.view_vars) in
      let () = DD.ninfo_hprint (add_str "        sst:" (pr_list (pr_pair
                                                                   !CP.print_sv !CP.print_sv))) sst no_pos in
      (*type comparitive*)
      if List.exists (fun (sv1, sv2) -> not (cmp_typ (CP.type_of_spec_var sv1) (CP.type_of_spec_var sv2))) sst then [] else
        let f1 = x_add Cformula.subst sst f1 in
        let vnode = Cformula.mkViewNode (self_sv ) vdcl.Cast.view_name
            (vdcl.Cast.view_vars) no_pos in
        let f2 = Cformula.formula_of_heap vnode no_pos in
        if Lemutil.checkeq_sem iprog prog f1 f2 [def] [] [] then
          (* let self_ss = [(self_sv,r)] in *)
          (* [Cformula.h_subst self_ss vnode] *)
          let matched_vnode = Cformula.mkViewNode r vdcl.Cast.view_name paras no_pos in
          [matched_vnode]
        else []
    else []
  in
  (*return the first result*)
  let rec map_ret_first fnc vdcls=
    match vdcls with
    | [] -> []
    | v::rest -> let eq_views = fnc v in
      if eq_views = [] then map_ret_first fnc rest else eq_views
  in
  match def.Cformula.def_cat with
  | CP.HPRelDefn (hp, r, paras) -> begin
      let () = DD.ninfo_hprint (add_str "        hp:" !CP.print_sv) hp no_pos in
      let args = r::paras in
      let eq_views = map_ret_first (helper args r paras) vdcls in
      (hp,eq_views)
    end
  | _ -> report_error no_pos "SA3.match_one_hp_views: support HPRELDEF only"

let match_one_hp_views iprog prog cur_m (vdcls: CA.view_decl list) def=
  let pr1 = Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list Cprinter.prtt_string_of_h_formula in
  Debug.no_1 "match_one_hp_views" pr1 (pr_pair !CP.print_sv pr2)
    (fun _ -> match_one_hp_views_x iprog prog cur_m vdcls def)
    def

(*to improve: handle nested data structures *)
let match_hps_views_x iprog prog sel_hps (hp_defs: Cformula.hp_rel_def list) (vdcls: Cast.view_decl list):
  (CP.spec_var* Cformula.h_formula list) list=
  let match_one_fnc = if (!Globals.syntatic_mode) then Sautil.match_one_hp_views else
      (match_one_hp_views) in
  let hrel_vdcls, others  = List.partition (fun vdcl -> vdcl.Cast.view_kind =View_HREL) prog.Cast.prog_view_decls in
  let () = prog.Cast.prog_view_decls <- others in
  let hp_defs1 = List.filter (fun def -> match def.Cformula.def_cat with
      | CP.HPRelDefn (hp,r,paras) -> (CP.mem_svl hp sel_hps &&
                                      not (List.for_all (fun sv -> not (CP.is_node_typ sv)) (r::paras))
                                     )
      | _ -> false
    ) hp_defs in
  (*sort topo: to fix bug this function*)
  (* let sorted_scc, mutrec_defs = Cfutil.hp_defs_topo_sort hp_defs1 in *)
  let equiv_hp_defs, non_equiv_hp_defs, hp_sst = Cfutil.classify_equiv_hp_defs hp_defs1 in
  (*process bottom-up*)
  let m = List.fold_left (fun cur_m def ->
      let hp,new_ls_m = match_one_fnc iprog prog cur_m vdcls def in
      if new_ls_m = [] then cur_m else
        let equiv_match = try
            let hp_equivs = List.fold_left (fun r (hp1,hp2) ->
                if CP.eq_spec_var hp2 hp then r@[hp1] else r
              ) [] hp_sst in
            List.map (fun hp3 -> (hp3, new_ls_m)) hp_equivs
          with _ -> []
        in
        cur_m@((hp,new_ls_m)::equiv_match)
    ) [] non_equiv_hp_defs in
  (*extract view_equiv*)
  let view_equivs = List.fold_left (fun r (hp, hfs) ->
      let hp_name = CP.name_of_spec_var hp in
      r@(List.fold_left (fun r1 hf ->
          match hf with
          | CF.ViewNode vn ->
            r1@[(hp_name, vn.CF.h_formula_view_name)]
          | _ -> r1
        ) [] hfs )
    ) [] m in
  let () = x_tinfo_hp (add_str "view_equivs: " (pr_list (pr_pair pr_id pr_id))) view_equivs no_pos in
  let () = prog.CA.prog_view_equiv <- prog.CA.prog_view_equiv@view_equivs in
  let () = prog.Cast.prog_view_decls <- prog.Cast.prog_view_decls@hrel_vdcls in
  m
(* (List.filter (fun (_,l) -> l<>[]) m) *)

let match_hps_views iprog prog sel_hps (hp_defs: Cformula.hp_rel_def list) (vdcls: Cast.view_decl list):
  (CP.spec_var* Cformula.h_formula list) list=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln  Cprinter.prtt_string_of_h_formula  in
  let pr3a = fun (hp,vns) -> (!CP.print_sv hp) ^ " === " ^
                             (* ( String.concat " OR " view_names) *) (pr2 vns) in
  let pr3 = pr_list_ln pr3a in
  let pr4 = pr_list_ln (Cprinter.string_of_view_decl) in
  Debug.no_2 "match_hps_views" pr1 pr4 pr3
    (fun _ _ -> match_hps_views_x iprog prog sel_hps hp_defs vdcls) hp_defs vdcls


(***************************************************************
                     END LIB MATCHING
 ****************************************************************)
let partition_constrs_x constrs post_hps0 dang_hps=
  let () = DD.info_ihprint (add_str ">>>>>> step 2 - PARTITION" pr_id) " partition constrains: pre, post, pre-obligation, post-obligation<<<<<<" no_pos in
  let get_pre_fix_hp pre_fix_hps cs=
    let ohp = Cformula.extract_hrel_head cs.Cformula.hprel_rhs in
    match ohp with
    | Some (hp) -> if (CP.mem_svl hp pre_fix_hps) then pre_fix_hps else
        let lhps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
        if CP.mem_svl hp lhps && (Cformula.extract_hrel_head cs.Cformula.hprel_lhs = None) then
          (pre_fix_hps@[hp])
        else pre_fix_hps
    | None -> pre_fix_hps
  in
  let classify new_post_hps pre_fix_hps (pre_cs,post_cs, pre_fix_cs, pre_oblg,tupled_hps, post_oblg) cs =
    let is_post_constr hps=
      try
        let ohp = Cformula.extract_hrel_head cs.Cformula.hprel_rhs in
        match ohp with
        | Some (hp) -> (CP.mem_svl hp hps)
        | None -> false
      with _ -> false
    in
    let is_fold_form hps=
      try
        let ohp = Cformula.extract_hrel_head cs.Cformula.hprel_rhs in
        match ohp with
        | Some hp -> (CP.mem_svl hp hps) && (Cformula.extract_hrel_head cs.Cformula.hprel_lhs = None)
        | None -> false
      with _ -> false
    in
    if is_post_constr new_post_hps then (pre_cs,post_cs@[cs],pre_fix_cs, pre_oblg,tupled_hps,post_oblg) else

    if is_fold_form pre_fix_hps then
      (pre_cs,post_cs,pre_fix_cs@[cs], pre_oblg,tupled_hps,post_oblg)
    else
      let lhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
      if (CP.intersect_svl pre_fix_hps lhs_hps) != [] then
        (pre_cs,post_cs,pre_fix_cs, pre_oblg@[cs],tupled_hps,post_oblg)
      else
      if CP.intersect_svl (new_post_hps) lhs_hps = [] then
        (*identify pre-oblg*)
        let l_hds, l_hvs,lhrels =Cformula.get_hp_rel_formula cs.Cformula.hprel_lhs in
        let r_hds, r_hvs,rhrels =Cformula.get_hp_rel_formula cs.Cformula.hprel_rhs in
        if (List.length l_hds > 0 || List.length l_hvs > 0 ) && List.length lhrels > 0 &&
           (* (List.length r_hds > 0 || List.length r_hvs > 0) && *)
           List.length (List.filter (fun (hp,_,_) -> not(CP.mem_svl hp dang_hps)) rhrels) > 0
        then
          (pre_cs,post_cs,pre_fix_cs,pre_oblg@[cs],
           (* tupled_hps@(CP.diff_svl (List.map (fun (a,_,_) -> a) rhrels) lhs_hps) *)
           tupled_hps@(CP.diff_svl lhs_hps pre_fix_hps)
          ,post_oblg)
        else
          (pre_cs@[cs],post_cs,pre_fix_cs,pre_oblg,tupled_hps,post_oblg)
      else (pre_cs,post_cs,pre_fix_cs, pre_oblg,tupled_hps,post_oblg@[cs])
  in
  let pre_fix_hps0 = List.fold_left get_pre_fix_hp [] constrs in
  let () = Debug.ninfo_hprint (add_str "    pre_fix_hps0" !CP.print_svl) pre_fix_hps0 no_pos in
  let pre_fix_hps = CP.diff_svl pre_fix_hps0 post_hps0 in
  let pre_constrs,post_constrs, pre_fix_constrs, pre_oblg, tupled_dep_on_hps, post_oblg_constrs = List.fold_left (classify post_hps0 pre_fix_hps) ([],[],[],[],[],[]) constrs in
  let () = Debug.ninfo_hprint (add_str "    tupled_dep_on_hps" !CP.print_svl) tupled_dep_on_hps no_pos in
  (*partition pre-constrs, filter ones in pre-obligation*)
  let pre_constrs1, pre_oblg_ext = List.partition (fun cs ->
      let lhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
      CP.intersect_svl lhs_hps tupled_dep_on_hps = []
    ) pre_constrs in
  (pre_constrs1,post_constrs, pre_fix_constrs, pre_oblg@pre_oblg_ext, post_oblg_constrs, pre_fix_hps)

let partition_constrs constrs post_hps dang_hps=
  let (pre_constrs,post_constrs, pre_fix_constrs, pre_oblg, post_oblg_constrs, pre_fix_hps) as res = partition_constrs_x constrs post_hps dang_hps in
  if !VarGen.sap then
    begin
      let pr1 = pr_list_num Cprinter.string_of_hprel_short in
      let () = x_binfo_pp "=============>>>>" no_pos in
      let () = x_binfo_hp (add_str "AFTER" pr_id) "" no_pos in
      let () = x_binfo_hp (add_str "pre ass" pr1) pre_constrs no_pos in
      let () = x_binfo_hp (add_str "pre-oblg" pr1) pre_oblg no_pos in
      let () = x_binfo_hp (add_str "post ass" pr1) post_constrs no_pos in
      let () = x_binfo_hp (add_str "post-oblg" pr1) post_oblg_constrs no_pos in
      let () = DD.binfo_end "partition_constrs" in
      ()
    end;
  res

let partition_constrs constrs post_hps dang_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  Debug.no_3 "partition_constrs" pr1 pr2 pr2 (pr_hexa pr1 pr1 pr1 pr1 pr1 pr2)
    (fun _ _ _ -> partition_constrs constrs post_hps dang_hps) constrs post_hps dang_hps

(***************************************************************
                     PROCESS INFER ACTION
 ****************************************************************)

let infer_analize_dang prog is=
  let () = DD.ninfo_hprint (add_str ">>>>>> step 1: find dangling ptrs, link pre and post-preds dangling preds<<<<<<" pr_id) "" no_pos in
  let constrs1, unk_hpargs1, unk_map1, link_hpargs1, _ = x_add Sacore.analize_unk prog is.CF.is_post_hps is.CF.is_constrs
      is.Cformula.is_unk_map is.Cformula.is_dang_hpargs is.Cformula.is_link_hpargs in
  { is with
    Cformula.is_constrs = constrs1;
    Cformula.is_link_hpargs = is.Cformula.is_link_hpargs@link_hpargs1;
    Cformula.is_dang_hpargs = is.Cformula.is_dang_hpargs@unk_hpargs1;
    Cformula.is_unk_map = is.Cformula.is_unk_map@unk_map1
  }

let infer_split_base prog is=
  if !Globals.sa_sp_split_base || !Globals.sa_infer_split_base then
    (* let unk_hps1 = List.map fst is.IC.is_dang_hpargs in *)
    (* let link_hps1 = List.map fst is.IC.is_link_hpargs in *)
    let () = DD.info_ihprint (add_str ">>>>>> step 1 - SYN-BASE" pr_id) " split constraints based on pre and post-preds<<<<<<" no_pos in
    let n_constrs, n_unk_map, n_link_hpargs =
      split_base_constr prog is.Cformula.is_cond_path is.Cformula.is_constrs is.Cformula.is_post_hps is.Cformula.is_sel_hps [] is.Cformula.is_unk_map
        (List.map fst is.Cformula.is_dang_hpargs) (List.map fst is.Cformula.is_link_hpargs)
    in
    { is with
      Cformula.is_constrs = n_constrs;
      Cformula.is_link_hpargs = is.Cformula.is_link_hpargs@n_link_hpargs;
      Cformula.is_unk_map = is.Cformula.is_unk_map@n_unk_map;
    }
  else is

let infer_pre_synthesize_x prog proc_name callee_hps is pre_constrs need_preprocess detect_dang=
  let rec extract_guard_rec constrs hp args p_acc=
    match constrs with
    | [] -> p_acc
    | cs::rest -> begin
        try
          let hp1,args1 = CF.extract_HRel_f cs.CF.hprel_rhs in
          if CP.eq_spec_var hp hp1 && not(CP.mem_svl hp1 is.CF.is_post_hps) then
            let sel_p = CP.filter_var (CF.get_pure cs.CF.hprel_lhs) args1 in
            let ss = List.combine args1 args in
            let n_p_acc = CP.mkAnd p_acc (CP.subst ss sel_p) no_pos in
            let () = DD.ninfo_hprint (add_str "p_acc" !CP.print_formula) p_acc no_pos in
            let () = DD.ninfo_hprint (add_str "n_p_acc" !CP.print_formula) n_p_acc no_pos in
            extract_guard_rec rest hp args n_p_acc
          else extract_guard_rec rest hp args p_acc
        with _ -> extract_guard_rec rest hp args p_acc
      end
  in
  (*add guard: for rec*)
  let find_extra_guard_rec pdefs=
    match pdefs with
    | [(hp,args,unk_svl, cond, olhs,og, orhs)] ->
      if CP.isConstTrue cond then
        (*look up rec proving*)
        let rec_guard = extract_guard_rec is.CF.is_all_constrs hp args (CP.mkTrue no_pos) in
        let n_cond = if not (CP.isConstTrue rec_guard) && (Tpdispatcher.is_sat_raw (MCP.mix_of_pure rec_guard)) then
            rec_guard
          else cond
        in
        let () = DD.ninfo_hprint (add_str " n_cond" !CP.print_formula)  n_cond no_pos in
        let n_cond1 = match orhs with
          | Some _ -> Some (hp, args, n_cond)
          | None -> None
        in
        n_cond1
      else None
    | _ -> None
  in
  let rec combine_extra_gaurd hp_defs hp args guard res=
    match hp_defs with
    | [] -> res
    | def::rest -> begin
        let hp1, args1 = CF.extract_HRel def.CF.def_lhs in
        if CP.eq_spec_var hp hp1 then
          let ss = List.combine args args1 in
          let n_guard = CP.subst ss guard in
          match def.CF.def_cat with
          | CP.HPRelDefn (_,r,_) ->
            let n_guard2 = CP.filter_var n_guard [r] in
            let n_rhs = List.map (fun (f, og) ->
                (CF.mkAnd_pure f (MCP.mix_of_pure n_guard2) no_pos,og))
                def.CF.def_rhs in
            let ndef = {def with CF.def_rhs = n_rhs} in
            res@[ndef]@rest
          | _ -> combine_extra_gaurd rest hp args guard (res@[def])
        else combine_extra_gaurd rest hp args guard (res@[def])
      end
  in
  (*******************END*****************************)
  DD.info_ihprint (add_str "  trivial assumptions" pr_id) "" no_pos;
  let constrs0 = List.map (Sautil.weaken_strengthen_special_constr_pre true) pre_constrs in
  let unk_hps1 = (List.map fst is.Cformula.is_dang_hpargs) in
  let link_hps = (List.map fst is.Cformula.is_link_hpargs) in
  let () = DD.ninfo_hprint (add_str ">>>>>> pre-predicates: step pre-5: group & simpl impl<<<<<<" pr_id) "" no_pos in
  let pr_par_defs,rem_constrs1 = get_par_defs_pre constrs0 in
  let () = DD.info_ihprint (add_str "  Syn-Case and Syn-Group-Pre" pr_id) "" no_pos in
  let par_defs, rem_constrs2, hconj_unify_cond = combine_pdefs_pre prog unk_hps1 link_hps pr_par_defs in
  let () = DD.ninfo_hprint (add_str ">>>>>> pre-predicates: step pre-8: strengthen<<<<<<" pr_id) "" no_pos in
  let () = DD.info_ihprint (add_str "  Syn-Pre-Def and Syn-Pre-Approx" pr_id) "" no_pos in
  let extra_rec_guard_opt = find_extra_guard_rec par_defs in
  let rem_constrs3, hp_defs, defined_hps = generalize_hps prog true callee_hps is.CF.is_dang_hpargs link_hps is.CF.is_post_hps [] [] constrs0 par_defs in
  (* check hconj_unify_cond*)
  let hp_defs1, new_equivs, unk_equivs, non_dang_hps = if hconj_unify_cond = [] then
      (hp_defs,[], [], [])
    else
      let is_sat, new_hpdefs, equivs, unk_equivs,punk_equivs = Sacore.reverify_cond prog unk_hps1 link_hps hp_defs hconj_unify_cond in
      if not is_sat then report_error no_pos "SA.infer_shapes_init_pre: HEAP CONJS do not SAT"
      else (new_hpdefs, equivs@punk_equivs, unk_equivs, List.map fst punk_equivs)
  in
  (*let combine extra rec conditions*)
  let hp_defs2 = match extra_rec_guard_opt with
    | None -> hp_defs1
    | Some (hp,args, guard) -> combine_extra_gaurd hp_defs1 hp args guard []
  in
  { is with
    Cformula.is_dang_hpargs = List.filter (fun (hp,_) -> not (CP.mem_svl hp non_dang_hps)) is.Cformula.is_dang_hpargs ;
    Cformula.is_link_hpargs = List.filter (fun (hp,_) -> not (CP.mem_svl hp non_dang_hps)) is.Cformula.is_link_hpargs ;
    Cformula.is_hp_equivs = new_equivs@unk_equivs;
    CF.is_hp_defs = is.CF.is_hp_defs@hp_defs2;
  }

let infer_pre_synthesize prog proc_name callee_hps is pre_constrs need_preprocess detect_dang=
  let pr1 = Cprinter.string_of_infer_state_short in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_2 "infer_pre_synthesize" pr1 pr2 pr1
    (fun _ _ -> infer_pre_synthesize_x prog proc_name callee_hps is pre_constrs need_preprocess detect_dang)
    is pre_constrs

(*compute greatest fixpoint for each set of constraints*)
let infer_pre_fix_x iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang pre_fix_hps=
  (***********INTENAL*************)
  (* let get_pre_fwd post_hps pre_fix_pdefs= *)
  (*   let pre_fix_pdefs_ext = List.map (fun (hp,args,f) -> *)
  (*       (hp,args, [], CP.mkTrue no_pos, Some f, None, None) *)
  (*   ) pre_fix_pdefs in *)
  (*   Sautil.get_pre_fwd post_hps pre_fix_pdefs_ext *)
  (* in *)
  let unk_hps = List.map fst (is.Cformula.is_dang_hpargs@is.Cformula.is_link_hpargs) in
  let do_subst_pre pre_fix_pdefs_grp pre_def_grps=
    let groups0 = List.map  (fun (hp, args, f) -> (hp,args, None, f, [])) pre_fix_pdefs_grp in
    (* let groups1 = pardef_subst_fix prog unk_hps (groups0@pre_def_grps) in *)
    let groups1 = List.fold_left (fun r pdef_f ->
        let b, new_pdefs = Sautil.succ_subst prog pre_def_grps unk_hps false pdef_f in
        if b then r@new_pdefs else r@[pdef_f]
      ) [] groups0 in
    (*filter out groups of pre-preds which defined already*)
    (* let groups2 =  List.fold_left (fun r_grps grp -> *)
    (*     match grp with *)
    (*       | [] -> r_grps *)
    (*       | ((hp,_,_,_,_)::_) -> *)
    (*             (\* if not (CP.mem_svl hp predef_hps) then *\) *)
    (*             let grp1 = List.map (fun (hp,args,_,f,_) -> (hp,args,f)) grp in *)
    (*             r_grps@[grp1] *)
    (*                 (\* else *\) *)
    (*                 (\*   r_grps *\) *)
    (* ) [] groups1 in *)
    List.map (fun (hp,args,_,f,_) -> (hp,args,f)) groups1
  in
  let () = DD.info_ihprint(add_str ">>>>>> gfp computation for pre-preds <<<<<"
                             pr_id) "" no_pos in
  let rec partition_grp rem_pdefs grps=
    match rem_pdefs with
    | [] -> grps
    | (hp0,args0, f0)::rest ->
      let grp,rest = List.partition (fun (hp1,_, _) ->
          CP.eq_spec_var hp0 hp1
        ) rest in
      partition_grp rest (grps@[((hp0,args0, f0)::grp)])
  in
  let rec pair_pre_fix_defined_pdefs pre_fix defined_pdefs defined_defs res=
    match  pre_fix with
    | [] -> res
    | (pdefs)::rest -> begin
        match pdefs with
        | ((hp,_,_)::_) -> begin
            try
              let predefined = List.find (fun pdefs1 -> match pdefs1 with
                  | (hp1,_,_)::_ -> CP.eq_spec_var hp hp1
                  | _ -> false
                ) defined_pdefs in
              let predef = do_subst_pre predefined defined_defs in
              pair_pre_fix_defined_pdefs rest defined_pdefs defined_defs (res@[(pdefs, predef)])
            with _ -> pair_pre_fix_defined_pdefs rest defined_pdefs defined_defs (res@[(pdefs,[])])
          end
        | _ -> pair_pre_fix_defined_pdefs rest defined_pdefs defined_defs res
      end
  in
  (********END**********)
  (*partition constraints*)
  let pdefs0,tmp_pdefs = get_par_defs_pre_fix pre_fix_hps is.CF.is_post_hps is.CF.is_constrs in
  (*subst defined preds if applicable - swl.ss*)
  (* let pre_hps_need_fwd= get_pre_fwd is.Cformula.is_post_hps pdefs0 in *)
  (* let pre_defs, pre_hps = Sautil.extract_fwd_pre_defs pre_hps_need_fwd is.CF.is_hp_defs in *)
  let defs = List.map (fun def ->
      let hp,args = CF.extract_HRel def.CF.def_lhs in
      List.fold_left (fun r (f,og) ->
          r@(List.map (fun f1 -> (hp,args, og, f1, [])
                      ) (CF.list_of_disjs f))
        ) [] def.CF.def_rhs
    ) is.CF.is_hp_defs in
  let pdefs_grps0 = partition_grp pdefs0 [] in
  let defined_pdefs_grps0 = partition_grp tmp_pdefs [] in
  let pdefs_fix_pre_grps0 = pair_pre_fix_defined_pdefs pdefs_grps0 defined_pdefs_grps0 defs [] in
  (* let pdefs_grps1 = do_subst_pre pdefs_grps0 pre_hps pre_defs in *)
  (*for each set of constraints, compure greatest fixpoint*)
  let fix_defs, n_unk_hpargs = List.fold_left (fun (r_defs, r_unk_hpargs) (pdefs, defined_branches) ->
      let def, n_unk_hpargs = Sacore.compute_gfp prog true is defined_branches pdefs in
      (r_defs@[def], r_unk_hpargs@n_unk_hpargs)
    ) ([],[]) pdefs_fix_pre_grps0 (* pdefs_grps0 *) in
  let _, _, new_map = Sacore.generate_xpure_view_hp (List.map Sacore.build_args_locs n_unk_hpargs) is.CF.is_unk_map in
  let n_dang_hpargs, n_link_hpargs = if !Globals.pred_elim_dangling then
      (* dang predicate has at least one inst arg *)
      let n_dang_hps, n_link_hps = List.partition (fun (hp,args) ->
          let locs_i = Sautil.get_pos_of_hp_args_inst prog hp in
          let args_inst = Sautil.retrieve_args_from_locs args locs_i in
          args_inst != []
        ) n_unk_hpargs in
      (is.Cformula.is_dang_hpargs@n_dang_hps, is.Cformula.is_link_hpargs@n_link_hps)
    else (is.Cformula.is_dang_hpargs, is.Cformula.is_link_hpargs@n_unk_hpargs)
  in
  let () = DD.ninfo_hprint (add_str "  n_link_hpargs:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) n_link_hpargs no_pos in
  let () = DD.ninfo_hprint (add_str "  n_dang_hpargs:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) n_dang_hpargs no_pos in
  {is with CF.is_constrs = [];
           Cformula.is_dang_hpargs = n_dang_hpargs;
           Cformula.is_link_hpargs = n_link_hpargs;
           Cformula.is_unk_map = new_map;
           Cformula.is_hp_defs = is.Cformula.is_hp_defs@fix_defs
  }

let infer_pre_fix iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang pre_fix_hps=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_2 "infer_pre_fix" pr1 !CP.print_svl pr1
    (fun _ _ -> infer_pre_fix_x iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang pre_fix_hps)
    is pre_fix_hps

(*compute least fixpoint for each set of constraints*)
let infer_post_fix_x iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang post_fix_hps=
  let () = DD.info_ihprint (add_str ">>>>>> lfp computation for post-preds <<<<<"pr_id) "" no_pos in
  let rec partition_grp rem_pdefs grps=
    match rem_pdefs with
    | [] -> grps
    | (hp0,args0, f0)::rest ->
      let grp,rest = List.partition (fun (hp1,_, _) ->
          CP.eq_spec_var hp0 hp1
        ) rest in
      partition_grp rest (grps@[((hp0,args0, f0)::grp)])
  in
  (*partition constraints*)
  let pdefs,_ = get_par_defs_pre_fix [] is.CF.is_post_hps is.CF.is_constrs in
  let pdefs_grps = partition_grp pdefs [] in
  (*for each set of constraints, compure greatest fixpoint*)
  let dang_hps = List.map fst (is.Cformula.is_dang_hpargs@is.Cformula.is_link_hpargs) in
  let fix_defs = List.map (Sacore.compute_lfp prog dang_hps is.CF.is_hp_defs) pdefs_grps in
  {is with Cformula.is_constrs = [];
           Cformula.is_hp_defs = is.Cformula.is_hp_defs@fix_defs
  }

let infer_post_fix iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang post_fix_hps=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_2 "infer_post_fix" pr1 !CP.print_svl pr1
    (fun _ _ -> infer_post_fix_x iprog prog proc_name callee_hps is_pre is need_preprocess detect_dang post_fix_hps)
    is post_fix_hps

let infer_post_synthesize_x prog proc_name callee_hps is need_preprocess detect_dang=
  let constr0a = Sautil.remove_dups_constr is.CF.is_constrs in
  let () = DD.ninfo_hprint (add_str ">>>>>> post-predicates: step post-4: weaken<<<<<<" pr_id) "" no_pos in
  let () = DD.info_ihprint (add_str "   trivial ass of Post" pr_id) "" no_pos in
  let constrs0 = List.map (Sautil.weaken_strengthen_special_constr_pre false) constr0a in
  let dang_hps = List.map fst (is.Cformula.is_dang_hpargs@is.Cformula.is_link_hpargs) in
  (* let ss = List.filter (fun (hp1, hp2) -> CP.intersect_svl [hp1;hp2] dang_hps == []) is.Cformula.is_hp_equivs in *)
  (* let constrs1 = if ss = [] then constrs0 else *)
  (*   List.map (fun cs -> {cs with Cformula.hprel_lhs = x_add Cformula.subst ss cs.Cformula.hprel_lhs; *)
  (*       Cformula.hprel_rhs = x_add Cformula.subst ss cs.Cformula.hprel_rhs; *)
  (*   }) constrs0 *)
  (* in *)
  let constrs1 = Sautil.subst_equiv_hprel is.CF.is_hp_equivs constrs0 in
  let () = DD.info_ihprint (add_str "   Syn-Group-Post" pr_id) "" no_pos in
  let par_defs = get_par_defs_post constrs1 in
  (*subst pre-preds into if they are not recursive -do with care - not inlining the top guard*)
  let top_guard_hp_defs, pre_defs = List.partition (Sautil.is_top_guard_hp_def dang_hps) is.CF.is_hp_defs in
  let top_guard_hps = List.fold_left (fun r def ->
      match def.Cformula.def_cat with
      | CP.HPRelDefn (hp,_,_) -> r@[hp]
      | _ -> r
    ) [] top_guard_hp_defs in
  let pre_hps_need_fwd= CP.diff_svl (Sautil.get_pre_fwd is.CF.is_post_hps par_defs) top_guard_hps in
  let pre_defs, pre_hps = Sautil.extract_fwd_pre_defs pre_hps_need_fwd pre_defs in
  let () = DD.info_ihprint (add_str "   Syn-Post-Def" pr_id) "" no_pos in
  let pair_names_defs = generalize_hps_par_def prog false [] is.Cformula.is_dang_hpargs (List.map fst is.Cformula.is_link_hpargs) is.Cformula.is_post_hps
      pre_defs pre_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
  let n_hp_defs = is.Cformula.is_hp_defs@hp_defs in
  let post_defs1,unify_equiv_map2 = if !Globals.pred_unify_post then
      Sacore.do_unify prog false (List.map fst is.CF.is_dang_hpargs) (List.map fst is.CF.is_link_hpargs)
        is.Cformula.is_post_hps n_hp_defs
    else
      (n_hp_defs, [])
  in
  (*consj_post_unify??*)
  (* let dang_hps = List.map fst (is.Cformula.is_dang_hpargs@is.Cformula.is_link_hpargs) in *)
  (* let ss = List.filter (fun (hp1, hp2) -> CP.intersect_svl [hp1;hp2] dang_hps == []) is.Cformula.is_hp_equivs in *)
  (* let n_hp_defs1 = if ss = [] then n_hp_defs else *)
  (*   List.map (fun (a,hf,g, def) -> let f = x_add Cformula.subst ss def in *)
  (*   let fs = Cformula.list_of_disjs f in *)
  (*   let _, args = Cformula.extract_HRel hf in *)
  (*   let fs1 = Gen.BList.remove_dups_eq (Sautil.check_relaxeq_formula args) fs in *)
  (*   (a,hf,g, Cformula.disj_of_list fs1 (Cformula.pos_of_formula def))) n_hp_defs *)
  (* in *)

  (*move to infer_shape_proper for more general*)
  (* let post_defs2,tupled_defs = Sautil.partition_tupled post_defs1 in *)
  (* (\*before inlining, we try do inter-unify*\) *)
  (* let post_defs2a = if !Globals.pred_unify_inter then Sacore.pred_unify_inter prog dang_hps post_defs2 else  post_defs2 in *)
  (* let post_defs3 = def_subst_fix prog dang_hps (post_defs2a@top_guard_hp_defs) in *)
  (* simplify *)
  let post_defs2 = Sacore.simplify_def prog post_defs1 in
  {is with Cformula.is_constrs = [];
           Cformula.is_hp_equivs = is.Cformula.is_hp_equivs@unify_equiv_map2;
           Cformula.is_hp_defs = post_defs2@top_guard_hp_defs (* post_defs3@tupled_defs *)}

let infer_post_synthesize prog proc_name callee_hps is need_preprocess detect_dang=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_post_synthesize" pr1 pr1
    (fun _ -> infer_post_synthesize_x prog proc_name callee_hps is need_preprocess detect_dang) is

(*for each oblg generate new constrs with new hp post in rhs*)
(*call to infer_shape? proper? or post?*)
let rec infer_shapes_from_fresh_obligation_x iprog cprog iflow proc_name callee_hps is_pre is sel_lhps sel_rhps need_preprocess detect_dang def_hps=
  let unk_hps = List.map fst (is.CF.is_dang_hpargs@is.CF.is_link_hpargs) in
  (*if rhs is emp heap, should retain the constraint*)
  let pre_constrs, pre_oblg = List.partition (fun cs -> Cfutil.is_empty_heap_f cs.CF.hprel_rhs) is.CF.is_constrs in
  let ho_constrs0, nondef_post_hps  = List.fold_left (collect_ho_ass iprog cprog is_pre def_hps unk_hps) ([],[]) pre_oblg in
  let ho_constrs = ho_constrs0@pre_constrs in
  if ho_constrs = [] then is else
    (***************  PRINTING*********************)
    let () =  if !VarGen.sap then
        begin
          let pr = pr_list_ln Cprinter.string_of_hprel_short in
          print_endline_quiet "";
          print_endline_quiet "\n*************************************************";
          print_endline_quiet "*******relational assumptions (obligation)********";
          print_endline_quiet "****************************************************";
          print_endline_quiet (pr ho_constrs0);
          print_endline_quiet "*************************************"
        end;
    in
    let () = if !VarGen.sap then
        begin
          let pr = pr_list_ln Cprinter.string_of_hprel_short in
          print_endline_quiet "";
          print_endline_quiet "\n*************************************************";
          print_endline_quiet "*******relational assumptions (pre-assumptions)********";
          print_endline_quiet "****************************************************";
          print_endline_quiet (pr pre_constrs);
          print_endline_quiet "*************************************"
        end;
    in
    (***************  END PRINTING*********************)
    let new_sel_hps = (CP.diff_svl (is.Cformula.is_post_hps@sel_rhps) nondef_post_hps) in
    let is1 = infer_init iprog cprog proc_name is.Cformula.is_cond_path ho_constrs callee_hps (sel_lhps@sel_rhps)
        (*post-preds in lhs which dont have ad definition should be considered as pre-preds*)
        new_sel_hps
        is.Cformula.is_unk_map 
        (List.filter (fun (hp,_) -> not (CP.mem_svl hp new_sel_hps)) is.Cformula.is_dang_hpargs)
        (List.filter (fun (hp,_) -> not (CP.mem_svl hp new_sel_hps)) is.Cformula.is_link_hpargs )
        need_preprocess detect_dang iflow
    in
    let is2 = x_add infer_core iprog cprog proc_name callee_hps is1 need_preprocess detect_dang in
    {is2 with Cformula.is_constrs = [];
              Cformula.is_hp_defs = is.Cformula.is_hp_defs@is2.Cformula.is_hp_defs;
    }

and infer_shapes_from_fresh_obligation iprog cprog iflow proc_name callee_hps
    is_pre is sel_lhps sel_rhps need_preprocess detect_dang def_hps=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_shapes_from_fresh_obligation" pr1 pr1
    (fun _ -> infer_shapes_from_fresh_obligation_x iprog cprog iflow proc_name callee_hps is_pre is sel_lhps sel_rhps need_preprocess detect_dang def_hps) is

and infer_shapes_from_obligation_x iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang=
  (*******************INTERNAL********************)
  let def_hps = List.fold_left (fun ls d ->
      match d.Cformula.def_cat with
      |  CP.HPRelDefn (hp,_,_) -> ls@[hp]
      | CP.HPRelLDefn hps -> ls@hps
      | _ -> ls
    ) [] is.Cformula.is_hp_defs in
  let back_up_state ()=
    (* let cur_ass = ass_stk# get_stk in *)
    (* let () = ass_stk # reset in *)
    let cur_hpdefs =  CF.rel_def_stk # get_stk in
    let () = CF.rel_def_stk # reset in
    let cur_ihpdcl = iprog.Iast.prog_hp_decls in
    let cur_chpdcl = prog.Cast.prog_hp_decls in
    let cviews =  prog.Cast.prog_view_decls in
    let iviews =  iprog.Iast.prog_view_decls in
    let gen_sleek_file = !Globals.sa_gen_slk in
    let () = Globals.sa_gen_slk := false in
    (cur_hpdefs, cur_ihpdcl, cur_chpdcl, cviews, iviews, gen_sleek_file)
  in
  let restore_state (cur_hpdefs, cur_ihpdcl, cur_chpdcl, cviews, iviews, gen_sleek_file)=
    (* let () = ass_stk # reset in *)
    (* let () = ass_stk # push_list cur_ass in *)
    let () = CF.rel_def_stk # reset in
    let () = CF.rel_def_stk # push_list cur_hpdefs in
    let idiff = Gen.BList.difference_eq Iast.cmp_hp_def cur_ihpdcl iprog.Iast.prog_hp_decls in
    let () = iprog.Iast.prog_hp_decls <- (iprog.Iast.prog_hp_decls@idiff) in
    let cdiff = Gen.BList.difference_eq Cast.cmp_hp_def cur_chpdcl prog.Cast.prog_hp_decls in
    let () = prog.Cast.prog_hp_decls <- (prog.Cast.prog_hp_decls@cdiff) in
    let () = prog.Cast.prog_view_decls <- cviews in
    (* let () = iprog.Iast.prog_view_decls in *)
    let () = Globals.sa_gen_slk := gen_sleek_file in
    ()
  in
  let classify_hps (r_lhs, r_rhs, dep_def_hps, r_oblg_constrs,r_rem_constrs) cs=
    let lhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
    let rhs_hps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_rhs in
    let dep_define_hps1, rem_lhs = List.partition (fun hp -> CP.mem_svl hp def_hps) lhs_hps in
    let dep_define_hps2, rem_rhs = List.partition (fun hp -> CP.mem_svl hp def_hps) rhs_hps in
    if (* (rem_lhs = [] && rem_rhs=[]) || *)(is_pre && rem_rhs = [] && rem_lhs = []) ||
                                            ((not is_pre) && (rem_lhs <> [])) then
      (r_lhs, r_rhs, dep_def_hps, r_oblg_constrs, r_rem_constrs@[cs])
    else
      (r_lhs@rem_lhs, r_rhs@rem_rhs, dep_def_hps@dep_define_hps1@dep_define_hps2,r_oblg_constrs@[cs], r_rem_constrs)
  in
  (****************END INTERNAL********************)
  let constrs0 = is.Cformula.is_constrs in
  let unk_hps = List.map fst (is.CF.is_dang_hpargs@is.CF.is_link_hpargs) in
  if constrs0 = [] then is else
    let settings = back_up_state () in
    let constrs1 = Sautil.remove_dups_constr constrs0 in
    (*the remain contraints will be treated as tupled ones.*)
    let sel_lhs_hps, sel_rhs_hps, dep_def_hps, oblg_constrs, rem_constr = List.fold_left classify_hps ([],[],[],[],[]) constrs1 in
    if oblg_constrs = [] then
      let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in
      DD.info_ihprint (add_str "proving:\n" pr1) rem_constr no_pos;
      let () = if rem_constr = [] then () else
          (*prove rem_constr*)
          (*transform defs to cviews*)
          let need_trans_hprels = List.filter (fun d ->
              match d.Cformula.def_cat with
              |  CP.HPRelDefn (hp,_,_) -> (* CP.mem_svl hp dep_def_hps *) true
              | _ -> false
            ) is.Cformula.is_hp_defs in
          let () = DD.ninfo_hprint (add_str "dep_def_hps" !CP.print_svl) dep_def_hps no_pos in
          let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog prog proc_name need_trans_hprels in
          let in_hp_names = List.map CP.name_of_spec_var dep_def_hps in
          (*for each oblg, subst + simplify*)
          let rem_constr2 = Sacore.trans_constr_hp_2_view iprog prog proc_name is.CF.is_hp_defs
              in_hp_names chprels_decl rem_constr in
          let todo_unk = List.fold_left (fun (r1,r2) cs ->
              collect_ho_ass iprog prog is_pre def_hps unk_hps (r1,r2) cs
            ) ([],[]) rem_constr2 in
          ()
      in
      let _  = restore_state settings in
      (*do revert view --> defined hprel if applicable (in_hp_names) ??? *)
      is
    else
      (* let () = DD.info_pprint ("dep_def_hps: " ^ (!CP.print_svl dep_def_hps)) no_pos in *)
      let need_trans_hprels, over_hpdefs = List.fold_left (fun (r1,r2) d ->
          match d.Cformula.def_cat with
          |  CP.HPRelDefn (hp,_,_) ->
            if CP.mem_svl hp dep_def_hps then
              if List.exists (fun (f,_) -> Cfutil.is_heap_conjs f) d.CF.def_rhs then
                (r1, r2@[hp])
              else (r1@[d], r2)
            else (r1,r2)
          | _ -> r1,r2
        ) ([],[]) is.CF.is_hp_defs in
      let () = DD.ninfo_hprint (add_str "over_hpdefs: " !CP.print_svl) over_hpdefs no_pos in
      let oblg_constrs1, overlap_oblg = List.partition (fun cs ->
          let hps = (CF.get_hp_rel_name_formula cs.CF.hprel_lhs)@(CF.get_hp_rel_name_formula cs.CF.hprel_rhs) in
          (CP.intersect_svl hps over_hpdefs) = []
        ) oblg_constrs in
      (*transform defs to cviews*)
      let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog prog proc_name need_trans_hprels in
      let in_hp_names = List.map CP.name_of_spec_var dep_def_hps in
      (*for each oblg, subst + simplify*)
      let constrs2 = Sacore.trans_constr_hp_2_view iprog prog proc_name is.CF.is_hp_defs
          in_hp_names chprels_decl oblg_constrs1 in
      (*for each oblg generate new constrs with new hp post in rhs*)
      (*call to infer_shape? proper? or post?*)
      let is1 = {is with Cformula.is_constrs = constrs2;} in
      let n_is=
        let r = infer_shapes_from_fresh_obligation iprog prog iflow proc_name callee_hps
            is_pre is1 sel_lhs_hps sel_rhs_hps need_preprocess detect_dang def_hps in
        r
      in
      let pr1 = pr_list_ln  Cprinter.string_of_hprel_short in
      DD.info_ihprint (add_str "rem_constr:\n" pr1) rem_constr no_pos;
      let _  = restore_state settings in
      (*do revert view --> defined hprel if applicable (in_hp_names) *)
      let n_is = {n_is with Cformula.is_hp_defs = Saout.trans_hp_def_view_2_hp iprog prog proc_name in_hp_names n_is.Cformula.is_hp_defs} in
      if rem_constr = [] then
        (*return*)
        n_is
      else
        (*loop*)
        let n_is1 = {n_is with Cformula.is_constrs = rem_constr;} in
        let n_is2 = infer_shapes_from_obligation iprog prog iflow proc_name callee_hps is_pre n_is1 need_preprocess detect_dang in
        n_is2

and infer_shapes_from_obligation iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_shapes_from_obligation" pr1 pr1
    (fun _ -> infer_shapes_from_obligation_x iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang) is

(*===========fix point==============*)
and infer_process_pre_preds iprog prog proc_name callee_hps b_is_pre is (pre_fix_hps, pre_oblg_constrs0)
    need_preprocess detect_dang =
  let () = DD.info_ihprint (add_str ">>>>>>PRE" pr_id) " derive predicates for pre-predicates<<<<<<" no_pos in
  DD.info_ihprint (add_str ">>>>>> Sorting and Syn-Norm-Conseq <<<<<<" pr_id) "" no_pos;
  (*************INTERNAL**************)
  (***************END*******************)
  let sel_hps = is.Cformula.is_sel_hps in
  let post_hps = is.Cformula.is_post_hps in
  let dang_hps = List.map fst is.Cformula.is_dang_hpargs in
  let link_hps = List.map fst is.Cformula.is_link_hpargs in
  let ignore_hps = dang_hps@link_hps in
  (*find equal pre-preds: has one assumption.
    in the new algo, those will be generalized as equiv. do not need to substed
  *)
  (*frozen_hps: they have been synthesized already*)
  let rec helper_x is frozen_hps frozen_constrs pre_oblg_constrs0 =
    let constrs = is.Cformula.is_constrs in
    begin
      let equal_cands, complex_hps,rem_constrs = x_add IC.icompute_action_pre constrs post_hps frozen_hps pre_fix_hps in
      let equal_hps, new_frozen_constrs = List.fold_left (fun (ls1,ls2) (hp, constrs) -> ls1@[hp], ls2@constrs)
          ([],[]) equal_cands
      in
      let n_is1, frozen_constrs1,pre_oblg_constrs = if equal_hps <> [] then
          let () = DD.info_ihprint (add_str " sorted. next pred" !CP.print_svl) equal_hps no_pos in
          let pre_act = IC.igen_action_pre equal_hps new_frozen_constrs in
          let is1 = {is with Cformula.is_constrs = rem_constrs} in
          let n_is = x_add iprocess_action iprog prog proc_name callee_hps is1 pre_act need_preprocess detect_dang in
          (*">>>>>> Syn-Norm-Ante (UNFOLD IN LHS)<<<<<<"*)
          (*pred-constrs*)
          let _, rem_constrs1 = unfold_def_LHS prog ignore_hps n_is.Cformula.is_constrs equal_hps n_is.Cformula.is_hp_defs in
          (*pred-oblg*)
          (* let () = DD.info_ihprint (add_str ">>>>>> xxxxx 0 (UNFOLD IN RHS) <<<<<<" pr_id) "" no_pos in *)
          let _, pre_oblg_constrs1 = unfold_def_LHS prog ignore_hps pre_oblg_constrs0 equal_hps n_is.Cformula.is_hp_defs in
          let n_is1 = {n_is with CF.is_constrs = rem_constrs1} in
          (n_is1, frozen_constrs@new_frozen_constrs, pre_oblg_constrs1)
        else is,frozen_constrs,pre_oblg_constrs0
      in
      let frozen_hps0 = frozen_hps@equal_hps in
      (* second phases *)
      if equal_hps = [] then
        (*stop*)
        let n_is2,pre_oblg_constrs2 =  if complex_hps <> [] then
            let () = DD.info_ihprint (add_str " sorted (complex). next pred" !CP.print_svl) complex_hps no_pos in
            let is_not_in_complex complex_hps cs=
              let lhps = Cformula.get_hp_rel_name_formula cs.Cformula.hprel_lhs in
              if List.length lhps<2 && CP.intersect_svl lhps complex_hps = [] then true else false
            in
            let _, constrs1,_  = subst_cs prog sel_hps post_hps dang_hps link_hps (frozen_hps@equal_hps)
                (frozen_constrs1) complex_hps constrs in
            let pre_oblg_constrsa, complex_constrs = List.partition (is_not_in_complex complex_hps) constrs1 in
            let pre_act = IC.igen_action_pre complex_hps complex_constrs in
            let n_is11 = {n_is1 with Cformula.is_constrs = pre_oblg_constrsa} in
            let n_is12 = x_add iprocess_action iprog prog proc_name callee_hps n_is11 pre_act need_preprocess detect_dang in
            (*">>>>>> Syn-Norm-Ante (UNFOLD IN LHS)<<<<<<"*)
            (*pred-constrs*)
            let _, rem_constrs1 = unfold_def_LHS prog ignore_hps n_is12.Cformula.is_constrs complex_hps n_is12.Cformula.is_hp_defs in
            (*pred-oblg*)
            (* let () = DD.info_ihprint (add_str ">>>>>> xxxxx 1 (UNFOLD IN RHS) <<<<<<" pr_id) "" no_pos in *)
            let _, pre_oblg_constrs1 = unfold_def_LHS prog ignore_hps pre_oblg_constrs complex_hps n_is12.Cformula.is_hp_defs in
            let n_is13 = {n_is12 with  Cformula.is_constrs = rem_constrs1} in
            (n_is13,pre_oblg_constrs1)
          else n_is1,pre_oblg_constrs
        in
        (* (constrs,[]) *)
        (n_is2,[],pre_oblg_constrs2)
      else
        let () = if !VarGen.sap then DD.info_ihprint (add_str ">>>>>> Syn-Norm-Conseq (UNFOLD IN RHS- FROZEND) <<<<<<" pr_id) "" no_pos else () in
        (*pred-constrs*)
        let is_changed, constrs2,unfrozen_hps  = subst_cs prog sel_hps post_hps dang_hps link_hps (frozen_hps@equal_hps)
            (frozen_constrs1)
            complex_hps n_is1.Cformula.is_constrs in
        (*pred-oblg*)
        (* let () = DD.info_ihprint (add_str ">>>>>> xxxxx  2  <<<<<<" pr_id) "" no_pos in *)
        let is_changed2, pre_oblg_constrs2,unfrozen_hps2  = subst_cs prog sel_hps post_hps dang_hps link_hps (frozen_hps@equal_hps)
            (frozen_constrs1)
            complex_hps pre_oblg_constrs in
        let () = DD.ninfo_hprint (add_str "  pre_oblg_constrs2:" (pr_list_ln Cprinter.string_of_hprel_short)) pre_oblg_constrs2 no_pos in
        let unfrozen_hps1 = CP.remove_dups_svl (CP.intersect_svl unfrozen_hps frozen_hps0) in
        let frozen_hps1 = CP.diff_svl frozen_hps0 unfrozen_hps1 in
        let () = if unfrozen_hps1 <> [] then
            x_binfo_pp (" unfreeze: " ^ (!CP.print_svl unfrozen_hps) )no_pos
          else ()
        in
        (*for debugging*)
        let () = DD.ninfo_hprint (add_str "   new constrs:" (pr_list_ln Cprinter.string_of_hprel_short)) constrs2 no_pos in
        let helper is frozen_hps frozen_constrs pre_oblg_constrs=
          let pr = Cprinter.string_of_infer_state_short in
          Debug.no_1 "infer_process_pre_preds" pr (fun (is,_,_) -> pr is)
            (fun _ -> helper_x is frozen_hps frozen_constrs pre_oblg_constrs) is
        in
        (*END for debugging*)
        let n_is3, non_unk_hps1,pre_oblg_constrs3 =
          let constrs3 = if is_changed then constrs2 else n_is1.Cformula.is_constrs in
          (* helper new_cs2 constrs2 (frozen_hps@equal_hps) in *)
          let n_is = {n_is1 with Cformula.is_constrs = constrs3} in
          helper n_is frozen_hps1 frozen_constrs1 pre_oblg_constrs2
        in
        (* (norm_constrs,[]) *)
        (n_is3, [],pre_oblg_constrs3)
    end
  in
  let () = DD.info_ihprint (add_str "   is:"  Cprinter.string_of_infer_state_short) is no_pos in
  let r_is,a,n_pre_oblg_constrs = helper_x is [] [] pre_oblg_constrs0 in
  let () = DD.info_ihprint (add_str "   r_is:" Cprinter.string_of_infer_state_short) r_is no_pos in
  let () = DD.ninfo_hprint (add_str "  pre_oblg_constrs0:" (pr_list_ln Cprinter.string_of_hprel_short)) pre_oblg_constrs0 no_pos in
  let () = DD.ninfo_hprint (add_str "  n_pre_oblg_constrs:" (pr_list_ln Cprinter.string_of_hprel_short)) n_pre_oblg_constrs no_pos in
  (* let hp_defs1a,tupled_defs = Sautil.partition_tupled r_is.CF.is_hp_defs in *)
  (* let top_guard_hpdefs, hp_defs1 = List.partition (Sautil.is_top_guard_hp_def (dang_hps@link_hps)) hp_defs1a in *)
  (* let r_is1 = {r_is with Cformula.is_hp_defs = (def_subst_fix prog (dang_hps@link_hps) hp_defs1)@top_guard_hpdefs@tupled_defs } in *)
  (r_is,a,n_pre_oblg_constrs)

(* and infer_pre_trans_closure prog is= *)
(*   let n_constrs,_ = infer_pre_preds prog is.Cformula.is_post_hps [] *)
(*     (List.map fst is.Cformula.is_dang_hpargs) *)
(*     (List.map fst is.Cformula.is_link_hpargs) is.Cformula.is_constrs *)
(*   in *)
(*   { is with *)
(*       Cformula.is_constrs = n_constrs; *)
(*   } *)

and infer_shapes_norm_seg_x iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang=
  let defs = is.CF.is_hp_defs in
  let defs1 = Sacore.pred_norm_seg iprog prog (IC.get_unk_hps is) defs in
  {is with CF.is_hp_defs = defs1 }

and infer_shapes_norm_seg iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang=
  let pr1 = Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_shapes_norm_seg" pr1 pr1
    (fun _ -> infer_shapes_norm_seg_x iprog prog iflow proc_name callee_hps is_pre is need_preprocess detect_dang) is

and infer_shapes_proper_x iprog prog proc_name callee_hps is need_preprocess detect_dang=
  let unk_hps = List.map fst is.Cformula.is_dang_hpargs in
  let link_hps = List.map fst is.Cformula.is_link_hpargs in
  let () = DD.ninfo_hprint (add_str "unk_hps" !CP.print_svl) unk_hps no_pos in
  let () = DD.ninfo_hprint (add_str "link_hps" !CP.print_svl) link_hps no_pos in
  (*partition constraints into 4 groups: pre-predicates, pre-oblg,post-predicates, post-oblg*)
  let pre_constrs,post_constrs0, pre_fix_constrs, pre_oblg_constrs0, post_oblg_constrs, pre_fix_hps =
    partition_constrs is.Cformula.is_constrs is.Cformula.is_post_hps (unk_hps@link_hps)
  in
  let post_hps1 = is.Cformula.is_post_hps in
  (*pre-synthesize*)
  (*need to pass pre_oblg_constrs0 for closure computation*)
  let is_pre = {is with Cformula.is_constrs = pre_constrs(* @pre_oblg_constrs0 *);
                        Cformula.is_post_hps = post_hps1;
               } in
  (*need to pass pre_oblg_constrs0 for closure computation*)
  let is_pre0, _, pre_oblg_constrs1a=  infer_process_pre_preds iprog prog proc_name callee_hps true is_pre (pre_fix_hps, pre_oblg_constrs0)
      need_preprocess detect_dang in
  let pre_oblg_constrs1, new_pre_fix_constrs = Sacore.reclassify_pre_obligation prog is_pre0 pre_fix_hps pre_oblg_constrs1a in
  let is_pre1 = {is_pre0 with CF.is_constrs = List.map (Sautil.simp_match_unknown unk_hps link_hps) is_pre0.CF.is_constrs} in
  (*pre-fix-synthesize*)
  let pre_fix_constrs = pre_fix_constrs@new_pre_fix_constrs in
  let is_pre2 = if pre_fix_constrs = [] then is_pre1 else
      let is_pre_fix =  {is_pre1 with Cformula.is_constrs = pre_fix_constrs} in
      let pre_fix_act = x_add_1 IC.icompute_action_pre_fix pre_fix_hps in
      x_add iprocess_action iprog prog proc_name callee_hps is_pre_fix pre_fix_act need_preprocess detect_dang
  in
  (*pre-oblg*)
  (* let () = DD.info_ihprint (add_str "PRE-OBLG" pr_id) "" no_pos in *)
  (* let () = DD.ninfo_hprint (add_str "  pre_oblg_constrs1:" (pr_list_ln Cprinter.string_of_hprel_short)) pre_oblg_constrs1 no_pos in *)
  let is_pre_oblg1 = if (* is_pre1.Cformula.is_constrs *)pre_oblg_constrs1 = [] then is_pre2
    else
      (*unknown preds generated during gfp have a chance to inferred here*)
      let pre_fix_unk_hpargs = if !Globals.pred_elim_dangling then
          (Gen.BList.difference_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is_pre2.Cformula.is_dang_hpargs is_pre1.Cformula.is_dang_hpargs)
        else
          (Gen.BList.difference_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is_pre2.Cformula.is_link_hpargs is_pre1.Cformula.is_link_hpargs)
      in
      let () = DD.ninfo_hprint (add_str " pre_fix_unk_hpargs" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) pre_fix_unk_hpargs no_pos in
      let is_pre_oblg =  {is_pre2 with Cformula.is_constrs = pre_oblg_constrs1;
                                       (* Cformula.is_dang_hpargs = is_pre1.Cformula.is_dang_hpargs; *)
                                       (* Cformula.is_link_hpargs = is_pre1.Cformula.is_link_hpargs; *)
                         } in
      let () = DD.info_ihprint (add_str "PRE-OBLG" pr_id) "" no_pos in
      let pre_obl_act = IC.icompute_action_pre_oblg () in
      x_add iprocess_action iprog prog proc_name callee_hps is_pre_oblg pre_obl_act need_preprocess detect_dang
  in
  let is_pre3 = is_pre_oblg1 in
  let () = DD.ninfo_hprint (add_str "   is_pre3.Cformula.is_link_hpargs 2:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) is_pre3.Cformula.is_link_hpargs no_pos in
  (*post-synthesize*)
  let () = DD.info_ihprint (add_str ">>>>>>POST" pr_id) " derive predicates for post-predicates<<<<<<" no_pos in
  let post_constrs, post_fix_hps, post_fix_constrs = Sautil.classify_post_fix post_constrs0 in
  let is_post1 = if post_constrs =[] then is_pre3 else
      let is_post = {is_pre3 with Cformula.is_constrs = post_constrs } in
      let post_act = IC.icompute_action_post () in
      let is_post = x_add iprocess_action iprog prog proc_name callee_hps is_post post_act need_preprocess detect_dang in
      is_post
  in
  (*post-fix-synthesize*)
  let is_post2a = if post_fix_constrs = [] then is_post1 else
      let is_post_fix = {is_post1 with Cformula.is_constrs = post_fix_constrs} in
      let post_fix_act = IC.icompute_action_post_fix post_fix_hps in
      x_add iprocess_action iprog prog proc_name callee_hps is_post_fix post_fix_act need_preprocess detect_dang
  in
  let is_post2 =
    let dang_hps = unk_hps@link_hps in
    let hp_defs1,tupled_defs = Sautil.partition_tupled is_post2a.CF.is_hp_defs in
    (*before inlining, we try do inter-unify*)
    let hp_defs2 = if !Globals.pred_unify_inter then Sacore.pred_unify_inter prog dang_hps hp_defs1 else hp_defs1 in
    let hp_defs3 = if not !Globals.sae then
        def_subst_fix prog is_post2a.CF.is_post_hps dang_hps is_post2a.CF.is_prefix_hps (hp_defs2)
      else (hp_defs2)
    in
    let hp_defs4 = List.map (fun def ->
        let hp0,args0 = CF.extract_HRel def.CF.def_lhs in
        if CP.mem_svl hp0 is_post2a.CF.is_sel_hps then
          let n_rhs = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) -> Sautil.check_relaxeq_formula args0 f1 f2) def.CF.def_rhs in
          {def with CF.def_rhs = n_rhs}
        else def
      ) hp_defs3 in
    {is_post2a with CF.is_hp_defs = hp_defs3@tupled_defs}
  in
  (*post-oblg*)
  let is_post_oblg1 = if post_oblg_constrs = [] then is_post2
    else
      let () = DD.info_ihprint (add_str "POST-OBLG" pr_id) "" no_pos in
      let is_post_oblg = {is_post2 with Cformula.is_constrs = post_oblg_constrs } in
      let post_obl_act = IC.icompute_action_post_oblg () in
      x_add iprocess_action iprog prog proc_name callee_hps is_post_oblg post_obl_act need_preprocess detect_dang
  in
  let htrue_hpargs, defs2b = Sautil.convert_HTrue_2_None is_post_oblg1.CF.is_hp_defs in
  let defs2 = Sacore.generate_hp_def_from_unk_hps defs2b is_post_oblg1.CF.is_dang_hpargs
      (List.fold_left (fun ls d-> ls@(Cformula.get_hpdef_name_w_tupled d.Cformula.def_cat)) [] is_post_oblg1.Cformula.is_hp_defs)
      is_post_oblg1.Cformula.is_post_hps is_post_oblg1.Cformula.is_unk_map is_post_oblg1.Cformula.is_hp_equivs
  in
  let defs3,link_hpargs3 = if !Globals.pred_elim_dangling then
      let defs3a,remain_links = Sacore.transform_xpure_to_pure prog defs2 is_post_oblg1.CF.is_unk_map
          (is_post_oblg1.Cformula.is_link_hpargs@htrue_hpargs) in
      (*we have already transformed link/unk preds into pure form.
        Now return [] so that we do not need generate another unk preds*)
      (defs3a, remain_links@(List.filter (fun (hp,_) -> CP.mem_svl hp is_post_oblg1.CF.is_sel_hps) is_post_oblg1.CF.is_link_hpargs))
    else (Sacore.elim_dangling_conj_heap prog defs2 (List.map fst (is_post_oblg1.CF.is_link_hpargs@is_post_oblg1.CF.is_dang_hpargs@htrue_hpargs)),is_post_oblg1.CF.is_link_hpargs@htrue_hpargs)
  in
  let is_post = {is_post_oblg1 with Cformula.is_link_hpargs = link_hpargs3;
                      CF.is_prefix_hps = pre_fix_hps;
                      Cformula.is_hp_defs = defs3;
  }
  in
  if !Globals.pred_norm_seg then
    x_add iprocess_action iprog prog proc_name callee_hps is_post IC.I_norm_seg need_preprocess detect_dang
  else is_post

and infer_shapes_proper iprog prog proc_name callee_hps is need_preprocess detect_dang=
  let pr1= Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_shapes_proper" pr1 pr1
    (fun _ -> infer_shapes_proper_x iprog prog proc_name callee_hps is need_preprocess detect_dang)
    is
(***************************************************************
                     END PROCESS INFER ACTION
 ****************************************************************)
and iprocess_action_x iprog prog proc_name callee_hps is act need_preprocess detect_dang=
  let rec_fct l_is l_act = iprocess_action_x iprog prog proc_name callee_hps l_is l_act need_preprocess detect_dang in
  match act with
  | IC.I_pre_add_dangling -> failwith "to be implemented"
  | IC.I_infer_dang -> infer_analize_dang prog is
  (* | IC.I_pre_trans_closure -> infer_pre_trans_closure prog is *)
  | IC.I_split_base -> infer_split_base prog is
  | IC.I_partition -> infer_shapes_proper iprog prog proc_name callee_hps is need_preprocess detect_dang
  | IC.I_pre_synz (hps, constrs) -> infer_pre_synthesize prog proc_name callee_hps is constrs need_preprocess detect_dang
  | IC.I_pre_fix hps -> infer_pre_fix iprog prog proc_name callee_hps true is need_preprocess detect_dang hps
  | IC.I_pre_oblg -> infer_shapes_from_obligation iprog prog is.Cformula.is_flow proc_name callee_hps true is need_preprocess  detect_dang
  | IC.I_post_synz -> infer_post_synthesize prog proc_name callee_hps is need_preprocess detect_dang
  | IC.I_post_fix hps -> infer_post_fix iprog prog proc_name callee_hps false is need_preprocess detect_dang hps
  | IC.I_post_oblg -> infer_shapes_from_obligation iprog prog is.Cformula.is_flow proc_name callee_hps false is need_preprocess  detect_dang
  | IC.I_norm_seg -> infer_shapes_norm_seg iprog prog is.Cformula.is_flow proc_name callee_hps false is need_preprocess  detect_dang
  | IC.I_seq ls_act -> List.fold_left (fun is (_,act) -> rec_fct is act) is ls_act


and iprocess_action iprog prog proc_name callee_hps is act need_preprocess detect_dang=
  let pr1 = IC.string_of_iaction in
  let pr2 = Cprinter.string_of_infer_state in
  let pr3 = !CP.print_svl in
  Debug.no_3 "iprocess_action" (add_str "hps" pr3) pr1 pr2 pr2
    (fun _ _ _ -> iprocess_action_x iprog prog proc_name callee_hps is act need_preprocess detect_dang) callee_hps act is

and infer_init iprog prog proc_name cond_path constrs0 callee_hps sel_hps
    post_hps unk_map unk_hpargs0a link_hpargs need_preprocess detect_dang iflow =
  (* let prog_vars = [] in *) (*TODO: improve for hip*)
  (********************************)
  let unk_hpargs0b = List.fold_left (fun ls ((hp,_),xpure) ->
      let args = match xpure.CP.xpure_view_node with
        | None -> xpure.CP.xpure_view_arguments
        | Some r -> r::xpure.CP.xpure_view_arguments
      in
      ls@[(hp,args)]
    ) [] unk_map
  in
  let unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (unk_hpargs0a@unk_hpargs0b) in
  let is = IC.mk_is constrs0 constrs0 link_hpargs unk_hpargs unk_map sel_hps post_hps cond_path iflow [] [] in
  (* let act = IC.icompute_action_init need_preprocess detect_dang in *)
  (* iprocess_action iprog prog proc_name callee_hps is act need_preprocess detect_dang *)
  is

and infer_core_x iprog prog proc_name callee_hps is need_preprocess detect_dang =
  let act = IC.icompute_action_init need_preprocess detect_dang in
  x_add iprocess_action iprog prog proc_name callee_hps is act need_preprocess detect_dang

and infer_core iprog prog proc_name callee_hps is need_preprocess detect_dang =
  let pr1 = Cprinter.string_of_infer_state in
  let pr2 = !CP.print_svl in
  Debug.no_2 "infer_core" pr2 pr1 pr1
    (fun _ _ -> infer_core_x iprog prog proc_name callee_hps is need_preprocess detect_dang) 
    callee_hps is

let infer_shapes_divide_x iprog prog proc_name (constrs0: Cformula.hprel list) callee_hps sel_hps all_post_hps
    hp_rel_unkmap unk_hpargs0 link_hpargs_w_path need_preprocess detect_dang iflow =
  let rectify_type_root hp_def=
    match hp_def.Cformula.def_cat with
    | CP.HPRelDefn (hp,((CP.SpecVar (rt, r_id, rp)) as r),paras) -> begin
        match rt with
        | Named id -> if String.compare id "" = 0  then
            let svl = (Cformula.h_fv hp_def.Cformula.def_lhs)@(List.fold_left (fun l (f,_) -> l@(Cformula.fv f)) [] hp_def.Cformula.def_rhs) in
            let r_svl = List.filter (fun ((CP.SpecVar (rt1, r_id1, rp1))) ->
                String.compare r_id r_id1 = 0
              ) svl in
            if r_svl = [] then hp_def else
              let nr = (CP.SpecVar (CP.type_of_spec_var (List.hd r_svl), r_id, rp)) in
              let ss = [(r,nr)] in
              {hp_def with Cformula.def_cat = CP.HPRelDefn (hp,nr,paras);
                           Cformula.def_lhs = Cformula.h_subst ss hp_def.Cformula.def_lhs;
                           Cformula.def_rhs = List.map (fun (f,og) -> (x_add Cformula.subst ss f, og)) hp_def.Cformula.def_rhs;
              }
          else hp_def
        | _ -> hp_def
      end
    | _ -> hp_def
  in
  let process_one_path (cond_path, link_hpargs, constrs1)=
    let () = DD.ninfo_hprint (add_str "all_post_hps" !CP.print_svl) all_post_hps no_pos in
    (* let () = DD.info_hprint (add_str "sel_hps" !CP.print_svl) sel_hps no_pos in *)
    let is0 = infer_init iprog prog proc_name cond_path constrs1
        callee_hps sel_hps all_post_hps hp_rel_unkmap unk_hpargs0
        link_hpargs need_preprocess detect_dang iflow in
    let is = if !Globals.sa_syn then
        let is1a = x_add infer_core iprog prog proc_name callee_hps is0 need_preprocess detect_dang in
        let is1 = {is1a with CF.is_hp_defs = List.map rectify_type_root is1a.CF.is_hp_defs;
                             (* CF.is_sel_hps = sel_hps; *)
                             (* CF.is_post_hps = all_post_hps; *)
                  } in
        let unk_hps = List.map fst (is1.CF.is_dang_hpargs@is1.CF.is_link_hpargs) in
        let is2a = if !Globals.pred_elim_useless then
            (*detect and elim useless paramters*)
            {is1 with CF.is_hp_defs = Sacore.norm_elim_useless_paras prog
                          unk_hps (* (CP.remove_dups_svl is1.CF.is_sel_hps) *) sel_hps
                          all_post_hps is1.CF.is_hp_defs}
          else is1
        in
        let is2=
          if !pred_norm_overr then
            let n_hp_defs = Sacore.norm_overr is2a.is_hp_defs in
            {is2a with CF.is_hp_defs = n_hp_defs}
          else is2a
        in
        let post_hps = is2.CF.is_post_hps in
        let is3 = if not !Globals.pred_seg_unify then is2 else
            let hp_defs1 = is2.CF.is_hp_defs in
            let hp_defs2 = List.map (fun def ->
                match def.CF.def_cat with
                | CP.HPRelDefn (hp, r, args) ->
                  if CP.mem_svl hp post_hps then
                    let n_rhs = Sautil.norm_fold_seg prog hp_defs1 hp r args unk_hps def.CF.def_rhs in
                    let n_def = {def with CF.def_rhs = n_rhs} in
                    n_def
                  else def
                | _ -> def
              ) hp_defs1
            in
            {is2 with CF.is_hp_defs = hp_defs2}
        in
        (* is3 *)
        (* unfold view, if it is not rec *)
        let unfold_fnc f sv = Solver.unfold_nth 45 (prog, None) f sv true 0 no_pos in
        let helper f = Cfutil.unfold_non_rec_views prog unfold_fnc (Cast.is_rec_view_def prog) f in
        let hp_defs4 = List.map (fun def ->
            let n_def = match def.CF.def_cat with
              | CP.HPRelDefn (hp, r, args) ->
                if CP.mem_svl hp post_hps then
                  let n_rhs = List.map (fun (f, og) ->
                      helper f, og) def.CF.def_rhs in
                  let n_def = {def with CF.def_rhs = n_rhs} in
                  n_def
                else def
              | _ -> def
            in
            {def with CF.def_flow = Some iflow;}
          ) is3.CF.is_hp_defs
        in
        let is4 = {is3 with CF.is_hp_defs = hp_defs4 } in
        (* let () = print_endline ("is4: " ^ (Cprinter.string_of_infer_state_short is4)) in *)
        is4
      else
        (* let () =  print_endline (Cformula.string_of_cond_path is0.Cformula.is_cond_path) in *)
        is0
    in
    is
  in
  let ls_cond_danghps_constrs = if !Globals.sa_dnc then
      Sacore.partition_constrs_4_paths link_hpargs_w_path constrs0
    else if (* !Globals.sae *) false then
      Saerror.partition_constrs_4_paths link_hpargs_w_path constrs0 prog proc_name
    else
      let cond_path, link_hpargs1 =
        match link_hpargs_w_path with
        | [] -> ([],[])
        | _ -> ([],List.map snd link_hpargs_w_path)
      in
      [(cond_path, link_hpargs1,  constrs0)]
  in
  (*synthesize for each path*)
  let ls_res = List.map process_one_path ls_cond_danghps_constrs in
  (* let todo_unk = List.map (fun ls -> print_endline (Cprinter.string_of_infer_state_short ls)) ls_res in *)
  ls_res

let infer_shapes_divide iprog prog proc_name (constrs0: Cformula.hprel list) callee_hps sel_hps all_post_hps
    hp_rel_unkmap unk_hpargs0 link_hpargs_w_path need_preprocess detect_dang iflow=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln Cprinter.string_of_infer_state_short in
  Debug.no_1 "infer_shapes_divide" pr1 pr2
    (fun _ ->  infer_shapes_divide_x iprog prog proc_name (constrs0) callee_hps sel_hps all_post_hps
        hp_rel_unkmap unk_hpargs0 link_hpargs_w_path need_preprocess detect_dang iflow)
    constrs0

let infer_shapes_conquer_x iprog prog proc_name ls_is sel_hps iflow=
  (***********INTERNAL***************)
  (*globals_ubk_hps are dangling preds in all paths.
    if a pred is partial dangling, we should rename/remove it. it atributes to more precise subst/inlining
    in non-dangling branches.
  *)
  let process_path_defs_setting globals_unk_hps is =
    (* let () = print_endline ("Infer state before: " ^ (Cprinter.string_of_infer_state is)) in *)
    let dang_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is.Cformula.is_dang_hpargs in
    (* let todo_unk = List.map (fun (sp, spl) -> print_endline ("dang: " ^ (Cprinter.string_of_spec_var sp))) dang_hpargs in *)
    let link_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is.Cformula.is_link_hpargs in
    (* let todo_unk = List.map (fun (sp, spl) -> print_endline ("link: " ^ (Cprinter.string_of_spec_var sp))) link_hpargs in *)
    let local_unk_hpargs = List.filter (fun (hp,_) -> not (CP.mem_svl hp globals_unk_hps))
        (if !Globals.pred_elim_dangling then dang_hpargs else
           link_hpargs)
    in
    (* let todo_unk = List.map (fun (sp, spl) -> print_endline ("local: " ^ (Cprinter.string_of_spec_var sp))) local_unk_hpargs in *)
    let is = if !Globals.sa_dnc (* || !Globals.sae *) then
        (* let () = print_endline "sa_dnc" in *)
        (*for the local_unk_hps, we fresh them and subst/remove them in local branch*)
        (* let () = print_endline ("local length: " ^ string_of_int (List.length local_unk_hpargs)) in *)
        let new_unk_hpargs,ss = List.fold_left (fun (r1,r2) (hp,args) ->
            let is_pre = not (CP.mem_svl hp is.Cformula.is_post_hps) in
            let nhp = Sautil.fresh_raw_hp_rel prog is_pre true hp no_pos in
            (r1@[(nhp,args)], r2@[(hp,nhp)])
          ) ([],[]) local_unk_hpargs in
        (* let todo_unk = List.map (fun (sp, spl) -> print_endline ("new_unk: " ^ (Cprinter.string_of_spec_var sp))) new_unk_hpargs in *)
        let n_hp_defs = List.map (fun hp_def ->
            {hp_def with Cformula.def_rhs = List.map (fun (f,og) -> (x_add Cformula.subst ss f,og)) hp_def.Cformula.def_rhs}
          ) is.Cformula.is_hp_defs in
        (* let todo_unk = List.map (fun hp_def -> print_endline ("hp_rel_def: " ^ (Cprinter.string_of_hp_rel_def hp_def))) n_hp_defs in *)
        let n_dang_hpargs, n_link_hpargs = if !Globals.pred_elim_dangling then
            (dang_hpargs@new_unk_hpargs, link_hpargs)
          else (dang_hpargs, link_hpargs@new_unk_hpargs)
        in
        (* let () = DD.info_hprint (add_str "n_dang_hpargs" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) n_dang_hpargs no_pos in *)
        (* let () = DD.info_hprint (add_str "n_link_hpargs" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) n_link_hpargs no_pos in *)
        let is1 = {is with Cformula.is_hp_defs = n_hp_defs;
            Cformula.is_dang_hpargs = n_dang_hpargs;
            Cformula.is_link_hpargs = n_link_hpargs;
        } in
        is1
    else is
    in
    (* let dang_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is.CF.is_dang_hpargs in *)
    let () = Debug.ninfo_hprint (add_str "    link_hpargs" (pr_list (pr_pair !CP.print_sv !CP.print_svl)))  link_hpargs no_pos in
    let hp_defs1,tupled_defs = Sautil.partition_tupled is.CF.is_hp_defs in
    let dang_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is.Cformula.is_dang_hpargs in
    let link_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) is.Cformula.is_link_hpargs in
    let () = DD.ninfo_hprint (add_str "   is.Cformula.is_dang_hpargs:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) is.Cformula.is_dang_hpargs no_pos in
    let () = DD.ninfo_hprint (add_str "   is.Cformula.is_link_hpargs:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) is.Cformula.is_link_hpargs no_pos in
    let hp_defs1,tupled_defs = Sautil.partition_tupled is.Cformula.is_hp_defs in
    let cl_sel_hps, defs, tupled_defs2=
      if !Globals.pred_elim_unused_preds then
        let cl_sel_hps0 = CP.remove_dups_svl ((List.map fst link_hpargs)@
                                              (List.fold_left (fun ls d -> ls@(Cformula.get_hp_rel_name_h_formula d.Cformula.def_lhs)) [] hp_defs1))
        in
        let cl_sel_hps, hp_defs2 = Sautil.find_closed_sel_hp_def hp_defs1 cl_sel_hps0
            (List.map fst link_hpargs) is.Cformula.is_hp_equivs in
        (cl_sel_hps, hp_defs2, [])
      else
        let tupled_defs1 = List.map (fun d ->
            let (a, hf, og,f) = Cformula.flatten_hp_rel_def d in
            {
              Cformula.hprel_def_kind = a;
              Cformula.hprel_def_hrel = hf;
              Cformula.hprel_def_guard = og;
              Cformula.hprel_def_body = [(is.Cformula.is_cond_path, Some f, Some iflow)];
              Cformula.hprel_def_body_lib = (* Some f *) [];
              Cformula.hprel_def_flow = Some iflow;
            }
          ) tupled_defs
        in
        let cl_sel_hps = (List.map fst link_hpargs)@
                         (List.fold_left (fun ls d -> ls@(Cformula.get_hp_rel_name_h_formula d.Cformula.def_lhs)) [] hp_defs1)
        in
        (cl_sel_hps, hp_defs1,tupled_defs1)
    in
    let hpdefs = List.map (fun d ->
        let (k, hf, og, f) = Cformula.flatten_hp_rel_def d in
        Cformula.mk_hprel_def k hf og [(is.Cformula.is_cond_path, Some f)] None (Some iflow)
      ) defs in
    let () = DD.ninfo_hprint (add_str "   is.Cformula.is_link_hpargs 2:" (pr_list (pr_pair !CP.print_sv !CP.print_svl))) link_hpargs no_pos in
    let link_hpdefs = Sacore.generate_hp_def_from_link_hps prog iflow is.Cformula.is_cond_path is.Cformula.is_hp_equivs
        (link_hpargs) in
    let link_hp_defs = List.map (fun hpdef ->
        let fs = List.fold_left (fun ls (_, f_opt,_) ->
            match f_opt with
            | None -> ls
            | Some f -> ls@[f]
          ) [] hpdef.Cformula.hprel_def_body
        in
        let f = if fs = [] then Cformula.formula_of_heap Cformula.HTrue no_pos else
            Cformula.disj_of_list fs no_pos
        in
        Cformula.mk_hp_rel_def1 hpdef.Cformula.hprel_def_kind hpdef.Cformula.hprel_def_hrel [(f,hpdef.Cformula.hprel_def_guard)] None) link_hpdefs
    in
    (cl_sel_hps@(List.map fst link_hpargs), hpdefs@link_hpdefs,
     tupled_defs2, is.Cformula.is_hp_defs@link_hp_defs)
  in
  (***********END INTERNAL***************)
  let post_hps, dang_hps, link_hps = if ls_is = [] then ([],[],[])
    else
      let fst_is =List.hd ls_is in
      List.fold_left (fun (ls1,ls2,ls3) is ->
          (ls1@ is.Cformula.is_post_hps , CP.intersect_svl ls2 (List.map fst is.Cformula.is_dang_hpargs),
           CP.intersect_svl ls3  (List.map fst is.Cformula.is_link_hpargs)))
        (fst_is.Cformula.is_post_hps,(List.map fst fst_is.Cformula.is_dang_hpargs),(List.map fst fst_is.Cformula.is_link_hpargs)) (List.tl ls_is)
  in
  let unk_hps = if !Globals.pred_elim_dangling then dang_hps else link_hps in
  let cl_sel_hps, path_defs, tupled_defs, all_hpdefs = List.fold_left (fun (ls1, ls2,ls3, ls4) path_setting ->
      let r1,r2,r3, r4 = process_path_defs_setting unk_hps path_setting in
      let () = DD.ninfo_hprint (add_str "   r2:" (pr_list_ln Cprinter.string_of_hprel_def)) r2 no_pos in
      (ls1@r1, ls2@[r2], ls3@r3, ls4@r4)
    ) ([],[],[], []) ls_is
  in
  let cl_sel_hps1 = CP.remove_dups_svl cl_sel_hps in
  let cmb_defs = Sautil.combine_path_defs cl_sel_hps1 path_defs iflow in
  let all_hpdefs, cmb_defs = Sautil.filter_non_sel sel_hps all_hpdefs cmb_defs in
  let n_all_hpdefs0a, n_cmb_defs0 = if !Globals.sa_dnc then
      Sacore.compute_lfp_def prog (CP.remove_dups_svl post_hps)
        (CP.remove_dups_svl dang_hps) all_hpdefs cmb_defs
    else (all_hpdefs, cmb_defs)
  in
  let n_all_hp_defs0b = Sautil.combine_hpdefs n_all_hpdefs0a in
  (*unify-post*)

  (*split pred*)
  let n_all_hp_defs1a, n_cmb_defs  = if !Globals.pred_split then
      let n_all_hp_defs0c, split_map =
        let r = Sacore.pred_split_hp iprog prog unk_hps Infer.rel_ass_stk Cformula.rel_def_stk n_all_hp_defs0b in
        r
      in
      (*update n_cmb_defs0*)
      let n_cmb_defs0a = if split_map = [] then n_cmb_defs0 else
          let split_hps, split_comp_hps = List.fold_left (fun (r1, r2) (hp,_,comps,_,_) ->
              let comps_hps = List.map fst comps in
              (r1@[hp], r2@comps_hps)
            ) ([],[]) split_map in
          let n_cmb_defs0b = Sautil.pred_split_update_hpdefs iflow split_hps n_cmb_defs0 n_all_hp_defs0c in
          let comps_hp_defs = List.fold_left (fun r hp ->
              try
                let hp_def = Cformula.look_up_hp_def n_all_hp_defs0c hp in
                r@[hp_def]
              with _ -> r
            ) [] split_comp_hps in
          let comps_hpdefs = List.map (fun d ->
              let (k, hf, og, f) = Cformula.flatten_hp_rel_def d in
              Cformula.mk_hprel_def k hf og [([], Some f)] None (Some iflow)
            ) comps_hp_defs in
          n_cmb_defs0b@comps_hpdefs
      in
      (n_all_hp_defs0c, n_cmb_defs0a)
    else
      (n_all_hp_defs0b, n_cmb_defs0)
  in
  let n_cmb_defs, n_all_hp_defs1 = if !Globals.pred_seg_split then
      let new_hp_defs, splited_hps, split_hp_defs = Sacore.pred_seg_split_hp iprog prog unk_hps Infer.rel_ass_stk Cformula.rel_def_stk n_all_hp_defs1a in
      let n_cmb_defs0 = if splited_hps = [] then n_cmb_defs
        else
          (*remove hpdefs of splited_hps*)
          let n_cmb_defs0a = List.filter (fun hpdef ->
              match hpdef.CF.hprel_def_kind with
              | CP.HPRelDefn (hp,_,_) -> not (CP.mem_svl hp splited_hps)
              | _ -> true
            ) n_cmb_defs in
          (*transform split_hp_defs to split_hpdefs*)
          let split_hpdefs = List.map (fun hp_def ->
              {CF.hprel_def_kind = hp_def.CF.def_cat;
               CF.hprel_def_hrel = hp_def.CF.def_lhs;
               CF.hprel_def_guard = None;
               CF.hprel_def_body = List.map (fun (f,_) -> ([],Some f,  Some iflow)) hp_def.CF.def_rhs;
               CF.hprel_def_body_lib = [];
               Cformula.hprel_def_flow =  Some iflow;
              }
            ) split_hp_defs in
          (n_cmb_defs0a@split_hpdefs)
      in
      (n_cmb_defs0, new_hp_defs)
    else n_cmb_defs,n_all_hp_defs1a in
  (* reuse: check equivalent form - substitute *)
  let n_cmb_defs1, n_all_hp_defs2 = (* Sautil.reuse_equiv_hpdefs prog *) (n_cmb_defs, n_all_hp_defs1) in
  (*reuse with lib*)
  let n_cmb_defs2 = if !Globals.pred_equiv then
      let lib_matching = match_hps_views iprog prog cl_sel_hps1 n_all_hp_defs2
          (List.filter (fun vdcl -> vdcl.Cast.view_kind == View_NORM) prog.Cast.prog_view_decls) in
      (* let () = DD.info_pprint ("        sel_hp_rel:" ^ (!CP.print_svl sel_hps)) no_pos in *)
      (* let () =  DD.info_pprint (" matching: " ^ *)
      (*     (let pr = pr_list_ln (fun (hp,view_names) -> (!CP.print_sv hp) ^ " :== " ^ *)
      (*         ( String.concat " OR " (List.map Cprinter.prtt_string_of_h_formula view_names))) in pr lib_matching)) no_pos in *)
      collect_sel_hpdef n_cmb_defs1 sel_hps dang_hps lib_matching
    else n_cmb_defs1
  in
  let n_cmb_defs3, n_all_hp_defs3 = if !Globals.pred_equiv then
      Sacore.check_equiv_wo_libs iprog prog iflow sel_hps post_hps dang_hps n_cmb_defs2 n_all_hp_defs2 []
    else (n_cmb_defs2, n_all_hp_defs2)
  in
  let () = List.iter (fun hp_def -> CF.rel_def_stk # push hp_def) (n_cmb_defs3@tupled_defs) in
  let () = if (* (!Globals.sae) *) false then
      Saerror.create_specs (CF.rel_def_stk # get_stk) prog proc_name
    else () in
  ((* (n_cmb_defs3@tupled_defs) *)[],(* cmb_defs, *) n_all_hp_defs3, CP.remove_dups_svl (dang_hps@link_hps))

let infer_shapes_conquer iprog prog proc_name ls_is sel_hps flow_int=
  let pr1 = pr_list_ln Cprinter.string_of_infer_state_short in
  let pr2= pr_triple pr_none (pr_list_ln Cprinter.string_of_hp_rel_def) !CP.print_svl in
  Debug.no_2 "infer_shapes_conquer" pr1 !CP.print_svl pr2
    (fun _ _ -> infer_shapes_conquer_x iprog prog proc_name ls_is sel_hps flow_int)
    ls_is sel_hps

(*
obsolete, not in used. For backward compati. called by one obsolete function in sleekengine
*)
let infer_shapes_conquer_old iprog prog proc_name ls_path_defs_setting sel_hps iflow=
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
  let () = List.iter (fun hp_def -> CF.rel_def_stk # push hp_def) (cmb_defs@tupled_defs) in
  cmb_defs

let infer_shapes_ops iprog prog proc_name (constrs0: CF.hprel list) sel_hps post_hps hp_rel_unkmap unk_hpargs0a link_hpargs0 need_preprocess detect_dang flow_int: (CF.hprel list * CF.hp_rel_def list * CP.spec_var list)
(* (Cformula.hprel list * Cformula.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list ) *) =
  (*move to outer func*)
  (* let callee_hpdefs = *)
  (*   try *)
  (*       Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name *)
  (*   with _ -> [] *)
  (* in *)
  (* let callee_hps = List.map (fun (hpname,_,_) -> Cformula.get_hpdef_name hpname) callee_hpdefs in *)
  (* let print_generated_slk_file ()= *)
  (*   let () = if !Globals.sa_gen_slk then *)
  (*     let reg = Str.regexp "\.ss" in *)
  (*     let file_name1 = "logs/gen_" ^ (Str.global_replace reg ".slk" (List.hd !Globals.source_files)) in *)
  (*     let file_name2 = "logs/mod_" ^ (Str.global_replace reg ".slk" (List.hd !Globals.source_files)) in *)
  (*     (\* WN : no file printing here, so misleading messages *\) *)
  (*     (\* let () = print_endline ("\n generate: " ^ file_name1) in *\) *)
  (*     (\* let () = print_endline ("\n generate: " ^ file_name2) in *\) *)
  (*     () *)
  (*   else () *)
  (*   in () *)
  (* in *)
  let orig_lemma_ep = !Globals.lemma_ep in
  try
    (*turn off lemma printing during normalization*)
    let () = Globals.lemma_ep := false in
    let callee_hps = [] in
    let () = if !VarGen.sap then
        DD.info_hprint (add_str "  sel_hps" !CP.print_svl) sel_hps no_pos
      else ()
    in
    let () = DD.ninfo_hprint (add_str "  sel post_hps"  !CP.print_svl) post_hps no_pos in
    let all_post_hps = CP.remove_dups_svl (post_hps@(Sautil.collect_post_preds prog constrs0)) in
    let () = DD.ninfo_hprint (add_str "  all post_hps" !CP.print_svl) all_post_hps no_pos in
    let unk_hpargs0b = List.fold_left (fun ls ((hp,_),xpure) ->
        let args = match xpure.CP.xpure_view_node with
          | None -> xpure.CP.xpure_view_arguments
          | Some r -> r::xpure.CP.xpure_view_arguments
        in
        ls@[(hp,args)]
      ) [] hp_rel_unkmap
    in
    let unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (unk_hpargs0a@unk_hpargs0b) in
    let constrs1, quans_constrs = List.fold_left (fun (r1,r2) cs ->
        if Cfutil.contain_folall_pure cs.CF.hprel_lhs || Cfutil.contain_folall_pure cs.CF.hprel_rhs then
          (r1, r2@[cs])
        else (r1@[cs], r2)
      ) ([],[]) constrs0 in
    let ls_path_is = infer_shapes_divide iprog prog proc_name constrs1
        callee_hps sel_hps all_post_hps hp_rel_unkmap unk_hpargs link_hpargs0 need_preprocess detect_dang flow_int
    in
    (* let todo_unk = List.map (fun is -> print_endline (Cprinter.string_of_infer_state_short is)) ls_path_is in *)
    let r = if !Globals.sa_syn then
        match ls_path_is with
        | [] -> ([],[],[])
        | _ -> (*conquer HERE*)
          infer_shapes_conquer iprog prog proc_name ls_path_is sel_hps flow_int
      else ([],[],[])
    in
    let () = Globals.lemma_ep := orig_lemma_ep in
    (* let () = print_generated_slk_file () in *)
    r
  with _ ->
    let () = Globals.lemma_ep := orig_lemma_ep in
    (* let () = print_generated_slk_file () in *)
    let () = print_endline_quiet ("\n --error: "^" at:"^(get_backtrace_quiet ())) in
    ([],[],[])

let infer_shapes iprog prog proc_name (constrs0: CF.hprel list) 
  sel_hps post_hps hp_rel_unkmap unk_hpargs0a link_hpargs0 need_preprocess detect_dang flow_int: 
  (CF.hprel list * CF.hp_rel_def list * CP.spec_var list) =
  if not !Globals.new_pred_syn then
    infer_shapes_ops iprog prog proc_name constrs0
      sel_hps post_hps hp_rel_unkmap unk_hpargs0a 
      link_hpargs0 need_preprocess detect_dang flow_int
  else
    let hprels = CF.add_infer_type_to_hprel constrs0 in
    let sel_hprels, others = SynUtils.select_hprel_assume hprels (List.map CP.name_of_spec_var sel_hps) in
    let derived_views, nhprels = x_add Syn.derive_view iprog prog others sel_hprels in (* shape_derive_view [sel_hps] *)
    let derived_views = 
      if not !Globals.pred_elim_node then derived_views
      else Syn.elim_tail_pred_list iprog prog derived_views
    in
    let view_aset, derived_views =
      if !Globals.pred_equiv then
        let view_aset = Syn.aux_pred_reuse iprog prog derived_views in
        let derived_views = List.map (fun v -> 
          try Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls v.Cast.view_name
          with _ -> v) derived_views in
        view_aset, derived_views
      else [], derived_views
    in
    let () = y_binfo_hp (add_str "\n===== DERIVED VIEWS =====\n" 
      (pr_list_ln Cprinter.string_of_view_decl_short)) derived_views in
    (nhprels, [], [])

let infer_shapes (iprog: Iast.prog_decl) (prog: Cast.prog_decl) (proc_name:ident)
    (hp_constrs: Cformula.hprel list) (sel_hp_rels: CP.spec_var list) (sel_post_hp_rels: CP.spec_var list)
    (hp_rel_unkmap: ((CP.spec_var * int list) * CP.xpure_view) list)
    (unk_hpargs: (CP.spec_var * CP.spec_var list) list)
    (link_hpargs: (int list * (Cformula.CP.spec_var * Cformula.CP.spec_var list)) list)
    (need_preprocess: bool) (detect_dang:bool) flow_int:
  (* (Cformula.cond_path_type * Cformula.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) = *)
  (* (Cformula.hprel list * Cformula.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) = *)
  (CF.hprel list * CF.hp_rel_def list * CP.spec_var list) =
  (* let pr0 = pr_list !CP.print_exp in *)
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  (* let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in *)
  (* let pr4 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in *)
  let pr4 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5a = pr_list (pr_pair Cformula.string_of_cond_path (pr_pair !CP.print_sv !CP.print_svl)) in
  let () = if !Globals.print_heap_pred_decl && !VarGen.sap then
      let all_hps = Cformula.get_hp_rel_name_assumption_set hp_constrs in
      let all_hp_decls = List.fold_left (fun ls hp ->
          try
            let hp_decl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
            ls@[hp_decl]
          with _ -> ls
        ) [] all_hps
      in
      if !Globals.sleek_flag || not (!VarGen.sap) then () 
      else
        let () = print_endline_quiet "\nHeap Predicate Declarations" in
        let () = print_endline_quiet "===========================" in
        let () = List.iter (fun hpdcl -> print_string (Cprinter.string_of_hp_decl hpdcl)) all_hp_decls in
        ()
    else ()
  in
  Debug.no_7 "infer_shapes" 
    (add_str "proc_name" pr_id)
    (add_str "hp_constrs" pr1) 
    (add_str "sel_hp_rels" !CP.print_svl) 
    (add_str "sel_post_hp_rels" !CP.print_svl) 
    (add_str "hp_rel_unkmap" pr4)
    (add_str "unk_hpargs" pr5) 
    (add_str "link_hpargs" pr5a) 
    (pr_triple pr1 pr2 !CP.print_svl)
    (fun _ _ _ _ _ _ _ -> infer_shapes iprog prog proc_name hp_constrs sel_hp_rels
        sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs
        need_preprocess detect_dang flow_int)
    proc_name hp_constrs sel_hp_rels sel_post_hp_rels hp_rel_unkmap unk_hpargs link_hpargs


(**************************)
 (*For validation*)
let check_horm_data_decl_x tmpl_data_decl data_decl=
  (*subs type s= temp t, t into tmpl ptr fiels*)
  let get_ptr ((t,id),_,b,_)=
    if is_pointer t then
      [(id,b)]
    else []
  in
  let get_ptr_and_susbt (id1,id2) ((t,id),_,b,_)=
    if is_pointer t then
      if id = id1 then
        [(id2,b)]
      else [(id,b)]
    else []
  in
  let rec eq_ordered_ids tmpl_idbs idbs=
    match tmpl_idbs,idbs with
    | [], [] -> true
    | (id1,b1)::ids1,(id2,b2)::ids2 ->
      if id1=id2 && b1=b2 then eq_ordered_ids ids1 ids2
      else false
    | _ -> false
  in
  let tmpl_idbs = List.concat (List.map (get_ptr_and_susbt
                                           (tmpl_data_decl.Iast.data_name, data_decl.Iast.data_name))
                                 tmpl_data_decl.Iast.data_fields) in
  let idbs = List.concat (List.map get_ptr data_decl.Iast.data_fields) in
  eq_ordered_ids tmpl_idbs idbs

let check_horm_data_decl tmpl_data_decl data_decl=
  let pr1 = Iprinter.string_of_data_decl in
  Debug.no_2 "check_horm_data_decl" pr1 pr1 string_of_bool
    (fun _ _ -> check_horm_data_decl_x tmpl_data_decl data_decl)
    tmpl_data_decl data_decl

let build_horm_view_x templ_view_decls horm_dd=
  let look_up_views data_name vds=
    let rec helper lvds res=
      match lvds with
      | [] -> res
      | vd::ss ->
        if vd.Iast.view_data_name = data_name then
          helper ss (res@[vd])
        else helper ss res
    in
    helper vds []
  in
  let generate_view ((tmp_data_name,tmp_data_fields),(data_name,data_fields))
      view=
    (*assume they have the same number of fields*)
    let n_view_name = view.Iast.view_name ^ "_" ^ data_name in
    let ss =
      List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] [(tmp_data_name,data_name);(view.Iast.view_name,n_view_name)] in
    let n_view_invariant = Ipure.subst ss view.Iast.view_invariant in
    let n_view_formula = Iformula.subst_w_data_name_struc ss view.Iast.view_formula in
    let n_view_inv_lock =
      match view.Iast.view_inv_lock with
      | None -> None
      | Some f -> Some (Iformula.subst ss f)
    in
    { view with
      Iast.view_name = n_view_name;
      Iast.view_pos = no_pos;
      Iast.view_data_name = data_name;
      Iast.view_type_of_self = None;
      Iast.view_typed_vars = view.Iast.view_typed_vars;
      Iast.view_invariant = n_view_invariant;
      Iast.view_baga_inv = None;
      Iast.view_baga_over_inv = None;
      Iast.view_baga_under_inv = None;
      Iast.view_formula = n_view_formula;
      Iast.view_inv_lock = n_view_inv_lock;
    }
  (*   {  *)
  (*     Iast.view_name = n_view_name; *)
  (*     Iast.view_pos = no_pos; *)
  (*     Iast.view_data_name = data_name; *)
  (*     Iast.view_type_of_self = None; *)
  (*     Iast.view_typed_vars = view.Iast.view_typed_vars; *)
  (*     Iast.view_invariant = n_view_invariant; *)
  (*     Iast.view_baga_inv = None; *)
  (*     Iast.view_baga_over_inv = None; *)
  (*     Iast.view_baga_under_inv = None; *)
  (*     Iast.view_formula = n_view_formula; *)
  (*     Iast.view_inv_lock = n_view_inv_lock; *)
  (*     Iast.view_vars = view.Iast.view_vars; *)
  (*     Iast.view_ho_vars = view.Iast.view_ho_vars; *)
  (*     Iast.view_imm_map = view.Iast.view_imm_map; *)
  (*     Iast.view_labels = view.Iast.view_labels; *)
  (*     Iast.view_modes = view.Iast.view_modes; *)
  (*     Iast.view_is_prim = view.Iast.view_is_prim; *)
  (*     Iast.view_is_hrel = view.Iast.view_is_hrel; *)
  (*     Iast.view_kind = view.Iast.view_kind; *)
  (*     Iast.view_derv = view.Iast.view_derv; *)
  (*     Iast.view_parent_name = view.Iast.view_parent_name; *)
  (*     Iast.view_prop_extns = view.Iast.view_prop_extns; *)
  (*     Iast.view_derv_info = view.Iast.view_derv_info; *)
  (*     Iast.view_mem = view.Iast.view_mem; *)
  (*     Iast.view_pt_by_self = view.Iast.view_pt_by_self; *)
  (*     Iast.try_case_inference = view.Iast.try_case_inference; *)
  (*     Iast.view_materialized_vars = view.Iast.view_materialized_vars; *)
  (*   } *)
  in
  let (tmp_data_name,tmp_data_fields),(data_name,data_fields) = horm_dd in
  let cand_views = look_up_views tmp_data_name templ_view_decls in
  List.map (generate_view horm_dd) cand_views

let build_horm_view templ_view_decls horm_dd=
  let pr1 = fun ((templ_data_name,_),(data_name,_)) -> (templ_data_name ^ ":" ^ data_name) in
  let pr2 = pr_list_ln Iprinter.string_of_view_decl in
  Debug.no_2 "build_horm_view" pr2 pr1 pr2
    (fun _ _ ->  build_horm_view_x templ_view_decls horm_dd) templ_view_decls horm_dd

let compute_view_data_name templ_ddefs templ_vdefs vdef=
  let data_name =
    if (String.length vdef.Iast.view_data_name) = 0 then
      let (cands,_)= Iast.find_data_view vdef templ_ddefs no_pos in
      (* let () = print_endline ("Feasible self type: " ^ (String.concat "," cands)) in *)
      List.hd cands
    else vdef.Iast.view_data_name
  in
  {vdef with Iast.view_data_name = data_name}

(*generate horm view*)
let generate_horm_view_x templ_data_decls templ_view_decls data_decls=
  (*find horm*)
  let find_horm_data_decl ldata_decls tmpl_data_decl=
    let helper templ_data_decl data_decl=
      if check_horm_data_decl tmpl_data_decl data_decl then
        [((templ_data_decl.Iast.data_name,templ_data_decl.Iast.data_fields),
          (data_decl.Iast.data_name,data_decl.Iast.data_fields))]
      else []
    in
    List.concat (List.map (helper tmpl_data_decl) ldata_decls)
  in
  let horm_dds = List.concat (List.map (find_horm_data_decl data_decls) templ_data_decls) in
  let new_templ_vdefs = List.map (compute_view_data_name templ_data_decls templ_view_decls) templ_view_decls in
  List.concat (List.map (build_horm_view new_templ_vdefs) horm_dds)

let generate_horm_view templ_data_decls templ_view_decls data_decls=
  let pr1 = pr_list_ln Iprinter.string_of_data_decl in
  let pr2 = pr_list_ln Iprinter.string_of_view_decl in
  Debug.no_3 "generate_horm_view" pr1 pr2 pr1 pr2
    (fun _ _ _ -> generate_horm_view_x templ_data_decls templ_view_decls data_decls) templ_data_decls templ_view_decls data_decls


let () = Lemma.infer_shapes := infer_shapes
