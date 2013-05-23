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
module SAU = Sautility

let rel_def_stk : CF.hprel_def Gen.stack_pr = new Gen.stack_pr
  Cprinter.string_of_hprel_def_lib (==)

(***************************************************************)
           (*========SIMPLIFICATION============*)
(***************************************************************)
let rec simplify_one_constr prog unk_hps constr=
  begin
      let (lhs, rhs) = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
      match lhs,rhs with
        | CF.Base lhs_b, CF.Base rhs_b ->
            begin
                let l,r,matched = SAU.simplify_one_constr_b prog unk_hps lhs_b rhs_b in
                 (* if l.CF.formula_base_heap = CF.HEmp && *)
                 (*   (MCP.isConstMTrue l.CF.formula_base_pure) then *)
                if SAU.is_unk_f (CF.Base l) || SAU.is_unk_f (CF.Base r) ||
                (SAU.is_empty_f (CF.Base l) && SAU.is_empty_f (CF.Base r)) then
                  let _ = DD.ninfo_pprint (" input: " ^(Cprinter.prtt_string_of_formula_base lhs_b) ^ " ==> " ^
                                                  (Cprinter.prtt_string_of_formula_base rhs_b)) no_pos in
                  let _ =  DD.ninfo_pprint (" output: drop") no_pos in
                   []
                else
                  (*it may subst into some unk_hps, should detect it*)
                  let hp_args = (CF.get_HRels l.CF.formula_base_heap)@
                    (CF.get_HRels r.CF.formula_base_heap) in
                  let hp_args1 = Gen.BList.remove_dups_eq SAU.check_simp_hp_eq
                    hp_args in
                  (*get hp that all args are unk*)
                  let unk_hp_args = List.filter (fun (hp,args) ->
                  (Gen.BList.difference_eq CP.eq_spec_var args constr.CF.unk_svl) = []) hp_args1 in
                  let new_constr = {constr with CF.predef_svl = constr.CF.predef_svl@matched;
                      CF.unk_hps = Gen.BList.remove_dups_eq SAU.check_simp_hp_eq
                          (constr.CF.unk_hps@unk_hp_args);
                       CF.hprel_lhs = CF.Base l;
                       CF.hprel_rhs = CF.Base r;
                                   }
                  in
                  let _ =  DD.ninfo_pprint (" simplify: new cs:" ^ ( Cprinter.string_of_hprel new_constr)) no_pos in
                  [new_constr]
              end
        | _ -> report_error no_pos "sa.simplify_one_constr"
  end

let simplify_constrs_x prog unk_hps constrs=
  List.concat (List.map (simplify_one_constr prog unk_hps) constrs)

let simplify_constrs prog unk_hps constrs=
   let pr = pr_list_ln (Cprinter.string_of_hprel) in
  Debug.no_1 "simplify_constrs" pr pr
      (fun _ -> simplify_constrs_x prog unk_hps constrs) constrs

(***************************************************************)
           (*===========END SIMPLIFICATION===========*)
(***************************************************************)

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
let rec get_closed_ptrs_one rdn ldns rdns rcur_match ss=
  (* let _ =  DD.info_pprint ("    rdn: " ^ (!CP.print_sv rdn) ) no_pos in *)
  let rec find_args_subst largs rargs lm rm=
    match largs, rargs with
      | [],[] -> (lm,rm)
      | la::ls,ra::rs -> if CP.mem_svl ra rcur_match then
            (*find all matched previously. one lhs can match many rhs*)
            let l_ss = fst (List.split (List.filter (fun (_,r) -> CP.eq_spec_var r ra) ss)) in
            let _ =  DD.ninfo_pprint ("    l_ss: " ^ (!CP.print_svl l_ss) ) no_pos in
            if CP.mem_svl la l_ss then
               let _ =  DD.ninfo_pprint ("    la: " ^ (!CP.print_sv la) ) no_pos in
               let _ =  DD.ninfo_pprint ("    ra: " ^ (!CP.print_sv ra) ) no_pos in
              find_args_subst ls rs lm rm (*matched already*)
            else find_args_subst ls rs (lm@[la]) (rm@[ra])
          else find_args_subst ls rs (lm@[la]) (rm@[ra])
      | _ -> report_error no_pos "sa.get_closed_ptrs: 1"
  in
  let rec look_up_rdn m_dn rdns res=
    match rdns with
      | [] -> res
      | (data_name,node_name,args)::rest ->
          let r=
            if CP.mem_svl m_dn (node_name::args) then
              [(data_name,node_name,args)]
            else []
          in
          look_up_rdn m_dn rest (res@r)
  in
  if ldns = [] || rdns = [] then
    ([],[]) (*either lhs1 or rhs2 does not have any node*)
  else
    begin
        (* let (ld_name, lsv, largs) = List.hd ldn_match in *)
        (* let (rd_name, rsv, rargs) = List.hd rdn_match in *)
        let rec helper1 (ld_name, lsv, largs) rdn_m =
          match rdn_m with
            | [] -> []
            | (rd_name, rsv, rargs)::rs ->
                let _ =  DD.ninfo_pprint ("    lsv: " ^ (!CP.print_sv lsv)) no_pos in
                let _ =  DD.ninfo_pprint ("    rsv: " ^ (!CP.print_sv rsv)) no_pos in
                if (String.compare ld_name rd_name=0) && ((CP.eq_spec_var lsv rsv) || CP.intersect_svl rargs largs <> [])then
                  rsv::rargs
                else helper1 (ld_name, lsv, largs) rs
        in
        let rec helper2 ldn_m=
          match ldn_m with
            | [] -> ([],[]) (*all node intersected are diff in type*)
            | (ld_name, lsv, largs):: ls ->
                let lsv1 = CP.subs_one ss lsv in
                (* if CP.mem_svl lsv1 rcur_match then helper2 ls *)
                (* else *)
                  begin
                      let largs1 = List.map (CP.subs_one ss) largs in
                      (*look_up rdn in rdns*)
                      let cur_rdns = look_up_rdn rdn rdns [] in
                      let rargs = helper1 (ld_name, lsv1, largs1) cur_rdns in
                      if rargs = [] then helper2 ls
                      else
                        let _ =  DD.ninfo_pprint ("    largs: " ^ (!CP.print_svl (lsv::largs))) no_pos in
                        let _ =  DD.ninfo_pprint ("    largs1: " ^ (!CP.print_svl (lsv1::largs1))) no_pos in
                        let _ =  DD.ninfo_pprint ("    rargs: " ^ (!CP.print_svl (rargs))) no_pos in
                        find_args_subst (lsv::largs) rargs [] []
                  end
        in
        let lm,rm = helper2 ldns in
        let _ =  DD.ninfo_pprint ("    lm " ^ (!CP.print_svl (lm))) no_pos in
        let _ =  DD.ninfo_pprint ("    rm " ^ (!CP.print_svl (rm))) no_pos in
        if lm = [] then ([],[]) (*all node intersected are diff in type*)
        else (rm, List.combine lm rm)
    end

and get_closed_matched_ptrs ldns rdns rcur_match ss=
  let rec helper old_m old_ss inc_m=
    let _ =  DD.ninfo_pprint ("    old_m " ^ (!CP.print_svl old_m)) no_pos in
    (*find matching ldns and rdns*)
    let r = List.map (fun m -> get_closed_ptrs_one m ldns rdns old_m old_ss) inc_m in
    let incr_match, incr_ss = List.split r in
    if incr_match = [] then
      old_m, old_ss
    else
      let n_incr_m = (List.concat incr_match) in
      helper (CP.remove_dups_svl (old_m@n_incr_m)) (old_ss@(List.concat incr_ss)) n_incr_m
  in
  helper rcur_match ss rcur_match

(*
step 1: apply transitive implication
        B |= C ---> E
  ---------------------------------
  c1 = A |- B ;c2 = C |- D ===> c3=A |- D * E
*)
let rec find_imply prog lunk_hps runk_hps lhs1 rhs1 lhs2 rhs2=
  let sort_hps_x hps = List.sort (fun (CP.SpecVar (_, id1,_),_)
      (CP.SpecVar (_, id2, _),_)-> String.compare id1 id2) hps
  in
  let sort_hps hps=
    let pr1 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
    Debug.no_1 "sort_hps" pr1 pr1
        (fun _ ->  sort_hps_x hps) hps
  in
 (*precondition: ls1 and ls2 are sorted*)
  (*we may enhance here, ls1, ls2 are not necessary the same: ls2 >= ls1*)
  let rec check_hrels_imply ls1 ls2 ldns rdns lhs_hps subst matched args res_rename=
    match ls1,ls2 with
      | [],[] -> (subst,matched,args,res_rename)
      | (id1, args1)::ss1,(id2, args2)::ss2 ->
          if CP.eq_spec_var id1 id2 then
            begin
                (* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *)
                (*   !Globals.sa_equiv_chain && not(check_equiv_chains args1 args2 ldns rdns) then *)
                (*   check_hrels_imply ls1 ss2 ldns rdns lhs_hps *)
                (*     (subst) (matched) (args) res_rename *)
                (* else *)
                  check_hrels_imply ss1 ss2 ldns rdns lhs_hps
                    (subst@(List.combine args1 args2)) (matched@[id2]) (args@args2) res_rename
            end
          else (* begin *)
              (* (\*unk hps*\) *)
              (* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *)
              (*   List.length args1 = List.length args2 && not (List.mem id2 lhs_hps) then *)
              (*   check_hrels_imply ss1 ss2 lhs_hps (subst@(List.combine args1 args2)) *)
              (*       (matched@[id1]) (args@args2) (res_rename@[(id1,(id2,args2))]) *)
              (* else *)
            check_hrels_imply ls1 ss2 ldns rdns lhs_hps subst matched args res_rename
          (* end *)
      | [], _ -> (subst,matched,args,res_rename)
      | _ -> ([],[],[],[])
  in
  let transform_hrel (hp,eargs,_)= (hp, List.concat (List.map CP.afv eargs)) in
  let transform_dn dn= (dn.CF.h_formula_data_name, dn.CF.h_formula_data_node,
                        List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t ) dn.CF. h_formula_data_arguments) in
  let rec is_inconsistent_x ss done_ss=
    match ss with
      | [] -> false
      | (sv1,sv2)::rest->
          try
              let sv22 = List.assoc sv1 (rest@done_ss) in
              if CP.eq_spec_var sv2 sv22 then
                is_inconsistent_x rest (done_ss@[(sv1,sv2)])
              else true
          with Not_found -> is_inconsistent_x rest (done_ss@[(sv1,sv2)])
  in
  let rec is_inconsistent ss done_ss=
    let pr1= pr_list (pr_pair !CP.print_sv !CP.print_sv) in
    Debug.no_1 "is_inconsistent" pr1 string_of_bool
        (fun _ -> is_inconsistent_x ss done_ss) ss
  in
  (*matching hprels and return subst*)
  let ldns,lvns,lhrels = CF.get_hp_rel_bformula lhs1 in
  let rdns,_,rhrels = CF.get_hp_rel_bformula rhs2 in
  let l_rhrels = sort_hps (List.map transform_hrel lhrels) in
  let r_rhrels = sort_hps (List.map transform_hrel rhrels) in
  (*m_args2: matched svl of rhs2*)
  let subst,matched_hps, m_args2,rhs_hps_rename = check_hrels_imply l_rhrels r_rhrels ldns rdns (List.map fst l_rhrels) [] [] [] [] in
  let r=
    if matched_hps = [] then None
    else
      begin
          (*for debugging*)
          let _ = Debug.ninfo_pprint ("     m_args2: " ^ (!CP.print_svl  m_args2)) no_pos in
          let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
          let _ =  Debug.ninfo_pprint ("     subst: " ^ (pr_ss subst)) no_pos in
          (*END for debugging*)
          (*matching hnodes (in matched_hps) and return subst*)
          let lhns1 = List.map transform_dn ldns in
          let rhns1 = List.map transform_dn rdns in
          (*all_matched_svl2: all matched slv of rhs2*)
          let all_matched_svl2,subst1 = get_closed_matched_ptrs lhns1 rhns1 m_args2 subst in
          let _ = Debug.ninfo_pprint ("    all matched: " ^ (!CP.print_svl all_matched_svl2)) no_pos in
          let _ =  Debug.ninfo_pprint ("     subst1: " ^ (pr_ss subst1)) no_pos in
          if  (is_inconsistent subst1 []) then None else
      (*subst in lhs1*)
          let n_lhs1 = CF.subst_b subst1 lhs1 in
          (*check pure implication*)
          let nldns,nlvns,_ = CF.get_hp_rel_bformula n_lhs1 in
          let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure)
            (SAU.look_up_closed_ptr_args prog nldns nlvns all_matched_svl2) in
          let rmf = (MCP.pure_of_mix rhs2.CF.formula_base_pure) in
          (* let _ = Debug.info_pprint ("    n_lhs1: " ^ (Cprinter.string_of_formula_base n_lhs1)) no_pos in *)
          let _ = Debug.ninfo_pprint ("    lmf: " ^ (!CP.print_formula lmf)) no_pos in
          let _ = Debug.ninfo_pprint ("    rmf: " ^ (!CP.print_formula rmf)) no_pos in
          let b,_,_ = TP.imply rmf lmf "sa:check_hrels_imply" true None in
          let lpos = (CF.pos_of_formula lhs2) in
          if b then
            let l_res = {n_lhs1 with
              CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                  n_lhs1.CF.formula_base_heap SAU.select_dnode
                  SAU.select_vnode SAU.select_hrel  all_matched_svl2  all_matched_svl2 matched_hps}
            in
            (*drop hps and matched svl in n_rhs2*)
            let r_res = {rhs2 with
                CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                    rhs2.CF.formula_base_heap SAU.select_dnode
                    SAU.select_vnode SAU.select_hrel all_matched_svl2 all_matched_svl2 matched_hps;
                CF.formula_base_pure = MCP.mix_of_pure
                    (CP.filter_var_new
                         (MCP.pure_of_mix rhs2.CF.formula_base_pure) all_matched_svl2)}
            in
            (*avoid clashing --> should refresh remain svl of lhs2*)
            let slv2 = CP.remove_dups_svl ((CF.fv lhs2)@
                                                  (CF.fv (CF.Base rhs2))) in
            (*do not rename HP names*)
            let hp_names = CP.remove_dups_svl ((CF.get_hp_rel_name_formula lhs2)@(CF.get_hp_rel_name_bformula rhs2)) in
            (*remove hp name*)
            let diff1 = Gen.BList.difference_eq CP.eq_spec_var slv2 hp_names in
            let _ = Debug.ninfo_pprint ("    diff1: " ^ (!CP.print_svl diff1)) no_pos in
            (*elim matched svl*)
            let diff2 = Gen.BList.difference_eq CP.eq_spec_var diff1 all_matched_svl2 in
            let _ = Debug.ninfo_pprint ("    diff2: " ^ (!CP.print_svl diff2)) no_pos in
            (*refresh it*)
            let fresh_diff2 = CP.fresh_spec_vars diff2 in
            let ss2 = List.combine diff2 fresh_diff2 in
            let n_lhs2 = CF.subst ss2 lhs2 in
            (*end refresh*)
            (*combine l_res into lhs2*)
            let l =  CF.mkStar n_lhs2 (CF.Base l_res) CF.Flow_combine lpos in
            let n_rhs1 = CF.subst subst1 rhs1 in
            (*avoid clashing --> should refresh remain svl of r_res*)
            let r_res1 = CF.subst ss2 (CF.Base r_res) in
            (*elim duplicate hprel in r_res1 and n_rhs1*)
            let nr_hprel = CF.get_HRels_f n_rhs1 in
            let nrest_hprel = CF.get_HRels_f r_res1 in
            let diff3 = Gen.BList.intersect_eq SAU.check_hp_arg_eq nr_hprel nrest_hprel in
            let r_res2,_ = CF.drop_hrel_f r_res1 (List.map (fun (hp,_) -> hp) diff3) in
            let r = CF.mkStar n_rhs1 r_res2 CF.Flow_combine (CF.pos_of_formula n_rhs1) in
            (Some (l, r,subst1, ss2))
          else None
      end
  in
  r

and find_imply_subst_x prog constrs new_cs=
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
    match cs1.CF.hprel_lhs,cs2.CF.hprel_rhs with
      | CF.Base lhs1, CF.Base rhs2 ->
          let r = find_imply prog (List.map fst cs1.CF.unk_hps) (List.map fst cs2.CF.unk_hps) lhs1 cs1.CF.hprel_rhs cs2.CF.hprel_lhs rhs2 in
          begin
              match r with
                | Some (l,r,lhs_ss, rhs_ss) ->
                    (*check duplicate*)
                    if check_constr_duplicate (l,r) constrs then []
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
      | _ -> report_error no_pos "sa.find_imply_one"
  in
  (*new_cs: one x one*)
  let rec helper_new_only don rest res=
    match rest with
      | [] -> res
      | cs::ss ->
          let _ = Debug.ninfo_pprint ("    lhs: " ^ (Cprinter.string_of_hprel cs)) no_pos in
          let r = List.concat (List.map (find_imply_one cs) (don@ss@res)) in
          (helper_new_only (don@[cs]) ss (res@r))
  in
  (*new_cs x constr*)
  let rec helper_old_new rest res=
    match rest with
      | [] -> res
      | cs::ss ->
          let r = List.fold_left ( fun ls cs1 -> ls@(find_imply_one cs cs1)) res constrs in
           helper_old_new ss r
  in
  let new_cs1 = if List.length new_cs < 1 then [] else helper_new_only [] new_cs [] in
  let new_cs2 = helper_old_new new_cs [] in
  (new_cs1@new_cs2)

and find_imply_subst prog constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "find_imply_subst" pr1 pr1
      (fun _ -> find_imply_subst_x prog constrs new_cs) constrs

and is_non_recursive_cs dang_hps constr=
  let lhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_lhs in
  let rhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_rhs in
  ((CP.intersect lhrel_svl rhrel_svl) = [])

and subst_cs_w_other_cs_x prog dang_hps constrs new_cs=
  (*remove recursive cs*)
  let constrs1 = List.filter (is_non_recursive_cs dang_hps) constrs in
  let new_cs1 = List.filter (is_non_recursive_cs dang_hps) new_cs in
  find_imply_subst prog constrs1 new_cs1
(*=========END============*)

let rec subst_cs_w_other_cs prog dang_hps constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
   Debug.no_1 "subst_cs_w_other_cs" pr1 pr1
       (fun _ -> subst_cs_w_other_cs_x prog dang_hps constrs  new_cs) constrs

let subst_cs_x prog dang_hps constrs new_cs =
  (*subst by constrs*)
  DD.ninfo_pprint "\n subst with other assumptions" no_pos;
  let new_cs1 = subst_cs_w_other_cs prog dang_hps constrs new_cs in
  (constrs@new_cs, new_cs1,[])

let subst_cs prog dang_hps hp_constrs new_cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "subst_cs" pr1 (pr_triple pr1 pr1 !CP.print_svl)
      (fun _ -> subst_cs_x prog dang_hps hp_constrs new_cs) new_cs

(*===========fix point==============*)
let apply_transitive_impl_fix prog callee_hps hp_rel_unkmap unk_hps (constrs: CF.hprel list) =
  let dang_hps = (fst (List.split hp_rel_unkmap)) in
  let rec helper_x (constrs: CF.hprel list) new_cs non_unk_hps=
    DD.ninfo_pprint ">>>>>> step 1a: simplification <<<<<<" no_pos;
    let new_cs1 = (* simplify_constrs prog unk_hps *) new_cs in
     Debug.info_hprint (add_str "apply_transitive_imp LOOP: " (pr_list_ln Cprinter.string_of_hprel)) constrs no_pos;
    begin
        DD.ninfo_pprint ">>>>>> step 1b: do apply_transitive_imp <<<<<<" no_pos;
        let constrs2, new_cs2, new_non_unk_hps = subst_cs prog dang_hps constrs new_cs1 in
        (*for debugging*)
        let helper (constrs: CF.hprel list) new_cs non_unk_hps=
          let pr = pr_list_ln Cprinter.string_of_hprel in
          Debug.no_1 "apply_transitive_imp_fix" pr (fun (cs,_) -> pr cs)
              (fun _ -> helper_x constrs new_cs non_unk_hps) new_cs
        in
        (*END for debugging*)
        let norm_constrs, non_unk_hps1 =
          if List.length new_cs2 = 0 then (constrs2@new_cs2, new_non_unk_hps)
          else
            helper constrs2 new_cs2 (non_unk_hps@new_non_unk_hps) in
        ( norm_constrs, CP.remove_dups_svl non_unk_hps1)
      end
  in
  helper_x [] constrs []

(***************************************************************
                      END APPLY TRANS IMPL
****************************************************************)

(***************************************************************
                      PARTIAL DEFS
****************************************************************)
let mk_pdef hp_sv args unk_svl imp_cond olhs orhs=
  (hp_sv, args,  unk_svl, imp_cond, olhs , orhs)

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
          ([(mk_pdef hp args cs.CF.unk_svl p None (Some cs.CF.hprel_rhs), cs)], [])
      | None -> ([], [cs])
  in
  List.fold_left (fun (pdefs,rem_cs) cs ->
      let ls1, ls2 = mk_par_def cs in
      (pdefs@ls1, rem_cs@ls2)
  )
      ([], []) constrs0

let combine_pdefs_pre pr_par_defs=
  let rec refine_cond rem_pr_par_defs ((hp,args,unk_svl, cond, lhs, orhs), cs)=
    match rem_pr_par_defs with
      | [] -> begin
          let new_pdef = match orhs with
            | Some rhs -> (hp,args,unk_svl, cond, lhs, Some (CF.mkAnd_pure rhs (MCP.mix_of_pure cond) (CF.pos_of_formula rhs)))
            | None -> report_error no_pos "sa2.combine_pdefs_pre: should not None"
          in
          ([new_pdef],[])
      end
      | ((_,_,_,cond1,_,_),_)::rest ->
          (* let _ = print_endline ("cond: " ^ ( !CP.print_formula cond)) in *)
          (* let _ = print_endline ("cond1: " ^ ( !CP.print_formula cond1)) in *)
          if not (TP.is_sat_raw (MCP.mix_of_pure (CP.mkAnd cond cond1 no_pos))) then
            refine_cond rest ((hp,args,unk_svl, cond, lhs, orhs), cs)
          else
            ([], [cs])
  in
  let rec helper rem_pr_par_defs done_pr_par_defs res_pdefs res_cs=
    match rem_pr_par_defs with
      | [] -> (res_pdefs, res_cs)
      | pr::rest ->
          let ls1,ls2 = refine_cond (done_pr_par_defs@rest) pr in
          helper rest (done_pr_par_defs@[pr]) (res_pdefs@ls1) (res_cs@ls2)
  in
  helper pr_par_defs [] [] []

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

(*for par_defs*)
let generalize_one_hp_x prog hpdefs non_ptr_unk_hps unk_hps par_defs=
  (*collect definition for each partial definition*)
  let obtain_and_norm_def hp args0 (a1,args,f,unk_args)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let f1 = (CF.subst subst f) in
    let f2 =
      if !Globals.sa_dangling then
        CF.annotate_dl f1 (List.filter (fun hp1 -> not (CP.eq_spec_var hp hp1)) unk_hps)
      else f1
    in
    let unk_args1 = List.map (CP.subs_one subst) unk_args in
    (* (\*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *\) *)
    (f2,unk_args1)
  in
  DD.ninfo_pprint ">>>>>> generalize_one_hp: <<<<<<" no_pos;
  if par_defs = [] then ([],[]) else
    begin
        let hp, args, _,_ = (List.hd par_defs) in
        (*find the root: ins2,ins3: root is the second, not the first*)
        let args0 = List.map (CP.fresh_spec_var) args in
    (* DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")") no_pos; *)
        let defs,ls_unk_args = List.split (List.map (obtain_and_norm_def hp args0) par_defs) in
        let r,non_r_args = SAU.find_root args0 defs in
        (*make explicit root*)
        let defs0 = List.map (SAU.mk_expl_root r) defs in
        let unk_svl = CP.remove_dups_svl (List.concat (ls_unk_args)) in
  (*normalize linked ptrs*)
        let defs1 = SAU.norm_hnodes args0 defs0 in
        (*remove unkhp of non-node*)
        let defs2 = (* List.map remove_non_ptr_unk_hp *) defs1 in
  (*remove duplicate*)
        let defs3 = Gen.BList.remove_dups_eq (fun f1 f2 -> SAU.check_relaxeq_formula f1 f2) defs2 in
        if CP.mem_svl hp unk_hps then
          (SAU.mk_unk_hprel_def hp args0 defs3 no_pos,[])
        else
          let defs4 = SAU.remove_equiv_wo_unkhps hp unk_hps defs3 in
   (*remove duplicate with self-recursive*)
        (* let base_case_exist,defs4 = SAU.remove_dups_recursive hp args0 unk_hps defs3 in *)
  (*find longest hnodes common for more than 2 formulas*)
  (*each hds of hdss is def of a next_root*)
           (* let defs5 = List.filter (fun f -> have_roots args0 f) defs4 in *)
          let defs,elim_ss = SAU.get_longest_common_hnodes_list prog hpdefs unk_hps unk_svl hp r non_r_args args0 defs4 in
          if defs <> [] then (defs,elim_ss) else
            report_error no_pos "shape analysis: FAIL"
    end

let generalize_one_hp prog defs non_ptr_unk_hps unk_hps par_defs=
  let pr1 = pr_list_ln SAU.string_of_par_def_w_name_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  let pr3 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  Debug.no_1 "generalize_one_hp" pr1 (pr_pair pr2 pr3)
      (fun _ -> generalize_one_hp_x prog defs non_ptr_unk_hps unk_hps par_defs) par_defs

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

let generalize_hps_par_def_x prog non_ptr_unk_hps unk_hpargs post_hps par_defs=
  (*partition the set by hp_name*)
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
      | [] -> parts
      | (a1,a2,a3,a4)::xs ->
          let part,remains= List.partition (fun (hp_name,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[(a1,a2,a3,a4)]@part])
  in
  let unk_hps = (List.map fst unk_hpargs) in
  let par_defs1 = List.concat (List.map (get_pdef_body unk_hps post_hps) par_defs) in
  let par_defs2 = List.filter is_valid_pardef par_defs1 in
  let groups = partition_pdefs_by_hp_name par_defs2 [] in
  (*remove dups in each group*)
  let groups1 = List.map SAU.remove_dups_pardefs_w_neqNull groups in
  (*
    subst such that each partial def does not contain other hps
    dont subst recursively search_largest_matching between two formulas
  *)
  (* let pr1 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl)) in *)
  (* let _ = DD.info_pprint ("      groups1: " ^ (pr1 groups1)) no_pos in *)

  let groups2 = pardef_subst_fix prog unk_hps groups1 in
  (* let _ = Debug.info_pprint ("     END: " ) no_pos in *)
  (*remove empty*)
  let groups3 = List.filter (fun grp -> grp <> []) groups2 in
  (*each group, do union partial definition*)
  let hpdefs,elim_ss = List.fold_left (fun (hpdefs,elim_ss) pdefs->
      let new_defs,ss = generalize_one_hp prog hpdefs non_ptr_unk_hps unk_hps pdefs in
      ((hpdefs@new_defs), elim_ss@ss)
  ) ([],[]) groups3
  in
  let hpdefs1 =
    if !Globals.sa_elim_useless then
      List.map (fun (hp,(a,b,def)) ->
          (hp, (a,b,CF.subst_hrel_f def elim_ss))) hpdefs
    else
      hpdefs
  in
  hpdefs1

let generalize_hps_par_def prog non_ptr_unk_hps unk_hpargs post_hps par_defs=
  let pr1 = pr_list_ln SAU.string_of_par_def_w_name in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr3 = fun (_,a)-> pr2 a in
  Debug.no_2 "generalize_hps_par_def" !CP.print_svl pr1 (pr_list_ln pr3)
      (fun _ _ -> generalize_hps_par_def_x prog non_ptr_unk_hps unk_hpargs post_hps par_defs) post_hps par_defs

(**********get more definition from cs once, by right should loop************)
let generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs=
  let generalize_hps_one_cs constr=
    let lhs,rhs = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
    let lhds, lhvs,l_hp = CF.get_hp_rel_formula lhs in
    let rhds, rhvs,r_hp = CF.get_hp_rel_formula rhs in
    let hp_args = List.map (fun (id, eargs, _) -> (id, List.concat (List.map CP.afv eargs))) (l_hp@r_hp) in
    (*filer def hp out*)
    let diff = List.filter (fun (hp1,_) -> not(CP.mem_svl hp1 (hpdefs@callee_hps))) hp_args in
    match diff with
      | [] -> ([],[]) (*drop constraint, no new definition*)
      | [(hp,args)] -> begin
          if CP.mem_svl hp hpdefs then (*defined already drop constraint, no new definition*)
            let _ = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
            let _ = DD.ninfo_pprint ("         " ^ (!CP.print_sv hp) ^ " is defined already: drop the constraint") no_pos in
            ([constr],[])
          else if CP.mem_svl hp unk_hps then
            let _ = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
            let _ = DD.ninfo_pprint ("         " ^ (!CP.print_sv hp) ^ " is unknown. pass to next step") no_pos in
            ([constr],[])
          else
            let keep_ptrs = SAU.look_up_closed_ptr_args prog (lhds@rhds) (lhvs@rhvs) args in
            let p = CF.pos_of_formula lhs in
            let nlhs = CF.mkStar lhs rhs  CF.Flow_combine p in
            let hpargs = CF.get_HRels_f nlhs in
            let hpdefs1 =
              let lhps = CF.get_hp_rel_name_formula lhs in
              let rhps = CF.get_hp_rel_name_formula rhs in
              if (CP.intersect_svl lhps rhps) = [] then hpdefs else hpdefs@[hp]
            in
            let hpargs1 = List.filter (fun (hp1,_) -> CP.mem_svl hp1 hpdefs1) hpargs in
            let keep_def_hps = List.concat (List.map (SAU.get_intersect_hps keep_ptrs) hpargs1) in
            let r = CF.drop_data_view_hrel_nodes nlhs SAU.check_nbelongsto_dnode SAU.check_nbelongsto_vnode SAU.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in
            if (not (SAU.is_empty_f r)) then
              let _ = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
              let _ = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")=" ^
                  (Cprinter.prtt_string_of_formula r) ) no_pos in
                  ([],[(CP.HPRelDefn hp, (*CF.formula_of_heap*)
                  (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, p)) , r)])
            else
              ([constr],[])
        end
      | _ -> ([constr],[]) (*keep constraint, no new definition*)
  in
  let r = List.map generalize_hps_one_cs cs in
  let cs1, hp_defs = List.split r in
  (*combine hp_defs*)
  let hpdefs = SAU.combine_hpdefs (List.concat hp_defs) in
  (List.concat cs1, hpdefs)

let generalize_hps_cs prog callee_hps hpdefs unk_hps cs=
   let pr1 = pr_list_ln Cprinter.string_of_hprel in
   let pr3  = pr_list Cprinter.string_of_hp_rel_def in
   let pr4 (_,b) = pr3 b in
  Debug.no_3 "generalize_hps_cs" pr1 !CP.print_svl !CP.print_svl pr4
      (fun _ _ _ -> generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs) cs  callee_hps hpdefs

let generalize_hps_x prog callee_hps unk_hps sel_post_hps cs par_defs=
  DD.ninfo_pprint ">>>>>> step 6: generalization <<<<<<" no_pos;
(*general par_defs*)
  let non_ptr_unk_hps = List.concat (List.map (fun (hp,args) ->
      if List.exists (fun a ->
          not ( CP.is_node_typ a))
        args then [hp]
      else []) unk_hps) in
  let pair_names_defs = generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
(*for each constraints, we may pick more definitions*)
  let remain_constr, hp_def1 = generalize_hps_cs prog callee_hps hp_names (List.map fst unk_hps) cs in
  (*room for unk predicates processing*)
  (remain_constr, (hp_defs@hp_def1))

let generalize_hps prog callee_hps unk_hps sel_post_hps cs par_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln SAU.string_of_par_def_w_name in
  let pr3 = pr_list Cprinter.string_of_hp_rel_def in
  Debug.no_3 "generalize_hp" !CP.print_svl pr1 pr2 (pr_pair pr1 pr3)
      (fun _ _ _ -> generalize_hps_x prog callee_hps unk_hps sel_post_hps cs par_defs) callee_hps cs par_defs

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
  let m = List.map (SAU.match_one_hp_views vdcls) hp_defs in
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

let infer_shapes_init_post prog (constrs0: CF.hprel list) non_ptr_unk_hps sel_post_hps hp_rel_unkmap :(CP.spec_var list * CF.hp_rel_def list) =
  let unk_hps = [] in
  let par_defs = get_par_defs_post constrs0 in
  let _ = DD.info_pprint ">>>>>> post-predicates: step 3: remove redundant x!=null<<<<<<" no_pos in

  let _ = DD.info_pprint ">>>>>> post-predicates: step 4: weaken<<<<<<" no_pos in
  let pair_names_defs = generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
  (hp_names,hp_defs)

let infer_shapes_init_pre_x prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps hp_rel_unkmap :(CP.spec_var list * CF.hp_rel_def list) =
  let unk_hps = [] in
  let _ = DD.info_pprint ">>>>>> pre-predicates: step 3: simpl impl<<<<<<" no_pos in
  let pr_par_defs,rem_constr1 = get_par_defs_pre constrs0 in
  let _ = DD.info_pprint ">>>>>> pre-predicates: step 4: combine<<<<<<" no_pos in
  let par_defs, rem_constrs2 = combine_pdefs_pre pr_par_defs in
  let _ = DD.info_pprint ">>>>>> pre-predicates: step 6: remove redundant x!=null<<<<<<" no_pos in

  let _ = DD.info_pprint ">>>>>> pre-predicates: step 6: strengthen<<<<<<" no_pos in
  let rem_constrs3, hp_defs = generalize_hps prog callee_hps unk_hps sel_post_hps constrs0 par_defs in
 (* generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in *)
  (* let hp_names,hp_defs = List.split pair_names_defs in *)
  ([],hp_defs)

let infer_shapes_init_pre prog (constrs0: CF.hprel list) callee_hps non_ptr_unk_hps sel_post_hps hp_rel_unkmap :(CP.spec_var list * CF.hp_rel_def list) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.ho_1 "infer_shapes_init_pre" pr1 (pr_pair pr2 pr3)
      (fun _ -> infer_shapes_init_pre_x prog constrs0 callee_hps non_ptr_unk_hps sel_post_hps hp_rel_unkmap) constrs0

let partition_constrs_x constrs post_hps=
  let is_post_cs cs =
    let is_post =
      try
        let ohp = CF.extract_hrel_head cs.CF.hprel_rhs in
        match ohp with
          | Some hp -> (CP.mem_svl hp post_hps)
          | None -> false
      with _ -> false
    in
    is_post
  in
  List.partition is_post_cs constrs

let partition_constrs constrs post_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_svl in
  Debug.no_2 "partition_constrs" pr1 pr2 (pr_pair pr1 pr1)
      (fun _ _ -> partition_constrs_x constrs post_hps) constrs post_hps

let infer_shapes_core prog proc_name (constrs0: CF.hprel list) callee_hps sel_hp_rels sel_post_hps hp_rel_unkmap : (CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list)=
  (*move to outer func*)
  let callee_hps = [] in
  (********************************)
  (*unk analysis*)
  (* let constrs1c,unk_hps,hp_defs_split = analize_unk prog hp_rel_unkmap constrs1b in*)
  let unk_hps = [] in
  let _ = DD.info_pprint ">>>>>> step 1: apply transitive impilication<<<<<<" no_pos in
  let constrs1, non_unk_hps = apply_transitive_impl_fix prog callee_hps hp_rel_unkmap
    (List.map fst unk_hps) constrs0 in
  let _ = DD.info_pprint ">>>>>> step 2: remove unused predicates: not yet<<<<<<" no_pos in
  (*TODO: process constrs like H(x) & x = null --> G(x): separate into 2 constraints*)
  (*partition constraints into 2 groups: pre-predicates, post-predicates*)
  let post_constrs, pre_constrs = partition_constrs constrs1 sel_post_hps in
  (*find inital sol*)
  let _ = DD.info_pprint ">>>>>> pre-predicates<<<<<<" no_pos in
  let pre_hps, pre_defs = infer_shapes_init_pre prog pre_constrs callee_hps [] sel_post_hps hp_rel_unkmap in
  let _ = DD.info_pprint ">>>>>> post-predicates<<<<<<" no_pos in
  let post_hps, post_defs = infer_shapes_init_post prog post_constrs [] sel_post_hps hp_rel_unkmap in
  let defs = (pre_defs@post_defs) in
  (constrs1, defs,[])

let infer_shapes_x prog proc_name (constrs0: CF.hprel list) sel_hps sel_post_hps hp_rel_unkmap :(CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list) =
  (*move to outer func*)
  (* let callee_hpdefs = *)
  (*   try *)
  (*       Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name *)
  (*   with _ -> [] *)
  (* in *)
  (* let callee_hps = List.map (fun (hpname,_,_) -> SAU.get_hpdef_name hpname) callee_hpdefs in *)
  let unk_hp_svl1 = [] in
  let callee_hps = [] in
  let constr, hp_defs, c = infer_shapes_core prog proc_name constrs0 callee_hps sel_hps sel_post_hps hp_rel_unkmap in
  let m = match_hps_views hp_defs prog.CA.prog_view_decls in
  let sel_hp_defs = collect_sel_hp_def hp_defs sel_hps unk_hp_svl1 m in
  let _ = List.iter (fun hp_def -> rel_def_stk # push hp_def) sel_hp_defs in
  (constr, hp_defs, c)

let infer_shapes prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hp_rels hp_rel_unkmap:
 (CF.hprel list * CF.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) =
  let pr0 = pr_list !CP.print_exp in
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in
  let pr4 = pr_list (pr_pair !CP.print_sv CP.string_of_xpure_view) in
  Debug.no_4 "infer_shapes" pr_id pr1 !CP.print_svl pr4 (pr_triple pr1 pr2 pr3)
      (fun _ _ _ _ -> infer_shapes_x prog proc_name hp_constrs sel_hp_rels sel_post_hp_rels hp_rel_unkmap) proc_name hp_constrs sel_post_hp_rels hp_rel_unkmap
