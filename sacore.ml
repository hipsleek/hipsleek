open Globals
open Gen
open Label_only

module DD = Debug
module Err = Error
module CA = Cast
module AS = Astsimp
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher
module SAU = Sautility
module SAO = Saout
module Inf = Infer

let cmp_hp_pos (hp1,pos1) (hp2,pos2)= (CP.eq_spec_var hp1 hp2) && pos1=pos2

let cs_rhs_is_only_neqNull cs=
  let lhs_hpargs = CF.get_HRels_f cs.CF.hprel_lhs in
  let args = List.fold_left (fun ls (_, args) -> ls@args) [] lhs_hpargs in
  CF.is_only_neqNull args [] cs.CF.hprel_rhs


(* (\* *)
(* That means the following priorities: *)
(*    1. H(..) --> H2(..) *)
(*    2. H(..) | G --> H2(..) *)
(*    3. H(..) * D --> H2(..) *)
(*    4. H(..)  --> D*H2(..) *)
(* *\) *)
(* let ranking_frozen_mutrec_preds_x pr_hp_cs= *)
(*   let pre_preds_4_equal_w_prio = List.map (fun (hp,cs,deps) -> *)
(*       let is_lhs_emp = (CF.extract_hrel_head cs.CF.hprel_lhs <> None) in *)
(*       let is_rhs_emp = (CF.extract_hrel_head cs.CF.hprel_rhs <> None) in *)
(*       let is_empty_both = is_lhs_emp && (deps=[]) in *)
(*       let is_guard = (cs.CF.hprel_guard <> None) && is_rhs_emp in *)
(*       (hp,cs, is_empty_both, is_guard, (not is_lhs_emp) && is_rhs_emp , CF.get_h_size_f cs.CF.hprel_rhs) *)
(*   ) *)
(*     pr_hp_cs *)
(*   in *)
(*   (\*first ranking*\) *)
(*   let fst_ls = List.filter (fun (_,_, is_empty_both, _, _ , _) ->  is_empty_both) pre_preds_4_equal_w_prio in *)
(*   match fst_ls with *)
(*     | (hp,cs,_,_,_,_)::_ -> [(hp,[cs])] *)
(*     | _ -> begin *)
(*         let snd_ls = List.filter (fun (_,_, _, is_guard, _ , _) ->  is_guard) pre_preds_4_equal_w_prio in *)
(*         match snd_ls with *)
(*           | (hp,cs,_,_,_,_)::_ -> [(hp,[cs])] *)
(*           | _ -> begin *)
(*               let rd_ls = List.filter (fun (_,_, _, _, is_emp_r , _) ->  is_emp_r) pre_preds_4_equal_w_prio in *)
(*               match rd_ls with *)
(*                 | (hp,cs,_,_,_,_)::_ -> [(hp,[cs])] *)
(*                 | _ -> begin *)
(*                     let hp,cs,_,_,_,_ = List.fold_left (fun (hp0,cs0,a0,b0,c0, s0) (hp1,cs1,a1,b1,c1, s1) -> *)
(*                         if s1<s0 then (hp1,cs1,a1,b1,c1, s1) else (hp0,cs0,a0, b0, c0, s0) *)
(*                     ) (List.hd pre_preds_4_equal_w_prio) (List.tl pre_preds_4_equal_w_prio) in *)
(*                     [(hp,[cs])] *)
(*                   end *)
(*             end *)
(*       end *)

(* let ranking_frozen_mutrec_preds pr_hp_cs= *)
(*   let pr1 = Cprinter.string_of_hprel_short in *)
(*   let pr2 = pr_list_ln (pr_pair !CP.print_sv (pr_list_ln pr1)) in *)
(*   let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 !CP.print_svl) in *)
(*   Debug.no_1 "ranking_frozen_mutrec_preds" pr3 pr2 *)
(*       (fun _ -> ranking_frozen_mutrec_preds_x pr_hp_cs) *)
(*       pr_hp_cs *)

(* (\* *)
(*   find all pre-preds that has only one assumption ===> equal *)
(* *\) *)
(* let search_pred_4_equal_x constrs post_hps frozen_hps= *)
(*   let ignored_hps = post_hps@frozen_hps in *)
(*   let partition_pre_preds (pre_preds, rem_constrs, tupled_hps) cs= *)
(*     let l_hpargs = CF.get_HRels_f cs.CF.hprel_lhs in *)
(*     let r_hpargs = CF.get_HRels_f cs.CF.hprel_rhs in *)
(*     let rhps = List.map fst r_hpargs in *)
(*     match l_hpargs with *)
(*       | [] -> (pre_preds, rem_constrs@[cs],tupled_hps) *)
(*       | [(hp,_)] -> if CP.mem_svl hp ignored_hps then (pre_preds, rem_constrs@[cs],tupled_hps) *)
(*         else *)
(*          (pre_preds@[(hp,cs, CP.diff_svl rhps (ignored_hps))],rem_constrs,tupled_hps) *)
(*       | _ -> let linter = List.fold_left (fun ls (hp,args) -> *)
(*             if not (CP.mem_svl hp ignored_hps) && List.exists (fun (_,args1) -> *)
(*                 SAU.eq_spec_var_order_list args args1 *)
(*             ) r_hpargs then *)
(*               ls@[hp] *)
(*             else ls *)
(*         ) [] l_hpargs in *)
(*             if linter  = [] then (pre_preds, rem_constrs@[cs], tupled_hps@(List.map fst l_hpargs)) *)
(*             else *)
(*               (pre_preds@(List.map (fun hp -> (hp,cs, CP.diff_svl rhps (ignored_hps))) linter), rem_constrs,tupled_hps) *)
(*   in *)
(*   let check_is_guard cs = match cs.CF.hprel_guard with *)
(*     | None -> false *)
(*     | Some _ -> true *)
(*   in *)
(*   (\* let pr1 = Cprinter.string_of_hprel_short in *\) *)
(*   let rec partition_equal (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps) ls_pre= *)
(*    match ls_pre with *)
(*      | [] -> (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps) *)
(*      | (hp0, cs0, dep_hps0)::rest -> *)
(*            (\* let _ = Debug.info_pprint ("   cs0: " ^ (pr1 cs0)) no_pos in *\) *)
(*            let _ = Debug.ninfo_pprint ("   hp0: " ^ (!CP.print_sv hp0)) no_pos in *)
(*            let is_rec, is_guard, dep_hps, grp,rest1 = List.fold_left (fun (r_rec,r_guard, r_deps, ls1,ls2) (hp1,cs1,dep_hps1) -> *)
(*                (\* let _ = Debug.info_pprint ("   cs1: " ^ (pr1 cs1)) no_pos in *\) *)
(*                if CP.eq_spec_var hp1 hp0 then *)
(*                  (r_rec || CP.mem_svl hp1 dep_hps1, r_guard || ( check_is_guard cs1), r_deps@dep_hps1,  ls1@[cs1], ls2) *)
(*                else *)
(*                  (r_rec, r_guard,r_deps, ls1, ls2@[(hp1,cs1,dep_hps1)]) *)
(*            ) (CP.mem_svl hp0 dep_hps0,  check_is_guard cs0, dep_hps0, [],[]) rest in *)
(*            let grp1 = (cs0::grp) in *)
(*            (\* let _ = Debug.info_pprint ("   is_guard: " ^ (string_of_bool is_guard)) no_pos in *\) *)
(*            (\* let _ = Debug.info_pprint ("   is_rec: " ^ (string_of_bool is_rec)) no_pos in *\) *)
(*            (\*has more than one constraints: disj but not recursive also join the race*\) *)
(*            let n_res = if List.length grp1 > 1 then *)
(*              if not is_rec && is_guard then *)
(*                (\* let _ = Debug.info_pprint ("   0: ") no_pos in *\) *)
(*                (cand_equal, complex_nrec_ndep, complex_non_rec@[(hp0,grp1)], complex_hps) *)
(*              else if  not is_rec && dep_hps = [] then *)
(*                (cand_equal, complex_nrec_ndep@[(hp0,grp1)], complex_non_rec, complex_hps) *)
(*              else *)
(*                (\* let _ = Debug.info_pprint ("   1: ") no_pos in *\) *)
(*                (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps@[hp0]) *)
(*            else *)
(*              if is_guard then *)
(*                (\* let _ = Debug.info_pprint ("   2: ") no_pos in *\) *)
(*                (cand_equal, complex_nrec_ndep, complex_non_rec@[(hp0,grp1)], complex_hps) *)
(*              else if is_rec then *)
(*                (\* let _ = Debug.info_pprint ("   3: ") no_pos in *\) *)
(*                (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps@[hp0]) *)
(*              else *)
(*                (\* let _ = Debug.info_pprint ("   4: ") no_pos in *\) *)
(*                (cand_equal@[(hp0,cs0, dep_hps0)],complex_nrec_ndep, complex_non_rec, complex_hps) *)
(*            in *)
(*            partition_equal n_res rest1 *)
(*   in *)
(*   (\*tupled_hps: will be processed as pre-oblg *\) *)
(*   let pr_pre_preds, _, tupled_hps = List.fold_left partition_pre_preds ([],[],[]) constrs in *)
(*   let pre_preds_cand_equal0, complex_nrec_ndep, complex_nonrec_guard_grps, complex_hps = *)
(*     partition_equal ([],[],[],[]) pr_pre_preds *)
(*   in *)
(*   let pr2 (a,_,_) = !CP.print_sv a in *)
(*   let _ = Debug.ninfo_pprint ("    pre_preds_cand_equal: " ^ ((pr_list pr2) pre_preds_cand_equal0)) no_pos in *)
(*   let _ = Debug.ninfo_pprint ("    tupled_hps: " ^ (!CP.print_svl tupled_hps)) no_pos in *)
(*   (\*filter the tupled_hps *\) *)
(*   let pre_preds_cand_equal1 = List.filter (fun (hp,_,_) -> not (CP.mem_svl hp tupled_hps)) pre_preds_cand_equal0 in *)
(*   (\*filter frozen candidates that depends on others. they will be synthesized next round.*\) *)
(*   (\* let cand_equal_hps = List.map fst3 pre_preds_cand_equal1 in *\) *)
(*   let nonrec_complex_guard_hps = List.map fst complex_nonrec_guard_grps in *)
(*   (\*remove one that depends on the guard, the guard should go first*\) *)
(*   let _ = Debug.ninfo_pprint ("    nonrec_complex_guard_hps: " ^ (!CP.print_svl nonrec_complex_guard_hps)) no_pos in *)
(*   let pre_preds_4_equal = List.fold_left (fun ls_cand (hp,cs,deps) -> *)
(*       if CP.intersect_svl deps nonrec_complex_guard_hps = [] then *)
(*         ls_cand@[(hp,cs)] *)
(*       else ls_cand *)
(*   ) [] pre_preds_cand_equal1 in *)
(*   (\*mut rec dep*\) *)
(*   let pre_preds_4_equal1 = (\* if pre_preds_4_equal = [] && pre_preds_cand_equal1 <> [] then *\) *)
(*     if  pre_preds_4_equal  <> [] then *)
(*     ranking_frozen_mutrec_preds pre_preds_cand_equal1 *)
(*     else [] *)
(*   in *)
(*   (\*process_complex, nonrec, non depend on others *)
(*     testcases: check-dll.ss; check-sorted *)
(*   *\) *)
(*   let pre_preds_4_equal2 = if pre_preds_4_equal1 = [] then *)
(*     (\*remove the tupled ones*\) *)
(*     let complex_nrec_ndep1 = List.filter (fun (hp,_) -> not(CP.mem_svl hp tupled_hps)) complex_nrec_ndep in *)
(*     match complex_nrec_ndep1 with *)
(*       | (hp,constrs)::_ ->  [(hp,constrs)] *)
(*       | _ -> [] *)
(*   else pre_preds_4_equal1 *)
(*   in *)
(*   let pre_preds_4_equal3 = if pre_preds_4_equal2 = [] then *)
(*     (\*process_complex, nonrec*\) *)
(*     match complex_nonrec_guard_grps with *)
(*       | (hp,constrs)::_ ->  [(hp,constrs)] *)
(*       | _ -> [] *)
(*   else pre_preds_4_equal2 *)
(*   in *)
(*   (pre_preds_4_equal3, complex_hps) *)

(* let search_pred_4_equal constrs post_hps frozen_hps= *)
(*   let pr1 = Cprinter.string_of_hprel_short in *)
(*   let pr2 = pr_list_ln (pr_pair !CP.print_sv (pr_list_ln pr1)) in *)
(*   let pr3 = pr_list_ln pr1 in *)
(*   Debug.no_3 "search_pred_4_equal" pr3 !CP.print_svl !CP.print_svl (pr_pair pr2 !CP.print_svl) *)
(*       (fun _ _ _ -> search_pred_4_equal_x constrs post_hps frozen_hps) *)
(*       constrs post_hps frozen_hps *)

let rec build_unk_locs args n unk_svl res=
  match args with
    | [] -> res
    | sv::rest -> let new_res=
        if CP.mem_svl sv unk_svl then
        (res@[n])
        else res
      in
      build_unk_locs rest (n+1) unk_svl new_res

let rec lookup_xpure_view hp_pos0 rem_map done_map=
  match rem_map with
    | [] -> None,done_map
    | (hp_pos1,xpv)::tl ->
          if Gen.BList.intersect_eq cmp_hp_pos hp_pos0 hp_pos1 <> [] then
            let new_hp_pos = Gen.BList.remove_dups_eq cmp_hp_pos (hp_pos0@hp_pos1) in
            Some xpv,done_map@[(new_hp_pos,xpv)]@tl
          else lookup_xpure_view hp_pos0 tl (done_map@[(hp_pos1,xpv)])

(*
  priority of xpure name:
  - unk_hps in lhs
  - unk_hps in rhs
  - partial unk_hps in lhs
  - partial unk_hps in rhs
*)
let generate_xpure_view_w_pos_x ls_hp_pos_sv total_unk_map pos=
  let generate_xpure_view_one_sv unk_map (ls_hp_pos,sv)=
    let p,unk_map =
      let xpvs,new_map = lookup_xpure_view ls_hp_pos unk_map [] in
      match xpvs with
        | Some xp ->
              let new_xpv = {xp with CP.xpure_view_arguments = [sv];} in
              let p = CP.mkFormulaFromXP new_xpv in
              (p,new_map)
        | None ->
              let hp_name = (* CP.fresh_old_name *)
                (* (CP.name_of_spec_var (fst (List.hd ls_hp_pos)))  *)
                let name,_ = List.hd ls_hp_pos in
                (CP.name_of_spec_var name) (* ^ "_" ^ (string_of_int p) *)
              in
              let xpv = { CP.xpure_view_node = None;
              CP.xpure_view_name = hp_name;
              CP.xpure_view_arguments = [sv];
              CP.xpure_view_remaining_branches= None;
              CP.xpure_view_pos = pos;
              }
              in
              let p = CP.mkFormulaFromXP xpv in
              (p,unk_map@[(ls_hp_pos,xpv)])
    in
    (p,unk_map)
  in
  let ps,ls_unk_map = List.fold_left (fun (ps,cur_map) (ls_hp_pos,sv) ->
      let p, new_map = generate_xpure_view_one_sv cur_map (ls_hp_pos,sv) in
      (ps@[p], new_map)
  ) ([],total_unk_map) ls_hp_pos_sv in
  (CP.conj_of_list ps pos, ls_unk_map)

let generate_xpure_view_w_pos ls_hp_pos_sv total_unk_map pos=
  let pr1 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) !CP.print_sv) in
  let pr2 = pr_pair !CP.print_formula
    (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  Debug.no_1 "generate_xpure_view_w_pos" pr1 pr2
      (fun _ -> generate_xpure_view_w_pos_x ls_hp_pos_sv total_unk_map pos) ls_hp_pos_sv

let rec find_pos n sv res (hp,args)=
  match args with
    | [] -> res
    | sv1::rest -> if CP.eq_spec_var sv sv1 then (res@[(hp,n)])
      else
        find_pos (n+1) sv res (hp,rest)

let generate_unk_svl_map ls_hpargs sv=
  (List.fold_left (find_pos 0 sv) [] ls_hpargs,sv)

let generate_map_x l_hpargs r_hpargs unk_map pos=
  let l_args = List.fold_left (fun ls (_, args) -> ls@args) [] l_hpargs in
  let r_args = List.fold_left (fun ls (_, args) -> ls@args) [] r_hpargs in
  let unk_svl1 = CP.remove_dups_svl (CP.intersect_svl l_args r_args) in
  let ls_hp_pos_sv = List.map (generate_unk_svl_map (l_hpargs@r_hpargs)) unk_svl1 in
  let unk_pure,new_map = generate_xpure_view_w_pos ls_hp_pos_sv unk_map pos in
  (unk_svl1, unk_pure, new_map)

let generate_map unk_l_hpargs r_hpargs unk_map pos=
  let pr1= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  let pr2 = !CP.print_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "generate_map" pr3 pr3 pr1 (pr_triple !CP.print_svl pr2 pr1)
      (fun _ _ _ -> generate_map_x unk_l_hpargs r_hpargs unk_map pos)
      unk_l_hpargs r_hpargs unk_map

let generate_xpure_view_hp_x drop_hpargs total_unk_map=
  let rec lookup_xpure_view hp rem_map=
    match rem_map with
      | [] -> []
      | ((hp1,_),xpv)::tl ->
          if CP.eq_spec_var hp hp1 then
            [xpv]
          else lookup_xpure_view hp tl
  in
  let generate_xpure_view_one_hp pos unk_map (hp,args, locs)=
    let hp_name = CP.name_of_spec_var hp in
    let p,unk_svl,unk_map =
      let xpvs = lookup_xpure_view hp unk_map in
      match xpvs with
        | [xp] -> (* let xp_r, xp_args = match xp.CP.xpure_view_node with *)
          (*     | None -> None, xp.CP.xpure_view_arguments *)
          (*     |Some _ -> Some (List.hd args), (List.tl args) *)
          (* in *)
          let new_args = SAU.retrieve_args_from_locs args locs in
          let new_xpv = {xp with (* CP.xpure_view_node =  List.hd new_args; *)
              CP.xpure_view_arguments =  new_args
          }
          in
          let p = CP.mkFormulaFromXP new_xpv in
          (p,args,unk_map)
        | [] ->
              let xpv = { CP.xpure_view_node = None;
              CP.xpure_view_name = hp_name;
              CP.xpure_view_arguments = args;
              CP.xpure_view_remaining_branches= None;
              CP.xpure_view_pos = no_pos;
              }
              in
              let p = CP.mkFormulaFromXP xpv in
              (p,args, unk_map@[((hp,locs),xpv)])
        | _ -> report_error no_pos "cformula.generate_xpure_view: impossible"
    in
    (p,unk_svl,unk_map)
  in
  let ps,ls_fr_svl,ls_unk_map = List.fold_left ( fun (ps, unk_svl, unk_map) hp_args_locs ->
      let p, new_unk_svl, new_map = generate_xpure_view_one_hp no_pos unk_map hp_args_locs in
      (ps@[p], unk_svl@new_unk_svl, new_map)
  ) ([], [], total_unk_map) drop_hpargs in
  (CP.remove_dups_svl ls_fr_svl, CP.conj_of_list ps no_pos, ls_unk_map)

let generate_xpure_view_hp drop_hpargs total_unk_map=
  let pr1 = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) in
  (* let pr3 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr3 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr2 = pr_triple !CP.print_svl !CP.print_formula pr3 in
  Debug.no_1 "generate_xpure_view_hp" pr1 pr2
      (fun _ -> generate_xpure_view_hp_x drop_hpargs total_unk_map) drop_hpargs

let generate_unk_svl_pos cs_unk_svl (hp,args)=
  let hp_unk_svl = CP.intersect_svl args cs_unk_svl in
  let locs = build_unk_locs args 0 hp_unk_svl [] in
  (hp, hp_unk_svl, locs)

let generate_map_unk_hp_x l_hpargs r_hpargs unk_map pos=
  let l_args = List.fold_left (fun ls (_, args) -> ls@args) [] l_hpargs in
  let r_args = List.fold_left (fun ls (_, args) -> ls@args) [] r_hpargs in
  let unk_svl1 = CP.remove_dups_svl (CP.intersect_svl l_args r_args) in
  if unk_svl1 = [] then ([], CP.mkTrue pos, unk_map) else
  let ls_hp_args_pos = List.map (generate_unk_svl_pos unk_svl1)
    (Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (l_hpargs@r_hpargs)) in
  let _,unk_pure,new_map = generate_xpure_view_hp ls_hp_args_pos unk_map in
  (unk_svl1, unk_pure, new_map)

let generate_map_unk_hp unk_l_hpargs r_hpargs unk_map pos=
  (* let pr1= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr1 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr2 = !CP.print_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "generate_map_unk_hp" pr3 pr3 pr1 (pr_triple !CP.print_svl pr2 pr1)
      (fun _ _ _ -> generate_map_unk_hp_x unk_l_hpargs r_hpargs unk_map pos)
      unk_l_hpargs r_hpargs unk_map

let generate_linking_full_hp_x unk_map unk_hps lhs_hpargs rhs_hpargs ss post_hps pos=
  let post_hpargs = List.filter (fun (hp, _) -> CP.mem_svl hp post_hps) rhs_hpargs in
  if post_hpargs = [] then ([], CP.mkTrue pos, unk_map) else
    let lhs_hpargs1 = List.map (fun (hp,args) -> (hp, CP.subst_var_list ss args)) lhs_hpargs in
    let post_hpargs1 = List.map (fun (hp,args) -> (hp, CP.subst_var_list ss args)) post_hpargs in
    let lhs_hpargs2 = List.filter (fun (hp, _) -> not(CP.mem_svl hp post_hps) && CP.mem_svl hp unk_hps) lhs_hpargs1 in
    generate_map_unk_hp lhs_hpargs2 post_hpargs1 unk_map pos

let generate_linking_full_hp unk_map unk_hps lhs_hpargs rhs_hpargs ss post_hps pos=
  let pr1 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = !CP.print_formula in
  let pr5 = pr_triple pr2 pr4 pr1 in
  Debug.no_5 "generate_linking_full_hp" pr1 pr2 pr3 pr3 pr2 pr5
      (fun _ _ _ _ _ -> generate_linking_full_hp_x unk_map unk_hps lhs_hpargs rhs_hpargs ss post_hps pos)
      unk_map unk_hps lhs_hpargs rhs_hpargs post_hps

let generate_linking unk_map lhs_hpargs rhs_hpargs post_hps pos=
  let rec lookup_xpure_view hp rem_map=
    match rem_map with
      | [] -> None
      | ((hp1,locs),xpv)::tl ->
          if CP.eq_spec_var hp hp1 then
            Some (locs,xpv)
          else lookup_xpure_view hp tl
  in
  (* let rec build_full_locs args n res= *)
  (*   match args with *)
  (*     | [] -> res *)
  (*     | _::rest -> build_full_locs rest (n+1) (res@[n]) *)
  (* in *)
  let generate_xpure_view_map unk_map (pre_hp, post_hps, args)=
    let p,unk_svl,unk_map =
      let oxpv = lookup_xpure_view pre_hp unk_map in
      let post_hps1 = List.filter (fun hp ->
          lookup_xpure_view hp unk_map = None) post_hps in
      match oxpv with
        | Some (locs,xp) ->
              let new_xpv = {xp with
                  CP.xpure_view_arguments =  args
              }
              in
              let new_maps = List.map (fun hp -> ((hp, locs), new_xpv)) post_hps1 in
              let p = CP.mkFormulaFromXP new_xpv in
              (p,args,unk_map@new_maps)
        | None ->
              (* let hp_name = CP.name_of_spec_var pre_hp in *)
              (* let xpv = { CP.xpure_view_node = None; *)
              (* CP.xpure_view_name = hp_name; *)
              (* CP.xpure_view_arguments = args; *)
              (* CP.xpure_view_remaining_branches= None; *)
              (* CP.xpure_view_pos = no_pos; *)
              (* } *)
              (* in *)
              (* let locs = build_full_locs args 0 [] in *)
              (* let new_maps = List.map (fun hp -> *)
              (*     ((hp, locs), xpv)) (pre_hp::post_hps1) in *)
              (* let p = CP.mkFormulaFromXP xpv in *)
              (* (p ,args, unk_map@new_maps) *)
              (CP.mkTrue pos, [], unk_map)
    in
    (p,unk_svl,unk_map)
  in
  let post_hpargs = List.filter (fun (hp, _) -> CP.mem_svl hp post_hps) rhs_hpargs in
  let lhs_hpargs1 = List.filter (fun (hp, _) -> not (CP.mem_svl hp post_hps)) lhs_hpargs in
  if post_hpargs <> [] then
    (*   let lhs_hpargs1 = List.map (fun (hp,args) -> (hp, CP.subst_var_list ss args)) lhs_hpargs in *)
  (*   let post_hpargs1 = List.map (fun (hp,args) -> (hp, CP.subst_var_list ss args)) post_hpargs in *)
    let unk_hps_args = List.fold_left (fun ls (hp1, args1) ->
        let m_post_hpargs =  List.filter (fun (hp2,args2) ->
             SAU.eq_spec_var_order_list args1 args2
        ) post_hpargs
        in
        if m_post_hpargs = [] then ls else
        let m_post_hps = List.map fst m_post_hpargs in
        ls@[(hp1,m_post_hps, args1)]
    ) [] lhs_hpargs1
    in
    let ps,unk_svl, ls_unk_map = List.fold_left (fun (ps,cur_svl, cur_map) unk ->
        let p, new_svl, new_map = generate_xpure_view_map cur_map unk in
        (ps@[p], cur_svl@new_svl, new_map)
    ) ([],[],unk_map) unk_hps_args in
    (CP.remove_dups_svl unk_svl, CP.conj_of_list ps pos, ls_unk_map)
  else
    let unk_hpargs = List.filter (fun hpargs1 ->
        List.exists (fun hpargs2 -> SAU.check_hp_arg_eq hpargs1 hpargs2) rhs_hpargs
    ) lhs_hpargs1
    in
    generate_map_unk_hp unk_hpargs unk_hpargs unk_map pos
  (* generate_linking_full_hp unk_map unk_hps lhs_hpargs rhs_hpargs ss post_hps pos *)

let analize_unk_new_x prog constrs total_unk_map=
  let dalnging_analysis (constrs1,unk_map) cs =
    let l_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
      (CF.get_hprel cs.CF.hprel_lhs) in
    let r_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
      (CF.get_hprel cs.CF.hprel_rhs) in
    let unk_svl =
      let unk_svl = List.fold_left (fun o_unk_svl (_,l_args) ->
          o_unk_svl@(List.fold_left (fun i_unk_svl (_, r_args) ->
              i_unk_svl@(CP.intersect_svl l_args r_args)
          ) [] r_hpargs)
      ) [] l_hpargs
      in
      CP.remove_dups_svl (CP.diff_svl (unk_svl) cs.CF.unk_svl)
    in
    let pos = CF.pos_of_formula cs.CF.hprel_lhs in
    let ls_hp_pos_sv = List.map (generate_unk_svl_map (l_hpargs@r_hpargs)) unk_svl in
    let unk_pure,new_map = generate_xpure_view_w_pos ls_hp_pos_sv unk_map pos in
    let unk_svl1 = cs.CF.unk_svl@unk_svl in
    let new_lhs = CF.mkAnd_pure cs.CF.hprel_lhs (MCP.mix_of_pure unk_pure) pos in
    let cs1 = {cs with CF.unk_svl = unk_svl1;
        CF.hprel_lhs = new_lhs}
    in
    (constrs1@[cs1],new_map)
  in
  let new_constrs,new_map = List.fold_left (dalnging_analysis) ([],[]) constrs in
  (new_constrs,total_unk_map@(List.map (fun (ls_hp_pos, xp) -> List.map fst ls_hp_pos,xp) new_map))

let analize_unk_new prog constrs total_unk_map=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 (cs,_) = pr1 cs in
  Debug.no_1 "analize_unk_new" pr1 pr2
      (fun _ -> analize_unk_new_x prog constrs total_unk_map) constrs


(*=============UNKOWN================*)
(*find diff for each hrel*)
(*return unk_hp_locs * full_unk_args_locs*)
let build_hp_unk_locs known_svl unk_hps fn_cmp (hp_name, args)=
   let rec helper args (res1,res2) index all=
    match args with
      | [] -> res1,res2
      | a::ass -> if (fn_cmp a all) (* || not(CP.is_node_typ a) *) then
            helper ass (res1,res2) (index+1) all
          else helper ass (res1@[index], res2@[a]) (index+1) all
   in
   let rec helper1 args res index=
    match args with
      | [] -> res
      | a::ass -> helper1 ass (res@[index]) (index+1)
  in
  let get_unk_ptr all_ptrs (hp_name, largs)=
    (* if all_ptrs = [] then [(hp_name,[-1])] (\*[] mean dont have any information*\) *)
    (* else *)
      begin
          let res,unk_args =
            if CP.mem_svl hp_name unk_hps then
              (helper1 largs [] 0, largs) (*this is a dangling predicate*)
            else
              helper largs ([],[]) 0 all_ptrs
          in
          if res = [] then ([(hp_name,[], [-1])],[]) (*renturn -1 to indicate that none is allowed to drop*)
          else
            (*check full unk hp*)
            (* let pr1 = pr_list string_of_int in *)
            (* let _ = Debug.info_pprint ("   hp: " ^ (!CP.print_sv hp_name)) no_pos in *)
            (* let _ = Debug.info_pprint ("     res: " ^ (pr1 res)) no_pos in *)
            (* let _ = Debug.info_pprint ("     largs: " ^ (!CP.print_svl largs)) no_pos in *)
            if (List.length res) = (List.length largs) then
              ([(hp_name, largs, res)],[(hp_name, largs,res)])
            else ([(hp_name,unk_args, res)],[])
      end
  in
  get_unk_ptr known_svl (hp_name, args)

let check_equality_constr lhpargs lhs_f_rem rhs svl2=
  (*handle equality*)
  (* let _ = Debug.info_pprint ("   svl2: " ^ (!CP.print_svl svl2)) no_pos in *)
  if svl2 <> [] then svl2 else
    match lhpargs with
      | [(_,args)] ->
            (* let _ = Debug.info_pprint ("   rhs: " ^ (!CF.print_formula rhs)) no_pos in *)
            if SAU.is_empty_heap_f lhs_f_rem && SAU.is_empty_heap_f rhs then
              match args with
                | sv::_ ->
                      let ( _,mix_f,_,_,_) = CF.split_components rhs in
                      let reqs2 = (MCP.ptr_equations_without_null mix_f) in
                      let cl_svl = CP.remove_dups_svl (CF.find_close [sv] reqs2) in
                      (* let _ = Debug.info_pprint ("   cl_svl: " ^ (!CP.print_svl cl_svl)) no_pos in *)
                      if (* List.length cl_svl >1 && *)
                        CP.diff_svl cl_svl args = [] then
                        args
                      else svl2
                | _ -> svl2
            else svl2
      | _ -> svl2

(*analysis unknown information*)
let rec analize_unk_one prog unk_hps constr =
  let _ = Debug.ninfo_pprint ("   hrel: " ^ (Cprinter.string_of_hprel constr)) no_pos in
 (*elim hrel in the formula and returns hprel_args*)
  (*lhs*)
  let lhs1,lhrels = SAU.drop_get_hrel constr.CF.hprel_lhs in
  (*rhs*)
  let rhs1,rhrels = SAU.drop_get_hrel constr.CF.hprel_rhs in
(*find fv of lhs + rhs wo hrels*)
  (* let lsvl = SAU.get_raw_defined_w_pure prog lhs1 in *)
  (* let rsvl = SAU.get_raw_defined_w_pure prog rhs1 in *)
  let svl = SAU.get_raw_defined_w_pure prog constr.CF.predef_svl lhs1 rhs1 in
  (*handle equality*)
  let svl1 = check_equality_constr lhrels lhs1 constr.CF.hprel_rhs svl in
  (*return*)
  let unk_hp_locs,unk_hp_args_locs = List.split (List.map (build_hp_unk_locs (svl1) unk_hps CP.mem_svl) (lhrels@rhrels)) in
  (List.concat unk_hp_locs, List.concat unk_hp_args_locs)

and find_closure_post_hps_x post_hps ls_unk_hps_args =
  let cs_post_args,cs_poss_post_hpargs = List.fold_left (fun (r1,r2) (hp,args) ->
      if CP.mem_svl hp post_hps then (r1@args, r2) else (r1,r2@[(hp,args)])
  ) ([],[]) ls_unk_hps_args
  in
  (* let post_args = List.fold_left (fun ls (_,args) -> ls@args) [] cs_post_hpargs in *)
  let post_args = CP.remove_dups_svl cs_post_args in
  let new_post_hp = List.fold_left (fun ls (hp,args) ->
      if CP.intersect_svl args post_args <> [] then (ls@[hp]) else ls
  ) [] cs_poss_post_hpargs in
  new_post_hp

and find_closure_post_hps post_hps ls_unk_hps_args=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv pr1) in
  Debug.no_2 "find_closure_post_hps" pr1 pr2 pr1
      (fun _ _ -> find_closure_post_hps_x post_hps ls_unk_hps_args)
      post_hps ls_unk_hps_args

and double_check_unk prog post_hps unk_hp_args_locs unk_hps cs=
  let lhds, lhvs, lhrels = CF.get_hp_rel_formula cs.CF.hprel_lhs in
  let rhds, rhvs, rhrels = CF.get_hp_rel_formula cs.CF.hprel_rhs in
  let cs_hprels = List.map (fun (hp,eargs,_) ->
      (hp, List.fold_left List.append [] (List.map CP.afv eargs))) (lhrels@rhrels) in
  (*return: unk_args*)
  let rec retrieve_args_one_hp ls (hp,args)=
    match ls with
      | [] -> ([],args)
      | (hp1,_,locs)::ss -> if CP.eq_spec_var hp hp1 then
            begin
                (*find unknown hprel*)
                if (List.length args) = (List.length locs) then
                  (args,[])
                else
                  let unk_svl = CP.remove_dups_svl (SAU.retrieve_args_from_locs args locs) in
                  (unk_svl, CP.diff_svl args unk_svl)
            end
          else retrieve_args_one_hp ss (hp,args)
  in
  let double_check_one_constr unk_hp_args_locs cs_hprels=
    let unk_hp_names = List.map (fun (hp, _,_) -> hp) unk_hp_args_locs in
    let cs_hp_args = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq (cs_hprels) in
    let cs_unk_hps,cs_non_unk_hps = List.partition
      (fun (hp,_) -> CP.mem_svl hp unk_hp_names) cs_hp_args in
    (* definitely non unk*)
    let cs_non_unk_svl = List.concat (List.map (fun (_, args) -> args) cs_non_unk_hps) in
    (*possible unk*)
    let unk_svl_hps, cs_non_unk_svl2 = List.fold_left (fun (ls1, ls2) hp_args ->
        let unk_svl, non_unk_svl = retrieve_args_one_hp unk_hp_args_locs hp_args in
        (ls1@unk_svl, ls2@non_unk_svl)
    ) ([],[]) cs_unk_hps in
    let cs_non_unk_svl1 =
      CP.remove_dups_svl (* (SAU.look_up_closed_ptr_args prog (lhds@rhds) (lhvs@rhvs) *) (cs_non_unk_svl2@cs_non_unk_svl)
          (* ) *)
    in
    let poss_unk_svl_hps = CP.remove_dups_svl unk_svl_hps in
    let _ = Debug.ninfo_pprint ("  poss_unk_svl_hps: " ^ (!CP.print_svl poss_unk_svl_hps)) no_pos in
    let _ = Debug.ninfo_pprint ("  cs_non_unk_svl1: " ^ (!CP.print_svl cs_non_unk_svl1)) no_pos in
    (*actually unk = poss unk - non-unk*)
    let real_unk_svl_hps = Gen.BList.difference_eq CP.eq_spec_var poss_unk_svl_hps cs_non_unk_svl1 in
    let ls_unk_hps_args_locs, ls_full_unk_hps_args_locs = List.split (List.map (build_hp_unk_locs real_unk_svl_hps unk_hps
                                                                          (fun a ls -> not( CP.mem_svl a ls))) (cs_unk_hps))
    in
    let full_unk_hps_args_locs = List.concat ls_full_unk_hps_args_locs in
    let unk_hps_args_locs = List.concat ls_unk_hps_args_locs in
    let all_unk_hps = List.map (fun (a, _, _) -> a) unk_hps_args_locs in
    let punk_hpargs = List.filter (fun (hp,_) -> CP.mem_svl hp all_unk_hps) cs_unk_hps in
    let closure_post_hps = find_closure_post_hps post_hps (punk_hpargs) in
    (unk_hps_args_locs, full_unk_hps_args_locs, closure_post_hps)
  in
   let _ = Debug.ninfo_pprint ("  cs: " ^ (Cprinter.string_of_hprel cs)) no_pos in
  double_check_one_constr unk_hp_args_locs (cs_hprels)

(*
  for each constraint:
   + update svl + unk_hps
   + add XPure for each dangling pointer
   + split full hp
   + simplify
*)
and update_unk_one_constr_old_x prog unk_hp_locs unk_map cs=
  (*************************)
  (*      INTERNAL        *)
  (************************)
  let rec get_unk_svl rem_hpargs ls_unk_hp_locs res=
    match rem_hpargs with
      | [] -> CP.remove_dups_svl res
      | (hp,args)::rest ->
            try
              let locs = List.assoc hp ls_unk_hp_locs in
              let unk_svl = SAU.retrieve_args_from_locs args locs in
              get_unk_svl rest ls_unk_hp_locs (res@unk_svl)
            with Not_found -> get_unk_svl rest ls_unk_hp_locs res
  in

  (*************************)
  (*   END INTERNAL        *)
  (************************)
  let l_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
    (CF.get_hprel cs.CF.hprel_lhs) in
  let r_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
    (CF.get_hprel cs.CF.hprel_rhs) in
  let hp_args = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq (l_hpargs@r_hpargs) in

  (*get unk svl*)
  let unk_svl0 = get_unk_svl hp_args unk_hp_locs [] in
  (* let _ = Debug.info_pprint ("  unk_svl0: " ^ (!CP.print_svl unk_svl0)) no_pos in *)
  (*diff from present ones, we may find them prior to*)
  let ls_xpures =  CF.get_xpure_view cs.CF.hprel_lhs in
  let existing_svl = List.fold_left (fun ls (_, svl) -> ls@svl) [] ls_xpures in
  let unk_svl1 = CP.diff_svl unk_svl0 (cs.CF.unk_svl@ existing_svl) in
  (* let _ = Debug.info_pprint ("  unk_svl1: " ^ (!CP.print_svl unk_svl1)) no_pos in *)
  let new_constr, unk_hps1, new_map=
    if unk_svl1 = [] then (cs, [], unk_map) else
      (*for each unk sv: generate linking*)
      let pos = CF.pos_of_formula cs.CF.hprel_lhs in
      let ls_hp_pos_sv = List.map (generate_unk_svl_map hp_args) unk_svl1 in
      let unk_pure,new_map = generate_xpure_view_w_pos ls_hp_pos_sv unk_map pos in
      let unk_svl2 = cs.CF.unk_svl@unk_svl1 in
      let new_lhs = CF.mkAnd_pure cs.CF.hprel_lhs (MCP.mix_of_pure unk_pure) pos in

      (*find unk_hps: postpone the split: split new constraints*)
      let unk_hps = List.filter (fun (hp,args) -> CP.diff_svl args unk_svl2 = []) hp_args in
      let unk_hps1 = Gen.BList.difference_eq SAU.check_hp_arg_eq unk_hps cs.CF.unk_hps in

      let new_constr = {cs with CF.unk_svl = unk_svl1;
          CF.unk_hps = unk_hps1@cs.CF.unk_hps;
          CF.hprel_lhs = new_lhs;
      } in
      (new_constr, unk_hps1, new_map)
  in
  let _ = Debug.ninfo_pprint ("   new hrel: " ^
          (Cprinter.string_of_hprel new_constr)) no_pos in
  (new_constr, unk_hps1, new_map)

and update_unk_one_constr_old prog unk_hp_locs unk_map constr=
  let pr1 = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 =  (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = Cprinter.string_of_hprel in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5 = pr_triple pr3 pr4 pr2 in
  Debug.no_3 "update_unk_one_constr" pr1 pr2 pr3 pr5
      (fun _ _ _ -> update_unk_one_constr_old_x prog unk_hp_locs unk_map constr)
      unk_hp_locs unk_map constr

and update_unk_one_constr_x prog unk_hp_locs link_hps unk_map cs=
  (*************************)
  (*      INTERNAL        *)
  (************************)
   let rec lookup_xpure_view hp rem_map=
    match rem_map with
      | [] -> None
      | ((hp1,_),xpv)::tl ->
          if CP.eq_spec_var hp hp1 then
            Some xpv
          else lookup_xpure_view hp tl
  in
  let rec lookup_locs rem_unk_hp_locs hp=
    match rem_unk_hp_locs with
      | [] -> None
      | (hp1,locs)::rest -> if CP.eq_spec_var hp hp1 then
          Some locs
        else lookup_locs rest hp
  in
  let get_unk_args_locs res (hp,args)=
    match lookup_locs unk_hp_locs hp with
      | None -> res
      | Some locs ->
            res@[(hp, SAU.retrieve_args_from_locs args locs, locs)]
  in
  let rec lookup_lhs ls r_args=
    match ls with
      | [] -> None
      | (l_hp,l_args)::rest -> if List.length r_args = List.length l_args && CP.diff_svl l_args r_args = [] then
          Some (l_hp)
        else lookup_lhs rest r_args
  in
  let classify_unk_hp lhs_unkargs (ls0,ls1,ls2,ls3) (hp,args)=
    match lookup_locs unk_hp_locs hp with
      | None -> (ls0,ls1,ls2,ls3)
      | Some locs -> begin
          let unk_args = SAU.retrieve_args_from_locs args locs in
          match lookup_lhs lhs_unkargs unk_args with
            | None -> (ls0@[(hp,unk_args)] ,ls1@[(hp,unk_args,locs)],ls2,ls3)
            | Some l_hp -> if CP.eq_spec_var l_hp hp then
                (ls0,ls1,ls2,ls3@[hp])
              else (ls0@[((hp,unk_args))],ls1,ls2@[(l_hp,(hp,unk_args,locs))],ls3)
        end
  in
  let update_lhs f l_hpargs map pos=
    let l_unk_hpargslocs = List.fold_left get_unk_args_locs [] l_hpargs in
    if l_unk_hpargslocs =[] then ([], f, map) else
      let _, l_unk_pure, new_map = generate_xpure_view_hp l_unk_hpargslocs map in
      let new_lhs,_ = CF.drop_hrel_f f (List.map fst3 l_unk_hpargslocs) in
      let l_hpargs = List.map (fun (a,b,_) -> (a,b)) l_unk_hpargslocs in
      (l_hpargs, CF.mkAnd_pure new_lhs (MCP.mix_of_pure l_unk_pure) pos, new_map)
  in
  let generate_link (ls_pure, unk_map) (l_hp, (r_hp,r_args,locs))=
    let oxpv = lookup_xpure_view l_hp unk_map in
    match oxpv with
        | Some xp -> 
              let new_xpv = {xp with
                  CP.xpure_view_arguments =  r_args
              } in
              let p = CP.mkFormulaFromXP new_xpv in
              (ls_pure@[p],unk_map@[((r_hp,locs),new_xpv)])
        | None -> report_error no_pos "sac.generate_link"
  in
  let update_rhs rhs r_hpargs map lhs_unkargs pos=
    let rhs_unkargs, fr_unk, link_unk, drop_unk= List.fold_left (classify_unk_hp lhs_unkargs) ([],[],[],[]) r_hpargs in
    (**********************)
    (*drop*)
    let rhs1 = if drop_unk=[] then rhs else fst (CF.drop_hrel_f rhs drop_unk) in
    (**********************)
    (*fresh unk in lhs*)
    let rhs2, new_map1 =  if fr_unk = [] then (rhs1,map) else
      begin
        let _, r_unk_pure, new_map = generate_xpure_view_hp fr_unk map in
        let rhs21,_ = CF.drop_hrel_f rhs1 (List.map fst3 fr_unk) in
        let new_rhs2 = CF.mkAnd_pure rhs21 (MCP.mix_of_pure r_unk_pure) pos in
        (new_rhs2, new_map)
      end
    in
    (**********************)
    (*link unk rhs with lhs*)
    let rhs3, new_map2 = if link_unk = [] then (rhs2, new_map1)
    else
      let rhs_upures, new_map2 = List.fold_left generate_link ([], new_map1) link_unk in
      let rhs31,_ = CF.drop_hrel_f rhs2 (List.map (fun (_, (hp,_,_)) -> hp) link_unk) in
      let new_rp = CP.conj_of_list rhs_upures pos in
      let rhs3 = CF.mkAnd_pure rhs31 (MCP.mix_of_pure new_rp) pos in
      (rhs3, new_map2)
    in
    (rhs_unkargs, rhs3, new_map2)
  in
  let find_redundant_link_hps lhpargs rhpargs=
    let l_link_args = List.fold_left (fun ls (hp, args) ->
        if CP.mem_svl hp link_hps then (ls@args) else ls
    ) [] lhpargs
    in
    let rhs_link_hpargs = List.filter (fun (hp,_) -> CP.mem_svl hp link_hps) rhpargs in
    List.fold_left (fun ls (hp, args) ->
        if CP.diff_svl args l_link_args = [] then (ls@[hp]) else ls) [] rhs_link_hpargs
  in
  (*************************)
  (*   END INTERNAL        *)
  (************************)
  let l_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
    (CF.get_hprel cs.CF.hprel_lhs) in
  let r_hpargs = List.map(fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs))))
    (CF.get_hprel cs.CF.hprel_rhs) in
  let pos = CF.pos_of_formula cs.CF.hprel_lhs in
  let lhs_unk_hpargs, nlhs, new_map1 = update_lhs cs.CF.hprel_lhs l_hpargs unk_map pos in
  let rhs_unk_hpargs, nrhs, new_map2 = update_rhs cs.CF.hprel_rhs r_hpargs new_map1 lhs_unk_hpargs pos in
  let unk_hpargs = lhs_unk_hpargs@rhs_unk_hpargs in
  let new_constrs=
    if SAU.is_only_xpure_f nlhs && SAU.is_only_xpure_f nrhs then ([]) else
      let unk_svl = List.fold_left (fun ls2 (_,svl) -> (ls2@svl)) [] unk_hpargs in
      let new_cs = {cs with CF.unk_svl = CP.remove_dups_svl (cs.CF.unk_svl@unk_svl);
          CF.unk_hps = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2)
              (cs.CF.unk_hps @ unk_hpargs);
          CF.hprel_lhs = nlhs;
          CF.hprel_rhs = nrhs;
      }
      in
      ([new_cs])
  in
  let _ = Debug.ninfo_pprint ("   new hrel: " ^
          (let pr = pr_list Cprinter.string_of_hprel in pr new_constrs)) no_pos in
  let red_links = if link_hps = [] then [] else
    find_redundant_link_hps l_hpargs r_hpargs
  in
  (new_constrs, unk_hpargs, new_map2, red_links)

and update_unk_one_constr prog unk_hp_locs link_hps unk_map constr=
  let pr1 = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  (* let pr2 =  (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr3 = Cprinter.string_of_hprel in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5 = pr_quad (pr_list pr3) pr4 pr2 !CP.print_svl in
  Debug.no_3 "update_unk_one_constr" pr1 pr2 pr3 pr5
      (fun _ _ _ -> update_unk_one_constr_x prog unk_hp_locs link_hps unk_map constr)
      unk_hp_locs unk_map constr

let find_full_unk_hps_x prog post_hps full_hps unk_hp_args_locs=
  let is_full_unk_process (hp, locs)=
    let locs_i = SAU.get_pos_of_hp_args_inst prog hp in
    List.length locs_i <= List.length locs && Gen.BList.difference_eq (=) locs_i locs = []
  in
  let full_unk_locs,part_hpargs1 = List.fold_left (fun (ls1,ls2) (hp,args,locs) ->
      if CP.mem_svl hp full_hps then (ls1@[(hp,args,locs)],ls2) else (ls1,ls2@[(hp,args,locs)])
  ) ([],[]) unk_hp_args_locs
  in
  let link_hpargs1 = List.fold_left (fun ls (hp,args,locs) ->
      if is_full_unk_process (hp,locs) then (ls@[(hp,args)]) else ls
  ) [] part_hpargs1 in
  let  link_hpargs2 , unk_hp_locs2= List.fold_left (fun (ls1,ls2) (hp,args,locs) ->
      if CP.mem_svl hp post_hps then (ls1@[(hp,args)],ls2) else (ls1,ls2@[(hp,locs)])
  ) ( (*[]*) link_hpargs1, []) full_unk_locs
  in
  (unk_hp_locs2, link_hpargs2)

let find_full_unk_hps prog post_hps full_hps unk_hp_args_locs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr3 = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "find_full_unk_hps" pr1 pr1 pr3 (pr_pair pr2 pr4)
      (fun  _ _ _ -> find_full_unk_hps_x prog post_hps full_hps unk_hp_args_locs)
      post_hps full_hps unk_hp_args_locs

(*
 - this method has the same structure with elim_redundant_paras_lst_constr_x,
should use higher-order when stab.
 - identify dangling and unknown preds
 - if one reachs to post hps, it can not be a dangling pred. it may be an unknown one
*)
let analize_unk_x prog post_hps constrs total_unk_map unk_hpargs link_hpargs=
  let rec partition_cands_by_hp_name unks parts=
    match unks with
      | [] -> parts
      | (hp_name,args,ids)::xs ->
          let part,remains= List.partition (fun (hp_name1,_,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
          partition_cands_by_hp_name remains (parts@[[(hp_name,args,ids)]@part])
  in
  let intersect_cand_one_hp ls=
    let hp_names,ls_args, cands = split3 ls in
    let _ = Debug.ninfo_pprint ("   hprel: " ^ (!CP.print_svl hp_names)) no_pos in
    let _ = Debug.ninfo_pprint ("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)) no_pos in
    let locs = List.fold_left (fun ls1 ls2 ->
        Gen.BList.intersect_eq (=) ls1 ls2)
      (List.hd cands) (List.tl cands) in
    if locs = [] then []
    else [(List.hd hp_names, List.hd ls_args, locs)]
  in
  let rec drop_invalid_group ls res=
    match ls with
      | [] -> res
      | (hp,args, locs)::ss -> if locs = [-1] then drop_invalid_group ss res
          else drop_invalid_group ss (res@[(hp,args,locs)])
  in
  let helper (unk_cands,ls_full_unk_cands_w_args)=
  (*group cands into each hp*)
    let groups = partition_cands_by_hp_name unk_cands [] in
  (*each hp, intersect all candidate unks*)
    let unk_hp_locs1 = List.concat (List.map intersect_cand_one_hp groups) in
    let unk_hp_locs2 = drop_invalid_group unk_hp_locs1 [] in
    let unk_hps = List.map fst3 unk_hp_locs2 in
    let full_unk_hp_args2_locs = List.filter (fun (hp,_,_) -> CP.mem_svl hp unk_hps )
      ((* List.concat *) ls_full_unk_cands_w_args) in
    (Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) -> CP.eq_spec_var hp1 hp2) unk_hp_locs2,
     Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) -> CP.eq_spec_var hp1 hp2) full_unk_hp_args2_locs)
  in
  let unk_hps = List.map fst unk_hpargs in
  let ls_unk_cands,ls_full_unk_cands_w_args = List.fold_left (fun (ls1, ls2) cs ->
      let r1,r2 = analize_unk_one prog unk_hps cs in
      (ls1@r1, ls2@r2)
  ) ([],[]) constrs
  in
  let unk_hp_args01,_ = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
  (*for debugging*)
  let _ = Debug.ninfo_pprint ("  unks 1: " ^
      (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int))
                                             in pr unk_hp_args01)) no_pos
  in
  (*END for debugging*)
  (*double check across one cs*)
  let rec loop_helper closure_post_hps unk_hp_locs0=
    let ls_unk_cands,ls_full_unk_cands_w_args, n_closure_post_hps =
      List.fold_left (fun (r_unk_cands, r_full_unk_cands_w_args, r_c_post_hps) cs ->
        let n_unk_cands, n_full_unk_cands_w_args, n_c_post_hps = double_check_unk prog r_c_post_hps unk_hp_locs0 unk_hps cs in
        (r_unk_cands@ n_unk_cands, r_full_unk_cands_w_args@n_full_unk_cands_w_args, r_c_post_hps@ n_c_post_hps)
    ) ([], [], post_hps) constrs
    in
    let unk_hp_args02,full_unk_hp_args2_locs = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
    let ls_unk_cands1 = Gen.BList.remove_dups_eq (fun (hp1,_,locs1) (hp2,_,locs2) ->
        SAU.check_hp_locs_eq (hp1,locs1) (hp2,locs2))
      unk_hp_args02
    in
    let _ = Debug.ninfo_pprint ("  ls_unk_cands1: " ^
        (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int))
                                             in pr ls_unk_cands1)) no_pos
    in
    if ls_unk_cands1 = [] then ([],[],n_closure_post_hps) else
      let diff = Gen.BList.difference_eq (fun (hp1,_,locs1) (hp2,_,locs2) ->
        SAU.check_hp_locs_eq (hp1,locs1) (hp2,locs2)) unk_hp_locs0 ls_unk_cands1
      in
      if diff =[] then (ls_unk_cands1, full_unk_hp_args2_locs,n_closure_post_hps) else
        loop_helper n_closure_post_hps ls_unk_cands1
  in
  let unk_hp_args02,full_unk_hp_args2_locs, closure_post_hps = loop_helper post_hps unk_hp_args01 in
  (*********END double check ****************)
  let full_unk_hp_args2_locs = SAU.refine_full_unk unk_hp_args02 full_unk_hp_args2_locs in
  (*for debugging*)
  let _ = Debug.ninfo_pprint ("  unks 2: " ^ (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int))
  in pr unk_hp_args02)) no_pos
  in
  let _ = Debug.ninfo_pprint ("  full_unk_hp_args2_locs: " ^ (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int))
  in pr full_unk_hp_args2_locs)) no_pos
  in
  (* let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
  (*                            (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
  (* let _ = Debug.info_pprint ("  equivs0: " ^ (pr1 equivs0) ) no_pos in *)
  (*END for debugging*)
  (*END double check*)
   let detected_hps = (List.map fst link_hpargs)@unk_hps in
   let unk_hp_args1 = List.filter (fun (hp,args,_) ->
       (*all non-ptrs args: are not consider unknown*)
       ((List.filter (fun sv -> CP.is_node_typ sv) args) <> []) &&
       not (CP.mem_svl hp detected_hps)
   ) unk_hp_args02 in
   let full_hps = List.map (fun (hp, _, _) -> hp) full_unk_hp_args2_locs in
   (*find full unk_hps: I parameters + unk_svl*)
   let full_unk_hp_locs0, link_hpargs2 = find_full_unk_hps prog closure_post_hps full_hps unk_hp_args1 in
   let _ = Debug.ninfo_pprint ("  full_unk_hp_locs: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                              in pr full_unk_hp_locs0)) no_pos
   in
   let full_unk_hp_locs, link_hpargs2a =
     if !Globals.pred_elim_dangling then
       (full_unk_hp_locs0, [])
     else
       let rec assoc3 ls hp=
         match ls with
           | [] -> report_error no_pos "sac.analize_unk"
           | (hp1,args,_)::rest -> if CP.eq_spec_var hp hp1 then args else
               assoc3 rest hp
       in
       ([], List.map (fun (hp,locs) -> (hp,assoc3 unk_hp_args1 hp)) full_unk_hp_locs0)
   in
   let link_hpargs3 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) ((List.filter (fun (hp,_) -> not (CP.mem_svl hp post_hps)) link_hpargs2)@link_hpargs@link_hpargs2a) in
   let _ = Debug.ninfo_pprint ("  link_hpargs3: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr link_hpargs3)) no_pos
   in
   let link_hps = List.map fst link_hpargs3 in
   let rec update_helper cs unk_map res_cs res_unk_hps res_drop_links=
     match cs with
       | [] ->  (res_cs, res_unk_hps, unk_map,res_drop_links)
       | c::ss ->
             let new_cs, new_unk_hps, new_map, new_drop_links = update_unk_one_constr prog full_unk_hp_locs
               link_hps unk_map c in
           update_helper ss new_map (res_cs@new_cs) (res_unk_hps@new_unk_hps) (new_drop_links@res_drop_links)
   in
   let new_cs, new_unk_hpargs, new_map, link_hpargs4 =
     if full_unk_hp_locs =[] then
       (constrs, unk_hpargs, total_unk_map, link_hpargs3)
     else
       let new_constrs, unk_hpargs, new_map, drop_links = update_helper constrs total_unk_map [] [] [] in
       let new_constrs1, link_hpargs4a=
         if drop_links = [] then (new_constrs, link_hpargs3) else
           (* let _ = Debug.info_pprint ("  drop_links: " ^ (!CP.print_svl drop_links)) no_pos in *)
           (List.map (fun cs -> CF.drop_hprel_constr cs drop_links) new_constrs,
           List.filter (fun (hp,_) -> not(CP.mem_svl hp drop_links)) link_hpargs3)
       in
       (new_constrs1, unk_hpargs, new_map,link_hpargs4a)
   in
   let tot_unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (new_unk_hpargs@unk_hpargs) in
   let tot_unk_dang_hps = List.map fst (tot_unk_hpargs@link_hpargs4) in
   (*partial unknown*)
   let punk_map = List.fold_left (fun ls (hp,_,locs) ->
       if CP.mem hp tot_unk_dang_hps then ls else ls@[(hp,locs)]) [] unk_hp_args02
   in
   let _ = Debug.dinfo_pprint ("map after: " ^
       (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
       pr new_map)) no_pos in
   (*printing such that it is easy to construct a sleek test cases*)
   let _ = if !Globals.print_heap_pred_decl then
     let unk_hps = List.map fst tot_unk_hpargs in
     let _ = if unk_hps <> [] then
       let hp_names = List.map (CP.name_of_spec_var) unk_hps in
       let _ = print_endline ("\nDeclare_Dangling [" ^ (String.concat "," hp_names) ^ "].") in
       ()
     else ()
     in
     let link_hps = List.map fst link_hpargs4 in
     let _ = if link_hps <> [] then
       let hp_names = List.map (CP.name_of_spec_var) link_hps in
       let _ = print_endline ("\nDeclare_Unknown [" ^ (String.concat "," hp_names) ^ "].") in
       ()
     else ()
     in
     ()
   else ()
   in
   (new_cs, tot_unk_hpargs, new_map, link_hpargs4, punk_map)

let analize_unk prog post_hps constrs total_unk_map unk_hpargs link_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2a = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = pr_penta pr1 pr3 pr2 pr3 pr2a in
  Debug.no_2 "analize_unk" pr1 pr2 pr4
      (fun _ _ -> analize_unk_x prog post_hps constrs total_unk_map unk_hpargs link_hpargs)
      constrs total_unk_map

let generate_equiv_unkdef unk_hpargs (ls1,ls2) (hp1, hp2)=
  let args = List.assoc hp1 unk_hpargs in
  let r = List.hd args in
  let paras =  List.tl args in
  let hf = CF.HRel (hp2, List.map (fun sv -> CP.mkVar sv no_pos) args, no_pos) in
  let def = CF.formula_of_heap hf no_pos in
  let new_hpdef = (CP.HPRelDefn (hp1, r,paras ),
  CF.HRel (hp1, List.map (fun sv -> CP.mkVar sv no_pos) args, no_pos), None, def) in
  (ls1@[new_hpdef],ls2@[hp1])


let generate_hp_def_from_unk_hps_x hpdefs unk_hpargs defined_hps post_hps
      unk_map equivs=
  let rec obtain_xpure_new rem_map hp args=
    match rem_map with
      | [] -> report_error no_pos "sac.obtain_xpure"
      | ((hp1, locs), xp)::rest -> begin
          if CP.eq_spec_var hp hp1 then
            let unk_args = SAU.retrieve_args_from_locs args locs in
            let new_xpv = {xp with CP.xpure_view_arguments = unk_args;} in
                let p = CP.mkFormulaFromXP new_xpv in
                p
          else
            obtain_xpure_new rest hp args
        end
  in
  let mk_unkdef pos (hp,args)=
    (* let ps = obtain_xpure args 0 hp [] in *)
    (* let ps = obtain_xpure [(List.hd args)] 0 hp [] in *)
    (* let p = CP.conj_of_list ps pos in *)
    let p = obtain_xpure_new unk_map hp args in
    let def = CF.formula_of_pure_formula p pos in
    let _ = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^
                                    (!CP.print_svl args) ^ ")=" ^
                                    (Cprinter.prtt_string_of_formula (* (CF.formula_of_heap h_def no_pos) *) def)) pos
    in
    let r = List.hd args in
    let paras = List.tl args in
    let new_hpdef = (CP.HPRelDefn (hp, r, paras),
    (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args,pos)), None,
     (* CF.formula_of_heap h_def no_pos *) def)
    in
    (new_hpdef)
  in
  let helper defs (hp, args)=
    if (CP.mem_svl hp defined_hps)then
      defs
    else
      let new_hpdef = mk_unkdef no_pos (hp, args) in
      defs@[new_hpdef]
  in
  DD.ninfo_pprint ">>>>>> unknown hps: <<<<<<" no_pos;
  let unk_hps = List.map fst unk_hpargs in
  let unk_equivs = List.filter (fun (hp1, hp2) -> CP.mem_svl hp1 unk_hps &&
  CP.mem_svl hp1 unk_hps) equivs in
  let equiv_unk_hpdefs, define_unk_hps = List.fold_left (generate_equiv_unkdef unk_hpargs) ([],[]) unk_equivs in
  let unk_hpargs1 = List.filter (fun (hp,_) -> not (CP.mem_svl hp define_unk_hps)) unk_hpargs in
  let unk_hpdefs = List.fold_left helper [] unk_hpargs1 in
  let hpdefs1 = (unk_hpdefs@equiv_unk_hpdefs@hpdefs) in
  (hpdefs1)

let generate_hp_def_from_unk_hps hpdefs unk_hpargs defined_hps post_hps unk_map equivs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  (* let pr4 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr4 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  Debug.no_4 "generate_hp_def_from_unk_hps" pr2 pr1 !CP.print_svl pr4 pr1
      (fun _ _ _ _ -> generate_hp_def_from_unk_hps_x hpdefs unk_hpargs defined_hps post_hps unk_map equivs)
      unk_hpargs hpdefs defined_hps unk_map

let generate_hp_def_from_link_hps prog cond_path equivs link_hpargs=
  let trans_link_hpdef (k, hf, og, f)=
    {
      CF.hprel_def_kind = k;
      CF.hprel_def_hrel = hf;
      CF.hprel_def_guard = og;
      CF.hprel_def_body = [(cond_path, Some f)];
      CF.hprel_def_body_lib = Some f;
    }
  in
  let link_hps = List.map fst link_hpargs in
  let link_equivs = List.filter (fun (hp1, hp2) -> CP.mem_svl hp1 link_hps &&
  CP.mem_svl hp1 link_hps) equivs in
  let equiv_link_hpdefs, define_link_hps = List.fold_left (generate_equiv_unkdef link_hpargs) ([],[]) link_equivs in
  let link_hpargs1 = List.filter (fun (hp,_) -> not (CP.mem_svl hp define_link_hps)) link_hpargs in
  let link_hpdefs =List.map (SAU.mk_link_hprel_def prog cond_path) link_hpargs1 in
  ((List.map trans_link_hpdef equiv_link_hpdefs)@link_hpdefs)

let transform_unk_hps_to_pure_x hp_defs unk_hp_frargs =
  let subst_xpure lhpdefs (xp_hpargs) f0=
    let process_one_sv (hp1,args1)=
      let fr_svl = List.assoc hp1 unk_hp_frargs in
      let eqs = List.combine args1 fr_svl in
      let xp_ps = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 no_pos) eqs in
      CP.conj_of_list xp_ps no_pos
    in
    let process_p_helper p=
      let xp_ps = (List.map process_one_sv xp_hpargs) in
      (* let filtered_xp_ps = CP.filter_disj xp_ps rem_ps in *)
      let new_p = CP.conj_of_list (CP.remove_redundant_helper ((CP.list_of_conjs p)@ xp_ps) []) no_pos in
      new_p
    in
    let rec helper f=
      match f with
        | CF.Base fb ->
            let new_p =  process_p_helper (MCP.pure_of_mix fb.CF.formula_base_pure) in
            CF.Base{fb with CF.formula_base_pure = (MCP.mix_of_pure new_p)}
        | CF.Exists fe ->
            let new_p =  process_p_helper (MCP.pure_of_mix fe.CF.formula_exists_pure) in
            CF.Exists{fe with CF.formula_exists_pure = (MCP.mix_of_pure new_p)}
        | CF.Or orf -> CF.Or {orf with
            CF.formula_or_f1 = helper orf.CF.formula_or_f1;
            CF.formula_or_f2 = helper orf.CF.formula_or_f2;
        }
    in
    helper f0
  in
  let look_up_get_eqs_ss args0 ls_unk_hpargs_fr (used_hp,used_args)=
    try
        let _,fr_args = List.find (fun (hp,_) -> CP.eq_spec_var hp used_hp) ls_unk_hpargs_fr in
        (* let ss = List.combine used_args fr_args in *)
        (*NOW, NO LONGER SUPPORT UNK_SVL. WE JUST RETURN THE FIRST ONE !!!!*)
        let ss = List.combine [(List.hd used_args)] fr_args in
        let rs1,rs2 = List.partition (fun (sv1,_) -> CP.mem_svl sv1 args0) ss in
        if List.length rs1 = List.length args0 then
          ([used_hp],[([(used_hp,used_args)],[])],rs2)
        else
          ([used_hp],[([],rs1)],rs2)
    with
      | Not_found -> ([],[],[])
  in
  let subst_pure_hp_unk args0 ls_unk_hpargs_fr f=
    (* let _ = DD.info_pprint ("       f: " ^ (!CF.print_formula f)) no_pos in *)
    let ls_used_hp_args = CF.get_HRels_f f in
    let ls_xpures =  CF.get_xpure_view f in
    (*look up*)
    let r1 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_used_hp_args in
    let r2 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_xpures in
    let ls_used_unk_hps,ls_eqs, ls_ss = split3 (r1@r2) in
    let used_unk_hps = List.concat ls_used_unk_hps in
    let unk_need_subst, eqs = List.fold_left (fun (ls1,ls2) (a1,a2) -> (ls1@a1,ls2@a2)) ([],[]) (List.concat ls_eqs) in
    (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    (* let _ = DD.info_pprint ("       eqs: " ^ (pr1 eqs)) no_pos in *)
    let ss = List.concat ls_ss in
    (*remove unkhps*)
    let f1,_ =  CF.drop_unk_hrel (* CF.drop_hrel_f*) f used_unk_hps in
    (*subst*)
    let f2 = CF.subst ss f1 in
    (*add pure eqs*)
    let pos = CF.pos_of_formula f2 in
    (****************************************)
    (*LOC: now we dont need eqs for pred parameters
      (we abs preds as a set it should be set inclusion operators).
      so we set eqs = []*)
    (***************************************)
    let eqs = [] in
    let p_eqs = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) eqs in
    let p = CP.conj_of_list (CP.remove_redundant_helper p_eqs []) pos in
    let f3 = CF.mkAnd_pure f2 (MCP.mix_of_pure p) pos in
    (f3, unk_need_subst)
  in
  let subst_pure_hp_unk_hpdef ls_unk_hpargs_fr (rc, hf,g, def)=
    let hp,args0 = CF.extract_HRel hf in
    let fs = CF.list_of_disjs def in
    let fs1 = List.map (subst_pure_hp_unk args0 ls_unk_hpargs_fr) fs in
    let def1 = CF.disj_of_list (fst (List.split fs1)) (CF.pos_of_formula def) in
    (rc, hf, g, def1, fs1)
  in
  let subst_and_combine new_hpdefs pr_fs=
    let fs = List.map (fun (f, xp_args) ->
        if xp_args = [] then f else
        subst_xpure new_hpdefs xp_args f
    ) pr_fs
    in
    CF.disj_of_list fs no_pos
  in
  let ls_unk_hpargs_fr = unk_hp_frargs in
  (* let ls_unk_hpargs_fr = List.map transform_hp_unk unk_hpargs in *)
  let new_hpdefs = List.map (subst_pure_hp_unk_hpdef ls_unk_hpargs_fr) hp_defs in
  let new_hpdefs1 = List.map (fun (a,b,g,f,_) -> (a,b,g, f)) new_hpdefs in
  let new_hpdefs2 = List.map (fun (a,b,g,_,pr_f) -> (a,b,g, pr_f)) new_hpdefs in
  (*subst XPURE*)
  List.map (fun (a,b,g,pr_f) -> (a,b, g, subst_and_combine (*subst_xpure*) new_hpdefs1 pr_f)) new_hpdefs2

let transform_unk_hps_to_pure hp_defs unk_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_unk_hps_to_pure" pr1 pr2 pr1
      (fun _ _ -> transform_unk_hps_to_pure_x hp_defs unk_hpargs) hp_defs unk_hpargs

let transform_xpure_to_pure_x prog hp_defs unk_map link_hpargs=
  let fr_map = List.map (fun ((hp,_), xp) ->
      let args = match xp.CP.xpure_view_node with
        | None -> xp.CP.xpure_view_arguments
        | Some sv -> sv::xp.CP.xpure_view_arguments
      in
      let args_inst = SAU.get_hp_args_inst prog hp args in
      let (CP.SpecVar (t, _, p)) = hp in
      (CP.SpecVar(t, xp.CP.xpure_view_name, p),
      let dang_name = dang_hp_default_prefix_name ^ "_" ^ xp.CP.xpure_view_name (* ^ "_" ^dang_hp_default_prefix_name *)  in
      let (CP.SpecVar (t, _, p)) = List.hd args_inst in
      [CP.SpecVar (t, dang_name, p)])
  ) unk_map
  in
  let link_fr_map = List.map (fun ((hp,args)) ->
      let locs_i = SAU.get_pos_of_hp_args_inst prog hp in
      let args_inst = SAU.retrieve_args_from_locs args locs_i in
      (* let (CP.SpecVar (_, _, p)) = hp in *)
      let (CP.SpecVar (t, _, p)) = List.hd args_inst in
      (hp,
      let dang_name = dang_hp_default_prefix_name ^ "_" ^ (CP.name_of_spec_var hp) (* ^ "_" ^dang_hp_default_prefix_name *)  in
      [CP.SpecVar (t, dang_name, p)])
  ) link_hpargs
  in
  let tupled_defs,hp_defs1 = List.partition SAU.is_tupled_hpdef hp_defs in
  let hp_defs2 = transform_unk_hps_to_pure hp_defs1 (fr_map@link_fr_map) in
  (hp_defs2@tupled_defs)

let transform_xpure_to_pure prog hp_defs (unk_map:((CP.spec_var * int list) * CP.xpure_view) list) link_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_xpure_to_pure" pr1 pr2 pr1
      (fun _ _ -> transform_xpure_to_pure_x prog hp_defs unk_map link_hpargs)
      hp_defs link_hpargs

let rec gen_full_pos args n res=
  match args with
    | [] -> res
    | _::rest -> gen_full_pos rest (n+1) (res@[n])

let build_args_locs (hp, args)=
  let locs = gen_full_pos args 0 [] in
  (hp, args, locs)

let do_elim_unused_x cs unk_hps map=
  if unk_hps = [] then (cs, map, []) else
    let ls_l_hpargs1 = (CF.get_HRels_f cs.CF.hprel_lhs) in
    let ls_r_hpargs1 = (CF.get_HRels_f cs.CF.hprel_rhs) in
    let ls_l_hpargs2 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) ls_l_hpargs1 in
    let ls_r_hpargs2 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) ls_r_hpargs1 in
    let l_unk_hpargs = List.filter (fun (hp,_) -> CP.mem_svl hp unk_hps) ls_l_hpargs2 in
    let r_unk_hpargs = List.filter (fun (hp,_) -> CP.mem_svl hp unk_hps) ls_r_hpargs2 in
    let unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) (l_unk_hpargs@r_unk_hpargs) in
    if unk_hpargs = [] then (cs, map,[]) else
      let unk_svl = List.fold_left (fun ls (_, args) -> ls@args) []  unk_hpargs in
      let unk_svl1 = CP.remove_dups_svl unk_svl in
      let cs_unk_hps = (List.map fst unk_hpargs) in
      let new_lhs, new_map1 = if l_unk_hpargs =[] then (cs.CF.hprel_lhs, map) else
        let _, l_unk_pure, new_map = generate_xpure_view_hp (List.map build_args_locs l_unk_hpargs) map in
        let new_lhs,_ = CF.drop_hrel_f cs.CF.hprel_lhs cs_unk_hps in
        (CF.mkAnd_pure new_lhs (MCP.mix_of_pure l_unk_pure) no_pos, new_map)
      in
      let new_rhs, new_map2 = if r_unk_hpargs =[] then (cs.CF.hprel_rhs, new_map1) else
        let _, r_unk_pure, new_map = generate_xpure_view_hp (List.map build_args_locs r_unk_hpargs) new_map1 in
        let new_rhs,_ = CF.drop_hrel_f cs.CF.hprel_rhs cs_unk_hps in
        (CF.mkAnd_pure new_rhs (MCP.mix_of_pure r_unk_pure) no_pos, new_map)
      in
      let new_cs = {cs with CF.hprel_lhs = new_lhs;
          CF.hprel_rhs = new_rhs;
          CF.unk_svl = unk_svl1 ;
          CF.unk_hps = unk_hpargs;
      }
      in
      (new_cs, new_map2, unk_hpargs)

let do_elim_unused cs unused_hps map=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_hprel in
  (* let pr3= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in *)
  let pr3 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "do_elim_unused" pr1 pr2 pr3 (pr_triple pr2 pr3 pr4)
      (fun _ _ _ -> do_elim_unused_x cs unused_hps map) unused_hps cs map

let detect_dangling_pred_x constrs sel_hps unk_map=
  let all_hps = List.fold_left (fun ls cs ->
      ls@(CF.get_hp_rel_name_formula cs.CF.hprel_lhs)@(CF.get_hp_rel_name_formula cs.CF.hprel_rhs)
  ) [] constrs in
  let unk_hps = CP.diff_svl (CP.remove_dups_svl all_hps) sel_hps in
  (* let _ = DD.info_pprint ("unk_hps: " ^ (!CP.print_svl unk_hps)) no_pos in *)
  let new_constr, unk_map, unk_hgargs=
    if unk_hps = [] then (constrs,[], [])
    else
      List.fold_left (fun (constrs0, unk_map, unk_hgargs) cs ->
          let new_cs, new_map, new_unk_hpargs = do_elim_unused cs unk_hps unk_map in
          (constrs0@[new_cs], new_map, unk_hgargs@new_unk_hpargs)
      ) ([],unk_map, []) constrs
  in
  (new_constr, unk_map, Gen.BList.remove_dups_eq (fun (hp1, _) (hp2,_) -> CP.eq_spec_var hp1 hp2) unk_hgargs)

let detect_dangling_pred constrs sel_hps unk_map=
  let pr1 =  pr_list_ln Cprinter.string_of_hprel in
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "detect_dangling_pred" pr1 !CP.print_svl pr2 (pr_triple pr1 pr2 pr3)
      (fun _ _ _ -> detect_dangling_pred_x constrs sel_hps unk_map)
      constrs sel_hps unk_map

let get_dangling_pred constrs=
  let gen_map (hp,args)=
    let (hp, args, locs) = build_args_locs (hp,args) in
    let hp_name = CP.name_of_spec_var hp in
    let xpv = { CP.xpure_view_node = None;
    CP.xpure_view_name = hp_name;
    CP.xpure_view_arguments = args;
    CP.xpure_view_remaining_branches= None;
    CP.xpure_view_pos = no_pos;
    }
    in
    ((hp, locs), xpv)
  in
  let get_xpure cs=
    let unk_hpargs = (CF.get_xpure_view cs.CF.hprel_lhs)@(CF.get_xpure_view cs.CF.hprel_rhs) in
    unk_hpargs
  in
  let ls_unk_hpargs = List.fold_left (fun ls cs ->
      ls@(get_xpure cs)
  ) [] constrs in
  let ls_unk_hpargs1 = Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) ls_unk_hpargs in
  (List.map gen_map ls_unk_hpargs1,ls_unk_hpargs1)


let syn_unk constrs0 unk_map0 post_hps pos=
  let unk_hpargs0 = List.fold_left (fun ls ((hp,locs),xpure) ->
      let args = match xpure.CP.xpure_view_node with
        | None -> xpure.CP.xpure_view_arguments
        | Some sv -> sv::xpure.CP.xpure_view_arguments
      in
      if List.length locs = List.length args then
        ls@[(hp,args)]
      else ls
  ) [] unk_map0 in
  let unk_hpargs = Gen.BList.remove_dups_eq (fun (hp1, _) (hp2,_) -> CP.eq_spec_var hp1 hp2) unk_hpargs0 in
  let constrs, unk_map0, unk_hpargs = List.fold_left (fun (ls,cur_map, cur_unk) (cs) ->
      let rhs_hpargs = CF.get_HRels_f cs.CF.hprel_rhs in
      let new_unk, new_cs, new_map = if rhs_hpargs <> [] then
        let lhs_hpargs = CF.get_HRels_f cs.CF.hprel_lhs in
        let lhs_unk_hpargs = List.filter (fun (hp, _) ->
            List.exists (fun (hp1,_) -> CP.eq_spec_var hp hp1) cur_unk)
          lhs_hpargs
        in
        let rhs_unk_hp_args = List.filter (fun (r_hp,r_args) ->
            not (  List.exists (fun (hp1,_) -> CP.eq_spec_var r_hp hp1) cur_unk) &&
                List.exists (fun (_,l_args) -> List.length l_args = List.length r_args && CP.diff_svl l_args r_args = []) lhs_unk_hpargs
          ) rhs_hpargs
        in
        let _, xpure, new_map =  generate_linking cur_map lhs_unk_hpargs rhs_hpargs post_hps pos in
        let new_cs = {cs with CF.hprel_lhs = CF.mkAnd_pure cs.CF.hprel_lhs (MCP.mix_of_pure xpure) pos} in
        (cur_unk@rhs_unk_hp_args, new_cs, new_map)
      else (cur_unk, cs, cur_map)
      in
      let new_cs1, new_map1, _ = do_elim_unused new_cs
        (List.map fst new_unk) new_map in
      ls@[new_cs1],new_map1,new_unk
  ) ([], unk_map0 ,unk_hpargs) constrs0
  in
  (constrs, unk_map0, unk_hpargs)
(*=============**************************================*)
       (*=============END UNKOWN================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============CONSTR CLOSURE================*)
(*=============**************************================*)

(*always rename for the clash var of the second constraint
  before doing check_imply
- {f1, f2_b} \subset {lhs; rhs} of a constraint
*)
let rename_var_clash f1 f2_b=
   (*renaming vars of the lhs-based constraint*)
  let rsvl2 = CF.fv (CF.Base f2_b) in
  let lsvl2 = CF.fv f1 in
  let svl2 = CP.remove_dups_svl (rsvl2@lsvl2) in
  let hp_names = CP.remove_dups_svl ((CF.get_hp_rel_name_formula f1)@
      (CF.get_hp_rel_name_bformula f2_b)) in
  (*remove hp name*)
  let svl21 = CP.diff_svl svl2 hp_names in
  let fr_svl2 = CP.fresh_spec_vars svl21 in
  let sst = List.combine svl21 fr_svl2 in
  let nf2_b = CF.subst_b sst f2_b in
  let nf1 = CF.subst sst f1 in
  (nf1, nf2_b, sst)

(*
 perform lhs |- rhs * R (syntactic version)
*)
let check_imply prog lhs_b rhs_b=
  (************************************)
     (*         INTERNAL             *)
  (************************************)
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
              check_hrels_imply ss1 ss2 ldns rdns lhs_hps
                  (subst@(List.combine args1 args2)) (matched@[id2]) (args@args2) res_rename
            end
          else
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
  (************************************)
  (*         END INTERNAL             *)
  (************************************)
  let rdns,rvns,rhrels = CF.get_hp_rel_bformula rhs_b in
  let ldns,_,lhrels = CF.get_hp_rel_bformula lhs_b in
  let r_rhrels = sort_hps (List.map transform_hrel rhrels) in
  let l_rhrels = sort_hps (List.map transform_hrel lhrels) in
  (*m_args2: matched svl of lhs_b*)
  (*matching hprels and return subst*)
  let subst,matched_hps, m_args2,lhs_hps_rename = check_hrels_imply r_rhrels l_rhrels rdns ldns (List.map fst r_rhrels) [] [] [] [] in
  let r=
    if matched_hps = [] then None
    else
      begin
        (*for debugging*)
        (* let _ = Debug.ninfo_pprint ("     m_args2: " ^ (!CP.print_svl  m_args2)) no_pos in *)
        (* let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
        (* let _ =  Debug.ninfo_pprint ("     subst: " ^ (pr_ss subst)) no_pos in *)
        (*END for debugging*)
        (*matching hnodes (in matched_hps) and return subst*)
        let rhns1 = List.map transform_dn rdns in
        let lhns1 = List.map transform_dn ldns in
        (*all_matched_svl2: all matched slv of rhs2*)
         let cur_rnode_match = List.fold_left (fun ls (_,sv,_) ->
            if CP.mem_svl sv m_args2 then (ls@[sv]) else ls
          ) [] rhns1
        in
        let cur_node_match = List.fold_left (fun ls (_,sv,_) ->
            let sv1 = CP.subs_one subst sv in
            if CP.mem_svl sv1 cur_rnode_match then (ls@[sv]) else ls
          ) [] lhns1
        in
        let is_node_match,all_matched_svl1,subst1 = SAU.get_closed_matched_ptrs rhns1 lhns1 cur_node_match subst in
        if not is_node_match then None else
          let all_matched_svl2 = all_matched_svl1 @ m_args2 in
          (* let _ = Debug.ninfo_pprint ("    all matched: " ^ (!CP.print_svl all_matched_svl2)) no_pos in *)
          (* let _ =  Debug.ninfo_pprint ("     subst1: " ^ (pr_ss subst1)) no_pos in *)
          if  (is_inconsistent subst1 []) then None else
            let n_rhs_b = CF.subst_b subst1 rhs_b in
            (*check pure implication*)
            (* let nrdns,nrvns,_ = CF.get_hp_rel_bformula n_rhs_b in *)
            (*loc-1b1.slk*)
            (* let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure)
               (look_up_closed_ptr_args prog nrdns nrvns all_matched_svl2) in *)
            let rmf = (MCP.pure_of_mix n_rhs_b.CF.formula_base_pure) in
            let lmf = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
            let _ = Debug.ninfo_pprint ("    n_rhs_b: " ^ (Cprinter.string_of_formula_base n_rhs_b)) no_pos in
            (* let _ = Debug.info_pprint ("    lmf: " ^ (!CP.print_formula lmf)) no_pos in *)
            (* let _ = Debug.info_pprint ("    rmf: " ^ (!CP.print_formula rmf)) no_pos in *)
            let b,_,_ = TP.imply_one 20 lmf rmf "sa:check_hrels_imply" true None in
            if b then
              let r_res = {n_rhs_b with
                  CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                      n_rhs_b.CF.formula_base_heap SAU.select_dnode
                      SAU.select_vnode SAU.select_hrel all_matched_svl2  all_matched_svl2 matched_hps}
              in
              (*drop hps and matched svl in n_rhs2*)
              let l_res = {lhs_b with
                  CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                      lhs_b.CF.formula_base_heap SAU.select_dnode
                      SAU.select_vnode SAU.select_hrel all_matched_svl1 all_matched_svl1 matched_hps;
                  CF.formula_base_pure = MCP.mix_of_pure
                      (CP.filter_var_new
                          (MCP.pure_of_mix lhs_b.CF.formula_base_pure) all_matched_svl2)}
              in
              (* if not (SAU.is_empty_base r_res) then *)
                Some (l_res, subst1)
              (* else None *)
            else
              None
      end
  in r

let strengthen_conseq_comb res_rhs2 ss lhs1 lhs2 pos =
  (*combine res into f1*)
  let n_lhs1 = CF.subst ss lhs1 in
   let comb_rhs =  CF.mkStar n_lhs1 (CF.Base res_rhs2) CF.Flow_combine pos in
  (*avoid clashing --> should refresh remain svl of r_res*)
  (* let r_res1 = (CF.Base r_res) in *)
  (* (\*elim duplicate hprel in r_res1 and n_rhs1*\) *)
  (* let nr_hprel = CF.get_HRels_f n_f2 in *)
  (* let nrest_hprel = CF.get_HRels_f r_res1 in *)
  (* let diff3 = Gen.BList.intersect_eq check_hp_arg_eq nr_hprel nrest_hprel in *)
  (* let r_res2,_ = CF.drop_hrel_f r_res1 (List.map (fun (hp,_) -> hp) diff3) in *)
  (* let r = CF.mkStar n_f2 r_res2 CF.Flow_combine (CF.pos_of_formula n_f2) in *)
  (lhs2, comb_rhs)

let strengthen_ante_comb res ss1 f pos =
  (*subst*)
  let nf1 = CF.subst ss1 f in
  (*combine res into f1*)
  let nf2 =  CF.mkStar nf1 (CF.Base res) CF.Flow_combine pos in
  nf2

(*
a1: lhs1 --> rhs1
a2: lhs2 --> rhs2
rhs |- rhs1 * R
===============
replace a2 by
lhs2 --> lhs1 * R
*)

let check_apply_strengthen_conseq prog cs1 cs2=
  let _ = Debug.ninfo_pprint ("    cs2: " ^ (Cprinter.string_of_hprel cs2)) no_pos in
  let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_rhs in
  let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_rhs in
  let n_cs2=
  match f1,f2 with
      | CF.Base rhs1_b, CF.Base rhs2_b ->
          let nlhs2, nrhs2_b, ss2 = rename_var_clash cs2.CF.hprel_lhs rhs2_b in
          let nrhs2_b1 =  CF.mkAnd_base_pure nrhs2_b (MCP.mix_of_pure (CF.get_pure nlhs2)) no_pos in
          let _ = Debug.ninfo_pprint ("    nrhs2_b1: " ^ (Cprinter.string_of_formula_base nrhs2_b1)) no_pos in
          let _ = Debug.ninfo_pprint ("    rhs1_b: " ^ (Cprinter.string_of_formula_base rhs1_b)) no_pos in
          let r = check_imply prog nrhs2_b1 rhs1_b in
          begin
            match r with
              | Some (res_rhs2, ss1) -> begin
                    let l,r = strengthen_conseq_comb res_rhs2 ss1 cs1.CF.hprel_lhs nlhs2 no_pos in
                    let new_cs = {cs2 with
                        CF.predef_svl = CP.remove_dups_svl
                            ((CP.subst_var_list ss1 cs1.CF.predef_svl)@
                                (CP.subst_var_list ss2 cs2.CF.predef_svl));
                        CF.unk_svl = CP.remove_dups_svl
                            ((CP.subst_var_list ss1 cs1.CF.unk_svl)@
                                (CP.subst_var_list ss2 cs2.CF.unk_svl));
                        CF.unk_hps = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq
                            ((List.map (fun (hp,args) -> (hp,CP.subst_var_list ss1 args)) cs1.CF.unk_hps)@
                                (List.map (fun (hp,args) -> (hp,CP.subst_var_list ss2 args)) cs2.CF.unk_hps));
                        CF.hprel_lhs = l;
                        CF.hprel_rhs = r;
                    }
                    in
                    let _ = Debug.ninfo_pprint ("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)) no_pos in
                    Some new_cs
                end
              | None -> None
          end
      | _ -> report_error no_pos "sac.do_strengthen_conseq"
  in
  n_cs2

let do_strengthen prog constrs new_cs check_apply_fnc=
  (* let rec check_constr_duplicate (lhs,rhs) constrs= *)
  (*   match constrs with *)
  (*     | [] -> false *)
  (*     | cs::ss -> if SAU.checkeq_pair_formula (lhs,rhs) *)
  (*           (cs.CF.hprel_lhs,cs.CF.hprel_rhs) then *)
  (*           true *)
  (*         else check_constr_duplicate (lhs,rhs) ss *)
  (* in *)
  (*new_cs: one x one*)
  let rec helper_new_only don rest res=
    match rest with
      | [] -> (don@res)
      | cs1::rest1 ->
          let _ = Debug.ninfo_pprint ("    cs1: " ^ (Cprinter.string_of_hprel_short cs1)) no_pos in
          let new_rest, n_res = List.fold_left ( fun (ls1,ls2) cs2 ->
              let _ = Debug.ninfo_pprint ("    cs 2 (rest): " ^ (Cprinter.string_of_hprel_short cs2)) no_pos in
              let on_cs2 = check_apply_fnc prog cs1 cs2 in
              match on_cs2 with
                | None -> (ls1@[cs2],ls2)
                | Some n_cs2 -> (* if check_constr_duplicate (n_cs2.CF.hprel_lhs, n_cs2.CF.hprel_rhs) (constrs@new_cs) then ls@[cs2] else *) (ls1,ls2@[n_cs2])
          ) ([],res) rest1 in
          let new_don, n_res1 = List.fold_left ( fun (ls1,ls2) cs2 ->
              let _ = Debug.ninfo_pprint ("    cs 2 (done): " ^ (Cprinter.string_of_hprel_short cs2)) no_pos in
              let on_cs2 = check_apply_fnc prog cs1 cs2 in
              match on_cs2 with
                | None -> (ls1@[cs2],ls2)
                | Some n_cs2 -> (* if check_constr_duplicate (n_cs2.CF.hprel_lhs, n_cs2.CF.hprel_rhs) (constrs@new_cs) then ls@[cs2] else *) (ls1,ls2@[n_cs2])
          ) ([],n_res) don in
          helper_new_only (new_don@[cs1]) new_rest n_res1
  in
  (*new_cs x constr*)
  let rec helper_old_new rest res=
    match rest with
      | [] -> res
      | cs1::ss ->
          let r = List.fold_left ( fun ls cs2 ->
              let  on_cs2 = check_apply_fnc prog cs1 cs2 in
              match on_cs2 with
                | None -> ls@[cs2]
                | Some n_cs2 ->
                      ls@[n_cs2]
          ) res constrs in
           helper_old_new ss r
  in
  let new_cs1 = if List.length new_cs < 1 then [] else helper_new_only [] new_cs [] in
  (* let new_cs2 = helper_old_new new_cs [] in *)
  (new_cs1)

let do_strengthen_conseq prog constrs new_cs=
  do_strengthen prog constrs new_cs check_apply_strengthen_conseq

(*
a1: lhs1 --> rhs1
a2: lhs2 --> rhs2
lhs2 |- lhs1 * R
===============
replace a2 by
rhs1 * R --> rhs2
*)

let check_apply_strengthen_ante prog cs1 cs2=
  let _ = Debug.ninfo_pprint ("    cs2: " ^ (Cprinter.string_of_hprel cs2)) no_pos in
  let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_lhs in
  let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_lhs in
  let n_cs2=
  match f1,f2 with
      | CF.Base lhs1_b, CF.Base lhs2_b ->
          let r, nlhs2_b, ss2 = rename_var_clash cs2.CF.hprel_rhs lhs2_b in
          let ores = check_imply prog nlhs2_b lhs1_b in
          begin
            match ores with
              | Some (res, ss1) -> begin
                    let l = strengthen_ante_comb res ss1 cs1.CF.hprel_rhs no_pos in
                    let new_cs = {cs2 with
                        CF.predef_svl = CP.remove_dups_svl
                            ((CP.subst_var_list ss1 cs1.CF.predef_svl)@
                                (CP.subst_var_list ss2 cs2.CF.predef_svl));
                        CF.unk_svl = CP.remove_dups_svl
                            ((CP.subst_var_list ss1 cs1.CF.unk_svl)@
                                (CP.subst_var_list ss2 cs2.CF.unk_svl));
                        CF.unk_hps = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq
                            ((List.map (fun (hp,args) -> (hp,CP.subst_var_list ss1 args)) cs1.CF.unk_hps)@
                                (List.map (fun (hp,args) -> (hp,CP.subst_var_list ss2 args)) cs2.CF.unk_hps));
                        CF.hprel_lhs = l;
                        CF.hprel_rhs = r;
                    }
                    in
                    let _ = Debug.ninfo_pprint ("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)) no_pos in
                    Some new_cs
                end
              | None -> None
          end
      | _ -> report_error no_pos "sac.do_strengthen_conseq"
  in
  n_cs2

let do_strengthen_ante prog constrs new_cs=
  do_strengthen prog constrs new_cs check_apply_strengthen_ante


(*=============**************************================*)
       (*=============END CONSTR CLOSURE================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============PRE PREDS================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============END PRE PREDS================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============POST PREDS================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============END POST PREDS================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============UNIFY PREDS================*)
(*=============**************************================*)
(*************************************************)
(**********       CONJ-UNIFY       ***************)

(*************************************************)
(*move unk hps into the first position*)
let rec swap_map unk_hps ss r=
  match ss with
    | [] -> r
    | (sv1,sv2)::tl -> begin
        let b1 = CP.mem_svl sv1 unk_hps in
        let b2 = CP.mem_svl sv2 unk_hps in
        let new_ss =
          match b1,b2 with
            | true,false -> [(sv1,sv2)]
            | false,true -> [(sv2,sv1)]
            | _ -> []
        in
        swap_map unk_hps tl (r@new_ss)
      end

(*
This is mandatory
  A<x> <--> x::node<l,r> * H1<l> * H2<r>    H1<x> <--> H2<x>
--------------
  A<x> --->  x::node<l,r> * H1<l> * H2<r> /\ x::node<l,r> * H2<l> * H1<r>
*)
let unify_consj_pre_x prog unk_hps link_hps equivs0 pdefs=
  let dang_hps = (unk_hps@link_hps) in
  let rec unify_one rem_pdefs ((hp,args1,unk_svl1, cond1, olhs1, og1, orhs1) as pdef1, cs1) done_pdefs equivs=
    match rem_pdefs with
      | [] -> (done_pdefs,[(pdef1,cs1)], equivs)
      |  ((hp,args2,unk_svl2, cond2,  olhs2, og2, orhs2) as pdef2,cs2)::rest ->
            if CP.equalFormula cond1 cond2 then
              match orhs1,orhs2 with
                | Some f1, Some f2 -> begin
                      (* let ss = List.combine args1 args2 in *)
                      let nf1 = (* CF.subst ss *) f1 in
                      (* let nf2= SAU.mkConjH_and_norm prog args2 unk_hps [] nf1 f2 no_pos in *)
                      let ores = SAU.norm_formula prog args2 unk_hps [] f1 f2 equivs in
                      match ores with
                        | Some (new_f2, n_equivs) ->
                              (rest@done_pdefs,[((hp,args2,unk_svl2, cond2, olhs2, og2, Some new_f2), cs2)],n_equivs)
                        | None ->
                              unify_one rest (pdef1,cs1) (done_pdefs@[(pdef2,cs2)]) equivs
                  end
                | _ -> report_error no_pos "sac.unify_consj_pre: imppossible"
            else
              unify_one rest (pdef1,cs1) (done_pdefs@[(pdef2,cs2)]) equivs
  in
  let rec unify_consj defs res equivs1=
    match defs with
      | [] -> res,equivs1
      | pdef::rest -> let rem, don,n_equivs = unify_one rest pdef [] equivs1 in
        unify_consj rem (res@don) n_equivs
  in
  match pdefs with
    | [] -> [],equivs0
    |((hp,_,_,_,_,_,_),_)::_ ->
         if CP.mem_svl hp dang_hps then (pdefs, equivs0)  else
           unify_consj pdefs [] equivs0

let unify_consj_pre prog unk_hps link_hps equivs pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = !CP.print_formula in
  let pr3 oform= match oform with
    | None -> "None"
    | Some f -> Cprinter.prtt_string_of_formula f
  in
  let pr3a oform= match oform with
    | None -> "None"
    | Some f -> Cprinter.prtt_string_of_h_formula f
  in
  let pr4 (a,_) = (pr_hepta !CP.print_sv pr1 pr1 pr2 pr3 pr3a pr3) a in
  let pr5 = pr_list_ln pr4 in
  let pr6 = pr_pair pr5 (pr_list (pr_pair !CP.print_sv !CP.print_sv) ) in
  Debug.no_1 "unify_consj_pre" pr5 pr6
      (fun _ -> unify_consj_pre_x prog unk_hps link_hps equivs pdefs)
      pdefs

(*
This is mandatory
  A<x> --> x::node<l,r> * H1<l> * H2<r>    H1<x> <--> H2<x>
--------------
  A<x> --->  x::node<l,r> * H1<l> * H2<r> /\ x::node<l,r> * H2<l> * H1<r>
*)
let unify_branches_hpdef_x unk_hps link_hps hp_defs =
  let unk_hps = unk_hps@link_hps in
  let rec check_eq_one args fs f done_fs=
    match fs with
      | [] -> done_fs,[f]
      | f1::tl ->
          let b,m = CEQ.checkeq_formulas args f f1 in
          if b then
            let ss = swap_map unk_hps (List.hd m) [] in
            let parts = SAU.partition_subst_hprel ss [] in
            (* let pr = pr_list (pr_pair !CP.print_svl !CP.print_sv) in *)
            (* let _ = DD.info_pprint ("  parts: " ^ (pr parts)) no_pos in *)
            let new_f = List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f parts in
            (* let new_f1 = List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f1 parts in *)
            (tl@done_fs,[new_f(* ;new_f1 *)])
          else
            check_eq_one args tl f (done_fs@[f1])
  in
  let rec check_eq args fs res_fs=
    match fs with
      | [] -> res_fs
      | f::tl ->
          let rem,done_fs = check_eq_one args tl f [] in
          check_eq args rem (res_fs@done_fs)
  in
  let process_one_hpdef (a,hrel,og, f)=
    try
      let hp,args = CF.extract_HRel hrel in
      if CP.mem_svl hp unk_hps then
        (a,hrel,og,f)
      else
        let fs = CF.list_of_disjs f in
        let fs1 = check_eq [] fs [] in
        let p = CF.pos_of_formula f in
        let new_f = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 p)
          (List.hd fs1) (List.tl fs1) in
        (a,hrel,og,new_f)
    with _ -> (a,hrel,og,f)
  in
  DD.ninfo_pprint ">>>>>> unify: <<<<<<" no_pos;
  let r = List.map process_one_hpdef hp_defs in
  (r,[])

let unify_branches_hpdef unk_hps link_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_3 "unify_branches_hpdef" !CP.print_svl !CP.print_svl pr1 pr2
      (fun _ _ _ -> unify_branches_hpdef_x unk_hps link_hps hp_defs)
      unk_hps link_hps hp_defs

let equiv_cmp (hp11,hp12) (hp21,hp22)=
    (CP.eq_spec_var hp11 hp21 && CP.eq_spec_var hp12 hp22) ||
        (CP.eq_spec_var hp11 hp22 && CP.eq_spec_var hp12 hp21)

let equiv_cmp1 (hp11,hp12) (hp21,hp22)=
  (CP.eq_spec_var hp11 hp21 && CP.eq_spec_var hp12 hp22)

let lookup_equiv_hpdef hpdefs0 transform_fnc unk_hps eq_pairs hp args f=
  let rec helper hpdefs=
    match hpdefs with
      | [] -> let new_f = List.fold_left (fun f (hp1,hp) -> CF.subst_hprel f [hp1] hp) f (eq_pairs) in
            (new_f,eq_pairs)
      | (a1,hrel1,og1,f1)::tl -> try
          let hp1,eargs1,p1 = CF.extract_HRel_orig hrel1 in
          let args1 = List.concat (List.map CP.afv eargs1) in
          if CP.eq_spec_var hp hp1 || CP.mem_svl hp1 unk_hps ||
            (List.length args <> List.length args1) then
            helper tl
          else
            (* let ss = List.combine args1 args in *)
            (* let f10 = CF.subst ss f1 in *)
            let f10 = transform_fnc (hp1,args1) (hp,args) f1 in
            if SAU.checkeq_formula_list (CF.list_of_disjs f) (CF.list_of_disjs f10) then
              if List.exists (fun (hp2,hp3) -> equiv_cmp1 (hp1,hp) (hp2,hp3)) eq_pairs then
                let new_f = List.fold_left (fun f (hp1,hp) -> CF.subst_hprel f [hp1] hp) f10 (eq_pairs) in
                (new_f,eq_pairs)
              else
                let new_f = SAU.mkHRel_f hp1 args p1 in
                let n_eq_pairs = if List.exists (fun (hp2,hp3) -> equiv_cmp1 (hp,hp1) (hp2,hp3)) eq_pairs then
                  eq_pairs
                else (eq_pairs@[(hp,hp1)])
                in
                (new_f,n_eq_pairs)
            else helper tl
        with _ -> helper tl
  in
  helper hpdefs0

(*
This is optional --pred-equiv
  A<x> <--> x::node<l,r> * H1<l> * H2<r>    B<x> <--> A<x>
--------------
  A<x> <--->  x::node<l,r> * H1<l> * H2<r>
  B<x> <-->  x::node<l,r> * H1<l> * H2<r>
*)
let unify_syntax_equiv_hpdef_x prog unk_hps link_hps hp_defs equivs0=
   (**************** internal methods**********************)
  let unk_hps = unk_hps@link_hps in
  let syntax_transform_func (hp1,args1) (hp,args) f1=
    let ss = List.combine args1 args in
    let f10 = CF.subst ss f1 in
    f10
  in
  let process_one_hpdef all_hpdefs (eq_pairs,r_hpdefs) (a,hrel,og,f)=
    try
      let hp,args = CF.extract_HRel hrel in
      (* let _ = DD.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos in *)
      if CP.mem_svl hp unk_hps  then
        (eq_pairs,r_hpdefs@[(a,hrel,og,f)])
      else
        let new_f,new_eq_pairs = lookup_equiv_hpdef all_hpdefs syntax_transform_func unk_hps eq_pairs hp args f in
        (new_eq_pairs, r_hpdefs@[(a,hrel,og,new_f)])
    with _ -> (*tupled defs*)
        (eq_pairs,r_hpdefs@[(a,hrel,og,f)])
  in
  (****************END internal methods**********************)
  let equiv,res_hp_defs = List.fold_left (process_one_hpdef hp_defs)
    (equivs0,[]) hp_defs in
  (res_hp_defs, equiv)

let unify_syntax_equiv_hpdef prog unk_hps link_hps hp_defs equivs0 =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_2 "unify_syntax_equiv_hpdef" !CP.print_svl pr1 pr2
      (fun _ _ -> unify_syntax_equiv_hpdef_x prog unk_hps link_hps hp_defs equivs0)
      link_hps hp_defs

let unify_shape_equiv_x prog unk_hps link_hps hp_defs equivs0=
  let shape_transform_func (hp1,args1) (hp,args) f1=
    let ss = (List.combine args1 args)@[(hp1,hp)] in
    let f10 = CF.subst ss f1 in
    f10
  in
  let process_one_hpdef all_hpdefs (eq_pairs,r_hpdefs) (a,hrel,og,f)=
    try
      let hp,args = CF.extract_HRel hrel in
      (* let _ = DD.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos in *)
      if CP.mem_svl hp unk_hps then
        (eq_pairs,r_hpdefs@[(a,hrel,og,f)])
      else
        let new_f,new_eq_pairs = lookup_equiv_hpdef all_hpdefs shape_transform_func unk_hps eq_pairs hp args f in
        (new_eq_pairs, r_hpdefs@[(a,hrel,og,new_f)])
    with _ -> (*tupled defs*)
        (eq_pairs,r_hpdefs@[(a,hrel,og,f)])
  in
  (****************END internal methods**********************)
  let equiv,res_hp_defs = List.fold_left (process_one_hpdef hp_defs)
    (equivs0,[]) hp_defs in
  (res_hp_defs, equiv)

(*
This is optional --pred-equiv
  H1<x> <--> x=null \/ x::node<l,r> * H1<l> * H1<r>    H2<x> <--> H1<x>
--------------
  H1<x> <---> x=null \/ x::node<l,r> * H1<l> * H1<r>
  H2<y> <-->  y=null \/ y::node<l,r> * H2<l> * H2<r>
*)
let unify_shape_equiv prog unk_hps link_hps hpdefs equivs0=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_1 "unify_shape_equiv" pr1 pr2
      (fun _ -> unify_shape_equiv_x  prog unk_hps link_hps hpdefs equivs0) hpdefs

let unify_pred = unify_shape_equiv

let do_unify_x prog unk_hps link_hps defs0=
  let subst_equiv equivs (a,b,og, f)=
    let nf = if equivs = [] then f else
      List.fold_left (fun f0 (from_hps, to_hp) ->
          CF.subst_hprel f0 from_hps to_hp
      ) f equivs
    in
    (a,b, og, nf)
  in
  let unify_heap_conj (r_hp_defs, equivs0) (a,b,og,f)=
    try
      let _,args = CF.extract_HRel b in
      let nf, equivs1 = SAU.norm_heap_consj_formula prog args unk_hps [] f equivs0 in
      (r_hp_defs@[(a,b,og,nf)], equivs1)
    with _ -> (r_hp_defs@[(a,b,og,f)], equivs0)
  in
  (*unify heap conj*)
  let defs1, equivs1 = List.fold_left unify_heap_conj ([], []) defs0 in
  (*unify fields*)
  let defs2,equivs2= unify_branches_hpdef unk_hps link_hps defs1 in
  let equivs = Gen.BList.remove_dups_eq equiv_cmp (equivs1@equivs2) in
  (*unify syntax*)
  let defs, equivs =  unify_syntax_equiv_hpdef prog unk_hps link_hps defs2 (equivs) in
  let parts = SAU.partition_subst_hprel equivs [] in
  let defs1 = List.map (subst_equiv parts) defs in
  (defs1, equivs)

let do_unify prog unk_hps link_hps hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_svl in
  let pr3 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_3 "do_unify" pr2 pr2 pr1 pr3
      (fun _ _ _ -> do_unify_x prog unk_hps link_hps hp_defs)
      unk_hps link_hps hp_defs

let reverify_cond prog (unk_hps: CP.spec_var list) link_hps hpdefs cond_equivs=
  let skip_hps = unk_hps@link_hps in
  let cond_equivs1, unk_equivs = List.partition (fun (hp1, hp2) -> not(CP.mem_svl hp1 skip_hps
    || CP.mem_svl hp2 skip_hps)) cond_equivs in
  if cond_equivs1 <> [] then
    let defs1, equivs1 = do_unify prog unk_hps link_hps hpdefs in
    let diff = Gen.BList.difference_eq equiv_cmp cond_equivs1 equivs1 in
    if diff == [] then
      (true, defs1, equivs1, unk_equivs)
    else
      let defs2, equivs2 = unify_shape_equiv prog unk_hps link_hps defs1 equivs1 in
      let diff2 = Gen.BList.difference_eq equiv_cmp cond_equivs equivs2 in
      if diff2 == [] then
        (true, defs2, equivs2, unk_equivs)
      else (false, hpdefs, cond_equivs, unk_equivs)
  else
    (true, hpdefs, [], unk_equivs)

(*************************************************)
(**********       DISJ-UNIFY       ***************)
(*************************************************)

(*=============**************************================*)
       (*=============END UNIFY PREDS================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============OBLIGATION================*)
(*=============**************************================*)
(*hpdef for gettting root. becuase hp decl may be removed previously*)
let trans_constr_hp_2_view_x iprog cprog proc_name hpdefs in_hp_names chprels_decl constrs=
  let process_cs cs=
    let nlhs = SAO.trans_formula_hp_2_view iprog cprog proc_name
       chprels_decl hpdefs cs.CF.hprel_lhs in
    let nrhs = SAO.trans_formula_hp_2_view iprog cprog proc_name
      chprels_decl hpdefs cs.CF.hprel_rhs in
    {cs with CF.hprel_lhs = nlhs;
    CF.hprel_rhs = nrhs;}
  in
  let n_constrs = List.map process_cs constrs in
  (* let pr1= pr_list_ln Cprinter.string_of_hprel_short in *)
  (* let _ = print_endline ("n_constrs: " ^ (pr1 n_constrs))  in *)
  n_constrs

let trans_constr_hp_2_view iprog cprog proc_name in_hp_names chprels_decl constrs=
  let pr1= pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list pr_id in
  Debug.no_2 "trans_constr_hp_2_view" pr2 pr1 pr1
      (fun _ _ -> trans_constr_hp_2_view_x iprog cprog proc_name
          in_hp_names chprels_decl constrs)
      in_hp_names constrs

(*
(* List of vars needed for abduction process *)
*)
let do_entail_check_x vars cprog cs=
  let _ = Infer.rel_ass_stk # reset in
  let ante = cs.CF.hprel_lhs in
  let conseq = CF.struc_formula_of_formula cs.CF.hprel_rhs (CF.pos_of_formula  cs.CF.hprel_rhs) in
  let conseq = Solver.prune_pred_struc cprog true conseq in
  let pr = Cprinter.string_of_struc_formula in
  let _ = DD.tinfo_hprint (add_str "conseq(after prune)" pr) conseq no_pos in 
  let conseq = AS.add_param_ann_constraints_struc conseq in
  let _ = DD.tinfo_hprint (add_str "conseq(after add param)" pr) conseq no_pos in
  (*********PRINTING*****************)
  (* let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 2:" *)
  (*                       ^"\n ### ivars = "^(pr_list pr_id ivars) *)
  (*                       ^ "\n ### ante = "^(Cprinter.string_of_formula ante) *)
  (*                       ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq) *)
  (*                       ^"\n\n")) no_pos in *)
  (*********PRINTING*****************)
  let es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ante = Solver.normalize_formula_w_coers 11 cprog es ante cprog.CA.prog_left_coercions in
  (*********PRINTING*****************)
  (* let _ = if (!Globals.print_core || !Globals.print_core_all) then print_endline ("INPUT: \n ### ante = " ^ (Cprinter.string_of_formula ante) ^"\n ### conseq = " ^ (Cprinter.string_of_struc_formula conseq)) else () in *)
  (* let _ = Debug.devel_zprint (lazy ("\nrun_entail_check 3: after normalization" *)
  (*                       ^ "\n ### ante = "^(Cprinter.string_of_formula ante) *)
  (*                       ^ "\n ### conseq = "^(Cprinter.string_of_struc_formula conseq) *)
  (*                       ^"\n\n")) no_pos in *)
  (*********PRINTING*****************)
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  (* List of vars appearing in original formula *)
  let orig_vars = CF.fv ante @ CF.struc_fv conseq in
  (* Init context with infer_vars and orig_vars *)
  let (vrel,iv) = List.partition (fun v -> CP.is_rel_typ v) vars in
  let (v_hp_rel,iv) = List.partition (fun v -> CP.is_hprel_typ v) iv in
  let ctx = Inf.init_vars ctx iv vrel v_hp_rel orig_vars in
  (*********PRINTING*****************)
  (* let _ = if !Globals.print_core || !Globals.print_core_all *)
  (*   then print_string ("\nrun_infer:\n"^(Cprinter.string_of_formula ante) *)
  (*       (\* ^" "^(!CP.print_svl vars) *\) *)
  (*     ^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") *)
  (*   else () *)
  (* in *)
  (*********PRINTING*****************)
  let ctx =
    if !Globals.delay_proving_sat then ctx
    else CF.transform_context (Solver.elim_unsat_es 9 cprog (ref 1)) ctx in
  let _ = if (CF.isAnyFalseCtx ctx) then
        print_endline ("[Warning] False ctx")
  in
  let rs1, _ =  Solver.heap_entail_struc_init cprog false false
        (CF.SuccCtx[ctx]) conseq no_pos None
  in
  (* let _ = print_endline ("WN# 1:"^(Cprinter.string_of_list_context rs1)) in *)
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  let valid = ((not (CF.isFailCtx rs))) in
  if not valid then
    report_error no_pos ("Can not prove:\n" ^ (Cprinter.string_of_hprel_short cs))
  else
    let hprels = Inf.collect_hp_rel_list_context rs in
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
    hp_lst_assume

let do_entail_check vars cprog cs=
  let pr1 = Cprinter.string_of_hprel_short in
  Debug.no_2 "do_entail_check" pr1 !CP.print_svl (pr_list_ln pr1)
      (fun _ _-> do_entail_check_x vars cprog cs) cs vars



(*=============**************************================*)
       (*=============END OBLIGATION================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============DNC================*)
(*=============**************************================*)
let partition_constrs_4_paths link_hpargs0 constrs0 =
  let ls_link_hpargs = SAU.dang_partition link_hpargs0 in
  let ls_constrs_path = SAU.assumption_partition constrs0 in
  (* matching constrs_path with dang_path*)
  let ls_cond_danghps_constrs = SAU.pair_dang_constr_path ls_constrs_path ls_link_hpargs (pr_list_ln Cprinter.string_of_hprel_short) in
  ls_cond_danghps_constrs

(*=============**************************================*)
       (*=============END DNC================*)
(*=============**************************================*)

(*=============**************************================*)
       (*=============FIXPOINT================*)
(*=============**************************================*)
let gfp_gen_init_x prog is_pre r rec_fs=
  let find_greates_neg f=
    let svl = CF.get_ptrs_f f in
    let pos = (CF.pos_of_formula f) in
    if CP.mem_svl r svl then
      (*neg for sl is not well defined. use unkhp*)
      let (hf, n_hp) = SAU.add_raw_hp_rel prog is_pre [(r, I)] pos in
      CF.formula_of_heap_w_normal_flow hf pos
    else
      let p = CP.filter_var (CF.get_pure f) [r] in
      CF.formula_of_pure_N (CP.mkNot_s p) pos
  in
  let n_fs = List.map find_greates_neg rec_fs in
  CF.formula_of_disjuncts (rec_fs@n_fs)

let gfp_gen_init prog is_pre r rec_fs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln pr1 in
  Debug.no_2 "gfp_gen_init" !CP.print_sv pr2 pr1
      (fun _ _ -> gfp_gen_init_x prog is_pre r rec_fs)
      r rec_fs

let gfp_iter_x prog rec_fs fixn=
  fixn

let gfp_iter prog rec_fs fixn=
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_1 "gfp_iter" pr1 pr1
      (fun _ -> gfp_iter_x prog rec_fs fixn)
      fixn
(*
 now suppose the set of constraints include
  - base cases
  - recursive cases
  - dependent cases
*)
let norm args0 (hp1, args1, f1)=
  let ss =List.combine args1 args0 in
  (hp1, args0, CF.subst ss f1)

let classify hp (r_bases, r_recs, r_deps) f=
  let hps = CF. get_hp_rel_name_formula f in
  if hps = [] then
    (r_bases@[f], r_recs, r_deps)
  else if CP.diff_svl hps [hp] = [] then
    (r_bases, r_recs@[f], r_deps)
  else (r_bases, r_recs, r_deps@[f])

let compute_gfp_x prog is_pre is pdefs=
  (********INTERNAL*******)
  let skip_hps = List.map fst (is.CF.is_dang_hpargs@is.CF.is_link_hpargs) in
  (********END INTERNAL*******)
  let hp,def=
  match pdefs with
    | (hp0,args0,f0)::rest ->
          (*normalize*)
          let norm_pdefs = (hp0,args0,f0)::(List.map (norm args0) rest) in
          let norm_fs = (List.map (fun (_,_,f) -> f) norm_pdefs) in
          let r,non_r_args = SAU.find_root prog skip_hps args0 norm_fs in
          let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
          (*now assume base_fs =[] and dep_fs = [] and rec_fs != [] *)
          if base_fs =[] && dep_fs = [] then
            (*init*)
            let fix0 = gfp_gen_init prog is_pre r rec_fs in
            (*iterate*)
            let fixn = gfp_iter prog rec_fs fix0 in
            (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None fixn (CF.pos_of_formula f0))
          else
            report_error no_pos "sac.compute gfp: not support yet"
    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let _ = Debug.binfo_pprint ("    synthesize: " ^ (!CP.print_sv hp) ) no_pos in
  let _ = Debug.binfo_pprint ((Cprinter.string_of_hp_rel_def_short def)) no_pos in
  def

let compute_gfp prog is_pre is pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "compute_gfp" pr3 pr4
      (fun _ -> compute_gfp_x prog is_pre is pdefs) pdefs

let lfp_gen_init_x nonrec_fs=
  nonrec_fs

let lfp_gen_init nonrec_fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_1 "lfp_gen_init" pr1 pr1
      (fun _ -> lfp_gen_init_x nonrec_fs) nonrec_fs

let simplify_disj_set prog args unk_hps unk_svl pdefs pos=
  let rec helper2 pdefs res=
    match pdefs with
      | [] -> res
      | [pdef] -> res@[pdef]
      | (hp1,args1, g1, f1, svl1)::((hp2,args2, g2, f2, svl2)::rest) -> begin
          let b, nfs = SAU.simplify_disj prog args unk_hps unk_svl f1 f2 pos in
          if b then
            let npdefs=
              [(hp2,args2, g2, List.hd nfs, svl2)]
            in
            helper2 (res@npdefs@rest) []
          else
            helper2 rest (res@[(hp1,args1, g1, f1, svl1);(hp2,args2, g2, f2, svl2)])
        end
  in
  helper2 pdefs []

let lfp_iter_x prog step hp args dang_hps fix_0 nonrec_fs rec_fs=
  let apply_fix fix_i r_fs pdef_f=
    let _, fs = if fix_i = [] then (false, []) else
      SAU.succ_subst prog [fix_i] dang_hps true pdef_f in
    r_fs@fs
  in
  let pdef_rec_fs = List.map (fun f -> (hp,args, None, f, [])) rec_fs in
  let pdef_nonrec_fs = List.map (fun f -> (hp,args, None, f, [])) nonrec_fs in
  (*INTERNAL*)
  let rec rec_helper_x i pdef_fix_i=
    (**********PRINTING***********)
    let _ = DD.binfo_pprint ("   fix: " ^ (string_of_int i) ^ (
        let pr1  = Cprinter.prtt_string_of_formula in
        let fs = List.map (fun (_,_, _, f, _) -> f) pdef_fix_i in
        let f = if fs = [] then CF.mkFalse (CF.mkTrueFlow ())  no_pos else (CF.formula_of_disjuncts fs) in
        pr1 f )
    ) no_pos
    in
    (*******END PRINTING*********)
    (*apply rec for cur fix*)
    let fix_i_plus = pdef_nonrec_fs@(List.fold_left (apply_fix pdef_fix_i) [] pdef_rec_fs) in
    (*check whether it reaches the fixpoint*)
    (* let fix_i_plus1 = Gen.BList.remove_dups_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) -> *)
    (*     SAU.check_relaxeq_formula args f1 f2) fix_i_plus in *)
    let fix_i_plus1 = simplify_disj_set prog args dang_hps [] fix_i_plus no_pos in
    let diff = Gen.BList.difference_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) ->
        SAU.check_relaxeq_formula args f1 f2) fix_i_plus1 pdef_fix_i in
    let rec_helper pdef_fix_i=
      let pr1 (_,_, _, f, _) = Cprinter.prtt_string_of_formula f in
      let pr2 = pr_list_ln pr1 in
      Debug.no_1 "rec_helper" pr2 pr2
          (fun _ -> rec_helper_x pdef_fix_i) pdef_fix_i
    in
    (*recusive call*)
    if diff = [] then fix_i_plus1 else
    rec_helper (i+1) fix_i_plus1
  in
  (*END INTERNAL*)
  let pdef_fix_0 = List.map (fun f -> (hp,args, None, f, [])) fix_0 in
  let r = rec_helper_x step pdef_fix_0 in
  List.map (fun (_,_, _, f, _) -> f) r

let lfp_iter prog step hp args dang_hps fix_0 nonrec_fs rec_fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_5 "lfp_iter" !CP.print_sv !CP.print_svl pr1 pr1 pr1 pr1
      (fun _ _ _ _ _ -> lfp_iter_x prog step hp args dang_hps fix_0 nonrec_fs rec_fs)
      hp args fix_0 nonrec_fs rec_fs

let mk_expl_root_fnc hp ss r hf=
  let rec subst_root r ss eargs res=
    match eargs with
      | [] -> res
      | e::rest -> begin
          match e with
            | CP.Var (sv, p) ->
                  let args = [r;sv] in
                  if List.exists (fun (sv1,sv2) -> CP.diff_svl args [sv1;sv2] = []) ss then
                    (res@((CP.Var (r, p))::rest))
                  else subst_root r ss rest (res@[e])
            | _ -> subst_root r ss rest (res@[e])

        end
  in
  match hf with
    | CF.HRel (hp1, eargs, pos) ->
          let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
          if CP.mem_svl r args then hf else
            let n_eargs = subst_root r ss eargs [] in
            CF.HRel (hp1, n_eargs, pos)
    | _ -> hf

let compute_lfp_x prog is_pre is pdefs=
  (********INTERNAL*******)
  let mk_exp_root_x hp r f =
    let _, mf, _, _, _ = CF.split_components f in
    let ss = MCP.ptr_equations_without_null mf in
    (CF.trans_heap (mk_expl_root_fnc hp ss r) f)
  in
  let mk_exp_root hp r f =
    let pr1 = Cprinter.prtt_string_of_formula in
    Debug.no_2 "mk_exp_root" !CP.print_sv pr1 pr1
        (fun _ _ -> mk_exp_root_x hp r f) r f
  in
  let skip_hps = List.map fst (is.CF.is_dang_hpargs@is.CF.is_link_hpargs) in
  (********END INTERNAL*******)
  let hp,def=
  match pdefs with
    | (hp0,args0,f0)::rest ->
          let pos = CF.pos_of_formula f0 in
          (*normalize*)
          let norm_pdefs = (hp0,args0,f0)::(List.map (norm args0) rest) in
          let norm_fs0 = (List.map (fun (_,_,f) -> f) norm_pdefs) in
          let r,non_r_args = SAU.find_root prog skip_hps args0 norm_fs0 in
          let norm_fs = List.map (mk_exp_root hp0 r) norm_fs0 in
          (* let _ =  DD.info_pprint ("   r: " ^(!CP.print_sv r)) no_pos in *)
          let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
          (*init*)
          let fix_0 = (* (base_fs@dep_fs) *) [] in
          (*iterate*)
          let fixn = lfp_iter prog 0 hp0 args0 skip_hps fix_0 (base_fs@dep_fs) rec_fs in
          let def = CF.formula_of_disjuncts fixn in
          (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None def pos)
    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let _ = Debug.binfo_pprint ("    synthesize: " ^ (!CP.print_sv hp) ) no_pos in
  let _ = Debug.binfo_pprint ((Cprinter.string_of_hp_rel_def_short def)) no_pos in
  def

let compute_lfp prog is_pre is pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "compute_lfp" pr3 pr4
      (fun _ -> compute_lfp_x prog is_pre is pdefs) pdefs

(*=============**************************================*)
       (*=============END FIXPOINT================*)
(*=============**************************================*)
