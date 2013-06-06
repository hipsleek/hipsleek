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

let cmp_hp_pos (hp1,pos1) (hp2,pos2)= (CP.eq_spec_var hp1 hp2) && pos1=pos2
let rec lookup_xpure_view hp_pos0 rem_map done_map=
  match rem_map with
    | [] -> None,done_map
    | (hp_pos1,xpv)::tl ->
          if Gen.BList.intersect_eq cmp_hp_pos hp_pos0 hp_pos1 <> [] then
            let new_hp_pos = Gen.BList.remove_dups_eq cmp_hp_pos (hp_pos0@hp_pos1) in
            Some xpv,done_map@[(new_hp_pos,xpv)]@tl
          else lookup_xpure_view hp_pos0 tl (done_map@[(hp_pos1,xpv)])

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
              let hp_name = CP.fresh_old_name (CP.name_of_spec_var (fst (List.hd ls_hp_pos))) in
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

let generate_linking ls_hpargs sv=
  (List.fold_left (find_pos 0 sv) [] ls_hpargs,sv)

let generate_map_x l_hpargs r_hpargs unk_map pos=
  let l_args = List.fold_left (fun ls (_, args) -> ls@args) [] l_hpargs in
  let r_args = List.fold_left (fun ls (_, args) -> ls@args) [] r_hpargs in
  let unk_svl1 = CP.remove_dups_svl (CP.intersect_svl l_args r_args) in
  let ls_hp_pos_sv = List.map (generate_linking (l_hpargs@r_hpargs)) unk_svl1 in
  let unk_pure,new_map = generate_xpure_view_w_pos ls_hp_pos_sv unk_map pos in
  (unk_svl1, unk_pure, new_map)

let generate_map unk_l_hpargs r_hpargs unk_map pos=
  let pr1= (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  let pr2 = !CP.print_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "generate_map" pr3 pr3 pr1 (pr_triple !CP.print_svl pr2 pr1)
      (fun _ _ _ -> generate_map_x unk_l_hpargs r_hpargs unk_map pos)
      unk_l_hpargs r_hpargs unk_map

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
    let ls_hp_pos_sv = List.map (generate_linking (l_hpargs@r_hpargs)) unk_svl in
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
   let rec helper args res index all=
    match args with
      | [] -> res
      | a::ass -> if (fn_cmp a all) (* || not(CP.is_node_typ a) *) then
            helper ass res (index+1) all
          else helper ass (res@[index]) (index+1) all
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
          let res =
            if CP.mem_svl hp_name unk_hps then
              helper1 largs [] 0 (*this is a dangling predicate*)
            else
              helper largs [] 0 all_ptrs
          in
          if res = [] then ([(hp_name,[-1])],[]) (*renturn -1 to indicate that none is allowed to drop*)
          else
            (*check full unk hp*)
            (* let pr1 = pr_list string_of_int in *)
            (* let _ = Debug.info_pprint ("   hp: " ^ (!CP.print_sv hp_name)) no_pos in *)
            (* let _ = Debug.info_pprint ("     res: " ^ (pr1 res)) no_pos in *)
            (* let _ = Debug.info_pprint ("     largs: " ^ (!CP.print_svl largs)) no_pos in *)
            if (List.length res) = (List.length largs) then
              ([(hp_name, res)],[(hp_name, largs,res)])
            else ([(hp_name, res)],[])
      end
  in
  get_unk_ptr known_svl (hp_name, args)

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
  (*return*)
  let unk_hp_locs,unk_hp_args_locs = List.split (List.map (build_hp_unk_locs (svl) unk_hps CP.mem_svl) (lhrels@rhrels)) in
  (List.concat unk_hp_locs, List.concat unk_hp_args_locs)

and double_check_unk prog unk_hp_locs unk_hps cs=
  let lhds, lhvs, lhrels = CF.get_hp_rel_formula cs.CF.hprel_lhs in
  let rhds, rhvs, rhrels = CF.get_hp_rel_formula cs.CF.hprel_rhs in
  let cs_hprels = List.map (fun (hp,eargs,_) -> (hp, List.fold_left List.append [] (List.map CP.afv eargs))) (lhrels@rhrels) in
  (*return: unk_args*)
  let rec retrieve_args_one_hp ls (hp,args)=
    match ls with
      | [] -> ([],args)
      | (hp1,locs)::ss -> if CP.eq_spec_var hp hp1 then
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
  let double_check_one_constr unk_hp_locs cs_hprels=
    let unk_hp_names = List.map (fun (hp, _) -> hp) unk_hp_locs in
    let cs_hp_args = Gen.BList.remove_dups_eq SAU.check_hp_arg_eq (cs_hprels) in
    let cs_unk_hps,cs_non_unk_hps = List.partition
      (fun (hp,_) -> CP.mem_svl hp unk_hp_names) cs_hp_args in
    (* definitely non unk*)
    let cs_non_unk_svl = List.concat (List.map (fun (_, args) -> args) cs_non_unk_hps) in
    (*possible unk*)
    let unk_svl_hps, cs_non_unk_svl2 = List.fold_left (fun (ls1, ls2) hp_args ->
        let unk_svl, non_unk_svl = retrieve_args_one_hp unk_hp_locs hp_args in
        (ls1@unk_svl, ls2@non_unk_svl)
    ) ([],[]) cs_unk_hps in
    let cs_non_unk_svl1 =
      CP.remove_dups_svl (* (SAU.look_up_closed_ptr_args prog (lhds@rhds) (lhvs@rhvs) *) (cs_non_unk_svl2@cs_non_unk_svl)
          (* ) *)
    in
    let poss_unk_svl_hps = CP.remove_dups_svl unk_svl_hps in
    (*actually unk = poss unk - non-unk*)
    let real_unk_svl_hps = Gen.BList.difference_eq CP.eq_spec_var poss_unk_svl_hps
      cs_non_unk_svl1 in
    let ls_unk_hps_locs, ls_unk_hps_args_locs = List.split (List.map (build_hp_unk_locs real_unk_svl_hps unk_hps
                                                                          (fun a ls -> not( CP.mem_svl a ls))) (cs_unk_hps))
    in
    (List.concat ls_unk_hps_locs, List.concat ls_unk_hps_args_locs)
  in
  double_check_one_constr unk_hp_locs (cs_hprels)

(*
  for each constraint:
   + update svl + unk_hps
   + add XPure for each dangling pointer
   + split full hp
   + simplify
*)
and update_unk_one_constr_x prog unk_hp_locs unk_map cs=
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
  (*diff from present ones, we may find them prior to*)
  let ls_xpures =  CF.get_xpure_view cs.CF.hprel_lhs in
  let existing_svl = List.fold_left (fun ls (_, svl) -> ls@svl) [] ls_xpures in
  let unk_svl1 = CP.diff_svl unk_svl0 (cs.CF.unk_svl@ existing_svl) in
  let new_constr, unk_hps1, new_map=
    if unk_svl1 = [] then (cs, [], unk_map) else
      (*for each unk sv: generate linking*)
      let pos = CF.pos_of_formula cs.CF.hprel_lhs in
      let ls_hp_pos_sv = List.map (generate_linking hp_args) unk_svl1 in
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

and update_unk_one_constr prog unk_hp_locs unk_map constr=
  let pr1 = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 =  (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = Cprinter.string_of_hprel in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr5 = pr_triple pr3 pr4 pr2 in
  Debug.no_3 "update_unk_one_constr" pr1 pr2 pr3 pr5
      (fun _ _ _ -> update_unk_one_constr_x prog unk_hp_locs unk_map constr)
      unk_hp_locs unk_map constr

(*this method has the same structure with elim_redundant_paras_lst_constr_x,
should use higher-order when stab.*)
and analize_unk_x prog constrs total_unk_map =
  let rec partition_cands_by_hp_name unks parts=
    match unks with
      | [] -> parts
      | (hp_name,ids)::xs ->
          let part,remains= List.partition (fun (hp_name1,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
          partition_cands_by_hp_name remains (parts@[[(hp_name,ids)]@part])
  in
  let intersect_cand_one_hp ls=
    let hp_names,cands = List.split ls in
    let _ = Debug.ninfo_pprint ("   hprel: " ^ (!CP.print_svl hp_names)) no_pos in
    let _ = Debug.ninfo_pprint ("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)) no_pos in
    let locs = List.fold_left (fun ls1 ls2 ->
        Gen.BList.intersect_eq (=) ls1 ls2)
      (List.hd cands) (List.tl cands) in
    if locs = [] then []
    else [(List.hd hp_names, locs)]
  in
  let rec drop_invalid_group ls res=
    match ls with
      | [] -> res
      | (hp,locs)::ss -> if locs = [-1] then drop_invalid_group ss res
          else drop_invalid_group ss (res@[(hp,locs)])
  in
  let helper (ls_unk_cands,ls_full_unk_cands_w_args)=
    (* let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map fn constrs) in *)
    let unk_cands = List.concat ls_unk_cands in
  (*group cands into each hp*)
    let groups = partition_cands_by_hp_name unk_cands [] in
  (*each hp, intersect all candidate unks*)
    let unk_hp_locs1 = List.concat (List.map intersect_cand_one_hp groups) in
    let unk_hp_locs2 = drop_invalid_group unk_hp_locs1 [] in
    let unk_hps = List.map fst unk_hp_locs2 in
    let full_unk_hp_args2_locs = List.filter (fun (hp,_,_) -> CP.mem_svl hp unk_hps )
      (List.concat ls_full_unk_cands_w_args) in
    (Gen.BList.remove_dups_eq (fun (hp1,_) (hp2,_) -> CP.eq_spec_var hp1 hp2) unk_hp_locs2,
     Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) -> CP.eq_spec_var hp1 hp2) full_unk_hp_args2_locs)
  in
  (* let unk_hps = List.fold_left (fun ls (hps,_) ->ls@(List.map fst hps)) [] total_unk_map in *)
  let unk_hps = [] in
  let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map (analize_unk_one prog unk_hps) constrs) in
  let unk_hp_args01,_ = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
  (*for debugging*)
  let _ = Debug.ninfo_pprint ("  unks 1: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                             in pr unk_hp_args01)) no_pos
  in
  (*END for debugging*)
  (*double check across one cs*)
  let rec loop_helper unk_hp_locs0=
    let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map (double_check_unk prog unk_hp_locs0 unk_hps) constrs) in
    let unk_hp_args02,full_unk_hp_args2_locs = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
    let ls_unk_cands1 = Gen.BList.remove_dups_eq SAU.check_hp_locs_eq unk_hp_args02 in
    let _ = Debug.ninfo_pprint ("  ls_unk_cands1: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                             in pr ls_unk_cands1)) no_pos
    in
    if ls_unk_cands1 = [] then [],[] else
      let diff = Gen.BList.difference_eq SAU.check_hp_locs_eq unk_hp_locs0 ls_unk_cands1 in
      if diff =[] then (ls_unk_cands1, full_unk_hp_args2_locs) else
        loop_helper ls_unk_cands1
  in
  let unk_hp_args02,full_unk_hp_args2_locs = loop_helper unk_hp_args01 in
  (*********END double check ****************)
   let full_unk_hp_args2_locs = SAU.refine_full_unk unk_hp_args02 full_unk_hp_args2_locs in
   (*generate equivs mapping for all full unk hps*)
   let gen_equivs_from_full_unk_hps (hp,args,locs)=
     ((hp,locs), [(hp, args)])
   in
   (*for debugging*)
   let _ = Debug.ninfo_pprint ("  unks 2: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                              in pr unk_hp_args02)) no_pos
   in
   (* let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
   (*                            (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
   (* let _ = Debug.info_pprint ("  equivs0: " ^ (pr1 equivs0) ) no_pos in *)
  (*END for debugging*)
  (*END double check*)
   let rec update_helper cs unk_map res_cs res_unk_hps=
     match cs with
       | [] ->  (res_cs, res_unk_hps, unk_map)
       | c::ss ->
           let new_c, new_unk_hps, new_map= update_unk_one_constr prog unk_hp_args02 unk_map c in
           update_helper ss new_map (res_cs@[new_c]) (res_unk_hps@new_unk_hps)
   in
   let new_cs, unk_hps, new_map =
     if unk_hp_args02 =[] then
     (constrs, [], [])
     else update_helper constrs total_unk_map [] []
   in
   (new_cs, SAU.elim_eq_shorter_hpargs unk_hps, new_map)

let analize_unk prog constrs total_unk_map =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = pr_triple pr1 pr3 pr2 in
  Debug.no_2 "analize_unk" pr1 pr2 pr4
      (fun _ _ -> analize_unk_x prog constrs total_unk_map)
      constrs total_unk_map


let generate_hp_def_from_unk_hps_x hpdefs unk_hpargs defined_hps post_hps unk_map=
  let rec obtain_xpure rem_args n hp res=
    match rem_args with
      | [] -> res
      | sv::rest -> begin
            let oxpv,_ = lookup_xpure_view [(hp,n)] unk_map [] in
            match oxpv with
              | Some xp -> let new_xpv = {xp with CP.xpure_view_arguments = [sv];} in
                let p = CP.mkFormulaFromXP new_xpv in
                obtain_xpure rest (n+1) hp (res@[p])
              | None -> report_error no_pos "sac.obtain_xpure"
        end
  in
  let mk_unkdef pos (hp,args)=
    let ps = obtain_xpure args 0 hp [] in
    let p = CP.conj_of_list ps pos in
    let def = CF.formula_of_pure_formula p pos in
    let _ = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^
                                    (!CP.print_svl args) ^ ")=" ^
                                    (Cprinter.prtt_string_of_formula (* (CF.formula_of_heap h_def no_pos) *) def)) pos
    in
    let new_hpdef = (CP.HPRelDefn hp,
                                 (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args,pos)),
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

  let unk_hpdefs = List.fold_left helper [] unk_hpargs in
  let hpdefs1 = (unk_hpdefs@hpdefs) in
  (hpdefs1)

let generate_hp_def_from_unk_hps hpdefs unk_hpargs defined_hps post_hps unk_map=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = (pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view)) in
  Debug.no_4 "generate_hp_def_from_unk_hps" pr2 pr1 !CP.print_svl pr4 pr1
      (fun _ _ _ _ -> generate_hp_def_from_unk_hps_x hpdefs unk_hpargs defined_hps post_hps unk_map)
      unk_hpargs hpdefs defined_hps unk_map

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
        let ss = List.combine used_args fr_args in
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
    let p_eqs = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) eqs in
    let p = CP.conj_of_list (CP.remove_redundant_helper p_eqs []) pos in
    let f3 = CF.mkAnd_pure f2 (MCP.mix_of_pure p) pos in
    (f3, unk_need_subst)
  in
  let subst_pure_hp_unk_hpdef ls_unk_hpargs_fr (rc, hf, def)=
    let hp,args0 = CF.extract_HRel hf in
    let fs = CF.list_of_disjs def in
    let fs1 = List.map (subst_pure_hp_unk args0 ls_unk_hpargs_fr) fs in
    let def1 = CF.disj_of_list (fst (List.split fs1)) (CF.pos_of_formula def) in
    (rc, hf, def1, fs1)
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
  let new_hpdefs1 = List.map (fun (a,b,f,_) -> (a,b, f)) new_hpdefs in
  let new_hpdefs2 = List.map (fun (a,b,_,pr_f) -> (a,b, pr_f)) new_hpdefs in
  (*subst XPURE*)
  List.map (fun (a,b,pr_f) -> (a,b,  subst_and_combine (*subst_xpure*) new_hpdefs1 pr_f)) new_hpdefs2

let transform_unk_hps_to_pure hp_defs unk_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_unk_hps_to_pure" pr1 pr2 pr1
      (fun _ _ -> transform_unk_hps_to_pure_x hp_defs unk_hpargs) hp_defs unk_hpargs

let transform_xpure_to_pure_x hp_defs unk_map=
  let fr_map = List.map (fun (hps, xp) ->
      let args = match xp.CP.xpure_view_node with
        | None -> xp.CP.xpure_view_arguments
        | Some sv -> sv::xp.CP.xpure_view_arguments
      in
      let (CP.SpecVar (t, _, p)),_ = List.hd hps in
      (CP.SpecVar(t, xp.CP.xpure_view_name, p),
      (* List.map (CP.fresh_spec_var_prefix dang_hp_default_prefix_name) args)) unk_map *)
      let dang_name = dang_hp_default_prefix_name ^ "_" ^ xp.CP.xpure_view_name ^ "_" ^dang_hp_default_prefix_name  in
      List.map (fun (CP.SpecVar (t, _, p)) -> CP.SpecVar (t, dang_name, p)) args)
  ) unk_map
  in
  transform_unk_hps_to_pure hp_defs fr_map

let transform_xpure_to_pure hp_defs unk_map =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "transform_xpure_to_pure" pr1 pr1
      (fun _ -> transform_xpure_to_pure_x hp_defs unk_map) hp_defs


(*=============**************************================*)
(*=============END UNKOWN================*)
(*=============**************************================*)
