open Globals
open Gen
open Others
open Label_only

module DD = Debug
module Err = Error
module IA = Iast
module CA = Cast
module AS = Astsimp
module CP = Cpure
module IF = Iformula
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module TP = Tpdispatcher
module SAU = Sautility
module SAO = Saout
module Inf = Infer
module SC = Sleekcore
module LEM = Lemma

let infer_shapes = ref (fun (iprog: IA.prog_decl) (cprog: CA.prog_decl) (proc_name: ident)
  (hp_constrs: CF.hprel list) (sel_hp_rels: CP.spec_var list) (sel_post_hp_rels: CP.spec_var list)
  (hp_rel_unkmap: ((CP.spec_var * int list) * CP.xpure_view) list)
  (unk_hpargs: (CP.spec_var * CP.spec_var list) list)
  (link_hpargs: (int list * (Cformula.CP.spec_var * Cformula.CP.spec_var list)) list)
  (need_preprocess: bool) (detect_dang: bool) -> let a = ([] : CF.hprel list) in
  let b = ([] : CF.hp_rel_def list) in
  (a, b)
)

let cmp_hp_pos (hp1,pos1) (hp2,pos2)= (CP.eq_spec_var hp1 hp2) && pos1=pos2

let cs_rhs_is_only_neqNull cs=
  let lhs_hpargs = CF.get_HRels_f cs.CF.hprel_lhs in
  let args = List.fold_left (fun ls (_, args) -> ls@args) [] lhs_hpargs in
  CF.is_only_neqNull args [] cs.CF.hprel_rhs


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
            (* let _ = Debug.info_zprint (lazy (("   hp: " ^ (!CP.print_sv hp_name)))) no_pos in *)
            (* let _ = Debug.info_zprint (lazy (("     res: " ^ (pr1 res)))) no_pos in *)
            (* let _ = Debug.info_zprint (lazy (("     largs: " ^ (!CP.print_svl largs)))) no_pos in *)
            if (List.length res) = (List.length largs) then
              ([(hp_name, largs, res)],[(hp_name, largs,res)])
            else ([(hp_name,unk_args, res)],[])
      end
  in
  get_unk_ptr known_svl (hp_name, args)

let check_equality_constr lhpargs lhs_f_rem rhs svl2=
  let helper args f=
    match args with
      | sv::_ ->
            let ( _,mix_f,_,_,_) = CF.split_components f in
            let reqs2 = (MCP.ptr_equations_without_null mix_f) in
            let cl_svl = CP.remove_dups_svl (CF.find_close [sv] (reqs2)) in
            (* let _ = Debug.info_hprint (add_str "   cl_svl: " !CP.print_svl) cl_svl no_pos in *)
            if (* List.length cl_svl >1 && *)
              CP.diff_svl cl_svl args = [] then
                args
            else svl2
      | _ -> svl2
  in
  (*handle equality*)
  (* let _ = Debug.info_zprint (lazy (("   svl2: " ^ (!CP.print_svl svl2)))) no_pos in *)
  if svl2 <> [] then svl2 else
    match lhpargs with
      | [(_,args)] ->
            (* let _ = Debug.info_zprint (lazy (("   lhs_f_rem: " ^ (!CF.print_formula lhs_f_rem)))) no_pos in *)
            (* let _ = Debug.info_zprint (lazy (("   rhs: " ^ (!CF.print_formula rhs)))) no_pos in *)
            if SAU.is_empty_heap_f lhs_f_rem then
              let svl = helper args lhs_f_rem in
              if svl == [] && SAU.is_empty_heap_f rhs then
                helper args rhs
              else svl
            else
              svl2
      | _ -> svl2

(*analysis unknown information*)
let rec analize_unk_one prog unk_hps constr =
  (* let _ = Debug.info_zprint (lazy (("   hrel: " ^ (Cprinter.string_of_hprel_short constr)))) no_pos in *)
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
  let svl1a = SAU.get_defined_eqs constr.CF.hprel_lhs in
  let svl1 = check_equality_constr lhrels lhs1 constr.CF.hprel_rhs svl in
  (*return*)
  let unk_hp_locs,unk_hp_args_locs = List.split (List.map
      (build_hp_unk_locs (CP.remove_dups_svl (svl1@svl1a)) unk_hps CP.mem_svl)
      (lhrels@rhrels))
  in
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
    (* let _ = Debug.ninfo_zprint (lazy (("  poss_unk_svl_hps: " ^ (!CP.print_svl poss_unk_svl_hps)))) no_pos in *)
    (* let _ = Debug.ninfo_zprint (lazy (("  cs_non_unk_svl1: " ^ (!CP.print_svl cs_non_unk_svl1)))) no_pos in *)
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
   (* let _ = Debug.ninfo_zprint (lazy (("  cs: " ^ (Cprinter.string_of_hprel cs)))) no_pos in *)
   let _ = Debug.ninfo_hprint (add_str "  cs: " Cprinter.string_of_hprel) cs no_pos in
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
  (* let _ = Debug.info_zprint (lazy (("  unk_svl0: " ^ (!CP.print_svl unk_svl0)))) no_pos in *)
  (*diff from present ones, we may find them prior to*)
  let ls_xpures =  CF.get_xpure_view cs.CF.hprel_lhs in
  let existing_svl = List.fold_left (fun ls (_, svl) -> ls@svl) [] ls_xpures in
  let unk_svl1 = CP.diff_svl unk_svl0 (cs.CF.unk_svl@ existing_svl) in
  (* let _ = Debug.info_zprint (lazy (("  unk_svl1: " ^ (!CP.print_svl unk_svl1)))) no_pos in *)
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
    let _ = Debug.ninfo_zprint (lazy (("   hprel: " ^ (!CP.print_svl hp_names)))) no_pos in
    let _ = Debug.ninfo_zprint (lazy (("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)))) no_pos in
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
  (* let _ = Debug.ninfo_pprint ("  unks 1: " ^ *)
  (*     (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) *)
  (*                                            in pr unk_hp_args01)) no_pos *)
  (* in *)
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
    (* let _ = Debug.ninfo_pprint ("  ls_unk_cands1: " ^ *)
    (*     (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) *)
    (*                                          in pr ls_unk_cands1)) no_pos *)
    (* in *)
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
  let _ = Debug.ninfo_hprint (add_str "  unks 2: " (pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)))) unk_hp_args02 no_pos
  in
  let _ = Debug.ninfo_hprint (add_str "  full_unk_hp_args2_locs: " (pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)))) full_unk_hp_args2_locs no_pos
  in
  (* let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
  (*                            (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
  (* let _ = Debug.info_zprint (lazy (("  equivs0: " ^ (pr1 equivs0) ))) no_pos in *)
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
   (* let _ = Debug.ninfo_pprint ("  full_unk_hp_locs: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) *)
   (*                                            in pr full_unk_hp_locs0)) no_pos *)
   (* in *)
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
   let _ = Debug.ninfo_zprint (lazy (("  link_hpargs3: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr link_hpargs3)))) no_pos
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
           (* let _ = Debug.info_zprint (lazy (("  drop_links: " ^ (!CP.print_svl drop_links)))) no_pos in *)
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
   let _ = if !Globals.print_heap_pred_decl && !Globals.sap then
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
    (* let _ = DD.info_zprint (lazy (("       f: " ^ (!CF.print_formula f)))) no_pos in *)
    let ls_used_hp_args = CF.get_HRels_f f in
    let ls_xpures =  CF.get_xpure_view f in
    (*look up*)
    let r1 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_used_hp_args in
    let r2 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_xpures in
    let ls_used_unk_hps,ls_eqs, ls_ss = split3 (r1@r2) in
    let used_unk_hps = List.concat ls_used_unk_hps in
    let unk_need_subst, eqs = List.fold_left (fun (ls1,ls2) (a1,a2) -> (ls1@a1,ls2@a2)) ([],[]) (List.concat ls_eqs) in
    (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    (* let _ = DD.info_zprint (lazy (("       eqs: " ^ (pr1 eqs)))) no_pos in *)
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
  (* let _ = DD.info_zprint (lazy (("unk_hps: " ^ (!CP.print_svl unk_hps)))) no_pos in *)
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
        (* let _ = Debug.ninfo_zprint (lazy (("     m_args2: " ^ (!CP.print_svl  m_args2)))) no_pos in *)
        (* let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
        (* let _ =  Debug.ninfo_zprint (lazy (("     subst: " ^ (pr_ss subst)))) no_pos in *)
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
          (* let _ = Debug.ninfo_zprint (lazy (("    all matched: " ^ (!CP.print_svl all_matched_svl2)))) no_pos in *)
          (* let _ =  Debug.ninfo_zprint (lazy (("     subst1: " ^ (pr_ss subst1)))) no_pos in *)
          if  (is_inconsistent subst1 []) then None else
            let n_rhs_b = CF.subst_b subst1 rhs_b in
            (*check pure implication*)
            (* let nrdns,nrvns,_ = CF.get_hp_rel_bformula n_rhs_b in *)
            (*loc-1b1.slk*)
            (* let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure)
               (look_up_closed_ptr_args prog nrdns nrvns all_matched_svl2) in *)
            let rmf = (MCP.pure_of_mix n_rhs_b.CF.formula_base_pure) in
            let lmf = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
            let _ = Debug.ninfo_zprint (lazy (("    n_rhs_b: " ^ (Cprinter.string_of_formula_base n_rhs_b)))) no_pos in
            (* let _ = Debug.info_zprint (lazy (("    lmf: " ^ (!CP.print_formula lmf)))) no_pos in *)
            (* let _ = Debug.info_zprint (lazy (("    rmf: " ^ (!CP.print_formula rmf)))) no_pos in *)
            let b,_,_ = TP.imply_one 20 lmf rmf "sa:check_hrels_imply" true None in
            if b then
              (* let r_res = {n_rhs_b with *)
              (*     CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf *)
              (*         n_rhs_b.CF.formula_base_heap SAU.select_dnode *)
              (*         SAU.select_vnode SAU.select_hrel all_matched_svl2  all_matched_svl2 matched_hps} *)
              (* in *)
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
  let _ = Debug.ninfo_zprint (lazy (("    cs2: " ^ (Cprinter.string_of_hprel cs2)))) no_pos in
  let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_rhs in
  let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_rhs in
  let n_cs2=
  match f1,f2 with
      | CF.Base rhs1_b, CF.Base rhs2_b ->
          let nlhs2, nrhs2_b, ss2 = rename_var_clash cs2.CF.hprel_lhs rhs2_b in
          let nrhs2_b1 =  CF.mkAnd_base_pure nrhs2_b (MCP.mix_of_pure (CF.get_pure nlhs2)) no_pos in
          let _ = Debug.ninfo_zprint (lazy (("    nrhs2_b1: " ^ (Cprinter.string_of_formula_base nrhs2_b1)))) no_pos in
          let _ = Debug.ninfo_zprint (lazy (("    rhs1_b: " ^ (Cprinter.string_of_formula_base rhs1_b)))) no_pos in
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
                    let _ = Debug.ninfo_zprint (lazy (("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
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
          let _ = Debug.ninfo_zprint (lazy (("    cs1: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in
          let new_rest, n_res = List.fold_left ( fun (ls1,ls2) cs2 ->
              let _ = Debug.ninfo_zprint (lazy (("    cs 2 (rest): " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
              let on_cs2 = check_apply_fnc prog cs1 cs2 in
              match on_cs2 with
                | None -> (ls1@[cs2],ls2)
                | Some n_cs2 -> (* if check_constr_duplicate (n_cs2.CF.hprel_lhs, n_cs2.CF.hprel_rhs) (constrs@new_cs) then ls@[cs2] else *) (ls1,ls2@[n_cs2])
          ) ([],res) rest1 in
          let new_don, n_res1 = List.fold_left ( fun (ls1,ls2) cs2 ->
              let _ = Debug.ninfo_zprint (lazy (("    cs 2 (done): " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
              let on_cs2 = check_apply_fnc prog cs1 cs2 in
              match on_cs2 with
                | None -> (ls1@[cs2],ls2)
                | Some n_cs2 -> (* if check_constr_duplicate (n_cs2.CF.hprel_lhs, n_cs2.CF.hprel_rhs) (constrs@new_cs) then ls@[cs2] else *) (ls1,ls2@[n_cs2])
          ) ([],n_res) don in
          helper_new_only (new_don@[cs1]) new_rest n_res1
  in
  (*new_cs x constr*)
  (* let rec helper_old_new rest res= *)
  (*   match rest with *)
  (*     | [] -> res *)
  (*     | cs1::ss -> *)
  (*         let r = List.fold_left ( fun ls cs2 -> *)
  (*             let  on_cs2 = check_apply_fnc prog cs1 cs2 in *)
  (*             match on_cs2 with *)
  (*               | None -> ls@[cs2] *)
  (*               | Some n_cs2 -> *)
  (*                     ls@[n_cs2] *)
  (*         ) res constrs in *)
  (*          helper_old_new ss r *)
  (* in *)
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
  let _ = Debug.ninfo_zprint (lazy (("    cs2: " ^ (Cprinter.string_of_hprel cs2)))) no_pos in
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
                    let _ = Debug.ninfo_zprint (lazy (("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
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
                      (* let nf1 = (\* CF.subst ss *\) f1 in *)
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
  (* let pr3a oform= match oform with *)
  (*   | None -> "None" *)
  (*   | Some f -> Cprinter.prtt_string_of_h_formula f *)
  (* in *)
  let pr4 (a,_) = (pr_hepta !CP.print_sv pr1 pr1 pr2 pr3 pr3 pr3) a in
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
let unify_branches_hpdef_x prog unk_hps link_hps post_hps hp_defs =
  let unk_hps = unk_hps@link_hps in
  let rec check_eq_one hp args fs f done_fs=
    match fs with
      | [] -> done_fs,[f],[]
      | f1::tl ->
          (* let b,m = CEQ.checkeq_formulas args f f1 in *)
          let ores = SAU.norm_formula prog args unk_hps [] f f1 [] in
          match ores with
            | Some (new_f, n_equivs) ->
                  (tl@done_fs,[new_f],n_equivs)
            | None ->
                  check_eq_one hp args tl f (done_fs@[f1])
          (* if b then *)
          (*   let ss0 = swap_map unk_hps (List.fold_left (@) [] m) [] in *)
          (*   let ss = List.map (fun (sv1,sv2) -> if CP.eq_spec_var sv1 hp then (sv2,sv1) else (sv1,sv2)) ss0 in *)
          (*   let parts = SAU.partition_subst_hprel ss [] in *)
          (*   let pr = pr_list (pr_pair !CP.print_svl !CP.print_sv) in *)
          (*   let _ = DD.info_zprint (lazy (("  parts: " ^ (pr parts)))) no_pos in *)
          (*   let new_f = List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f parts in *)
          (*   (\* let new_f1 = List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f1 parts in *\) *)
          (*   (tl@done_fs,[new_f(\* ;new_f1 *\)], ss) *)
          (* else *)
          (*   check_eq_one hp args tl f (done_fs@[f1]) *)
  in
  let rec check_eq hp args fs res_fs res_ss=
    match fs with
      | [] -> res_fs,res_ss
      | f::tl ->
          let rem,done_fs,ss = check_eq_one hp args tl f [] in
          check_eq hp args rem (res_fs@done_fs) (res_ss@ss)
  in
  let process_one_hpdef (a,hrel,og, f)=
    try
      let hp,args = CF.extract_HRel hrel in
      if CP.mem_svl hp unk_hps then
        (a,hrel,og,f),[]
      else
        let fs = CF.list_of_disjs f in
        let fs1,ss = check_eq hp (args) fs [] [] in
        let ss1 = List.map (fun (sv1, sv2) -> if CP.mem_svl sv2 post_hps then (sv2,sv1) else (sv1,sv2)) ss in
        let fs2 =
          let parts = SAU.partition_subst_hprel ss1 [] in
          List.map (fun f ->
          List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f parts
          ) fs1
        in
        let p = CF.pos_of_formula f in
        let new_f = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 p)
          (List.hd fs2) (List.tl fs2) in
        (a,hrel,og,new_f),ss1
    with _ -> (a,hrel,og,f),[]
  in
  DD.ninfo_pprint ">>>>>> unify: <<<<<<" no_pos;
  let r,ss = List.fold_left (fun (r,r_ss) def ->
      let ndef,ss = process_one_hpdef def in
      (r@[ndef], r_ss@ss)
  ) ([],[]) hp_defs
  in
  (r,ss)

let unify_branches_hpdef prog unk_hps link_hps post_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_3 "unify_branches_hpdef" !CP.print_svl !CP.print_svl pr1 pr2
      (fun _ _ _ -> unify_branches_hpdef_x prog unk_hps link_hps post_hps hp_defs)
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
      (* let _ = DD.ninfo_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos in *)
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

let check_equiv_wo_libs_x iprog prog sel_hps post_hps unk_hps hpdefs hp_defs eqmap1=
  (*partition: matched with lib already*)
  let lib_hps, lib_hpdefs, rem_hpdefs = List.fold_left (fun (r1,r2,r3) hpdef->
      match hpdef.CF.hprel_def_body_lib with
        | None -> begin
            match hpdef.CF.hprel_def_kind with
              | CP.HPRelDefn (hp,_,_) ->
                    if CP.mem_svl hp sel_hps then
                      (r1, r2, r3@[hpdef])
                    else (r1@[hp], r2@[hpdef], r3)
              | _ -> (r1, r2@[hpdef], r3)
          end
        | Some _ ->begin
            match hpdef.CF.hprel_def_kind with
              | CP.HPRelDefn (hp,_,_) ->
                    (r1@[hp], r2@[hpdef], r3)
              | _ -> (r1, r2@[hpdef], r3)
          end
  ) ([],[],[]) hpdefs in
  let lib_hp_defs, post_hp_defs, hp_defs1 = List.fold_left (fun (r1,r2,r3) ((k,_,_,_) as hp_def)->
      match k with
        | CP.HPRelDefn (hp,_,_) -> if CP.mem_svl hp lib_hps then
            (r1@[hp_def], r2,r3)
          else (*move post-preds to the beginning*)
            if CP.mem_svl hp post_hps then
            (r1, r2@[hp_def],r3)
          else (r1, r2,r3@[hp_def])
        | _ -> (r1@[hp_def], r2,r3)
  ) ([],[],[]) hp_defs in
  let hp_defs1a = post_hp_defs@hp_defs1 in
  let hp_defs2, eqmap2=unify_pred prog [] unk_hps hp_defs1a eqmap1 in
  let rem_hpdefs1 = SAU.pred_split_update_hpdefs (List.map fst eqmap2) rem_hpdefs hp_defs2 in
  (rem_hpdefs1@lib_hpdefs, hp_defs2@lib_hp_defs)

let check_equiv_wo_libs iprog prog sel_hps post_hps unk_hps hpdefs hp_defs eqmap1=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def in
  Debug.no_3 "check_equiv_wo_libs" !CP.print_svl pr2 pr1 (pr_pair pr2 pr1)
      (fun _ _ _ -> check_equiv_wo_libs_x iprog prog sel_hps post_hps unk_hps hpdefs hp_defs eqmap1)
      sel_hps hpdefs hp_defs


(*do_conj_unify: pre only*)
let do_unify_x prog do_conj_unify unk_hps link_hps post_hps defs0=
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
  let defs1, equivs1 = if do_conj_unify then List.fold_left unify_heap_conj ([], []) defs0
  else (defs0, [])
  in
  (*unify fields*)
  let defs2,equivs2= unify_branches_hpdef prog unk_hps link_hps post_hps defs1 in
  let equivs2a = List.map (fun (sv1,sv2) -> if CP.mem_svl sv2 post_hps then (sv2,sv1) else (sv1,sv2)) (equivs1@equivs2) in
  let equivs = Gen.BList.remove_dups_eq equiv_cmp equivs2a in
  (*unify syntax*)
  let defs, equivs =  unify_syntax_equiv_hpdef prog unk_hps link_hps defs2 (equivs) in
  let equivs3a = List.map (fun (sv1,sv2) -> if CP.mem_svl sv2 post_hps then (sv2,sv1) else (sv1,sv2)) equivs in
  let parts = SAU.partition_subst_hprel equivs3a [] in
  let defs1 = List.map (subst_equiv parts) defs in
  (defs1, equivs)

let do_unify prog do_conj_unify unk_hps link_hps post_hps hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_svl in
  let pr3 = pr_pair pr1 (pr_list (pr_pair !CP.print_sv !CP.print_sv)) in
  Debug.no_3 "do_unify" pr2 pr2 pr1 pr3
      (fun _ _ _ -> do_unify_x prog do_conj_unify unk_hps link_hps post_hps hp_defs)
      unk_hps link_hps hp_defs

let reverify_cond_x prog (unk_hps: CP.spec_var list) link_hps hpdefs cond_equivs=
  let skip_hps = unk_hps@link_hps in
  let cond_equivs1, unk_equivs, punk_equivs = List.fold_left (fun (ls1,ls2,ls3) (hp1, hp2) -> let b1 = CP.mem_svl hp1 skip_hps in
  let b2 = CP.mem_svl hp2 skip_hps in
  match b1,b2 with
    | true,true -> (ls1,ls2@[(hp1,hp2)],ls3)
    | false, false -> (ls1@[(hp1,hp2)],ls2,ls3)
    | false, true -> (ls1,ls2,ls3@[(hp2,hp1)])
    | true, false -> (ls1,ls2,ls3@[(hp1,hp2)])
  ) ([],[],[]) cond_equivs in
  if cond_equivs1 <> [] then
    let defs1, equivs1 = do_unify prog true unk_hps link_hps [] hpdefs in
    let diff = Gen.BList.difference_eq equiv_cmp cond_equivs1 equivs1 in
    if diff == [] then
      (true, defs1, equivs1, unk_equivs, punk_equivs)
    else
      let defs2, equivs2 = unify_shape_equiv prog unk_hps link_hps defs1 equivs1 in
      let diff2 = Gen.BList.difference_eq equiv_cmp cond_equivs equivs2 in
      if diff2 == [] then
        (true, defs2, equivs2, unk_equivs, punk_equivs)
      else (false, hpdefs, cond_equivs, unk_equivs, punk_equivs)
  else
    (true, hpdefs, [], unk_equivs, punk_equivs)

let reverify_cond prog (unk_hps: CP.spec_var list) link_hps hpdefs cond_equivs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_penta string_of_bool pr2 pr3 pr3 pr3 in
  Debug.no_4 "reverify_cond" pr1 pr1 pr2 pr3 pr4
      (fun _ _ _ _ -> reverify_cond_x prog unk_hps link_hps hpdefs cond_equivs)
       unk_hps link_hps hpdefs cond_equivs

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
let trans_constr_hp_2_view iprog cprog proc_name hpdefs in_hp_names chprels_decl constrs=
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

(* let trans_constr_hp_2_view iprog cprog proc_name in_hp_names chprels_decl constrs= *)
(*   let pr1= pr_list_ln Cprinter.string_of_hprel_short in *)
(*   let pr2 = pr_list pr_id in *)
(*   Debug.no_2 "trans_constr_hp_2_view" pr2 pr1 pr1 *)
(*       (fun _ _ -> trans_constr_hp_2_view iprog cprog proc_name *)
(*           in_hp_names chprels_decl constrs) *)
(*       in_hp_names constrs *)

(*
(* List of vars needed for abduction process *)
*)
let do_entail_check_x vars cprog cs=
  let _ = Infer.rel_ass_stk # reset in
  let get_view_def vname=
    let _ = DD.ninfo_hprint (add_str "vname" pr_id) vname no_pos in
    let vdef = (Cast.look_up_view_def_raw 40 cprog.Cast.prog_view_decls vname) in
    (vname, vdef.Cast.view_un_struc_formula,vdef.Cast.view_vars)
  in
  let has_unknown vdef =
    let hrels = List.fold_left (fun r (f,_) ->
    r@((CF.get_hp_rel_name_formula f))) [] vdef in
     hrels <> []
  in
  let ante = cs.CF.hprel_lhs in
  let unfolded_rhs =
    let vnodes = CF.get_vnodes cs.CF.hprel_rhs in
    if vnodes = [] then cs.CF.hprel_rhs else
      let pr_views = List.map (fun vn ->
          match vn with
            | CF.ViewNode vn -> get_view_def vn.CF.h_formula_view_name
            | _ -> report_error no_pos "SAC.do_entail_check: impposible"
      ) vnodes in
      let need_unfold = List.fold_left (fun r (vname,vdef,_) ->
          if has_unknown vdef then
            r@[vname]
          else r
      ) [] pr_views in
      if need_unfold = [] then cs.CF.hprel_rhs else
        CF.do_unfold_view cprog pr_views cs.CF.hprel_rhs
  in
  let conseq = CF.struc_formula_of_formula unfolded_rhs (CF.pos_of_formula cs.CF.hprel_rhs) in
  let (valid, rs,v_hp_rel) = SC.sleek_entail_check vars cprog [] ante conseq in
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
let gfp_gen_init prog is_pre r base_fs rec_fs=
  let find_greates_neg (r_fs, r_unk_hpargs)f=
    let svl = CF.get_ptrs_f f in
    let pos = (CF.pos_of_formula f) in
    if CP.mem_svl r svl then
      (*neg for sl is not well defined. use unkhp*)
      let (hf, n_hp) = SAU.add_raw_hp_rel prog is_pre [(r, I)] pos in
      let f = CF.formula_of_heap_w_normal_flow hf pos in
      (r_fs@[f], r_unk_hpargs@[(n_hp, [r])])
    else
      let p = CP.filter_var (CF.get_pure f) [r] in
      let f = CF.formula_of_pure_N (CP.mkNot_s p) pos in
      (r_fs@[f], r_unk_hpargs)
  in
  let n_fs, n_unk_hpargs = List.fold_left find_greates_neg ([],[]) rec_fs in
  (CF.formula_of_disjuncts (base_fs@rec_fs@n_fs), n_unk_hpargs)

(* let gfp_gen_init prog is_pre r base_fs rec_fs= *)
(*   let pr1 = Cprinter.prtt_string_of_formula in *)
(*   let pr2 = pr_list_ln pr1 in *)
(*   Debug.no_2 "gfp_gen_init" !CP.print_sv pr2 (pr_pair pr1 !CP.print_svl) *)
(*       (fun _ _ -> gfp_gen_init prog is_pre r base_fs rec_fs) *)
(*       r rec_fs *)

let gfp_iter_x prog base_fs rec_fs fixn=
  fixn

let gfp_iter prog base_fs rec_fs fixn=
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_1 "gfp_iter" pr1 pr1
      (fun _ -> gfp_iter_x prog base_fs rec_fs fixn)
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
  let hp,def,n_unk_hpargs=
  match pdefs with
    | (hp0,args0,f0)::rest ->
          (*normalize*)
          let norm_pdefs = (hp0,args0,f0)::(List.map (norm args0) rest) in
          let norm_fs = (List.map (fun (_,_,f) -> f) norm_pdefs) in
          let r,non_r_args = SAU.find_root prog skip_hps args0 norm_fs in
          let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
          (*now assume base_fs =[] and dep_fs = [] and rec_fs != [] *)
          if (* base_fs =[] && *) dep_fs = [] then
            (*init*)
            let fix0, n_unk_hpargs = gfp_gen_init prog is_pre r base_fs rec_fs in
            (*iterate*)
            let fixn = gfp_iter prog base_fs rec_fs fix0 in
            (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None fixn (CF.pos_of_formula f0), n_unk_hpargs)
          else
            report_error no_pos "sac.compute gfp: not support yet"
    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let _ = Debug.binfo_pprint ("    synthesize (gfp): " ^ (!CP.print_sv hp) ) no_pos in
  let _ = Debug.binfo_pprint ((Cprinter.string_of_hp_rel_def_short def)) no_pos in
  (def,n_unk_hpargs)

let compute_gfp prog is_pre is pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = pr_pair Cprinter.string_of_hp_rel_def (pr_list (pr_pair !CP.print_sv pr1)) in
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
    r_fs@(List.filter (fun (_,_,_,f,_) -> not (SAU.is_unsat f)) fs)
  in
  let pdef_rec_fs = List.map (fun f -> (hp,args, None, f, [])) rec_fs in
  let pdef_nonrec_fs = List.map (fun f -> (hp,args, None, f, [])) nonrec_fs in
  (*INTERNAL*)
  let rec rec_helper i pdef_fix_i=
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
    let n_pdefs = (List.fold_left (apply_fix pdef_fix_i) [] pdef_rec_fs) in
    let n_pdefs1 = Gen.BList.remove_dups_eq (fun (_, args1, _, f1, _) (_, args2, _, f2,_) ->
        let ss = List.combine args1 args2 in
        SAU.check_relaxeq_formula args2 (CF.subst ss f1) f2
    ) n_pdefs in
    let fix_i_plus = pdef_nonrec_fs@n_pdefs1 in
    (*check whether it reaches the fixpoint*)
    (* let fix_i_plus1 = Gen.BList.remove_dups_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) -> *)
    (*     SAU.check_relaxeq_formula args f1 f2) fix_i_plus in *)
    let fix_i_plus1 = simplify_disj_set prog args dang_hps [] fix_i_plus no_pos in
    let diff = Gen.BList.difference_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) ->
        SAU.check_relaxeq_formula args f1 f2) fix_i_plus1 pdef_fix_i in
    (* let rec_helper pdef_fix_i= *)
    (*   let pr1 (_,_, _, f, _) = Cprinter.prtt_string_of_formula f in *)
    (*   let pr2 = pr_list_ln pr1 in *)
    (*   Debug.no_1 "rec_helper" pr2 pr2 *)
    (*       (fun _ -> rec_helper_x pdef_fix_i) pdef_fix_i *)
    (* in *)
    (*recusive call*)
    if diff = [] then fix_i_plus1 else
    rec_helper (i+1) fix_i_plus1
  in
  (*END INTERNAL*)
  let pdef_fix_0 = List.map (fun f -> (hp,args, None, f, [])) fix_0 in
  let r = rec_helper step pdef_fix_0 in
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

let compute_lfp_x prog dang_hps pdefs=
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
  let skip_hps = dang_hps in
  (********END INTERNAL*******)
  let hp,def=
  match pdefs with
    | [(hp0,args0,f0)] ->
          let r,non_r_args = SAU.find_root prog skip_hps args0 [f0] in
          (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None f0 (CF.pos_of_formula f0))
    | (hp0,args0,f0)::rest ->
          let pos = CF.pos_of_formula f0 in
          (*normalize*)
          let norm_pdefs = (hp0,args0,f0)::(List.map (norm args0) rest) in
          let norm_fs0 = (List.map (fun (_,_,f) -> f) norm_pdefs) in
          let r,non_r_args = SAU.find_root prog skip_hps args0 norm_fs0 in
          let norm_fs = List.map (mk_exp_root hp0 r) norm_fs0 in
          (* let _ =  DD.info_pprint ("   r: " ^(!CP.print_sv r)) no_pos in *)
          (**********PRINTING***********)
          let _ = DD.binfo_pprint ("   Initial recurrence: "  ^ (
              let pr1  = Cprinter.prtt_string_of_formula in
              let f = (CF.formula_of_disjuncts norm_fs) in
              pr1 f )
          ) no_pos
          in
          (*******END PRINTING*********)
          let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
          (*init*)
          let fix_0 = (* (base_fs@dep_fs) *) [] in
          (*iterate*)
          let fixn = lfp_iter prog 0 hp0 args0 skip_hps fix_0 (base_fs@dep_fs) rec_fs in
          let def = CF.formula_of_disjuncts fixn in
          (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None def pos)
    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let _ = Debug.binfo_pprint ("    synthesize (lfp): " ^ (!CP.print_sv hp) ) no_pos in
  let _ = Debug.binfo_pprint ((Cprinter.string_of_hp_rel_def_short def)) no_pos in
  def

let compute_lfp prog dang_hps pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "compute_lfp" pr3 pr4
      (fun _ -> compute_lfp_x prog dang_hps pdefs) pdefs


(*for each hp_def in hp_defs check whether it needs a lfp,
 if yes, perform, subst the result in hpdefs*)
let compute_lfp_def_x prog post_hps dang_hps hp_defs hpdefs=
  (********INTERNAL***********)
  let is_post_fix hp args f=
    let lhds, lhvs, hrels = CF.get_hp_rel_formula f in
    if lhds != [] || lhvs != [] then false else
      List.exists (fun (hp1, eargs,_) ->
          if CP.eq_spec_var hp hp1 then
            let args1 = List.fold_left List.append [] (List.map CP.afv eargs) in
            not (SAU.eq_spec_var_order_list args args1)
          else false
      ) hrels
  in
  let process_one_grp grp=
    match grp with
      | (hp_kind, hf, g, def)::_ -> begin
          match hp_kind with
            | CP.HPRelDefn (hp, r, paras) ->
                  if CP.mem_svl hp post_hps then
                    let pdefs = List.map (fun (_,hf,_, f) ->
                        let _,args = CF.extract_HRel hf in
                        (hp, args, f)
                    ) grp in
                    if List.length pdefs > 1 then
                      if List.exists (fun (hp, args, f) -> is_post_fix hp args f) pdefs then
                        (true, [(compute_lfp prog dang_hps pdefs)])
                      else (false, grp)
                    else (false, grp)
                  else (false, grp)
            | _ -> (false, grp)
        end
      | [] -> report_error no_pos "sac.compute_lfp_def.process_one_grp"
  in
  let rec update r_hpdefs hp new_fs done_hpdefs=
    match r_hpdefs with
      | [] -> (* report_error no_pos "sac.compute_lfp_def.update: why can not find?" *) done_hpdefs
      | hpdef::rest ->
            try
              let hp1 = CF.get_hpdef_name hpdef.CF.hprel_def_kind in
              if CP.eq_spec_var hp hp1 then
                let n_hpdef = {hpdef with CF.hprel_def_body = List.map (fun f -> ([], Some f)) new_fs;
                    CF.hprel_def_body_lib = None;
                }
                in
                done_hpdefs@[n_hpdef]@rest
              else
                update rest hp new_fs (done_hpdefs@[hpdef])
            with _ -> update rest hp new_fs (done_hpdefs@[hpdef])
  in
  let rec partition_helper rem_hp_defs grps non_post_defs =
    match rem_hp_defs with
      | [] -> grps, non_post_defs
      | (hp_kind, hf, g, def):: rest ->
            begin
              match hp_kind with
                | CP.HPRelDefn (hp, r, paras) ->
                      let grp, rest1, n_non_post_defs = List.fold_left (fun (ls1,ls2, ls3) (hp_kind1, hf1, g1, def1) ->
                          match hp_kind1 with
                            | CP.HPRelDefn (hp1, _, _) ->
                                  if CP.eq_spec_var hp hp1 then
                                    (ls1@[(hp_kind1, hf1, g1, def1)],ls2, ls3)
                                  else (ls1,ls2@[(hp_kind1, hf1, g1, def1)], ls3)
                            | _ -> (ls1,ls2, ls3@[(hp_kind1, hf1, g1, def1)])
                      ) ([], [], []) rest in
                      partition_helper rest1 (grps@[((hp_kind, hf, g, def)::grp)]) (non_post_defs@n_non_post_defs)
                | _ -> partition_helper rest grps (non_post_defs@[(hp_kind, hf, g, def)])
            end
  in
  let unify_disjuncts (r_grp, r_hpdefs) grp=
    match grp with
      | [] -> (r_grp,r_hpdefs)
      | [x] ->  (r_grp@[grp],r_hpdefs)
      | (hp_kind, hf, g, def)::_ -> begin
          match hp_kind with
            | CP.HPRelDefn (hp, r, paras) ->
                  let grp1 = Gen.BList.remove_dups_eq (fun (hp_kind1, hf1, g1, def1) (hp_kind2, hf2, g2, def2) ->
                      let _, args1 = CF.extract_HRel hf1 in
                      let _, args2 = CF.extract_HRel hf2 in
                      let ss = List.combine args1 args2 in
                       SAU.check_relaxeq_formula args2 (CF.subst ss def1) def2
                  ) grp in
                  if List.length grp1 < List.length grp then
                    let n_hpdefs = update r_hpdefs hp (List.fold_left (fun ls (hp_kind, hf, g, def) ->
                    ls@(CF.list_of_disjs def)) [] grp1) [] in
                    (r_grp@[grp1], n_hpdefs)
                  else
                    (r_grp@[grp],r_hpdefs)
            | _ -> (r_grp@[grp],r_hpdefs)
        end
  in
  (********END INTERNAL*******)
  (*group hp_defs*)
  let grp_hp_defs0, non_post_fix_defs = partition_helper hp_defs [] [] in
  let grp_hp_defs,hpdefs1 = List.fold_left (unify_disjuncts) ([],hpdefs) grp_hp_defs0 in
  (* let pr1 = pr_list_ln (pr_list_ln Cprinter.string_of_hp_rel_def) in *)
  (* let _ =  DD.info_pprint ("   grp_hp_defs0: " ^(pr1 grp_hp_defs0)) no_pos in *)
  (* let _ =  DD.info_pprint ("   grp_hp_defs: " ^(pr1 grp_hp_defs)) no_pos in *)
  let n_hp_defs, n_hpdefs = List.fold_left (fun (r_hp_defs, r_hpdefs) hp_defs ->
      let r, grp = process_one_grp hp_defs in
      if r then
        (*if success, fold in one*)
        let (hp_kind, hf, g, def) = List.hd grp in
        let n_hpdefs = update r_hpdefs (CF.get_hpdef_name hp_kind) (CF.list_of_disjs def) [] in
        (r_hp_defs@[(hp_kind, hf, g, def)], n_hpdefs)
      else (r_hp_defs@hp_defs, r_hpdefs)
  ) ([], hpdefs1) grp_hp_defs in
  (n_hp_defs@non_post_fix_defs), n_hpdefs

let compute_lfp_def prog post_hps dang_hps hp_defs hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def_short in
  Debug.no_3 "compute_lfp_def" !CP.print_svl pr1 pr2 (pr_pair pr1 pr2)
      (fun _ _ _ -> compute_lfp_def_x prog post_hps dang_hps hp_defs hpdefs)
      post_hps hp_defs hpdefs
(*=============**************************================*)
       (*=============END FIXPOINT================*)
(*=============**************************================*)


(*=============**************************================*)
       (*=============PRED SPLIT================*)
(*=============**************************================*)
let pred_split_cands_one_branch prog unk_hps hprel f=
  let do_partition hns hvs eqs args=
    let rec intersect_with_pre_parts parts svl r_parts r_svl=
      match parts with
        | [] -> (r_parts,r_svl)
        | svl1::tl->
              if CP.intersect_svl (r_svl@svl) svl1 = [] then
                intersect_with_pre_parts tl svl (r_parts@[svl1]) r_svl
              else intersect_with_pre_parts tl svl r_parts (CP.remove_dups_svl (r_svl@svl1))
    in
    let rec part_helper args0 parts=
      match args0 with
        | [] -> parts
        | [a] -> (parts@[[a]])
        | a::tl ->
              let part1 = CF.find_close [a] eqs in
              let part2 = SAU.look_up_closed_ptr_args prog hns hvs (CP.remove_dups_svl part1) in
              let part2a = (CF.find_close part2 eqs) in
              let new_parts,part2b = intersect_with_pre_parts parts part2a [] [] in
              let part3 = CP.remove_dups_svl (a::(CP.intersect_svl part2a tl)) in
              part_helper (CP.diff_svl tl part3) (new_parts@[part2b@part3])
    in
    let parts = part_helper args [] in
    (*if all args is partitioned in one group, do not split*)
    match parts with
      | [args0] -> if List.length args0 = List.length args then []
          else parts
      | _ -> parts
  in
  let hns, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mf,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let cands = hprel::hrs in
  let cands0, unk_args = List.fold_left (fun (r1,r2) (hp,el,l)->
      if not (CP.mem_svl hp unk_hps) then
        (r1@[(hp,el,l)],r2)
      else
        (r1,r2@(List.concat (List.map CP.afv el)))
  ) ([],[]) cands in
  let cands1 = List.filter (fun (hp,el,l) -> (List.length el) >= 2) cands0 in
  let cands2 = List.map (fun (hp,el,l) ->
      let args = List.concat (List.map CP.afv el) in
      let parts = do_partition hns hvs eqs args in
     (hp,args, List.filter (fun svl -> CP.diff_svl svl unk_args <> []) parts,l)
  ) cands1
  in
  (cands2)

let pred_split_cands_x prog unk_hps hp_defs=
  (*******INTERNAL*******)
  let rec process_one_pred hrel hp args cands fs=
    match fs with
      | [] -> true, cands
      | f::rest ->
            let n_cands = pred_split_cands_one_branch prog unk_hps hrel f in
            let is_split = List.fold_left (fun b (hp1, args1, parts, _) ->
                if CP.eq_spec_var hp hp1 && SAU.eq_spec_var_order_list args args1 then
                  (b && parts <> [])
                else b
            ) true n_cands in
            if not is_split then (false, [])
            else
              process_one_pred hrel hp args (cands@n_cands) rest
  in
  (*******END INTERNAL*******)
  let cands, non_split_hps = List.fold_left (fun (r, non_split_hps) (k, hf, _, f) ->
      let hrel, hp, args = match hf with
        | CF.HRel ((hp, eargs, _ ) as hrel) ->
              hrel, hp , List.concat (List.map CP.afv eargs)
        | _ -> report_error no_pos "SAC.pred_split_cands"
      in
      let to_split, n_cands =  process_one_pred hrel hp args [] (CF.list_of_disjs f) in
      if to_split then
        (r@n_cands, non_split_hps)
      else
        (r, non_split_hps@[hp])
  ) ([],[]) hp_defs
  in
  let cands1 = List.filter (fun (hp, _,_,_) -> not (CP.mem_svl hp non_split_hps)) cands in
  let cands2 = Gen.BList.remove_dups_eq (fun (hp1, args1,_,_) (hp2, args2, _,_) ->
      CP.eq_spec_var hp2 hp1 && SAU.eq_spec_var_order_list args2 args1
  ) cands1 in
  cands2

let pred_split_cands prog unk_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_quad !CP.print_sv !CP.print_svl (pr_list !CP.print_svl) string_of_full_loc) in
  Debug.no_1 "pred_split_cands" pr1 pr2
  (fun _ -> pred_split_cands_x prog unk_hps hp_defs) hp_defs

(*split one hp -> mutiple hp and produce corresponding heap formulas for substitution
 - one cand: (hp,args, parts,p)
*)
let check_split_global_x prog cands =
   let rec partition_cands_by_hp_name cands0 parts=
    match cands0 with
      | [] -> parts
      | (hp_name,args, ls_args,p)::xs ->
          let part,remains= List.partition (fun (hp_name1,_,_,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
          partition_cands_by_hp_name remains (parts@[[(hp_name,args,ls_args,p)]@part])
  in
  (*each partition, create new hp and its corresponding HRel formula*)
  let helper1 pos args =
    let args1 = List.map (fun sv -> (sv,I)) args in
    let hf,new_hp_sv = SAU.add_raw_hp_rel prog true args1 pos in
    ((new_hp_sv,args), hf)
  in
  (*for each grp*)
  let intersect_cand_one_hp grp=
    let rec parts_norm args0 grp0 res=
      match grp0 with
        | [] -> res
        | (_,args1,parts1,_)::tl ->
            let ss = List.combine args1 args0 in
            let parts11 = List.map (fun largs -> List.map (CP.subs_one ss) largs) parts1 in
            parts_norm args0 tl (res@[parts11])
    in
    let rec cmp_two_list_args ls_args1 ls_args2=
      match ls_args1,ls_args2 with
        | [],[] -> true
        | args1::tl1,args2::tl2 ->
            if SAU.eq_spec_var_order_list args1 args2 then
              cmp_two_list_args tl1 tl2
            else false
        | _ -> false
    in
    let (hp,args0,parts0,p0)=
      match grp with
        | [] -> report_error no_pos "sa.intersect_cand_one_hp"
        | hd::_ -> hd
    in
    let size = List.length parts0 in
    if size = 0 || List.exists (fun (_,args1,parts1,_) -> (List.length parts1)!=size) (List.tl grp) then
      []
    else
      let tl_parts = parts_norm args0 (List.tl grp) [] in
      if List.for_all (fun part -> cmp_two_list_args parts0 part) tl_parts then
        [(hp,args0,parts0,p0)]
      else []
  in
  let generate_split (hp,args0,parts0,p0) =
    let hps = List.map (helper1 p0) parts0 in
    let new_hp_args,new_hrel_fs = List.split hps in
    let new_hrels_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 p0)
      (List.hd new_hrel_fs) (List.tl new_hrel_fs) in
    let hrel0 = SAU.mkHRel hp args0 p0 in
    (hp, args0, new_hp_args, hrel0,new_hrels_comb)
  in
  let grps = partition_cands_by_hp_name cands [] in
  (*each group, the partition should be similar*)
  let to_split = List.concat (List.map intersect_cand_one_hp grps) in
  let res = List.map generate_split to_split in
  res

let check_split_global prog cands =
  let pr1 = pr_list_ln (pr_quad !CP.print_sv !CP.print_svl (pr_list !CP.print_svl) string_of_full_loc) in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_list (pr_penta !CP.print_sv !CP.print_svl pr4 pr2 pr2) in
  Debug.no_1 "check_split_global" pr1 pr3
       (fun _ -> check_split_global_x prog cands) cands

let prove_split_cand_x iprog cprog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs (hp, args, comps, lhs_hf, rhs_hf)=
  let back_up_state ()=
    let cur_ass = ass_stk# get_stk in
    let _ = ass_stk # reset in
    let cur_hpdefs =  hpdef_stk # get_stk in
    let _ = hpdef_stk # reset in
    (cur_ass, cur_hpdefs)
  in
  let restore_state (cur_ass, cur_hpdefs)=
    let _ = ass_stk # reset in
    let _ = ass_stk # push_list cur_ass in
    let _ = hpdef_stk # reset in
    let _ = hpdef_stk # push_list cur_hpdefs in
    ()
  in
  let rec look_up rest_defs rem=
    match rest_defs with
      | [] -> report_error no_pos "SAC.prove_split_cand"
      | ((_, hrel,_,_) as def)::rest->
            let hp1,_ = CF.extract_HRel hrel in
            if CP.eq_spec_var hp1 hp then
              def, rem@rest
            else
              look_up rest (rem@[def])
  in
  let rec comps_split comps f res=
    match comps with
      | [] -> res
      | (hp,args)::rest ->
            let f_comp = CF.drop_data_view_hrel_nodes f SAU.check_nbelongsto_dnode
              SAU.check_nbelongsto_vnode SAU.check_neq_hrelnode
              args args [hp] in
            let _ = Debug.ninfo_hprint (add_str  "f_comp " Cprinter.prtt_string_of_formula) f_comp no_pos in
            comps_split rest f (res@[f_comp])
  in
  let rec insert_para comps fs res=
    match comps,fs with
      | [],[] -> res
      | fs::rest_comps, f::rest -> insert_para rest_comps rest (res@[(fs@[f])])
      | _ -> report_error no_pos "sac.prove_split_cand: should be the same length 1"
  in
  let rec combine_comp comps1 ls_defs1 pos res=
    match comps1,ls_defs1 with
      | [],[] -> res
      | (hp, args)::rest1, fs::rest2 ->
            let _ = Debug.ninfo_hprint (add_str  "fs " (pr_list_ln Cprinter.prtt_string_of_formula)) fs no_pos in
            let fs1 = List.filter (fun f -> not (SAU.is_trivial f (hp,args))) fs in
            let r,paras = SAU.find_root cprog unk_hps args fs1 in
            let n_hp_defs = SAU.mk_hprel_def cprog false [] unk_hps [] hp (args, r, paras) fs1 [] pos in
            combine_comp rest1 rest2 pos (res@(List.map snd n_hp_defs))
      | _ -> report_error no_pos "sac.prove_split_cand: should be the same length 2"
  in
  (*res: list of disj of resulting split*)
  let subst_and_split res f=
    (*subst*)
    let f1 = CF.subst_hrel_f f ss_preds in
    let fs = comps_split comps f1 [] in
    let n_res = if res = [] then List.map (fun f -> [f]) fs else insert_para res fs [] in
    n_res
  in
  (*shared*)
  (*END share*)
  let prove_sem ((k, rel, og, f) as cur_hpdef) =
    let r,paras = match k with
      | CP.HPRelDefn (hp,r, paras) -> (r,paras)
      | _ -> report_error no_pos "SAC.prove_sem: support single hpdef only"
    in
    let proc_name = "split_pred" in
    (*transform to view*)
    let n_cviews,chprels_decl = SAO.trans_hprel_2_cview iprog cprog proc_name [cur_hpdef] in
    (*trans_hp_view_formula*)
    (* let f12 = SAO.trans_formula_hp_2_view iprog cprog proc_name chprels_decl [cur_hpdef] f in *)
    (*lemma need self for root*)
    let self_sv = CP.SpecVar (CP.type_of_spec_var r,self, Unprimed) in
    let vnode = CF.mkViewNode self_sv (CP.name_of_spec_var hp) paras no_pos in
    let f12 = CF.formula_of_heap vnode no_pos in
    let f22_0 = SAO.trans_formula_hp_2_view iprog cprog proc_name chprels_decl [cur_hpdef] (CF.formula_of_heap rhs_hf no_pos) in
    let sst = [(r, self_sv)] in
    (* let f12 = CF.subst sst f12_0 in *)
    let f22 = CF.subst sst f22_0 in
    let _ = Debug.ninfo_hprint (add_str  "f12 " Cprinter.prtt_string_of_formula) f12 no_pos in
    let _ = Debug.ninfo_hprint (add_str  "f22 " Cprinter.prtt_string_of_formula) f22 no_pos in
    (*iformula to construct lemma*)
    let if12 = AS.rev_trans_formula f12 in
    let if22 = AS.rev_trans_formula f22 in
    let _ = Debug.ninfo_hprint (add_str  "if12 " Iprinter.string_of_formula) if12 no_pos in
    let _ = Debug.ninfo_hprint (add_str  "if22 " Iprinter.string_of_formula) if22 no_pos in
    (*prove*)
    (* let valid,lc,_ = proving_fnc (List.map fst comps) f12 (CF.struc_formula_of_formula f22 no_pos) in *)
    (*construct lemma_infer*)
    let ilemma_inf = IA.mk_lemma (fresh_any_name "tmp_infer") IA.Left
      (List.map (fun (hp, _) -> CP.name_of_spec_var hp) comps) (IF.add_quantifiers [] if12) (IF.add_quantifiers [] if22) in
    let _ = Debug.info_hprint (add_str "\nilemma_infs:\n " (Iprinter.string_of_coerc_decl)) ilemma_inf no_pos in
    let lc_opt = LEM.sa_infer_lemmas iprog cprog [ilemma_inf] in
    match lc_opt with
      | Some lcs ->
            let comp_hp_defs =
              let hprels = List.fold_left (fun r_ass lc -> r_ass@(Inf.collect_hp_rel_list_context lc)) [] lcs in
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
              let (cur_ass, cur_defs) = back_up_state () in
              let _, hp_defs = !infer_shapes iprog cprog "temp" hp_lst_assume (List.map fst comps) (List.map fst comps)
                [] [] [] true true in
              let _ = restore_state (cur_ass, cur_defs) in
              let n_hp_def = (k, rel, og, CF.formula_of_heap rhs_hf no_pos) in
              let _ = DD.info_pprint (" pred_split (sem):" ^ (!CP.print_sv hp) ^ "(" ^ (!CP.print_svl args) ^ ") :== " ^
                  (Cprinter.prtt_string_of_h_formula rhs_hf)) no_pos in
              n_hp_def::hp_defs
            in
            (*todo: remove map also*)
            comp_hp_defs
      | None -> [cur_hpdef]
  in
  let prove_syn (k, rel, og, f) =
    let fs = CF.list_of_disjs f in
    let split = List.fold_left subst_and_split [] fs in
    let split_hp_defs = combine_comp comps split no_pos [] in
    let n_hp_def = (k, rel, og, CF.formula_of_heap rhs_hf no_pos) in
    let _ = DD.info_pprint (" pred_split (syn):" ^ (!CP.print_sv hp) ^ "(" ^ (!CP.print_svl args) ^ ") :== " ^
        (Cprinter.prtt_string_of_h_formula rhs_hf)) no_pos in
    (n_hp_def::split_hp_defs)
  in
  let (k, rel, og, f), rem_hp_defs = look_up hp_defs [] in
  (*try: do the split to obtain new defs sematically*)
  let split_hp_defs = if !Globals.syntatic_mode then
    (*syntactically*)
    prove_syn (k, rel, og, f)
  else prove_sem (k, rel, og, f)
  in
  split_hp_defs@rem_hp_defs

let prove_split_cand iprog cprog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs (hp, args, comps, lhs_hf, rhs_hf)=
  let pr1 = pr_list_num Cprinter.string_of_hp_rel_def in
  Debug.no_1 "prove_split_cand" pr1 pr1
      (fun _ -> prove_split_cand_x iprog cprog proving_fnc ass_stk hpdef_stk
          unk_hps ss_preds hp_defs (hp, args, comps, lhs_hf, rhs_hf))
      hp_defs

let find_closure_tuplep_hps tupled_hps hp_defs=
  let get_tupled_dep_hps tuple_deps (_, hrel,_, f)=
    let hps = CF.get_hp_rel_name_formula f in
    let hp0, _ = CF.extract_HRel hrel in
    let tupled_dep_hps = CP.intersect_svl hps tupled_hps in
    let deps = List.map  (fun hp1 -> (hp0, hp1)) tupled_dep_hps in
    tuple_deps@deps
  in
  if tupled_hps = [] then [] else
    let tpl_aset = CP.EMapSV.mkEmpty in
    let fst_sv = List.hd tupled_hps in
    let tpl_aset1 = List.fold_left (fun tpl sv1 -> CP.add_equiv_eq tpl fst_sv sv1) tpl_aset (List.tl tupled_hps) in
    let tuple_deps = List.fold_left (get_tupled_dep_hps) [] hp_defs in
    let tpl_aset2 = List.fold_left (fun tpl (sv1,sv2) -> CP.add_equiv_eq tpl sv1 sv2) tpl_aset1 tuple_deps in
    CP.EMapSV.find_equiv_all fst_sv tpl_aset2

(*return new hpdefs and hp split map *)
let pred_split_hp_x iprog prog ass_stk hpdef_stk unk_hps (hp_defs: CF.hp_rel_def list)  =
  let sing_hp_defs, tupled_hp_defs, tupled_hps = List.fold_left (fun (s_hpdefs, t_hpdefs, t_hps) ((def,_,_,_) as hp_def)->
      match def with
        | CP.HPRelDefn _ -> (s_hpdefs@[hp_def], t_hpdefs, t_hps)
        | CP.HPRelLDefn hps -> (s_hpdefs, t_hpdefs@[hp_def], t_hps@hps)
        | _ -> (s_hpdefs, t_hpdefs@[hp_def], t_hps)
  ) ([],[],[]) hp_defs
  in
  let closure_tupled_hps = find_closure_tuplep_hps tupled_hps sing_hp_defs in
  let sing_hp_defs1a, tupled_hp_defs1  = if List.length closure_tupled_hps > List.length tupled_hps then
    let sing_hp_defs2, tupled_hp_defs2 = List.partition (fun (def,_,_,_) ->
        match def with
            | CP.HPRelDefn (hp,_,_) -> not (CP.mem_svl hp closure_tupled_hps)
            | _ -> false
    ) sing_hp_defs in
    (sing_hp_defs2, tupled_hp_defs2@tupled_hp_defs)
  else
    sing_hp_defs,tupled_hp_defs
  in
  let sing_hp_defs1, sing_hp_def1b = List.partition (fun (_,_,_,f) -> let fs = CF.list_of_disjs f in
        if List.length fs < 2 then false else true) sing_hp_defs1a in
  (*compute candidates*)
  let split_cands = pred_split_cands prog unk_hps sing_hp_defs1 in
  (*split and obtain map*)
  let split_map_hprel_subst = check_split_global prog split_cands in
  let ss_preds = List.map (fun (_,_,_,a,b) -> (a,b)) split_map_hprel_subst in
  (*prove and do split*)
  let proving_fnc svl f1 = wrap_proving_kind PK_Pred_Split (Sleekcore.sleek_entail_check svl prog [] f1) in
  let sing_hp_defs2 = List.fold_left (fun hp_defs0 split ->
      prove_split_cand iprog prog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs0 split
  ) sing_hp_defs1 split_map_hprel_subst
  in
  let tupled_hp_defs2 = List.map (fun (a,b,c, f) -> (a,b,c, CF.subst_hrel_f f ss_preds)) (tupled_hp_defs1@sing_hp_def1b) in
  (sing_hp_defs2@tupled_hp_defs2,List.map (fun (a1,a2,a3,a4,_) -> (a1,a2,a3,a4)) split_map_hprel_subst)

let pred_split_hp iprog prog unk_hps ass_stk hpdef_stk (hp_defs: CF.hp_rel_def list): (CF.hp_rel_def list *
 (CP.spec_var*CP.spec_var list * (CP.spec_var*CP.spec_var list) list *CF.h_formula) list) =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_sv in
  let pr3 = Cprinter.string_of_h_formula in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = fun (a1,a2) -> (*ignore a3*)
      let pr = pr_pair pr1 (pr_list (pr_quad pr2 !CP.print_svl pr5 pr3)) in
      pr (a1, a2)
  in
  Debug.no_1 "pred_split_hp" pr1 pr4
      (fun _ -> pred_split_hp_x iprog prog unk_hps ass_stk hpdef_stk hp_defs) hp_defs

(*=============**************************================*)
       (*=============END PRED SPLIT================*)
(*=============**************************================*)
