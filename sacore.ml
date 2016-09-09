#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only

(* module DD = Debug *)
(* module Err = Error *)
(* module IA = Iast *)
(* module CA = Cast *)
(* module AS = Astsimp *)
module CP = Cpure
module IF = Iformula
module CF = Cformula
module CFU = Cfutil
module MCP = Mcpure
module CEQ = Checkeq
(* module TP = Tpdispatcher *)
(* module SAU = Sautil *)
(* module SAO = Saout *)
(* module Inf = Infer *)
(* module SC = Sleekcore *)
(* module LEM = Lemma *)

(* let infer_shapes = ref (fun (iprog: Iast.prog_decl) (cprog: Cast.prog_decl) (proc_name: ident) *)
(*   (hp_constrs: CF.hprel list) (sel_hp_rels: CP.spec_var list) (sel_post_hp_rels: CP.spec_var list) *)
(*   (hp_rel_unkmap: ((CP.spec_var * int list) * CP.xpure_view) list) *)
(*   (unk_hpargs: (CP.spec_var * CP.spec_var list) list) *)
(*   (link_hpargs: (int list * (Cformula.CP.spec_var * Cformula.CP.spec_var list)) list) *)
(*   (need_preprocess: bool) (detect_dang: bool) -> let a = ([] : CF.hprel list) in *)
(*   let b = ([] : CF.hp_rel_def list) in *)
(*   (a, b) *)
(* ) *)

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
        let new_args = Sautil.retrieve_args_from_locs args locs in
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
            Sautil.eq_spec_var_order_list args1 args2
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
        List.exists (fun hpargs2 -> Sautil.check_hp_arg_eq hpargs1 hpargs2) rhs_hpargs
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
        (* let () = Debug.info_zprint (lazy (("   hp: " ^ (!CP.print_sv hp_name)))) no_pos in *)
        (* let () = Debug.info_zprint (lazy (("     res: " ^ (pr1 res)))) no_pos in *)
        (* let () = Debug.info_zprint (lazy (("     largs: " ^ (!CP.print_svl largs)))) no_pos in *)
      if (List.length res) = (List.length largs) then
        ([(hp_name, largs, res)],[(hp_name, largs,res)])
      else ([(hp_name,unk_args, res)],[])
    end
  in
  let () = Debug.ninfo_zprint (lazy (("   known_svl: " ^ (!CP.print_svl known_svl)))) no_pos in
  get_unk_ptr known_svl (hp_name, args)

let check_equality_constr lhpargs lhs_f_rem rhs svl2=
  let helper args f=
    match args with
    | sv::_ ->
      let ( _,mix_f,_,_,_,_) = CF.split_components f in
      let reqs2 = (MCP.ptr_equations_without_null mix_f) in
      let cl_svl = CP.remove_dups_svl (CF.find_close [sv] (reqs2)) in
      (* let () = Debug.info_hprint (add_str "   cl_svl: " !CP.print_svl) cl_svl no_pos in *)
      if (* List.length cl_svl >1 && *)
        CP.diff_svl cl_svl args = [] then
        args
      else svl2
    | _ -> svl2
  in
  (*handle equality*)
  (* let () = Debug.info_zprint (lazy (("   svl2: " ^ (!CP.print_svl svl2)))) no_pos in *)
  if svl2 <> [] then svl2 else
    match lhpargs with
    | [(_,args)] ->
      (* let () = Debug.info_zprint (lazy (("   lhs_f_rem: " ^ (!CF.print_formula lhs_f_rem)))) no_pos in *)
      (* let () = Debug.info_zprint (lazy (("   rhs: " ^ (!CF.print_formula rhs)))) no_pos in *)
      if Cfutil.is_empty_heap_f lhs_f_rem then
        let svl = helper args lhs_f_rem in
        if svl == [] && Cfutil.is_empty_heap_f rhs then
          helper args rhs
        else svl
      else
        svl2
    | _ -> svl2

(*analysis unknown information*)
let rec analize_unk_one_x prog post_hps unk_hps constr =
  (* let () = Debug.info_zprint (lazy (("   hrel: " ^ (Cprinter.string_of_hprel_short constr)))) no_pos in *)
  (*elim hrel in the formula and returns hprel_args*)
  (*lhs*)
  let lhs1,lhrels = Sautil.drop_get_hrel constr.CF.hprel_lhs in
  (*rhs*)
  let rhs1,rhrels = Sautil.drop_get_hrel constr.CF.hprel_rhs in
  (*find fv of lhs + rhs wo hrels*)
  (* let lsvl = Sautil.get_raw_defined_w_pure prog lhs1 in *)
  (* let rsvl = Sautil.get_raw_defined_w_pure prog rhs1 in *)
  let svl = Sautil.get_raw_defined_w_pure prog constr.CF.predef_svl lhs1 rhs1 in
  (*handle equality*)
  let svl1a = Sautil.get_defined_eqs constr.CF.hprel_lhs in
  let svl1 = check_equality_constr lhrels lhs1 constr.CF.hprel_rhs svl in
  (*return*)
  let unk_hp_locs,unk_hp_args_locs = List.split (List.map
                                                   (build_hp_unk_locs (CP.remove_dups_svl (svl1@svl1a)) unk_hps CP.mem_svl)
                                                   (lhrels@rhrels))
  in
  (*not rec and post-oblg*)
  let l_hps = List.map fst lhrels in
  let r_hps = List.map fst rhrels in
  let post_oblg_hps = if CP.intersect_svl l_hps r_hps = [] &&
                         List.exists (fun hp -> CP.mem_svl hp post_hps) l_hps then
      r_hps
    else []
  in
  let fnc r (hp,args,pp)= if (CP.mem_svl hp post_oblg_hps) then
      r@[(hp,[],[-1])]
    else r@[(hp,args,pp)]
  in
  (List.fold_left fnc [] (List.concat unk_hp_locs),
   List.fold_left fnc [] (List.concat unk_hp_args_locs))

and analize_unk_one prog post_hps unk_hps constr =
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list (pr_triple !CP.print_sv pr2 (pr_list string_of_int)) in
  Debug.no_2 "analize_unk_one" pr2 pr1 (pr_pair pr3 pr3)
    (fun _ _ -> analize_unk_one_x prog post_hps unk_hps constr)
    unk_hps constr

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
  let l_hps = List.map (fun (hp,_,_) -> hp ) lhrels in
  let r_hps = List.map (fun (hp,_,_) -> hp ) rhrels in
  (*not rec and post-oblg*)
  let post_oblg_hps = if CP.intersect_svl l_hps r_hps = [] &&
                         List.exists (fun hp -> CP.mem_svl hp post_hps) l_hps then
      r_hps
    else []
  in
  (* let () = Debug.info_hprint (add_str "  post_oblg_hps: " !CP.print_svl) post_oblg_hps no_pos in *)
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
            let unk_svl = CP.remove_dups_svl (Sautil.retrieve_args_from_locs args locs) in
            (unk_svl, CP.diff_svl args unk_svl)
        end
      else retrieve_args_one_hp ss (hp,args)
  in
  let double_check_one_constr post_oblg_hps0 unk_hp_args_locs0 cs_hprels=
    (*post-oblg: should not consider as unknown preds: sll-get-last2.ss*)
    let unk_hp_args_locs = List.filter (fun (hp, _,_) -> not(CP.mem_svl hp post_oblg_hps0)) unk_hp_args_locs0 in
    let unk_hp_names = List.map (fun (hp, _,_) -> hp) unk_hp_args_locs in
    let cs_hp_args = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq (cs_hprels) in
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
      CP.remove_dups_svl (* (CF.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) *) (cs_non_unk_svl2@cs_non_unk_svl)
      (* ) *)
    in
    let poss_unk_svl_hps = CP.remove_dups_svl unk_svl_hps in
    let () = Debug.ninfo_zprint (lazy (("  poss_unk_svl_hps: " ^ (!CP.print_svl poss_unk_svl_hps)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("  cs_non_unk_svl1: " ^ (!CP.print_svl cs_non_unk_svl1)))) no_pos in
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
  let () = Debug.ninfo_hprint (add_str "  cs: " Cprinter.string_of_hprel) cs no_pos in
  double_check_one_constr post_oblg_hps unk_hp_args_locs (cs_hprels)

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
        let unk_svl = Sautil.retrieve_args_from_locs args locs in
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
  let hp_args = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq (l_hpargs@r_hpargs) in

  (*get unk svl*)
  let unk_svl0 = get_unk_svl hp_args unk_hp_locs [] in
  (* let () = Debug.info_zprint (lazy (("  unk_svl0: " ^ (!CP.print_svl unk_svl0)))) no_pos in *)
  (*diff from present ones, we may find them prior to*)
  let ls_xpures =  CF.get_xpure_view cs.CF.hprel_lhs in
  let existing_svl = List.fold_left (fun ls (_, svl) -> ls@svl) [] ls_xpures in
  let unk_svl1 = CP.diff_svl unk_svl0 (cs.CF.unk_svl@ existing_svl) in
  (* let () = Debug.info_zprint (lazy (("  unk_svl1: " ^ (!CP.print_svl unk_svl1)))) no_pos in *)
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
      let unk_hps1 = Gen.BList.difference_eq Sautil.check_hp_arg_eq unk_hps cs.CF.unk_hps in

      let new_constr = {cs with CF.unk_svl = unk_svl1;
                                CF.unk_hps = unk_hps1@cs.CF.unk_hps;
                                CF.hprel_lhs = new_lhs;
                       } in
      (new_constr, unk_hps1, new_map)
  in
  let () = Debug.ninfo_pprint ("   new hrel: " ^
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
      res@[(hp, Sautil.retrieve_args_from_locs args locs, locs)]
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
        let unk_args = Sautil.retrieve_args_from_locs args locs in
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
    if Sautil.is_only_xpure_f nlhs && Sautil.is_only_xpure_f nrhs then ([]) else
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
  let () = Debug.ninfo_pprint ("   new hrel: " ^
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
    let locs_i = Sautil.get_pos_of_hp_args_inst prog hp in
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
    let () = Debug.ninfo_zprint (lazy (("   hprel: " ^ (!CP.print_svl hp_names)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)))) no_pos in
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
      let r1,r2 = analize_unk_one prog post_hps unk_hps cs in
      (ls1@r1, ls2@r2)
    ) ([],[]) constrs
  in
  let unk_hp_args01,_ = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
  (*for debugging*)
  (* let () = Debug.info_pprint ("  unks 1: " ^ *)
  (*     (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) *)
  (*     in pr unk_hp_args01)) no_pos *)
  (* in *)
  (*END for debugging*)
  (**********************INTERNAL*******************************)
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
        Sautil.check_hp_locs_eq (hp1,locs1) (hp2,locs2))
        unk_hp_args02
    in
    (* let () = Debug.info_pprint ("  ls_unk_cands1: " ^ *)
    (*     (let pr = pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)) *)
    (*     in pr ls_unk_cands1)) no_pos *)
    (* in *)
    if ls_unk_cands1 = [] then ([],[],n_closure_post_hps) else
      let diff = Gen.BList.difference_eq (fun (hp1,_,locs1) (hp2,_,locs2) ->
          Sautil.check_hp_locs_eq (hp1,locs1) (hp2,locs2)) unk_hp_locs0 ls_unk_cands1
      in
      if diff =[] then
        (ls_unk_cands1, full_unk_hp_args2_locs,n_closure_post_hps)
      else
        loop_helper n_closure_post_hps ls_unk_cands1
  in
  (**********************END INTERNAL*******************************)
  let unk_hp_args02,full_unk_hp_args2_locs, closure_post_hps = if unk_hp_args01 = [] then ([], [], post_hps)
    else loop_helper post_hps unk_hp_args01 in
  (*********END double check ****************)
  let full_unk_hp_args2_locs = Sautil.refine_full_unk unk_hp_args02 full_unk_hp_args2_locs in
  (*for debugging*)
  let () = Debug.ninfo_hprint (add_str "  unks 2: " (pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)))) unk_hp_args02 no_pos
  in
  let () = Debug.ninfo_hprint (add_str "  full_unk_hp_args2_locs: " (pr_list (pr_triple !CP.print_sv !CP.print_svl (pr_list string_of_int)))) full_unk_hp_args2_locs no_pos
  in
  (* let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
  (*                            (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
  (* let () = Debug.info_zprint (lazy (("  equivs0: " ^ (pr1 equivs0) ))) no_pos in *)
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
  (* let () = Debug.ninfo_pprint ("  full_unk_hp_locs: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) *)
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
  let () = Debug.ninfo_zprint (lazy (("  link_hpargs3: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr link_hpargs3)))) no_pos
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
          (* let () = Debug.info_zprint (lazy (("  drop_links: " ^ (!CP.print_svl drop_links)))) no_pos in *)
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
  let () = x_dinfo_pp ("map after: " ^
                       (let pr = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
                        pr new_map)) no_pos in
  (*printing such that it is easy to construct a sleek test cases*)
  let () = if !Globals.print_heap_pred_decl && !VarGen.sap then
      let unk_hps = List.map fst tot_unk_hpargs in
      let () = if unk_hps <> [] then
          let hp_names = List.map (CP.name_of_spec_var) unk_hps in
          let () = print_endline_quiet ("\nDeclare_Dangling [" ^ (String.concat "," hp_names) ^ "].") in
          ()
        else ()
      in
      let link_hps = List.map fst link_hpargs4 in
      let () = if link_hps <> [] then
          let hp_names = List.map (CP.name_of_spec_var) link_hps in
          let () = print_endline_quiet ("\nDeclare_Unknown [" ^ (String.concat "," hp_names) ^ "].") in
          ()
        else ()
      in
      ()
    else ()
  in
  (new_cs, tot_unk_hpargs, new_map, link_hpargs4, punk_map)

(* type: Sautil.C.prog_decl -> *)
(*   CP.spec_var list -> *)
(*   CF.hprel list -> *)
(*   ((CP.spec_var * int list) * CP.xpure_view) list -> *)
(*   (CP.spec_var * CP.spec_var list) list -> *)
(*   (CP.spec_var * CP.spec_var list) list -> *)
(*   CF.hprel list * (CP.spec_var * CP.spec_var list) list * *)
(*   ((CP.spec_var * int list) * CP.xpure_view) list * *)
(*   (CP.spec_var * CP.spec_var list) list * (CP.spec_var * int list) list *)
let analize_unk prog post_hps constrs total_unk_map unk_hpargs link_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2a = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = pr_penta pr1 pr3 pr2 pr3 pr2a in
  Debug.no_5 "analize_unk_main" (add_str "hprels" pr1) (add_str "unk_map" pr2) 
    (add_str "post_hps" !CP.print_svl) (add_str "unk_hpargs" pr3) 
    (add_str "link_hpargs" pr3) pr4
    (fun _ _ _ _ _ -> analize_unk_x prog post_hps constrs total_unk_map unk_hpargs link_hpargs)
    constrs total_unk_map post_hps unk_hpargs link_hpargs

let generate_equiv_unkdef unk_hpargs (ls1,ls2) (hp1, hp2)=
  let args = List.assoc hp1 unk_hpargs in
  let r = List.hd args in
  let paras =  List.tl args in
  let hf = CF.HRel (hp2, List.map (fun sv -> CP.mkVar sv no_pos) args, no_pos) in
  let def = CF.formula_of_heap hf no_pos in
  let new_hpdef = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp1, r,paras ))
      (CF.HRel (hp1, List.map (fun sv -> CP.mkVar sv no_pos) args, no_pos)) [(def,None)]None  in
  (ls1@[new_hpdef],ls2@[hp1])


let generate_hp_def_from_unk_hps_x hpdefs unk_hpargs defined_hps post_hps
    unk_map equivs=
  let rec obtain_xpure_new rem_map hp args=
    match rem_map with
    | [] -> report_error no_pos "sac.obtain_xpure"
    | ((hp1, locs), xp)::rest -> begin
        if CP.eq_spec_var hp hp1 then
          let unk_args = Sautil.retrieve_args_from_locs args locs in
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
    let () = Debug.ninfo_pprint ((!CP.print_sv hp)^"(" ^
                                 (!CP.print_svl args) ^ ")=" ^
                                 (Cprinter.prtt_string_of_formula (* (CF.formula_of_heap h_def no_pos) *) def)) pos
    in
    let r = List.hd args in
    let paras = List.tl args in
    let new_hpdef = CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, r, paras))
        (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args,pos))
                                                                                                           (* CF.formula_of_heap h_def no_pos *) [(def, None)] None
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
  Debug.ninfo_pprint ">>>>>> unknown hps: <<<<<<" no_pos;
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

let generate_hp_def_from_link_hps prog iflow cond_path equivs link_hpargs=
  let trans_link_hpdef def=
    let fs, ogs = List.split def.CF.def_rhs in
    let f = CF.disj_of_list fs no_pos in
    let og = CF.combine_guard ogs in
    {
      CF.hprel_def_kind = def.CF.def_cat;
      CF.hprel_def_hrel = def.CF.def_lhs;
      CF.hprel_def_guard = og;
      CF.hprel_def_body = [(cond_path, Some f, Some iflow)];
      CF.hprel_def_body_lib = [(f, Some iflow)];
      CF.hprel_def_flow = Some iflow;
    }
  in
  let link_hps = List.map fst link_hpargs in
  let link_equivs = List.filter (fun (hp1, hp2) -> CP.mem_svl hp1 link_hps &&
                                                   CP.mem_svl hp1 link_hps) equivs in
  let equiv_link_hpdefs, define_link_hps = List.fold_left (generate_equiv_unkdef link_hpargs) ([],[]) link_equivs in
  let link_hpargs1 = List.filter (fun (hp,_) -> not (CP.mem_svl hp define_link_hps)) link_hpargs in
  let link_hpdefs =List.map (Sautil.mk_link_hprel_def prog iflow cond_path) link_hpargs1 in
  ((List.map trans_link_hpdef equiv_link_hpdefs)@link_hpdefs)

let transform_unk_hps_to_pure_x hp_defs unk_hp_frargs =
  let subst_xpure lhpdefs (xp_hpargs) f0=
    let process_one_sv (hp1,args1)=
      let fr_svl = List.assoc hp1 unk_hp_frargs in
      let eqs = List.combine args1 fr_svl in
      let xp_ps = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 no_pos) eqs in
      CP.conj_of_list xp_ps no_pos
    in
    let process_p_helper p xp_hpargs1=
      let xp_ps = (List.map process_one_sv xp_hpargs1) in
      (* let filtered_xp_ps = CP.filter_disj xp_ps rem_ps in *)
      let new_p = CP.conj_of_list (CP.remove_redundant_helper ((CP.list_of_conjs p)@ xp_ps) []) no_pos in
      new_p
    in
    let fst_inter svl ptrs=
      match svl with
      | sv::_ -> CP.mem_svl sv ptrs
      | [] -> false
    in
    let rec helper f=
      match f with
      | CF.Base fb ->
        let ptrs = Cformula.get_ptrs fb.CF.formula_base_heap in
        let xp_hpargs1 = List.filter (fun (_,svl) ->
            not(fst_inter svl ptrs)) xp_hpargs in
        let p = (MCP.pure_of_mix fb.CF.formula_base_pure) in
        let new_p =  if xp_hpargs1 =[] then p else 
            process_p_helper p xp_hpargs1 in
        CF.Base{fb with CF.formula_base_pure = (MCP.mix_of_pure new_p)}
      | CF.Exists fe ->
        let ptrs = Cformula.get_ptrs fe.CF.formula_exists_heap in
        let xp_hpargs1 = List.filter (fun (_,svl) -> not (fst_inter svl ptrs)) xp_hpargs in
        let p = (MCP.pure_of_mix fe.CF.formula_exists_pure) in
        let new_p =  if xp_hpargs1 =[] then p else
            process_p_helper p xp_hpargs1 in
        CF.Exists{fe with CF.formula_exists_pure = (MCP.mix_of_pure new_p)}
      | CF.Or orf -> CF.Or {orf with
                            CF.formula_or_f1 = helper orf.CF.formula_or_f1;
                            CF.formula_or_f2 = helper orf.CF.formula_or_f2;
                           }
    in
    let () = Debug.ninfo_zprint (lazy (("xp_hpargs: " ^ ((pr_list (pr_pair !CP.print_sv !CP.print_svl)) xp_hpargs)))) no_pos in
    helper f0
  in
  (*not in used*)
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
  (*not in used*)
  let subst_pure_hp_unk args0 ls_unk_hpargs_fr (f,g)=
    let () = Debug.ninfo_zprint (lazy (("       f: " ^ (!CF.print_formula f)))) no_pos in
    let ls_used_hp_args = CF.get_HRels_f f in
    let ls_xpures =  CF.get_xpure_view f in
    (*look up*)
    let r1 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_used_hp_args in
    let r2 = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_xpures in
    let ls_used_unk_hps,ls_eqs, ls_ss = split3 (r1@r2) in
    let used_unk_hps = List.concat ls_used_unk_hps in
    let unk_need_subst, eqs = List.fold_left (fun (ls1,ls2) (a1,a2) -> (ls1@a1,ls2@a2)) ([],[]) (List.concat ls_eqs) in
    let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
    let () = Debug.ninfo_zprint (lazy (("       eqs: " ^ (pr1 eqs)))) no_pos in
    let ss = List.concat ls_ss in
    (*remove unkhps*)
    let f1,_ =  CF.drop_unk_hrel (* CF.drop_hrel_f*) f used_unk_hps in
    (*subst*)
    let f2 = x_add CF.subst ss f1 in
    (*add pure eqs*)
    let () = Debug.ninfo_zprint (lazy (("       f2: " ^ (!CF.print_formula f2)))) no_pos in
    let pos = CF.pos_of_formula f2 in
    (****************************************)
    (*LOC: now we dont need eqs for pred parameters
      (we abs preds as a set it should be set inclusion operators).
      so we set eqs = []*)
    (***************************************)
    (* let eqs = [] in *)
    let p_eqs = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) eqs in
    let p = CP.conj_of_list (CP.remove_redundant_helper p_eqs []) pos in
    let f3 = CF.mkAnd_pure f2 (MCP.mix_of_pure p) pos in
    ((f3,g), unk_need_subst)
  in
  let subst_pure_hp_unk_hpdef ls_unk_hpargs_fr def=
    let hp,args0 = CF.extract_HRel def.CF.def_lhs in
    (* let fs,ogs = List.split def.CF.def_rhs in *)
    let fs1_wg_ss = List.map (subst_pure_hp_unk args0 ls_unk_hpargs_fr) def.CF.def_rhs in
    let fs1_wg = (* CF.disj_of_list *) (fst (List.split fs1_wg_ss)) (* no_pos *) in
    (def.CF.def_cat, def.CF.def_lhs, fs1_wg,fs1_wg_ss, def.CF.def_flow)
  in
  let subst_and_combine new_hpdefs fs_wg_ss=
    let n_fs_wg = List.map (fun ((f,g), xp_args) ->
        let nf = if xp_args = [] then f else
            subst_xpure new_hpdefs xp_args f
        in
        (nf, g)
      ) fs_wg_ss
    in
    n_fs_wg
    (* CF.disj_of_list fs no_pos *)
  in
  let ls_unk_hpargs_fr = unk_hp_frargs in
  (* let ls_unk_hpargs_fr = List.map transform_hp_unk unk_hpargs in *)
  let new_hpdefs = List.map (subst_pure_hp_unk_hpdef ls_unk_hpargs_fr) hp_defs in
  let new_hpdefs1 = List.map (fun (a,b,fs_wg,_,fl) -> (a,b, fs_wg,fl)) new_hpdefs in
  let new_hpdefs2 = List.map (fun (a,b,_, fs_wg_ss,fl) -> (a,b, fs_wg_ss,fl)) new_hpdefs in
  (*subst XPURE*)
  List.map (fun (a,b,fs_wg_ss,fl) ->
      let new_rhs = subst_and_combine (*subst_xpure*) new_hpdefs1 fs_wg_ss in
      { CF.def_cat = a; CF.def_lhs = b; CF.def_rhs = new_rhs; CF.def_flow= fl;}
    ) new_hpdefs2

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
      let args_inst = Sautil.get_hp_args_inst prog hp args in
      let (CP.SpecVar (t, _, p)) = hp in
      (CP.SpecVar(t, xp.CP.xpure_view_name, p),
       let dang_name = dang_hp_default_prefix_name ^ "_" ^ xp.CP.xpure_view_name (* ^ "_" ^dang_hp_default_prefix_name *)  in
       let (CP.SpecVar (t, _, p)) = List.hd args_inst in
       [CP.SpecVar (t, dang_name, p)])
    ) unk_map
  in
  let link_fr_map, remain_links = List.fold_left (fun (acc_res, acc_links) ((hp,args)) ->
      let locs_i = Sautil.get_pos_of_hp_args_inst prog hp in
      let args_inst = Sautil.retrieve_args_from_locs args locs_i in
      if args_inst = [] then (acc_res, acc_links@[(hp,args)]) else
        (* let (CP.SpecVar (_, _, p)) = hp in *)
        let (CP.SpecVar (t, _, p)) = List.hd args_inst in
        let r = (hp,
                 let dang_name = dang_hp_default_prefix_name ^ "_" ^ (CP.name_of_spec_var hp) (* ^ "_" ^dang_hp_default_prefix_name *)  in
                 [CP.SpecVar (t, dang_name, p)]) in
        acc_res@[r],acc_links
    ) ([],[]) link_hpargs
  in
  let tupled_defs,hp_defs1 = List.partition Sautil.is_tupled_hpdef hp_defs in
  let hp_defs2 = transform_unk_hps_to_pure hp_defs1 (fr_map@link_fr_map) in
  (hp_defs2@tupled_defs,remain_links)

let transform_xpure_to_pure prog hp_defs (unk_map:((CP.spec_var * int list) * CP.xpure_view) list) link_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_xpure_to_pure" pr1 pr2 (pr_pair pr1 pr2)
    (fun _ _ -> transform_xpure_to_pure_x prog hp_defs unk_map link_hpargs)
    hp_defs link_hpargs

let elim_dangling_conj_heap prog hp_defs unk_hps =
  if unk_hps = [] then hp_defs
  else
    (*Cfutil.formula_trans_heap_node (elim_dangling_conj_star unk_hps)*)
    List.map (fun def ->
        let n_rhs = List.map (fun (f, og) ->
            (Cfutil.elim_dangling_conj_star (Cfutil.elim_dangling_conj_star_hf unk_hps) f,og)
          ) def.CF.def_rhs in
        {def with CF.def_rhs = n_rhs;}
      )
      hp_defs

let elim_dangling_conj_heap prog hp_defs unk_hps =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_2 "elim_dangling_conj_heap" pr1 !CP.print_svl pr1
    (fun _ _ -> elim_dangling_conj_heap prog hp_defs unk_hps)
    hp_defs unk_hps

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
  (* let () = Debug.info_zprint (lazy (("unk_hps: " ^ (!CP.print_svl unk_hps)))) no_pos in *)
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
  let nf1 = x_add CF.subst sst f1 in
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
        (* let () = Debug.ninfo_zprint (lazy (("     m_args2: " ^ (!CP.print_svl  m_args2)))) no_pos in *)
        (* let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
        (* let () =  Debug.ninfo_zprint (lazy (("     subst: " ^ (pr_ss subst)))) no_pos in *)
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
        let is_node_match,all_matched_svl1,subst1 = Sautil.get_closed_matched_ptrs rhns1 lhns1 cur_node_match subst in
        if not is_node_match then None else
          let all_matched_svl2 = all_matched_svl1 @ m_args2 in
          (* let () = Debug.ninfo_zprint (lazy (("    all matched: " ^ (!CP.print_svl all_matched_svl2)))) no_pos in *)
          (* let () =  Debug.ninfo_zprint (lazy (("     subst1: " ^ (pr_ss subst1)))) no_pos in *)
          if  (is_inconsistent subst1 []) then None else
            let n_rhs_b = CF.subst_b subst1 rhs_b in
            (*check pure implication*)
            (* let nrdns,nrvns,_ = CF.get_hp_rel_bformula n_rhs_b in *)
            (*loc-1b1.slk*)
            (* let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure)
               (look_up_reachable_ptr_args prog nrdns nrvns all_matched_svl2) in *)
            let rmf = (MCP.pure_of_mix n_rhs_b.CF.formula_base_pure) in
            let lmf = (MCP.pure_of_mix lhs_b.CF.formula_base_pure) in
            let () = Debug.ninfo_zprint (lazy (("    n_rhs_b: " ^ (Cprinter.string_of_formula_base n_rhs_b)))) no_pos in
            (* let () = Debug.info_zprint (lazy (("    lmf: " ^ (!CP.print_formula lmf)))) no_pos in *)
            (* let () = Debug.info_zprint (lazy (("    rmf: " ^ (!CP.print_formula rmf)))) no_pos in *)
            let b,_,_ = x_add Tpdispatcher.imply_one 20 lmf rmf "sa:check_hrels_imply" true None in
            if b then
              (* let r_res = {n_rhs_b with *)
              (*     CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf *)
              (*         n_rhs_b.CF.formula_base_heap Sautil.select_dnode *)
              (*         Sautil.select_vnode Sautil.select_hrel all_matched_svl2  all_matched_svl2 matched_hps} *)
              (* in *)
              (*drop hps and matched svl in n_rhs2*)
              let l_res = {lhs_b with
                           CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf
                               lhs_b.CF.formula_base_heap CF.select_dnode
                               CF.select_vnode Sautil.select_hrel all_matched_svl1 all_matched_svl1 matched_hps;
                           CF.formula_base_pure = MCP.mix_of_pure
                               (CP.filter_var_new
                                  (MCP.pure_of_mix lhs_b.CF.formula_base_pure) all_matched_svl2)}
              in
              (* if not (Sautil.is_empty_base r_res) then *)
              Some (l_res, subst1)
              (* else None *)
            else
              None
      end
  in r

let strengthen_conseq_comb res_rhs2 ss lhs1 lhs2 pos =
  (*combine res into f1*)
  let n_lhs1 = x_add CF.subst ss lhs1 in
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
  let nf1 = x_add CF.subst ss1 f in
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
  let () = Debug.ninfo_zprint (lazy (("    cs2: " ^ (Cprinter.string_of_hprel cs2)))) no_pos in
  let qvars1, f1 = CF.split_quantifiers cs1.CF.hprel_rhs in
  let qvars2, f2 = CF.split_quantifiers cs2.CF.hprel_rhs in
  let n_cs2=
    match f1,f2 with
    | CF.Base rhs1_b, CF.Base rhs2_b ->
      let nlhs2, nrhs2_b, ss2 = rename_var_clash cs2.CF.hprel_lhs rhs2_b in
      let nrhs2_b1 =  CF.mkAnd_base_pure nrhs2_b (MCP.mix_of_pure (CF.get_pure nlhs2)) no_pos in
      let () = Debug.ninfo_zprint (lazy (("    nrhs2_b1: " ^ (Cprinter.string_of_formula_base nrhs2_b1)))) no_pos in
      let () = Debug.ninfo_zprint (lazy (("    rhs1_b: " ^ (Cprinter.string_of_formula_base rhs1_b)))) no_pos in
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
                          CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq
                              ((List.map (fun (hp,args) -> (hp,CP.subst_var_list ss1 args)) cs1.CF.unk_hps)@
                               (List.map (fun (hp,args) -> (hp,CP.subst_var_list ss2 args)) cs2.CF.unk_hps));
                          CF.hprel_lhs = l;
                          CF.hprel_rhs = r;
                         }
            in
            let () = Debug.ninfo_zprint (lazy (("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
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
  (*     | cs::ss -> if Sautil.checkeq_pair_formula (lhs,rhs) *)
  (*           (cs.CF.hprel_lhs,cs.CF.hprel_rhs) then *)
  (*           true *)
  (*         else check_constr_duplicate (lhs,rhs) ss *)
  (* in *)
  (*new_cs: one x one*)
  let rec helper_new_only don rest res=
    match rest with
    | [] -> (don@res)
    | cs1::rest1 ->
      let () = Debug.ninfo_zprint (lazy (("    cs1: " ^ (Cprinter.string_of_hprel_short cs1)))) no_pos in
      let new_rest, n_res = List.fold_left ( fun (ls1,ls2) cs2 ->
          let () = Debug.ninfo_zprint (lazy (("    cs 2 (rest): " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
          let on_cs2 = check_apply_fnc prog cs1 cs2 in
          match on_cs2 with
          | None -> (ls1@[cs2],ls2)
          | Some n_cs2 -> (* if check_constr_duplicate (n_cs2.CF.hprel_lhs, n_cs2.CF.hprel_rhs) (constrs@new_cs) then ls@[cs2] else *) (ls1,ls2@[n_cs2])
        ) ([],res) rest1 in
      let new_don, n_res1 = List.fold_left ( fun (ls1,ls2) cs2 ->
          let () = Debug.ninfo_zprint (lazy (("    cs 2 (done): " ^ (Cprinter.string_of_hprel_short cs2)))) no_pos in
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
a1: lhs1 --> rhs1 (*HP <-> def*)
a2: (lhs as lhs1 * R) --> rhs2 (* assumption*)
===============
replace a2 by
rhs1 * R --> rhs2
*)

let check_apply_strengthen_ante prog cs1 cs2=
  let () = Debug.ninfo_zprint (lazy (("    cs2: " ^ (Cprinter.string_of_hprel cs2)))) no_pos in
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
                          CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq
                              ((List.map (fun (hp,args) -> (hp,CP.subst_var_list ss1 args)) cs1.CF.unk_hps)@
                               (List.map (fun (hp,args) -> (hp,CP.subst_var_list ss2 args)) cs2.CF.unk_hps));
                          CF.hprel_lhs = l;
                          CF.hprel_rhs = r;
                         }
            in
            let () = Debug.ninfo_zprint (lazy (("    new cs2: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
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

let cmp_formula_opt args of1 of2=
  match of1,of2 with
  | Some f1, Some f2 ->
    let p1 = CF.get_pure f1 in
    let p2 = CF.get_pure f2 in
    CP.equalFormula p1 p2
  (* Sautil.check_relaxeq_formula args f1 f2 *)
  | None, None -> true
  | _ -> false

let unify_consj_pre_x prog unk_hps link_hps equivs0 pdefs=
  let dang_hps = (unk_hps@link_hps) in
  let rec unify_one rem_pdefs ((hp,args1,unk_svl1, cond1, olhs1, og1, orhs1) as pdef1, cs1) done_pdefs equivs=
    match rem_pdefs with
    | [] -> (done_pdefs,[(pdef1,cs1)], equivs)
    |  ((hp,args2,unk_svl2, cond2,  olhs2, og2, orhs2) as pdef2,cs2)::rest ->
      if CP.equalFormula cond1 cond2 && cmp_formula_opt args1 og1 og2 then
        match orhs1,orhs2 with
        | Some f1, Some f2 -> begin
            (* let ss = List.combine args1 args2 in *)
            (* let nf1 = (\* x_add CF.subst ss *\) f1 in *)
            (* let nf2= Sautil.mkConjH_and_norm prog args2 unk_hps [] nf1 f2 no_pos in *)
            let ores = Sautil.norm_formula prog hp args2 unk_hps [] f1 f2 equivs in
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
      let ores = Sautil.norm_formula prog hp args unk_hps [] f f1 [] in
      match ores with
      | Some (new_f, n_equivs) ->
        (tl@done_fs,[new_f],n_equivs)
      | None ->
        check_eq_one hp args tl f (done_fs@[f1])
        (* if b then *)
        (*   let ss0 = swap_map unk_hps (List.fold_left (@) [] m) [] in *)
        (*   let ss = List.map (fun (sv1,sv2) -> if CP.eq_spec_var sv1 hp then (sv2,sv1) else (sv1,sv2)) ss0 in *)
        (*   let parts = Sautil.partition_subst_hprel ss [] in *)
        (*   let pr = pr_list (pr_pair !CP.print_svl !CP.print_sv) in *)
        (*   let () = Debug.info_zprint (lazy (("  parts: " ^ (pr parts)))) no_pos in *)
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
  let process_one_hpdef (* (a,hrel,og, f) *) hp_def=
    try
      let hp,args = CF.extract_HRel hp_def.CF.def_lhs in
      if CP.mem_svl hp unk_hps then
        hp_def,[]
      else
        let fs0, ogs = List.split hp_def.CF.def_rhs in
        let fs = List.fold_left (fun r f -> r@(CF.list_of_disjs f)) [] fs0 in
        let fs1,ss = check_eq hp (args) fs [] [] in
        let ss1 = List.map (fun (sv1, sv2) -> if CP.mem_svl sv2 post_hps then (sv2,sv1) else (sv1,sv2)) ss in
        let fs2 =
          let parts = Sautil.partition_subst_hprel ss1 [] in
          List.map (fun f ->
              List.fold_left (fun f0 (from_hps, to_hp) -> CF.subst_hprel f0 from_hps to_hp) f parts
            ) fs1
        in
        let p = no_pos in
        let new_f = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 p)
            (List.hd fs2) (List.tl fs2) in
        {hp_def with CF.def_rhs = [(new_f, CF.combine_guard ogs)]},ss1
    with _ -> hp_def,[]
  in
  Debug.ninfo_pprint ">>>>>> unify: <<<<<<" no_pos;
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
    | hp_def::tl -> try
        let hp1,eargs1,p1 = CF.extract_HRel_orig hp_def.CF.def_lhs in
        let args1 = List.concat (List.map CP.afv eargs1) in
        if CP.eq_spec_var hp hp1 || CP.mem_svl hp1 unk_hps ||
           (List.length args <> List.length args1) then
          helper tl
        else
          let fs,ogs = List.split hp_def.CF.def_rhs in
          let f1 = CF.disj_of_list fs no_pos in
          (* let ss = List.combine args1 args in *)
          (* let f10 = x_add CF.subst ss f1 in *)
          let f10 = transform_fnc (hp1,args1) (hp,args) f1 in
          if Sautil.checkeq_formula_list(* _w_args args *) (CF.list_of_disjs f) (CF.list_of_disjs f10) then
            if List.exists (fun (hp2,hp3) -> equiv_cmp1 (hp1,hp) (hp2,hp3)) eq_pairs then
              let new_f = List.fold_left (fun f (hp1,hp) -> CF.subst_hprel f [hp1] hp) f10 (eq_pairs) in
              (new_f,eq_pairs)
            else
              let new_f = Sautil.mkHRel_f hp1 args p1 in
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
    let f10 = x_add CF.subst ss f1 in
    f10
  in
  let process_one_hpdef all_hpdefs (eq_pairs,r_hpdefs) hp_def=
    try
      let hp,args = CF.extract_HRel hp_def.CF.def_lhs in
      (* let () = Debug.ninfo_zprint (lazy (("       hp: " ^ (!CP.print_sv hp)))) no_pos in *)
      if CP.mem_svl hp unk_hps  then
        (eq_pairs,r_hpdefs@[hp_def])
      else
        let fs,ogs = List.split hp_def.CF.def_rhs in
        let f = CF.disj_of_list fs no_pos in
        let new_f,new_eq_pairs = lookup_equiv_hpdef all_hpdefs syntax_transform_func unk_hps eq_pairs hp args f in
        (new_eq_pairs, r_hpdefs@[{hp_def with CF.def_rhs = [(new_f, CF.combine_guard ogs)]}])
    with _ -> (*tupled defs*)
      (eq_pairs,r_hpdefs@[hp_def])
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
    let f10 = x_add CF.subst ss f1 in
    f10
  in
  let process_one_hpdef all_hpdefs (eq_pairs,r_hpdefs) hp_def=
    try
      let hp,args = CF.extract_HRel hp_def.CF.def_lhs in
      (* let () = Debug.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos in *)
      if CP.mem_svl hp unk_hps then
        (eq_pairs,r_hpdefs@[hp_def])
      else
        let fs,ogs = List.split hp_def.CF.def_rhs in
        let f = CF.disj_of_list fs no_pos in
        let new_f,new_eq_pairs = lookup_equiv_hpdef all_hpdefs shape_transform_func unk_hps eq_pairs hp args f in
        (new_eq_pairs, r_hpdefs@[{hp_def with CF.def_rhs = [(new_f,CF.combine_guard ogs)]}])
    with _ -> (*tupled defs*)
      (eq_pairs,r_hpdefs@[hp_def])
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

let check_equiv_wo_libs_x iprog prog iflow sel_hps post_hps unk_hps hpdefs hp_defs eqmap1=
  (*partition: matched with lib already*)
  let lib_hps, lib_hpdefs, rem_hpdefs = List.fold_left (fun (r1,r2,r3) hpdef->
      match hpdef.CF.hprel_def_body_lib with
      | [] -> begin
          match hpdef.CF.hprel_def_kind with
          | CP.HPRelDefn (hp,_,_) ->
            if CP.mem_svl hp sel_hps then
              (r1, r2, r3@[hpdef])
            else (r1@[hp], r2@[hpdef], r3)
          | _ -> (r1, r2@[hpdef], r3)
        end
      | _ ->begin
          match hpdef.CF.hprel_def_kind with
          | CP.HPRelDefn (hp,_,_) ->
            (r1@[hp], r2@[hpdef], r3)
          | _ -> (r1, r2@[hpdef], r3)
        end
    ) ([],[],[]) hpdefs in
  let lib_hp_defs, post_hp_defs, hp_defs1 = List.fold_left (fun (r1,r2,r3) (hp_def)->
      match hp_def.CF.def_cat with
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
  let rem_hpdefs1 = Sautil.pred_split_update_hpdefs iflow (List.map fst eqmap2) rem_hpdefs hp_defs2 in
  (rem_hpdefs1@lib_hpdefs, hp_defs2@lib_hp_defs)

let check_equiv_wo_libs iprog prog iflow sel_hps post_hps unk_hps hpdefs hp_defs eqmap1=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_def in
  Debug.no_3 "check_equiv_wo_libs" !CP.print_svl pr2 pr1 (pr_pair pr2 pr1)
    (fun _ _ _ -> check_equiv_wo_libs_x iprog prog iflow sel_hps post_hps unk_hps hpdefs hp_defs eqmap1)
    sel_hps hpdefs hp_defs


(*do_conj_unify: pre only*)
let do_unify_x prog do_conj_unify unk_hps link_hps post_hps defs0=
  let subst_equiv equivs hp_def =
    let nrhs = if equivs = [] then hp_def.CF.def_rhs else
        List.map (fun (f, og) -> let nf = List.fold_left (fun f0 (from_hps, to_hp) ->
            CF.subst_hprel f0 from_hps to_hp
          ) f equivs
            in ( nf, og)) hp_def.CF.def_rhs
    in
    {hp_def with CF.def_rhs = nrhs}
  in
  let unify_heap_conj (r_hp_defs, equivs0) hp_def=
    try
      let _,args = CF.extract_HRel hp_def.CF.def_lhs in
      let fs, ogs = List.split hp_def.CF.def_rhs in
      let f = CF.disj_of_list fs no_pos in
      let nf, equivs1 = Sautil.norm_heap_consj_formula prog args unk_hps [] f equivs0 in
      (r_hp_defs@[{hp_def with CF.def_rhs = [(nf,CF.combine_guard ogs)]}], equivs1)
    with _ -> (r_hp_defs@[hp_def], equivs0)
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
  let parts = Sautil.partition_subst_hprel equivs3a [] in
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


let norm_overr_x hpdefs=
  (*********INTERNAL************)
  let rec norm_overr_h_formula res hf=
    match hf with
    | CF.Conj {CF.h_formula_conj_h1=hf1;
               CF.h_formula_conj_h2=hf2;
               CF.h_formula_conj_pos=p} -> begin
        (* check either of hf* is unknown pred *)
        match hf1 with
        | CF.HRel _ -> hf2, res@[(hf1, hf2)]
        | _ -> begin
            match hf2 with
            | CF.HRel _ -> hf1, res@[(hf2, hf1)]
            | _ -> hf,res
          end
      end
    | CF.Star { CF.h_formula_star_h1=hf1;
                CF.h_formula_star_h2=hf2;
                CF.h_formula_star_pos = p;} ->
      let n_hf1,res1 = norm_overr_h_formula res hf1 in
      let n_hf2,res2 = norm_overr_h_formula res1 hf2 in
      let n_hf =  CF.Star { CF.h_formula_star_h1=n_hf1;
                            CF.h_formula_star_h2=n_hf2;
                            CF.h_formula_star_pos = p;} in
      n_hf,res2
    | _ -> hf,res
  in
  let rec norm_overr_formula f=
    match f with
    | CF.Base fb ->
      let nh,rels = norm_overr_h_formula [] fb.CF.formula_base_heap in
      CF.Base {fb with CF.formula_base_heap = nh}, rels
    | CF.Exists _ ->
      let quans, bare = CF.split_quantifiers f in
      let nbare, rels = norm_overr_formula bare in
      CF.add_quantifiers quans nbare, rels
    | CF.Or orf ->
      let f1,rels1 = norm_overr_formula orf.CF.formula_or_f1 in
      let f2,rels2 = norm_overr_formula orf.CF.formula_or_f2 in
      CF.Or {orf with CF.formula_or_f1 = f1;
                      CF.formula_or_f2 = f2}, rels2@rels2
  in
  let norm_overr_one hpdef=
    let n_rhs, new_hprels = List.fold_left (fun (r1,r2) (f,og) ->
        let nf, rels = norm_overr_formula f in
        (r1@[(nf,og)], r2@rels)
      ) ([],[]) hpdef.CF.def_rhs in
    {hpdef with CF.def_rhs = n_rhs},new_hprels
  in
  let add_one_rel hpdefs (hprel, rel)=
    let hp, args = CF.extract_HRel hprel in
    try
      let def, rest = CF.look_up_hp_def_with_remain hpdefs hp [] in
      let _,args0 = CF.extract_HRel def.CF.def_lhs in
      let n_rel = x_add CF.subst (List.combine args args0) (CF.formula_of_heap rel no_pos) in
      let n_def = {def with CF.def_rhs = def.CF.def_rhs@[(n_rel,None)]} in
      rest@[n_def]
    with _ ->
      let def = CF.mk_hp_rel_def hp (args, List.hd args, List.tl args) None (CF.formula_of_heap rel no_pos)  None no_pos in
      hpdefs@[def]
  in
  (*********INTERNAL************)
  let n_hpdefs, nrels = List.fold_left (fun (acc1,acc2) def ->
      let n_def, n_rels = norm_overr_one def in
      (acc1@[n_def], acc2@n_rels)
    ) ([],[]) hpdefs in
  (*to add nrels into hpdefs*)
  let n_hpdefs1 = List.fold_left (fun acc rel -> add_one_rel acc rel) n_hpdefs nrels in
  n_hpdefs1

let norm_overr hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "norm_overr" pr1 pr1
    (fun _ -> norm_overr_x hpdefs) hpdefs

(*************************************************)
(**********       DISJ-UNIFY       ***************)
(*************************************************)

(*=============**************************================*)
(*=============END UNIFY PREDS================*)
(*=============**************************================*)


(*************************************************)
(**********       INTER-UNIFY       ***************)
(*************************************************)
(*work with two branches first. to improve*)
let pred_unify_inter_x prog dang_hps hp_defs=
  (**************** INTERNAL ****************)
  let is_inter_hpdef d=
    let hp = CF.get_hpdef_name d.CF.def_cat in
    let fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] d.CF.def_rhs in
    if List.length fs != 2 then (*work with two branches first. to improve*) false else
      let hps = List.fold_left (fun r f -> r@(CF.get_hp_rel_name_formula f)) [] fs in
      let hps2 = CP.diff_svl hps (dang_hps@[hp]) in
      if CP.mem_svl hp hps || hps2 == [] then false
      else true
      (* List.exists (fun f-> *)
      (*     try *)
      (*       let () = CF.extract_HRel_f f in *)
      (*     true *)
      (*     with _ -> false *)
      (* ) fs *)
  in
  let check_pure_exist_x p f=
    let ps = CP.split_conjunctions p in
    let p1 = CF.get_pure f in
    let ps1 = CP.split_conjunctions p1 in
    (Gen.BList.difference_eq CP.equalFormula) ps ps1 = []
  in
  let check_pure_exist p f=
    let pr1 = !CP.print_formula in
    let pr2 = Cprinter.prtt_string_of_formula in
    Debug.no_2 "check_pure_exist" pr1 pr2 string_of_bool
      (fun _ _ -> check_pure_exist_x p f) p f
  in
  (*to improve*)
  let do_inter_unify hp_def other_hpdefs r dep_hp (pf,p_og) (dep_f, dep_og)=
    let () = Debug.ninfo_hprint (add_str "dep_hp" !CP.print_sv) dep_hp no_pos in
    match hp_def.CF.def_cat with
    | CP.HPRelDefn (hp ,_, other_args) -> begin
        (*find pure constraint p on root of pf - to improve*)
        let r_ps, other = List.partition (fun p -> CP.diff_svl (CP.fv p) [r] =[] )
            (CP.split_conjunctions (CF.get_pure pf) ) in
        let () = Debug.ninfo_hprint (add_str "other" (pr_list !CP.print_formula)) other no_pos in
        if other != [] then (false,hp_def) else
          (*check whether p contradict with counterpart in dep_p*)
          let r_p = (CP.join_conjunctions r_ps) in
          let dep_f_wpure = CF.mkAnd_pure dep_f (MCP.mix_of_pure r_p) no_pos in
          if not (Sautil.is_unsat dep_f_wpure) then (false,hp_def) else
            begin
              try
                (*check whether p is exsit in one branch of dep_hp*)
                let dep_hpdef = CF.look_up_hp_def other_hpdefs dep_hp in
                let dep_r = match dep_hpdef.CF.def_cat with
                  | CP.HPRelDefn (_ ,dr, _) -> dr
                  | _ -> raise Not_found
                in
                let ss = [(r, dep_r)] in
                let r_p_in_dep = CP.subst ss r_p in
                let dep_fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] dep_hpdef.CF.def_rhs in
                if List.exists (fun f -> check_pure_exist r_p_in_dep f) dep_fs then
                  (*do union combine - drop the counterpart in pf, mkAnd*)
                  let n_dep_f = CF.filter_var_pure r dep_f in
                  (true, {hp_def with CF.def_rhs = [(n_dep_f, dep_og)]})
                else (false,hp_def)
              with _ -> (false,hp_def)
            end
      end
    | _ -> (false, hp_def)
  in
  let find_inter hp_def other_hpdefs=
    let fs0 = List.fold_left (fun r (f,g) -> r@(List.map (fun f1 -> (f1,g)) (CF.list_of_disjs f))) [] hp_def.CF.def_rhs in
    match hp_def.CF.def_cat with
    | CP.HPRelDefn (hp ,r, other_args) -> begin
        match fs0 with
        | [(f1,og1);(f2,og2)] -> begin
            (*extract common*)
            let is_common, sharing_f0, n_fs, new_roots = Sautil.partition_common_diff prog hp (r::other_args) dang_hps [] f1 f2 no_pos in
            let fs, n_r, sharing_f = if is_common && List.length new_roots = 1 then
                n_fs, List.hd new_roots, sharing_f0
              else ([f1;f2], r, CF.mkTrue_nf no_pos)
            in
            let f1,f2 = match fs with
              | [f1;f2] -> f1,f2
              | _ -> report_error no_pos "SAC.ind_inter"
            in
            let dep_hps1 = CF.get_hp_rel_name_formula f1 in
            let dep_hps2 = CF.get_hp_rel_name_formula f2 in
            let b, n_hp_def = match dep_hps1,dep_hps2 with
              | [dep_hp],[] -> do_inter_unify hp_def other_hpdefs n_r dep_hp (f2,og2) (f1,og1)
              | [], [dep_hp] -> do_inter_unify hp_def other_hpdefs n_r dep_hp (f1,og1) (f2, og2)
              | _ ->  (false, hp_def)
            in
            if b then (b, {n_hp_def with CF.def_rhs =
                                           List.map (fun (f, og) -> (CF.mkStar f sharing_f CF.Flow_combine no_pos,og)) n_hp_def.CF.def_rhs})
            else (false, hp_def)
          end
        | _ -> (false,hp_def)
      end
    | _ -> (false, hp_def)
  in
  let rec do_one_step_inter rest done_hpdefs non_inter_hpdefs=
    match rest with
    | [] -> done_hpdefs
    | hp_def::rest1 ->
      let b,n_hp_def = find_inter hp_def (done_hpdefs@non_inter_hpdefs) in
      do_one_step_inter rest1 (done_hpdefs@[n_hp_def]) non_inter_hpdefs
  in
  (* let pr = pr_list_ln Cprinter.string_of_hp_rel_def in *)
  (****************END INTERNAL ****************)
  let inter_hp_defs, rem = List.partition is_inter_hpdef hp_defs in
  (* let () = Debug.ninfo_hprint (add_str "inter_hp_defs" pr) inter_hp_defs no_pos in *)
  let inter_hp_defs1 = do_one_step_inter inter_hp_defs [] rem in
  (inter_hp_defs1@rem)

let pred_unify_inter prog dang_hps hp_defs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_2 "pred_unify_inter" pr1 pr2 pr2
    (fun _ _ -> pred_unify_inter_x prog dang_hps hp_defs)
    dang_hps hp_defs

(*=============**************************================*)
(*=============INTER UNIFY PREDS================*)
(*=============**************************================*)
(*
  todo: bottom-up
*)
let norm_elim_useless_paras_x prog unk_hps sel_hps post_hps hp_defs=
  let unk_svl = [] in
  let check_and_elim is_pre cdefs (hp, r, non_r_args, def)=
    let _,args = CF.extract_HRel def.CF.def_lhs in
    let fs_wg = List.fold_left (fun r (f,og) -> r@(List.map (fun f1 -> (f1, og)) (CF.list_of_disjs f))) [] def.CF.def_rhs in
    let elimed,_, (n_args, r, n_paras), n_fs_wg,elim_ss,link_defs,n_hp = Sautil.elim_not_in_used_args prog unk_hps
        [((CF.mkHTrue_nf no_pos), None)] fs_wg hp (args, r, non_r_args) in
    if elimed then
      let hpdef = Sautil.mk_hprel_def_wprocess prog is_pre cdefs unk_hps unk_svl n_hp (n_args, r, n_paras) n_fs_wg no_pos in
      let new_defs1 = List.map (fun (hp,def) ->
          (hp, {def with CF.def_rhs = List.map (fun (f,og) ->( CF.subst_hrel_f f elim_ss, og)) def.CF.def_rhs})
        ) (link_defs@hpdef)
      in
      (snd (List.split new_defs1), elim_ss)
    else ([def],[])
    (*second way*)
    (* let new_defs, elim_ss = Sautil.check_and_elim_not_in_used_args prog is_pre cdefs unk_hps unk_svl *)
    (*             def.CF.def_rhs hp (args, r, non_r_args) in *)
    (* let new_defs1 = List.map (fun (hp,def) -> *)
    (*     (hp, {def with CF.def_rhs = List.map (fun (f,og) ->( CF.subst_hrel_f f elim_ss, og)) def.CF.def_rhs}) *)
    (* ) new_defs *)
    (* in *)
    (* (snd (List.split new_defs1), elim_ss) *)
  in
  let rec lookup_hpdef hpdefs hp0 args0 =
    match hpdefs with
    | def::rest ->let hp1,args1= CF.extract_HRel def.CF.def_lhs in
      if CP.eq_spec_var hp1 hp0 then
        (* not subst recurisve *)
        let succ_hps = List.fold_left (fun r (f, _) -> r@(CF.get_hp_rel_name_formula f)) [] def.CF.def_rhs in
        if CP.mem_svl hp1 succ_hps then [] else
          let ss = List.combine args1 args0 in
          List.map (fun (f, og) -> (x_add CF.subst ss f, CF.subst_opt ss og)) def.CF.def_rhs
      else lookup_hpdef rest hp0 args0
    | [] -> []
  in
  let rec apply_syntax_lemma hpdefs sel_hps syn_lemmas res=
    match hpdefs with
    | def::rest ->
      let hp,args= CF.extract_HRel def.CF.def_lhs in
      if CP.mem_svl hp sel_hps then
        (*** has quiv lemma**)
        try
          let (hp1,args1,hp2,args2) = List.find (fun (hp12,_,_,_) -> CP.eq_spec_var hp hp12) syn_lemmas in
          let n_rhs = lookup_hpdef hpdefs hp2 args2 in
          if n_rhs = [] then apply_syntax_lemma rest sel_hps syn_lemmas (res@[def]) else
            let ss = List.combine args1 args in
            let n_rhs1 = List.map (fun (f, og) -> (x_add CF.subst ss f, CF.subst_opt ss og)) n_rhs in
            let new_def = {def with CF.def_rhs = n_rhs1} in
            apply_syntax_lemma rest sel_hps syn_lemmas (res@[new_def])
        with _ ->
          apply_syntax_lemma rest sel_hps syn_lemmas (res@[def])
      else
        apply_syntax_lemma rest sel_hps syn_lemmas (res@[def])
    | [] -> res
  in
  let hn_trans_formula syn_lemmas hf=
    match hf with
    | CF.HRel (hp,eargs, pos)-> begin
        try
          let (hp1,args1,hp2,args2) = List.find (fun (hp12,_,_,_) -> CP.eq_spec_var hp hp12) syn_lemmas in
          let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
          (*subst*)
          let ss = List.combine args1 args in
          let args21 = CP.subst_var_list ss args2 in
          let n_eargs = List.map (fun sv -> CP.mkVar sv pos) args21 in
          CF.HRel (hp2,n_eargs, pos)
        with _ -> hf
      end
    | _ -> hf
  in
  let rec subst_syntax_lemma hpdefs sel_hps syn_lemmas res=
    match hpdefs with
    | def::rest ->
      let hp,args= CF.extract_HRel def.CF.def_lhs in
      (* let () = Debug.info_hprint (add_str "hp 1" !CP.print_sv) hp no_pos in *)
      (* if CP.mem_svl hp sel_hps then *)
      let syn_lemmas1 = List.filter (fun (hp1,_,_,_) -> not (CP.eq_spec_var hp hp1)) syn_lemmas in
      (* let () = Debug.info_hprint (add_str "hp" !CP.print_sv) hp no_pos in *)
      let n_rhs1 = List.map (fun (f, og) -> (CF.formula_trans_heap_node (hn_trans_formula syn_lemmas1) f, og)) def.CF.def_rhs in
      let new_def = {def with CF.def_rhs = n_rhs1} in
      subst_syntax_lemma rest sel_hps syn_lemmas (res@[new_def])
    (* else *)
    (*   subst_syntax_lemma rest sel_hps syn_lemmas (res@[def]) *)
    | [] -> res
  in
  (******************END************************)
  (* let hp_defs1_scc, mutrec_defs = CFU.hp_defs_topo_sort hp_defs in *)
  (* let hp_defs1 = List.concat hp_defs1_scc in *)
  let hp_defs1 = hp_defs in let mutrec_defs = [] in
  let sel_pre_defs, sel_post_defs, rem = List.fold_left ( fun (r1,r2,r3) def ->
      if List.for_all (fun (f,_) -> Sautil.is_empty_f f || Cformula.isAnyConstFalse f) def.CF.def_rhs then
        (r1,r2, r3@[def])
      else
        match def.CF.def_cat with
        | CP.HPRelDefn (hp, r, others) ->
          if CP.mem_svl hp unk_hps then (r1,r2,r3@[def]) else
          if CP.mem_svl hp post_hps then
            (r1,r2@[(hp, r, others, def)],r3)
          else (r1@[(hp, r, others, def)],r2,r3)
        | _ -> (r1,r2,r3@[def])
    ) ([],[],[]) hp_defs1 in
  let n_pre_defs, ss1 = List.fold_left (fun (r1,r2) ((hp, r, non_r_args, def) as tuple_def) ->
      let ndefs, ss = check_and_elim true [] tuple_def in
      (r1@ndefs, r2@ss)
    ) ([],[]) sel_pre_defs in
  let n_post_defs, ss2 = List.fold_left (fun (r1,r2) ((hp, r, non_r_args, def) as tuple_def) ->
      let ndefs, ss = check_and_elim false [] tuple_def in
      (r1@ndefs, r2@ss)
    ) ([],[]) sel_post_defs in
  (*may need subst ss1@ss2 into n defs if apcl.*)
  let equiv_lemmas = List.map (fun (hf1, hf2) ->
      let hp1,args1= CF.extract_HRel hf1 in
      let hp2,args2= CF.extract_HRel hf2 in
      (hp1,args1,hp2,args2)
    ) (ss1@ss2) in
  let () = Debug.ninfo_hprint (add_str "sel_hps" !CP.print_svl) sel_hps no_pos in
  let () = Debug.ninfo_hprint (add_str "equiv_lemmas" (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl !CP.print_sv !CP.print_svl))) equiv_lemmas no_pos in
  let n_pre_post_defs1 = apply_syntax_lemma (n_pre_defs@n_post_defs) sel_hps equiv_lemmas [] in
  let n_pre_post_defs2 = subst_syntax_lemma n_pre_post_defs1 sel_hps equiv_lemmas [] in
  (* let n_pre_post_defs1 = (n_pre_defs@n_post_defs) in *)
  (n_pre_post_defs2@rem@mutrec_defs)

let norm_elim_useless_paras prog unk_hps sel_hps post_hps hp_defs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_4 "norm_elim_useless_paras" pr1 pr1 pr1 pr2 pr2
    (fun _ _ _ _ ->  norm_elim_useless_paras_x prog unk_hps sel_hps post_hps hp_defs)
    unk_hps sel_hps post_hps hp_defs

(*=============**************************================*)
(*=============OBLIGATION================*)
(*=============**************************================*)
(*hpdef for gettting root. becuase hp decl may be removed previously*)
let trans_constr_hp_2_view iprog cprog proc_name hpdefs in_hp_names chprels_decl constrs=
  let process_cs cs=
    let nlhs = Saout.trans_formula_hp_2_view iprog cprog proc_name
        chprels_decl hpdefs [] cs.CF.hprel_lhs in
    let nrhs = Saout.trans_formula_hp_2_view iprog cprog proc_name
        chprels_decl hpdefs [] cs.CF.hprel_rhs in
    {cs with CF.hprel_lhs = nlhs;
             CF.hprel_rhs = nrhs;}
  in
  let n_constrs = List.map process_cs constrs in
  (* let pr1= pr_list_ln Cprinter.string_of_hprel_short in *)
  (* let () = print_endline ("n_constrs: " ^ (pr1 n_constrs))  in *)
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

(*check whether lhs of pre-obligation is inferred and LHS is pre-fix-hps
  if it is the case, move the constrs to examined in lfp computation
*)
let reclassify_pre_obligation_x prog is pre_fix_hps constrs=
  (*******INtERNAL*******)
  (* let post_hps = is.CF.is_post_hps in *)
  let def_hps = List.fold_left (fun ls d ->
      match d.CF.def_cat with
      |  CP.HPRelDefn (hp,_,_) -> ls@[hp]
      | CP.HPRelLDefn hps -> ls@hps
      | _ -> ls
    ) [] is.CF.is_hp_defs in
  let examine_one (res_oblgs,res_pre_fix) cs=
    let lhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
    let rhs_hps = CF.get_hp_rel_name_formula cs.CF.hprel_rhs in
    if CP.intersect_svl pre_fix_hps lhs_hps != [] && CP.diff_svl rhs_hps def_hps = [] then
      (res_oblgs,res_pre_fix@[cs])
    else
      (res_oblgs@[cs],res_pre_fix)
  in
  (*******INtERNAL*******)
  List.fold_left examine_one ([],[]) constrs

let reclassify_pre_obligation prog is pre_fix_hps constrs=
  let pr1 = Cprinter.string_of_infer_state_short in
  let pr2 = pr_list_ln Cprinter.string_of_hprel_short in
  Debug.no_3 "reclassify_pre_obligation" pr1 !CP.print_svl pr2 (pr_pair pr2 pr2)
    (fun _ _ _ -> reclassify_pre_obligation_x prog is pre_fix_hps constrs)
    is pre_fix_hps constrs

let do_entail_check_x vars iprog cprog cs=
  let update_explicit_root_x lhs rhs=
    let rec lookup_root root_sv vns=
      match vns with
      | [] -> []
      | vn::rest ->
        let r_sv2 = vn.CF.h_formula_view_node in
        if CP.eq_spec_var r_sv2 root_sv then
          let self_sv = CP.SpecVar (CP.type_of_spec_var root_sv,self, Unprimed) in
          [(root_sv, self_sv)]
        else lookup_root root_sv rest
    in
    let rec lookup_and_subst l_vns r_vns=
      match l_vns with
      | vn::rest -> begin
          let l_r_sv = vn.CF.h_formula_view_node in
          let ss = lookup_root l_r_sv r_vns in
          if ss = [] then lookup_and_subst rest r_vns else
            (x_add CF.subst ss lhs, x_add CF.subst ss rhs)
        end
      | _ -> (lhs, rhs)
    in
    let l_vns = CF.get_views lhs in
    let r_vns = CF.get_views rhs in
    lookup_and_subst l_vns r_vns
  in
  let update_explicit_root lhs rhs=
    let pr1 = Cprinter.prtt_string_of_formula in
    Debug.no_2 "update_explicit_root" pr1 pr1 (pr_pair pr1 pr1)
      (fun _ _ -> update_explicit_root_x lhs rhs) lhs rhs
  in
  let () = Infer.rel_ass_stk # reset in
  let get_view_def vname=
    let () = Debug.ninfo_hprint (add_str "vname" pr_id) vname no_pos in
    let vdef = (x_add Cast.look_up_view_def_raw x_loc cprog.Cast.prog_view_decls vname) in
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
  let (valid, rs,v_hp_rel) = x_add Sleekcore.sleek_entail_check 6 [] vars cprog [] ante conseq in
  (* let valid = ((not (CF.isFailCtx rs))) in *)
  let () = if not valid then
      report_warning no_pos ("FAIL: Can not prove:\n" ^ (Cprinter.string_of_hprel_short cs))
    else if vars = [] then
      (*add unsafe lemma (swl)*)
      (* let ante1,conseq1 = update_explicit_root ante cs.CF.hprel_rhs in *)
      (* let iante = Astsimp.rev_trans_formula ante1 in *)
      (* let iconseq = Astsimp.rev_trans_formula conseq1 in *)
      (* let l_coer = Iast.mk_lemma (fresh_any_name "sa") LEM_UNSAFE Iast.Left [] iante iconseq in *)
      (* let () = Lemma.manage_unsafe_lemmas [l_coer] iprog cprog in *)
      ()
    else ()
  in
  let hprels = Infer.collect_hp_rel_list_context rs in
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

let do_entail_check vars iprog cprog cs=
  let pr1 = Cprinter.string_of_hprel_short in
  Debug.no_2 "do_entail_check" pr1 !CP.print_svl (pr_list_ln pr1)
    (fun _ _-> do_entail_check_x vars iprog cprog cs) cs vars



(*=============**************************================*)
(*=============END OBLIGATION================*)
(*=============**************************================*)

(*=============**************************================*)
(*=============DNC================*)
(*=============**************************================*)
let partition_constrs_4_paths link_hpargs0 constrs0 =
  let ls_link_hpargs = Sautil.dang_partition link_hpargs0 in
  let ls_constrs_path = Sautil.assumption_partition constrs0 in
  (* matching constrs_path with dang_path*)
  let ls_cond_danghps_constrs = Sautil.pair_dang_constr_path ls_constrs_path ls_link_hpargs (pr_list_ln Cprinter.string_of_hprel_short) in
  ls_cond_danghps_constrs

(*=============**************************================*)
(*=============END DNC================*)
(*=============**************************================*)

(*=============**************************================*)
(*=============FIXPOINT================*)
(*=============**************************================*)
(*
  matching weaker_fs with stronger_fs:
   - match: get strongest
   - otherwise: drop
*)
let shape_gist_x prog hp args unk_hps defined_fs required_stronger_fs=
  (************INTERNAL************)
  (*check whether d_f ==> s_f*)
  let do_gist s_f d_f=
    let fs = [s_f; d_f] in
    let lldns_vns = List.fold_left (fun r2 f ->
        let hds,hvs,_ = CF.get_hp_rel_formula f in
        (r2@[hds,hvs,f])
      ) [] fs in
    let min,sh_ldns,sh_lvns,eqNulls,eqPures,hprels = Sautil.get_min_common prog args unk_hps lldns_vns in
    if min = 0  && eqNulls = [] && eqPures= [] && hprels=[] then
      false, s_f
    else true,d_f
  in
  let rec do_gist_helper d_f s_fs done_s_fs=
    match s_fs with
    | [] -> false,d_f,done_s_fs
    | s_f::s_rest ->
      (*check whether s_f ==> d_f*)
      let is_gist, gist_f = do_gist s_f d_f in
      if is_gist then true,gist_f, (done_s_fs@s_rest)
      else do_gist_helper d_f s_rest (done_s_fs@[s_f])
  in
  let rec match_helper d_fs s_fs res=
    match d_fs with
    | [] -> res@s_fs
    | f::d_rest -> let is_match,gist_f,s_rest = do_gist_helper f s_fs [] in
      let new_res = if is_match then (res@[gist_f]) else res in
      match_helper d_rest s_rest new_res
  in
  (************END INTERNAL************)
  match_helper defined_fs required_stronger_fs []

let shape_gist prog hp args unk_hps defined_fs required_stronger_fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_4 "shape_gist" !CP.print_sv !CP.print_svl pr1 pr1 pr1
    (fun _ _ _ _ -> shape_gist_x prog hp args unk_hps defined_fs required_stronger_fs)
    hp args defined_fs required_stronger_fs

let shape_widening_x prog hp args unk_hps pdefs pos=
  let shape_widen f1 f2=
    let is_common, sharing_f, n_fs ,next_roots = Sautil.partition_common_diff prog hp args unk_hps [] f1 f2 pos in
    if not is_common then (false, f1) else
      match n_fs with
      | [f21;f22] -> (*after reaarange + subst*)
        let hpargs1 = CF.get_HRels_f f21 in
        let hpargs2 = CF.get_HRels_f f22 in
        let ( _,mix_lf2,_,_,_,_) = CF.split_components f22 in
        let sst2 = MCP.ptr_equations_without_null mix_lf2 in
        let hpargs22 = List.map (fun (hp, args) ->
            (hp, List.fold_left Sautil.close_def args sst2)
          ) hpargs2 in
        let inter = Gen.BList.intersect_eq Sautil.check_hp_args_imply hpargs1 hpargs22 in
        let n_sharing =
          if inter = [] then sharing_f else
            let hp_fs = List.map (fun (hp,args) -> Sautil.mkHRel_f hp args pos) inter in
            List.fold_left (fun f1 f2 -> CF.mkStar f1 f2 CF.Flow_combine pos) sharing_f hp_fs
        in
        (is_common, n_sharing)
      | _ -> (is_common, sharing_f)
  in
  let rec helper sharing rest=
    match rest with
    | [] -> [sharing]
    | f::rest1 -> let is_common, sharing_f = shape_widen sharing f in
      if not is_common then [] else
        helper sharing_f rest1
  in
  match pdefs with
  | [] -> []
  | [pdef] -> [pdef]
  | (hp,args, c, f, d)::rest ->
    let rest_fs = List.map (fun (_,_, _, f, _) -> f) rest in
    let sharing_f = helper f rest_fs in
    match sharing_f with
    | [f1] -> [(hp,args, c, f1, d)]
    | _ -> pdefs

let shape_widening prog hp args unk_hps fs pos=
  let pr1 = pr_list (fun (_,_, _, f, _) -> Cprinter.prtt_string_of_formula f) in
  Debug.no_3 "shape_widening" !CP.print_sv !CP.print_svl pr1 pr1
    (fun _ _ _ -> shape_widening_x prog hp args unk_hps fs pos)
    hp args fs

let gfp_gen_init prog is_pre r base_fs rec_fs=
  let is_complete r fs=
    let ps = List.map CF.xpure_for_hnodes_f fs in
    let ps1 = List.map (fun p -> CP.filter_var p [r]) ps in
    let neg_p = (CP.conj_of_list ps1 no_pos) in
    let () = Debug.ninfo_zprint (lazy (("neg_p: " ^ (!CP.print_formula neg_p)))) no_pos in
    not (Tpdispatcher.is_sat_raw (MCP.mix_of_pure neg_p))
  in
  let find_greates_neg rcomplete (r_fs, r_unk_hpargs) f=
    let svl = CF.get_ptrs_f f in
    let pos = (CF.pos_of_formula f) in
    if CP.mem_svl r svl then
      (*neg for sl is not well defined. use unkhp*)
      if not rcomplete then
        let (hf, n_hp) = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog is_pre true [(r, I)] pos in
        let f = CF.formula_of_heap_w_normal_flow hf pos in
        (r_fs@[f], r_unk_hpargs@[(n_hp, [r])])
      else
        (r_fs, r_unk_hpargs)
    else
      let p = CP.filter_var (CF.get_pure f) [r] in
      let f = CF.formula_of_pure_N (CP.mkNot_s p) pos in
      (r_fs@[f], r_unk_hpargs)
  in
  let rcomplete = is_complete r (base_fs@rec_fs) in
  let n_fs, n_unk_hpargs = List.fold_left (find_greates_neg rcomplete) ([],[]) rec_fs in
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
let norm prog args0 (hp1, args1, f1)=
  let ss =List.combine args1 args0 in
  let nf1 = x_add CF.subst ss f1 in
  (hp1, args0, nf1)

let classify hp (r_bases, r_recs, r_deps) f=
  let hps = CF. get_hp_rel_name_formula f in
  if hps = [] then
    (r_bases@[f], r_recs, r_deps)
  else if CP.diff_svl hps [hp] = [] then
    (r_bases, r_recs@[f], r_deps)
  else (r_bases, r_recs, r_deps@[f])

let compute_gfp_x prog is_pre is predefs pdefs=
  (********INTERNAL*******)
  let skip_hps = List.map fst (is.CF.is_dang_hpargs@is.CF.is_link_hpargs) in
  (********END INTERNAL*******)
  if !Globals.sa_prefix_emp then
    let (hp0,args0,f0) = List.hd pdefs in
    let r,non_r_args = List.hd args0, List.tl args0  in
    let fixn = CF.formula_of_heap CF.HEmp no_pos in
    CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None fixn None no_pos,[]
  else
  let hp,def,n_unk_hpargs=
    match pdefs with
    | (hp0,args0,f0)::rest ->
      (*normalize*)
      let norm_pdefs = (hp0,args0,f0)::(List.map (norm prog args0) rest) in
      let norm_predefs = List.map (norm prog args0) predefs in
      let norm_fs0 = (List.map (fun (_,_,f) -> f) norm_pdefs) in
      let norm_fs = shape_gist prog hp0 args0 skip_hps (List.map (fun (_,_,f) -> f) norm_predefs) norm_fs0 in
      let r,non_r_args = Sautil.find_root prog (hp0::skip_hps) args0 norm_fs in
      let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
      (*now assume base_fs =[] and dep_fs = [] and rec_fs != [] *)
      (* if (\* base_fs =[] && *\) dep_fs = [] then *)
      (*init*)
      let fix0, n_unk_hpargs = gfp_gen_init prog is_pre r (base_fs@dep_fs) rec_fs in
      (*iterate*)
      let fixn = gfp_iter prog base_fs rec_fs fix0 in
      (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None fixn None (CF.pos_of_formula f0), n_unk_hpargs)
    (* else *)
    (* report_error no_pos "sac.compute gfp: not support yet" *)

    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let () = Debug.info_ihprint ( add_str "    synthesize (gfp) " !CP.print_sv) hp no_pos in
  let () = Debug.info_ihprint (add_str "" Cprinter.string_of_hp_rel_def_short) def no_pos in
  (def,n_unk_hpargs)

let compute_gfp prog is_pre is predefined_pdefs pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = pr_pair Cprinter.string_of_hp_rel_def (pr_list (pr_pair !CP.print_sv pr1)) in
  Debug.no_2 "compute_gfp" pr3 pr3 pr4
    (fun _ _ -> compute_gfp_x prog is_pre is predefined_pdefs pdefs) predefined_pdefs pdefs

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
        let b, nfs = Sautil.simplify_disj prog hp1 args unk_hps unk_svl f1 f2 pos in
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


let lfp_iter_x prog defs step hp args dang_hps fix_0 nonrec_fs rec_fs=
  (* let other_pdefs = *)
  (*   List.fold_left (fun r def -> *)
  (*       match def.CF.def_cat with *)
  (*         | CP.HPRelDefn _ -> *)
  (*               let hp1,args1 = CF.extract_HRel def.CF.def_lhs in *)
  (*               r@[(List.fold_left (fun r (f, og) -> *)
  (*                   r@List.map (fun f1 -> (hp1, args1, og, f1, [])) (CF.list_of_disjs f) *)
  (*               ) [] def.CF.def_rhs)] *)
  (*         | _ -> r *)
  (*   ) [] defs *)
  (* in *)
  (* let check_unfold_check_unsat ((hp3, args3, og3, f, svl) as pf)= *)
  (*   if Sautil.is_unsat f then false else *)
  (*     let succ_hps = CF.get_hp_rel_name_formula f in *)
  (*     let succ_hps1 = List.filter (fun hp2 -> not (CP.mem_svl hp2 dang_hps) && not(CP.eq_spec_var hp hp2)) succ_hps in *)
  (*     if succ_hps1 = [] then true else *)
  (*       let is_substed, fs = Sautil.succ_subst prog other_pdefs dang_hps false pf in *)
  (*       if not is_substed then true else *)
  (*         List.for_all (fun (_,_,_,f1,_) -> not (Sautil.is_unsat f1)) fs *)
  (* in *)
  let apply_fix fix_i r_fs pdef_f=
    let _, fs = if fix_i = [] then (false, []) else
        Sautil.succ_subst prog [fix_i] dang_hps true pdef_f in
    r_fs@(List.filter (fun ((_,_,_,f,_) )->
        not (Sautil.is_unsat f)
        (* check_unfold_check_unsat pf *)
      ) fs)
  in
  let pdef_rec_fs = List.map (fun f -> (hp,args, None, f, [])) rec_fs in
  let pdef_nonrec_fs = List.map (fun f -> (hp,args, None, f, [])) nonrec_fs in
  (*INTERNAL*)
  let rec rec_helper i pdef_fix_i=
    (**********PRINTING***********)
    let () = Debug.info_ihprint (add_str ("   fix: " ^ (string_of_int i) ^ (
        let pr1  = Cprinter.prtt_string_of_formula in
        let fs = List.map (fun (_,_, _, f, _) -> f) pdef_fix_i in
        let f = if fs = [] then CF.mkFalse (CF.mkTrueFlow ())  no_pos else (CF.formula_of_disjuncts fs) in
        pr1 f )
      ) pr_id) "" no_pos
    in
    (*******END PRINTING*********)
    (*apply rec for cur fix*)
    let n_pdefs = (List.fold_left (apply_fix pdef_fix_i) [] pdef_rec_fs) in
    let n_pdefs1 = Gen.BList.remove_dups_eq (fun (_, args1, _, f1, _) (_, args2, _, f2,_) ->
        let ss = List.combine args1 args2 in
        Sautil.check_relaxeq_formula args2 (x_add CF.subst ss f1) f2
      ) n_pdefs in
    let fix_i_plus0 = pdef_nonrec_fs@n_pdefs1 in
    let fix_i_plus = shape_widening prog hp args dang_hps fix_i_plus0 no_pos in
    (*check whether it reaches the fixpoint*)
    (* let fix_i_plus1 = Gen.BList.remove_dups_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) -> *)
    (*     Sautil.check_relaxeq_formula args f1 f2) fix_i_plus in *)
    let fix_i_plus1 = simplify_disj_set prog args dang_hps [] fix_i_plus no_pos in
    let diff = Gen.BList.difference_eq (fun (_,_, _, f1, _) (_,_, _, f2, _) ->
        Sautil.check_relaxeq_formula args f1 f2) fix_i_plus1 pdef_fix_i in
    (* let rec_helper pdef_fix_i= *)
    (*   let pr1 (_,_, _, f, _) = Cprinter.prtt_string_of_formula f in *)
    (*   let pr2 = pr_list_ln pr1 in *)
    (*   Debug.no_1 "rec_helper" pr2 pr2 *)
    (*       (fun _ -> rec_helper_x pdef_fix_i) pdef_fix_i *)
    (* in *)
    (*recusive call*)
    if diff = [] || i> (!sa_fix_bound) then fix_i_plus1 else
      rec_helper (i+1) fix_i_plus1
  in
  (*END INTERNAL*)
  let pdef_fix_0 = List.map (fun f -> (hp,args, None, f, [])) fix_0 in
  let r = rec_helper step pdef_fix_0 in
  List.map (fun (_,_, _, f, _) -> f) r

let lfp_iter prog defs step hp args dang_hps fix_0 nonrec_fs rec_fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_5 "lfp_iter" !CP.print_sv !CP.print_svl pr1 pr1 pr1 pr1
    (fun _ _ _ _ _ -> lfp_iter_x prog defs step hp args dang_hps fix_0 nonrec_fs rec_fs)
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
  | CF.DataNode dn ->
    if not (CP.eq_spec_var dn.CF.h_formula_data_node r) then
      if List.exists (fun (sv1,sv2) -> (CP.eq_spec_var dn.CF.h_formula_data_node sv1 && 
                                        CP.eq_spec_var sv2 r) || (CP.eq_spec_var dn.CF.h_formula_data_node sv2 && 
                                                                  CP.eq_spec_var sv1 r)) ss then
        CF.DataNode {dn with CF.h_formula_data_node = r}
      else hf
    else hf
  | _ -> hf

let elim_diverg_paras_x prog pdefs=
  (*******INTERNAL*******)
  let find_diverg_paras (hp,args,f)=
    let ls_rec_hpars = List.filter (fun (hp1,_) -> CP.eq_spec_var hp hp1) (CF.get_HRels_f f) in
    let f1, _ = CF.drop_hrel_f f [hp] in
    let svl = CF.get_ptrs_w_args_f  ~en_pure_field:false f1 in
    let ( _,mf,_,_,_,_) = CF.split_components f in
    let eqNulls = MCP.get_null_ptrs mf in
    let eqs = (MCP.ptr_equations_without_null mf) in
    let may_reach_ptrs = CP.remove_dups_svl ((svl@eqNulls@args)@(CF.find_close (svl@eqNulls@args) eqs)) in
    let diverg_pos = List.fold_left (fun acc (_,rec_args) ->
        let diverg_args = CP.diff_svl rec_args may_reach_ptrs in
        let pos = Sautil.get_all_locs rec_args diverg_args in
        pos@acc
      ) [] ls_rec_hpars in
    diverg_pos
    (* x_add CF.subst  *)
  in
  let elim_diverg_paras_pdef diver_pos (hp,args,f)=
    let ( _,mf,_,_,_,_) = CF.split_components f in
    let ls_rec_hpars = List.filter (fun (hp1,_) -> CP.eq_spec_var hp hp1) (CF.get_HRels_f f) in
    let eqs = (MCP.ptr_equations_without_null mf) in
    let diverg_svl0 = List.fold_left (fun r (_,args) ->
        r@(Sautil.retrieve_args_from_locs args diver_pos)
      ) [] ((hp,args)::ls_rec_hpars) in
    let diverg_svl1a = CP.remove_dups_svl diverg_svl0 in
    let () = Debug.ninfo_hprint (add_str  "diverg_svl1a " (!CP.print_svl)) diverg_svl1a no_pos in
    let non_diverg_svl = CP.diff_svl args diverg_svl1a in
    let diverg_svl1 = CP.diff_svl diverg_svl1a (CF.find_close non_diverg_svl eqs) in
    let diver_eqs = List.fold_left (fun r (sv1,sv2) ->
        let b1 = CP.mem_svl sv1 diverg_svl1 in
        let b2 = CP.mem_svl sv2 diverg_svl1 in
        match b1,b2 with
        | true,false -> r@[(sv1,sv2)]
        | false,true -> r@[(sv2,sv1)]
        | _ -> r
      ) [] eqs in
    (hp,args, x_add_1 CF.simplify_pure_f_old (x_add CF.subst diver_eqs f))
  in
  (*******END INTERNAL*******)
  let diverg_pos = List.fold_left (fun acc pdef -> acc@(find_diverg_paras pdef)) [] pdefs in
  let diverg_pos1 = Gen.BList.remove_dups_eq (fun i1 i2 -> i1=i2) diverg_pos in
  let () = Debug.ninfo_hprint (add_str  "diverg_pos " (pr_list string_of_int)) diverg_pos no_pos in
  List.map ( elim_diverg_paras_pdef diverg_pos1) pdefs

let elim_diverg_paras prog pdefs=
  let pr1 (_,_,f) = Cprinter.prtt_string_of_formula f in
  Debug.no_1 "elim_diverg_paras" (pr_list_ln pr1) (pr_list_ln pr1)
    (fun _ -> elim_diverg_paras_x prog pdefs) pdefs


let compute_lfp_x prog dang_hps defs pdefs=
  (********INTERNAL*******)
  let mk_exp_root_x hp r f =
    let _, mf, _, _, _, _ = CF.split_components f in
    let ss = MCP.ptr_equations_without_null mf in
    (CF.trans_heap (mk_expl_root_fnc hp ss r) f)
  in
  let mk_exp_root hp r f =
    let pr1 = Cprinter.prtt_string_of_formula in
    Debug.no_2 "mk_exp_root" !CP.print_sv pr1 pr1
      (fun _ _ -> mk_exp_root_x hp r f) r f
  in
  let skip_hps = dang_hps in
  (* let poss_widening dep_f = *)
  (* in *)
  (********END INTERNAL*******)
  let hp,def=
    match pdefs with
    | [(hp0,args0,f0)] ->
      let r,non_r_args = Sautil.find_root prog (hp0::skip_hps) args0 [f0] in
      (hp0, CF.mk_hp_rel_def hp0 (args0, r, non_r_args) None f0 None (CF.pos_of_formula f0))
    | (hp0,args0,f0)::rest ->
      let pos = CF.pos_of_formula f0 in
      (*normalize*)
      let norm_pdefs0 = (hp0,args0,f0)::(List.map (norm prog args0) rest) in
      let norm_pdefs1 = elim_diverg_paras prog  norm_pdefs0 in
      let norm_pdefs = List.fold_left (fun r (hp1,args1,f1) ->
          let f12, _ = CF.drop_hrel_f f1 [hp1] in
          let f13 = CF.remove_neqNulls_f (Sautil.elim_irr_eq_exps prog args1 f12) in
          if Sautil.is_empty_f f13 then
            r
          else r@[(hp1,args1,f1)]
        ) [] norm_pdefs1 in
      let norm_fs0 = (List.map (fun (_,_,f) -> f) norm_pdefs) in
      let r,non_r_args = Sautil.find_root prog (hp0::skip_hps) args0 norm_fs0 in
      let norm_fs = List.map (mk_exp_root hp0 r) norm_fs0 in
      (* let () =  Debug.info_pprint ("   r: " ^(!CP.print_sv r)) no_pos in *)
      (**********PRINTING***********)
      let () = Debug.info_ihprint (add_str ("   Initial recurrence: "  ^
                                            ((!CP.print_sv hp0) ^ "(" ^(!CP.print_svl args0) ^") ==>") ^
                                            (
                                              let pr1  = Cprinter.prtt_string_of_formula in
                                              let f = (CF.formula_of_disjuncts norm_fs) in
                                              pr1 f
                                            )) pr_id ) "" no_pos
      in
      (*******END PRINTING*********)
      let base_fs, rec_fs, dep_fs = List.fold_left (classify hp0) ([],[],[]) norm_fs in
      (*init*)
      let fix_0 = (* (base_fs@dep_fs) *) [] in
      (*iterate*)
      let fixn = lfp_iter prog defs 0 hp0 args0 skip_hps fix_0 (base_fs@dep_fs) rec_fs in
      (* let def = CF.formula_of_disjuncts fixn in *)
      let def0,is_diver = List.fold_left (fun (acc,acc_diver) f ->
          let hps = CF.get_hp_rel_name_formula f in
          acc@[(f,None)], acc_diver||(CP.mem_svl hp0 hps)
        ) ([],false) fixn in
      let def = if is_diver then 
          [((CF.mkBase CF.HTrue (MCP.mkMTrue no_pos) CvpermUtils.empty_vperm_sets 
               CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos ), None)] else def0 in
      let lhs = CF.HRel (hp0, List.map (fun x -> CP.mkVar x pos) args0, pos) in
      (hp0, CF.mk_hp_rel_def1 (CP.HPRelDefn (hp0, r, non_r_args)) lhs def None)
    | [] -> report_error no_pos "sac.compute gfp: sth wrong"
  in
  let () = Debug.info_ihprint ( add_str "    synthesize (lfp): " !CP.print_sv) hp no_pos in
  let () = Debug.info_ihprint (add_str "" Cprinter.string_of_hp_rel_def_short) def no_pos in
  def

let compute_lfp prog dang_hps defs pdefs=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 pr2) in
  let pr4 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "compute_lfp" pr3 pr4
    (fun _ -> compute_lfp_x prog dang_hps defs pdefs) pdefs


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
            not (Sautil.eq_spec_var_order_list args args1)
          else false
        ) hrels
  in
  let process_one_grp grp=
    match grp with
    | hp_def::_ -> begin
        match hp_def.CF.def_cat with
        | CP.HPRelDefn (hp, r, paras) ->
          if CP.mem_svl hp post_hps then
            let pdefs = List.map (fun def1 ->
                let f = CF.disj_of_list (List.map fst def1.CF.def_rhs) no_pos in
                let _,args = CF.extract_HRel def1.CF.def_lhs in
                (hp, args, f)
              ) grp in
            if List.length pdefs > 1 then
              if List.exists (fun (hp, args, f) -> is_post_fix hp args f) pdefs then
                (true, [(compute_lfp prog dang_hps hp_defs pdefs)])
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
          let n_hpdef = {hpdef with CF.hprel_def_body = List.map (fun f -> ([], Some f, None)) new_fs;
                                    CF.hprel_def_body_lib = [];
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
    | (def):: rest ->
      begin
        match def.CF.def_cat with
        | CP.HPRelDefn (hp, r, paras) ->
          let grp, rest1, n_non_post_defs = List.fold_left (fun (ls1,ls2, ls3) def1 ->
              match def1.CF.def_cat with
              | CP.HPRelDefn (hp1, _, _) ->
                if CP.eq_spec_var hp hp1 then
                  (ls1@[def1],ls2, ls3)
                else (ls1,ls2@[def1], ls3)
              | _ -> (ls1,ls2, ls3@[def1])
            ) ([], [], []) rest in
          partition_helper rest1 (grps@[(def::grp)]) (non_post_defs@n_non_post_defs)
        | _ -> partition_helper rest grps (non_post_defs@[(def)])
      end
  in
  let unify_disjuncts (r_grp, r_hpdefs) grp=
    match grp with
    | [] -> (r_grp,r_hpdefs)
    | [x] ->  (r_grp@[grp],r_hpdefs)
    | def::_ -> begin
        match def.CF.def_cat with
        | CP.HPRelDefn (hp, r, paras) ->
          let grp1 = Gen.BList.remove_dups_eq (fun def1 def2 ->
              let _, args1 = CF.extract_HRel def1.CF.def_lhs in
              let _, args2 = CF.extract_HRel def2.CF.def_lhs in
              let ss = List.combine args1 args2 in
              Sautil.check_relaxeq_formula args2
                (x_add CF.subst ss (CF.disj_of_list (List.map fst def1.CF.def_rhs) no_pos))
                (CF.disj_of_list (List.map fst def2.CF.def_rhs) no_pos)
            ) grp in
          if List.length grp1 < List.length grp then
            let n_hpdefs = update r_hpdefs hp (List.fold_left (fun ls def ->
                ls@(List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] def.CF.def_rhs)) [] grp1) [] in
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
  (* let () =  Debug.info_pprint ("   grp_hp_defs0: " ^(pr1 grp_hp_defs0)) no_pos in *)
  (* let () =  Debug.info_pprint ("   grp_hp_defs: " ^(pr1 grp_hp_defs)) no_pos in *)
  let n_hp_defs, n_hpdefs = List.fold_left (fun (r_hp_defs, r_hpdefs) hp_defs ->
      let r, grp = process_one_grp hp_defs in
      if r then
        (*if success, fold in one*)
        let def = List.hd grp in
        let fs,ogs = List.split def.CF.def_rhs in
        let n_hpdefs = update r_hpdefs (CF.get_hpdef_name def.CF.def_cat) fs [] in
        (r_hp_defs@[def], n_hpdefs)
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
let pred_split_cands_one_branch_x prog unk_hps hprel f=
  (*******************INTERNAL************************)
  (*partition args into dependent groups*)
  let do_partition hns hvs p eqs args=
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
        let part2 = CF.look_up_reachable_ptr_args prog hns hvs (CP.remove_dups_svl part1) in
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
  let group_helper cur_parts args_part=
    let parts1 = List.map (fun args ->
        let args1 = List.fold_left (fun r svl -> if CP.intersect_svl r svl != [] then (r@svl) else r) args args_part in
        CP.remove_dups_svl args1
      ) cur_parts in
    let parts2 = Gen.BList.remove_dups_eq (fun ls1 ls2 -> CP.diff_svl ls1 ls2 = []) parts1 in
    parts2
  in
  let acc_alias_from_eq_pairs tpl0 eqs=
    List.fold_left (fun tpl (sv1,sv2) -> CP.add_equiv_eq tpl sv1 sv2) tpl0 eqs
  in
  (*ls_eqs: all svs in this list are aliasing*)
  let rec acc_alias_from_eq_list tpl0 ls_eqs=
    match ls_eqs with
    | [] -> tpl0
    | sv::rest ->
      let eqs = List.map (fun sv2 -> (sv,sv2)) rest in
      let n_tpl =  acc_alias_from_eq_pairs tpl0 eqs in
      acc_alias_from_eq_list n_tpl rest
  in
  let rec partition_args_aset args tpl res=
    match args with
    | sv::rest -> let lst_eq_sv = CP.EMapSV.find_equiv_all sv tpl in
      let inter_rest,rest2 = List.partition (fun sv2 -> CP.mem_svl sv2 lst_eq_sv) rest in
      let n_res = if inter_rest = [] then res else
          res@[sv::inter_rest]
      in
      partition_args_aset rest2 tpl n_res
    | [] -> res
  in
  let build_args_aset args eqs eqNulls=
    let tpl_aset = CP.EMapSV.mkEmpty in
    let tpl_aset1 = acc_alias_from_eq_pairs tpl_aset eqs in
    let tpl_aset2 = acc_alias_from_eq_list tpl_aset1 eqNulls in
    partition_args_aset args tpl_aset2 []
  in
  (*******************END INTERNAL************************)
  let hns, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mf,_,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs mf) in
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
      let parts = do_partition hns hvs (MCP.pure_of_mix mf) eqs args in
      (*look_up hp partition*)
      let arg_parts_pos = Cast.look_up_hp_parts prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
      let parts1 = if arg_parts_pos = [] then parts else
          (*from pos to var*)
          let arg_parts = List.map (fun ls_pos -> CF.retrieve_args_from_locs args ls_pos) arg_parts_pos in
          let parts2 = group_helper parts arg_parts in
          match parts2 with
          | [args0] -> if List.length args0 = List.length args then []
            else parts2
          | _ -> parts2
      in
      (*build aliasing info*)
      let lst_aset = build_args_aset args eqs eqNulls in
      (hp,args, List.filter (fun svl -> CP.diff_svl svl unk_args <> []) parts1,l, lst_aset)
    ) cands1
  in
  (cands2)

let pred_split_cands_one_branch prog unk_hps hprel f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 (hp,_,_) = !CP.print_sv hp in
  let pr3 = pr_list_ln (pr_penta !CP.print_sv !CP.print_svl
                          (pr_list !CP.print_svl) string_of_full_loc (pr_list !CP.print_svl)) in
  Debug.no_2 "pred_split_cands_one_branch" pr2 pr1 pr3
    (fun _ _ ->  pred_split_cands_one_branch_x prog unk_hps hprel f)
    hprel f

let pred_split_cands_x prog unk_hps hp_defs=
  (*******INTERNAL*******)
  let rec process_one_pred hrel hp args cands fs=
    match fs with
    | [] -> true, cands
    | f::rest ->
      let n_cands = pred_split_cands_one_branch prog unk_hps hrel f in
      let is_split = List.fold_left (fun b (hp1, args1, parts, _, _) ->
          if CP.eq_spec_var hp hp1 && Sautil.eq_spec_var_order_list args args1 then
            (b && parts <> [])
          else b
        ) true n_cands in
      if not is_split then (false, [])
      else
        process_one_pred hrel hp args (cands@n_cands) rest
  in
  (* let rec remove_dups_cand args cands res= *)
  (*   match cands with *)
  (*     | [] -> res *)
  (*     | (hp1, args1,c,d,e)::rest -> begin *)
  (*         let part,rest1 = List.partition (fun (hp2, _,_,_,_) -> CP.eq_spec_var hp2 hp1 ) rest in *)
  (*         let split_kepts = try *)
  (*           let kept =List.find (fun (_,args2,_,_,_) -> Sautil.eq_spec_var_order_list args args2) ((hp1, args1,c,d,e)::part) in *)
  (*           [kept] *)
  (*         with _ -> [(hp1, args1,c,d,e)] *)
  (*         in *)
  (*         remove_dups_cand args rest1 (res@split_kepts) *)
  (*       end *)
  (* in *)
  (*******END INTERNAL*******)
  let cands, non_split_hps = List.fold_left (fun (r, non_split_hps) def ->
      let hrel, hp, args = match def.CF.def_lhs with
        | CF.HRel ((hp, eargs, _ ) as hrel) ->
          hrel, hp , List.concat (List.map CP.afv eargs)
        | _ -> report_error no_pos "SAC.pred_split_cands"
      in
      let fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] def.CF.def_rhs in
      let to_split, n_cands =  process_one_pred hrel hp args [] fs in
      let n_cands1 = (* remove_dups_cand args n_cands [] *) n_cands in
      (*  Gen.BList.remove_dups_eq  (fun (hp1, args1,_,_) (hp2, args2, _,_) -> *)
      (*     CP.eq_spec_var hp2 hp1 *)
      (* ) n_cands in *)
      if to_split then
        (r@n_cands1, non_split_hps)
      else
        (r, non_split_hps@[hp])
    ) ([],[]) hp_defs
  in
  let non_split_hps1 = non_split_hps@unk_hps in
  let cands1 = List.filter (fun (hp, _,_,_,_) -> not (CP.mem_svl hp non_split_hps1)) cands in
  let cands2 = Gen.BList.remove_dups_eq (fun (hp1, args1,_,_,_) (hp2, args2, _,_,_) ->
      CP.eq_spec_var hp2 hp1 && Sautil.eq_spec_var_order_list args2 args1
    ) cands1 in
  cands2

let pred_split_cands prog unk_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_penta !CP.print_sv !CP.print_svl (pr_list !CP.print_svl)
                          string_of_full_loc (pr_list !CP.print_svl)) in
  Debug.no_2 "pred_split_cands" !CP.print_svl pr1 pr2
    (fun _ _ -> pred_split_cands_x prog unk_hps hp_defs) unk_hps hp_defs

(*split one hp -> mutiple hp and produce corresponding heap formulas for substitution
  - one cand: (hp,args, parts,p)
*)
let check_split_global_x iprog prog cands =
  let rec partition_cands_by_hp_name cands0 parts=
    match cands0 with
    | [] -> parts
    | (hp_name,args, ls_args,p,ls_eqs)::xs ->
      let part,remains= List.partition (fun (hp_name1,_,_,_,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
      partition_cands_by_hp_name remains (parts@[[(hp_name,args,ls_args,p,ls_eqs)]@part])
  in
  (*each partition, create new hp and its corresponding HRel formula*)
  let hp_helper1 pos args =
    let args1 = List.map (fun sv -> (sv,I)) args in
    let hf,new_hp_sv = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog true false args1 pos in
    ((new_hp_sv,args), hf)
  in
  (*each partition, create new rel and its corresponding rel pure formula*)
  let rel_helper pos args =
    let new_rel_sv = Sautil.add_raw_rel prog args pos in
    (*add rel decl in iprog*)
    let irel_decl = { Iast.rel_name = CP.name_of_spec_var new_rel_sv;
                      Iast.rel_typed_vars = List.map (fun (CP.SpecVar (t,id,_)) -> (t,id)) args;
                      Iast.rel_formula = Ipure.mkTrue pos;
                    }
    in
    let () = iprog.Iast.prog_rel_decls <- (irel_decl :: iprog.Iast.prog_rel_decls) in
    let p_rel = CP.mkRel new_rel_sv (List.map (fun sv -> CP.mkVar sv pos) args) pos in
    ((new_rel_sv,args), p_rel)
  in
  (*if two args are aliasing, infer shape of one*)
  let refine_infer_pred ls_eqs args=
    let ls_eq1 = List.fold_left (fun r ls ->
        let inter = CP.intersect_svl args ls in
        if List.length inter > 1 then r@[inter] else r
      ) [] ls_eqs in
    ( List.fold_left (fun r aset ->
         match aset with
         | sv::rest -> CP.diff_svl r rest
         | _ -> r
       ) args ls_eq1)
  in
  (*for each grp*)
  let intersect_cand_one_hp grp=
    let rec parts_norm args0 grp0 res res_eqs=
      match grp0 with
      | [] -> res,res_eqs
      | (_,args1,parts1,_,ls_eqs1)::tl ->
        let ss = List.combine args1 args0 in
        let parts11 = List.map (fun largs -> List.map (CP.subs_one ss) largs) parts1 in
        let ls_eqs11 = List.map (fun largs -> List.map (CP.subs_one ss) largs ) ls_eqs1 in
        parts_norm args0 tl (res@[parts11]) (res_eqs@[ls_eqs11])
    in
    let rec cmp_two_list_args ls_args1 ls_args2=
      match ls_args1,ls_args2 with
      | [],[] -> true
      | args1::tl1,args2::tl2 ->
        if Sautil.eq_spec_var_order_list args1 args2 then
          cmp_two_list_args tl1 tl2
        else false
      | _ -> false
    in
    let (hp,args0,parts0,p0,lst_eqs0)=
      match grp with
      | [] -> report_error no_pos "sa.intersect_cand_one_hp"
      | hd::_ -> hd
    in
    let size = List.length parts0 in
    if size = 0 || List.exists (fun (_,args1,parts1,_,_) -> (List.length parts1)!=size) (List.tl grp) then
      []
    else
      let tl_parts, tl_lst_eqparts = parts_norm args0 (List.tl grp) [] [] in
      if List.for_all (fun part -> cmp_two_list_args parts0 part) tl_parts then
        let lst_eqs = if tl_lst_eqparts = [] then [] else
            List.fold_left (fun lst_eqs1 lst_eqs2 ->
                List.fold_left (fun r svl1 ->
                    if svl1=[] then r else
                      let ls_svl11 = List.map (fun svl2 -> CP.intersect_svl svl1 svl2) lst_eqs2 in
                      let ls_svl12 = List.filter (fun svl -> List.length svl > 1) ls_svl11 in
                      if ls_svl12 = [] then r else r@[(List.hd ls_svl12)]
                  ) [] lst_eqs1
              ) lst_eqs0 tl_lst_eqparts
        in
        [(hp,args0, List.map (refine_infer_pred lst_eqs) parts0,p0,lst_eqs)]
      else []
  in
  (*todo: generalize lst_eqs to lst_pure*)
  let generate_split (hp,args0,parts0,p0, lst_eqs0) =
    let hps = List.map (hp_helper1 p0) parts0 in
    let new_hp_args,new_hrel_fs = List.split hps in
    let rels = List.map (rel_helper p0) lst_eqs0 in
    let new_rel_args,new_rel_ps = List.split rels in
    let new_hrels_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 p0)
        (List.hd new_hrel_fs) (List.tl new_hrel_fs) in
    let new_rel_comb = List.fold_left (fun p1 p -> CP.mkAnd p1 p p0) (CP.mkTrue p0) new_rel_ps in
    let hrel0 = Sautil.mkHRel hp args0 p0 in
    (hp, args0, new_hp_args,new_rel_args, hrel0,new_hrels_comb, new_rel_comb)
  in
  (**************END INTERNAL******************)
  let grps = partition_cands_by_hp_name cands [] in
  (*each group, the partition should be similar*)
  let to_split = List.concat (List.map intersect_cand_one_hp grps) in
  let res = List.map generate_split to_split in
  res

let check_split_global iprog prog cands =
  let pr1 = pr_list_ln (pr_penta !CP.print_sv !CP.print_svl (pr_list !CP.print_svl) string_of_full_loc
                          (pr_list !CP.print_svl)) in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_list_ln (pr_hepta !CP.print_sv !CP.print_svl pr4 pr4 pr2 pr2 !CP.print_formula) in
  Debug.no_1 "check_split_global" pr1 pr3
    (fun _ -> check_split_global_x iprog prog cands) cands

(* ********************************* *************************** *)
(* *********** PRED SPLIT HELPERS *************************** *)
(* ********************************* *************************** *)
let back_up_state iprog cprog ass_stk hpdef_stk =
  let cur_ass = ass_stk# get_stk in
  let () = ass_stk # reset in
  let cur_hpdefs =  hpdef_stk # get_stk in
  let () = hpdef_stk # reset in
  let cur_ihpdcl = iprog.Iast.prog_hp_decls in
  let cur_chpdcl = cprog.Cast.prog_hp_decls in
  let cviews = cprog.Cast.prog_view_decls in
  (cur_ass, cur_hpdefs, cur_ihpdcl, cur_chpdcl, cviews)

let restore_state iprog cprog ass_stk hpdef_stk (cur_ass, cur_hpdefs, cur_ihpdcl, cur_chpdcl, cviews)=
  let () = ass_stk # reset in
  let () = ass_stk # push_list cur_ass in
  let () = hpdef_stk # reset in
  let () = hpdef_stk # push_list cur_hpdefs in
  let idiff = Gen.BList.difference_eq Iast.cmp_hp_def cur_ihpdcl iprog.Iast.prog_hp_decls in
  let () = iprog.Iast.prog_hp_decls <- (iprog.Iast.prog_hp_decls@idiff) in
  let cdiff = Gen.BList.difference_eq Cast.cmp_hp_def cur_chpdcl cprog.Cast.prog_hp_decls in
  let () = cprog.Cast.prog_hp_decls <- (cprog.Cast.prog_hp_decls@cdiff) in
  let () = cprog.Cast.prog_view_decls <- cviews in
  ()

let prove_right_implication_x iprog cprog proc_name infer_rel_svl lhs rhs gen_hp_defs=
  (*do unfold the rhs*)
  (* let pr_hp_defs = List.map (fun hp_def -> *)
  (*     let hp,args = CF.extract_HRel hp_def.CF.def_lhs in *)
  (*     (hp, hp_def, args) *)
  (* ) gen_hp_defs in *)
  (* let rhs1 = CF.do_unfold_hp_def cprog pr_hp_defs rhs in *)
  let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog cprog proc_name gen_hp_defs in
  let rhs2 = Saout.trans_formula_hp_2_view iprog cprog proc_name chprels_decl gen_hp_defs [] rhs in
  (* let (valid, _, _) = x_add Sleekcore.sleek_entail_check [] cprog [] rhs2 (CF.struc_formula_of_formula lhs no_pos) in *)
  (*iformula to construct lemma*)
  let ilhs = Rev_ast.rev_trans_formula lhs in
  let irhs = Rev_ast.rev_trans_formula rhs2 in
  let () = Debug.ninfo_hprint (add_str  "ilhs " Iprinter.string_of_formula) ilhs no_pos in
  let () = Debug.ninfo_hprint (add_str  "irhs " Iprinter.string_of_formula) irhs no_pos in
  (*construct lemma_safe*)
  let ilemma_inf = Iast.mk_lemma (fresh_any_name "tmp_safe") LEM_UNSAFE LEM_GEN Iast.Right
      (List.map CP.name_of_spec_var infer_rel_svl) (IF.add_quantifiers [] ilhs) (IF.add_quantifiers [] irhs) in
  let () = Debug.info_hprint (add_str "\nRight. ilemma_infs:\n " (Iprinter.string_of_coerc_decl)) ilemma_inf no_pos in
  let rel_fixs,_, lc_opt = Lemma.manage_infer_pred_lemmas [ilemma_inf] iprog cprog (x_add Cvutil.xpure_heap) in
  (* let lc_opt = Lemma.sa_infer_lemmas iprog cprog [ilemma_inf] in *)
  let valid, n_rhs = match lc_opt with
    | Some lcs -> begin
        if infer_rel_svl = [] then (true, rhs) else
          (* let oblgs = List.fold_left (fun r_ass lc -> r_ass@(Infer.collect_rel_list_context lc)) [] lcs in *)
          (* let r = Lemma.preprocess_fixpoint_computation cprog Solver.xpure_heap rhs oblgs infer_rel_svl [] in *)
          let ls_rel_args = CF.get_list_rel_args rhs in
          let rel_p = List.fold_left (fun p (post_rel, post_p, pre_rel, pre_p) ->
              (*normalize the paras (convert back to the orig)*)
              let rel_args_opt = CP.get_relargs_opt pre_rel in
              let pre_p1 =
                match rel_args_opt with
                | Some (rel,args) -> begin
                    try
                      let _,args0 = List.find (fun (rel1,_) -> CP.eq_spec_var rel rel1) ls_rel_args in
                      let ss0 = List.combine args args0 in
                      CP.subst ss0 pre_p
                    with _ -> pre_p
                  end
                | None -> pre_p
              in
              CP.mkAnd p pre_p1 no_pos
            ) (CP.mkTrue no_pos) rel_fixs in
          let rhs1 = CF.drop_sel_rel infer_rel_svl rhs in
          let rhs2 = CF.mkAnd_pure rhs1 (MCP.mix_of_pure rel_p) no_pos in
          (true, rhs2)
      end
    | None -> false, rhs
  in
  valid, n_rhs

let prove_right_implication iprog cprog proc_name infer_rel_svl lhs rhs gen_hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = Cprinter.prtt_string_of_formula in
  Debug.no_4 "prove_right_implication" !CP.print_svl pr2 pr2 pr1 (pr_pair string_of_bool pr2)
    (fun _ _ _ _ -> prove_right_implication_x iprog cprog proc_name infer_rel_svl lhs rhs gen_hp_defs)
    infer_rel_svl lhs rhs gen_hp_defs

(*normalize parameters of each hp_def like in rhs *)
let normalize_hp_defs_x rhs hp_defs=
  let norm_one ls_hpargs hp_def=
    try
      let hp,args = CF.extract_HRel hp_def.CF.def_lhs in
      let _,norm_args = List.find (fun (hp1,_) -> CP.eq_spec_var hp hp1) ls_hpargs in
      let ss0 = List.combine args norm_args in
      match hp_def.CF.def_cat with
      | CP.HPRelDefn (hp, r,paras) ->
        let nr = CP.subs_one ss0 r in
        let nparas = CP.subst_var_list ss0 paras in
        let n_lhs = CF.h_subst ss0 hp_def.CF.def_lhs in
        let n_rhs = List.map (fun (f,og) -> (x_add CF.subst ss0 f,og)) hp_def.CF.def_rhs in
        { hp_def with CF.def_cat = CP.HPRelDefn (hp, nr, nparas);
                      CF.def_lhs = n_lhs;
                      CF.def_rhs = n_rhs;
        }
      | _ -> hp_def
    with _ -> hp_def
  in
  let ls_hpargs = CF.get_HRels_f rhs in
  List.map (norm_one ls_hpargs) hp_defs


let normalize_hp_defs rhs hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = Cprinter.prtt_string_of_formula in
  Debug.no_2 "normalize_hp_defs" pr2 pr1 pr1
    (fun _ _ -> normalize_hp_defs_x rhs hp_defs)
    rhs hp_defs

(*
    output:
    0: fail two ways            1: succ left, fail right
    2: succ right, fail left    3: succ
    ---------
    list of split preds (1,2,3)
  *)
let prove_sem iprog cprog proc_name ass_stk hpdef_stk hp args
    infer_hps infer_split_rels infer_rel_svl rhs_f cur_hpdef cur_split_hpdefs old_ext_num=
  let need_find_new_split = cur_split_hpdefs =[] in
  let isettings = back_up_state iprog cprog ass_stk hpdef_stk in
  let () = Debug.ninfo_hprint (add_str " cur_hpdef (sem)"  Cprinter.string_of_hp_rel_def) cur_hpdef no_pos in
  let r,paras = match cur_hpdef.CF.def_cat with
    | CP.HPRelDefn (hp,r, paras) -> Cast.get_root_args_hprel cprog.Cast.prog_hp_decls (CP.name_of_spec_var hp) args (*(r,paras)*)
    | _ -> report_error no_pos "SAC.prove_sem: support single hpdef only"
  in
  (*transform to view*)
  let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog cprog proc_name (* [cur_hpdef] *) (cur_hpdef::cur_split_hpdefs) in
  (*trans_hp_view_formula*)
  (* let f12 = Sautil.trans_formula_hp_2_view iprog cprog proc_name chprels_decl [cur_hpdef] f in *)
  (*lemma need self for root*)
  let self_sv = CP.SpecVar (CP.type_of_spec_var r,self, Unprimed) in
  let vnode = CF.mkViewNode self_sv (CP.name_of_spec_var hp) paras no_pos in
  let f12 = CF.formula_of_heap vnode no_pos in
  let f22_0 = Saout.trans_formula_hp_2_view iprog cprog proc_name chprels_decl (* [cur_hpdef] *)(cur_hpdef::cur_split_hpdefs) [] rhs_f in
  (*need self for lemma*)
  let sst = [(r, self_sv)] in
  let rev_sst = [(self_sv,r)] in (*to revert the result*)
  (* let f12 = x_add CF.subst sst f12_0 in *)
  let f22 = x_add CF.subst sst f22_0 in
  let () = Debug.ninfo_hprint (add_str  "f12 " Cprinter.prtt_string_of_formula) f12 no_pos in
  let () = Debug.ninfo_hprint (add_str  "f22 " Cprinter.prtt_string_of_formula) f22 no_pos in
  (*iformula to construct lemma*)
  let if12 = Rev_ast.rev_trans_formula f12 in
  let if22 = Rev_ast.rev_trans_formula f22 in
  let () = Debug.ninfo_hprint (add_str  "if12 " Iprinter.string_of_formula) if12 no_pos in
  let () = Debug.ninfo_hprint (add_str  "if22 " Iprinter.string_of_formula) if22 no_pos in
  (*prove*)
  (*construct lemma_infer*)
  let infer_vars = if need_find_new_split then (List.map CP.name_of_spec_var (infer_hps@infer_split_rels))
    else ((List.map CP.name_of_spec_var infer_rel_svl))
  in
  let () = Debug.ninfo_hprint (add_str  "infer_vars " (pr_list pr_id)) infer_vars no_pos in
  let () = Debug.ninfo_hprint (add_str  "need_find_new_split " (string_of_bool)) need_find_new_split no_pos in
  let ilemma_inf = Iast.mk_lemma (fresh_any_name "tmp_infer") LEM_UNSAFE LEM_GEN
      Iast.Left
      infer_vars (IF.add_quantifiers [] if12) (IF.add_quantifiers [] if22) in
  let () = Debug.info_hprint (add_str "\nilemma_infs:\n " (Iprinter.string_of_coerc_decl)) ilemma_inf no_pos in
  (*L2: old*)
  (* let lc_opt = Lemma.sa_infer_lemmas iprog cprog [ilemma_inf] in *)
  let rel_fixs,hp_defs0, lc_opt = Lemma.manage_infer_pred_lemmas [ilemma_inf] iprog cprog (x_add Cvutil.xpure_heap) in
  let r =
    match lc_opt with
    | Some lcs ->
      let b,comp_hp_defs =
        let hp_defs, f23 = if not need_find_new_split then cur_split_hpdefs, f22 else
            (*L2: old*)
            (* let hprels = List.fold_left (fun r_ass lc -> r_ass@(Infer.collect_hp_rel_list_context lc)) [] lcs in *)
            (* let (_,hp_rest) = List.partition (fun hp -> *)
            (*     match hp.CF.hprel_kind with *)
            (*       | CP.RelDefn _ -> true *)
            (*       | _ -> false *)
            (* ) hprels *)
            (* in *)
            (* let (hp_lst_assume,(\* hp_rest *\)_) = List.partition (fun hp -> *)
            (*     match hp.CF.hprel_kind with *)
            (*       | CP.RelAssume _ -> true *)
            (*       | _ -> false *)
            (* ) hp_rest *)
            (* in *)
            (* let _, hp_defs = !Lemma.infer_shapes iprog cprog "temp" hp_lst_assume infer_hps infer_hps *)
            (* [] [] [] true true in *)
            let rhs_f1,f23 = if infer_split_rels = [] then rhs_f,f22 else
                let ls_rel_args = CF.get_list_rel_args rhs_f in
                let rel_p = List.fold_left (fun p (post_rel, post_p, pre_rel, pre_p) ->
                    (*normalize the paras (convert back to the orig)*)
                    let rel_args_opt = CP.get_relargs_opt post_rel in
                    let post_p1 =
                      match rel_args_opt with
                      | Some (rel,args) -> begin
                          try
                            let _,args0 = List.find (fun (rel1,_) -> CP.eq_spec_var rel rel1) ls_rel_args in
                            let ss0 = List.combine args args0 in
                            CP.subst ss0 post_p
                          with _ -> post_p
                        end
                      | None -> post_p
                    in
                    let () = Debug.ninfo_hprint (add_str "post_p1:\n " (!CP.print_formula)) post_p1 no_pos in
                    CP.mkAnd p post_p1 no_pos
                  ) (CP.mkTrue no_pos) rel_fixs in
                let rhs_f2 = CF.drop_sel_rel infer_rel_svl rhs_f in
                let nrhs = CF.mkAnd_pure rhs_f2 (MCP.mix_of_pure rel_p) no_pos in
                let f23a = CF.drop_sel_rel infer_rel_svl f22 in
                let f23b = CF.mkAnd_pure f23a (MCP.mix_of_pure (CP.subst sst rel_p)) no_pos in
                (nrhs, f23b)
            in
            (*normalize args of hp_defs for next rounds (with pure)*)
            (normalize_hp_defs rhs_f1 hp_defs0, f23)
        in
        (*we need to prove if12 <=== if22: zip example*)
        let is_implied, n_rhs = prove_right_implication iprog cprog proc_name infer_rel_svl f12 f23 hp_defs in
        if not is_implied then
          let () = print_endline_quiet (" can not pred_split (sem). add lemma: " ^ (!CP.print_sv hp) ^ "(" ^ (!CP.print_svl args) ^ ") --> " ^
                                        (Cprinter.prtt_string_of_formula rhs_f)) in
          (1, hp_defs)
        else
          (*susbt self to the orginal*)
          let n_rhs1 = x_add CF.subst rev_sst (Saout.trans_formula_view_2_hp iprog cprog proc_name
                                           (List.map (fun sv -> CP.name_of_spec_var sv) infer_hps) n_rhs) in
          let ogs = List.map snd cur_hpdef.CF.def_rhs in
          let n_hp_def = {cur_hpdef with CF.def_rhs = [(n_rhs1 , CF.combine_guard ogs)]} in
          let () = print_endline_quiet (" pred_split (sem):" ^ (!CP.print_sv hp) ^ "(" ^ (!CP.print_svl args) ^ ") :== " ^
                                        (Cprinter.prtt_string_of_formula n_rhs1)) in
          (3,n_hp_def::hp_defs)
      in
      (*todo: remove map also*)
      b,comp_hp_defs, (List.fold_left (fun r (post_rel,post_f,_,_) ->
          if not (CP.isConstFalse post_f || CP.isConstTrue post_f) then
            r@[(post_rel,post_f)]
          else r
        ) [] rel_fixs)
    | None -> 0,[],[]
  in
  let () = restore_state iprog cprog ass_stk hpdef_stk isettings in
  r

(* ********************************* *************************** *)
(* *********** END PRED SPLIT HELPERS *************************** *)
(* ********************************* *************************** *)

let pred_split_ext iprog cprog proc_name ass_stk hpdef_stk
    ((hp, args, comps, pure_comps, lhs_hf, rhs_hf0, rhs_rel_pure0) as old_split) cur_hpdef=
  (****************************************************************)
  (*************************INTERNAL*********************)
  (****************************************************************)
  let size_ext_hpdef hpdef=
    (*look up the view size extn*)
    let view_exts = Cast.look_up_view_def_ext_size cprog.Cast.prog_view_decls 1 1 in
    match view_exts with
    | [] -> let hp,args = CF.extract_HRel hpdef.CF.def_lhs in
      (hp, hpdef.CF.def_lhs , [], hpdef)
    | ext_v::_ ->
      let extn_arg = fresh_any_name Globals.size_rel_arg in
      let ext_sv = CP.SpecVar (Int , extn_arg ,Unprimed) in
      let hp,args = CF.extract_HRel hpdef.CF.def_lhs in
      let () =  Debug.ninfo_hprint (add_str "  args: " !CP.print_svl) args no_pos in
      (* let n_hp = CP.fresh_spec_var hp in *)
      let n_args = args@[ext_sv] in
      let n_lhs, n_hp = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) cprog true false (List.map (fun sv ->
          if CP.is_node_typ sv then (sv,I) else (sv,NI)) n_args) no_pos in
      (*new declaration for cprog*)
      let n_hpcl = Cast.look_up_hp_def_raw cprog.Cast.prog_hp_decls (CP.name_of_spec_var n_hp) in
      (*new declaration for iprog*)
      let todo_unk = Iast.mkhp_decl iprog n_hpcl.Cast.hp_name
          (List.map (fun (CP.SpecVar (t,id,_) ,ins) -> (t,id, ins)) n_hpcl.Cast.hp_vars_inst)
          n_hpcl.Cast.hp_part_vars n_hpcl.Cast.hp_root_pos n_hpcl.Cast.hp_is_pre (IF.mkTrue IF.n_flow no_pos)
      in
      let orig_pred_name = CP.name_of_spec_var hp in
      let extn_view_name = ext_v.Cast.view_name in
      let root_pos = x_add Cast.get_proot_hp_def_raw cprog.Cast.prog_hp_decls orig_pred_name in
      let data_name = Cast.get_root_typ_hprel cprog.Cast.prog_hp_decls orig_pred_name in
      let extn_props = Cast.look_up_extn_info_rec_field cprog.Cast.prog_data_decls data_name in
      (* let extn_props = [("REC")] in *)
      let extn_info = [((orig_pred_name,List.map CP.name_of_spec_var args),(extn_view_name, extn_props , [extn_arg] ), [root_pos])] in
      let n_rhs = Predicate.extend_pred_dervs iprog cprog [hpdef] n_hp n_args extn_info in
      (* let n_lhs = CF.HRel (n_hp, List.map (fun x -> CP.mkVar x no_pos) n_args, no_pos) in *)
      let n_de_cat = match hpdef.CF.def_cat with
        | CP.HPRelDefn _ ->  let r, others = Sautil.find_root cprog [n_hp] n_args (CF.list_of_disjs n_rhs) in
          CP.HPRelDefn (n_hp, r, others)
        | _ -> report_error no_pos "sac.size_ext_hpdef: support HPDEF only"
      in
      let exted_pred = CF.mk_hp_rel_def1 n_de_cat n_lhs [(n_rhs, None)] None in
      (n_hp,n_lhs, [ext_sv], exted_pred)
  in
  let pure_ext_x hpdefs=
    (*from the failure ==> kind of extension*)
    let ext_kind = Cfutil.analyse_error () in
    let n_setting=
      match ext_kind with
      | 0 ->
        (*size ext*)
        (*do extend: (new paras, new hpdefs)*)
        let extn_hpdefs = List.map size_ext_hpdef hpdefs in
        let n_infer_hps, n_rhfs, ext_pure_vars, n_hpdefs = List.fold_left ( fun (r1,r2,r3,r4) (n_hp,n_lhs, ext_svl, exted_pred) ->
            (r1@[n_hp],r2@[n_lhs],r3@ext_svl,r4@[exted_pred])
          ) ([],[],[], []) extn_hpdefs in
        let r_hf = CF.join_star_conjunctions n_rhfs in
        let infer_rel_ids, n_rhs = if ext_pure_vars = [] then ([], CF.formula_of_heap r_hf no_pos)
          else
            let nrel_name = fresh_any_name Globals.size_rel_name in
            let n_rel = {Cast.rel_name = nrel_name;
                         Cast.rel_vars = ext_pure_vars;
                         Cast.rel_formula = CP.mkTrue no_pos
                        } in
            let n_irel = {Iast.rel_name = nrel_name;
                          Iast.rel_typed_vars = List.map (fun (CP.SpecVar (t,id,_)) -> (t,id) ) ext_pure_vars;
                          Iast.rel_formula = Ipure.mkTrue no_pos
                         } in
            let () = iprog.Iast.prog_rel_decls <- iprog.Iast.prog_rel_decls@[n_irel] in
            (* let () = cprog.Cast.prog_rel_decls <- cprog.Cast.prog_rel_decls@[n_rel] in *)
            let () = cprog.Cast.prog_rel_decls # push n_rel in
            let rel_var = CP.SpecVar (RelT (List.map fst n_irel.Iast.rel_typed_vars) , nrel_name ,Unprimed) in
            let p_rel_ext = CP.mkRel rel_var (List.map (fun sv -> CP.mkVar sv no_pos) ext_pure_vars) no_pos in
            let p_rel = if  pure_comps=[] then p_rel_ext else
                CP.mkAnd p_rel_ext rhs_rel_pure0 no_pos in
            ([rel_var], CF.mkAnd_pure (CF.formula_of_heap r_hf no_pos) (MCP.mix_of_pure p_rel) no_pos)
        in
        Some (n_infer_hps, n_rhs, infer_rel_ids, n_hpdefs)
      | _ -> None
    in
    (*new rhs, new rels need to be inferred*)
    n_setting
  in
  let pure_ext hpdefs=
    let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
    let pr2 = pr_quad !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl pr1 in
    Debug.no_1 "SAC.pure_ext" pr1 (pr_option pr2)
      (fun _ -> pure_ext_x hpdefs) hpdefs
  in
  let rec prove_sem_ext infer_hps infer_pred_rels infer_ext_rels rhs_f cur_hpdef cur_split_hpdefs old_ext_num=
    let i,n_split_defs, rel_defs = prove_sem iprog cprog proc_name ass_stk hpdef_stk hp args
        infer_hps infer_pred_rels infer_ext_rels rhs_f cur_hpdef cur_split_hpdefs old_ext_num in
    (*check termination*)
    if i = old_ext_num then (false, [cur_hpdef], old_split) else
      match i with
      | 0 -> false, [cur_hpdef], old_split
      | 1 -> begin
          if !Globals.sa_ex then
            (*to size pure ext rhs*)
            let new_extn_opt = pure_ext n_split_defs in
            match new_extn_opt with
            | Some (n_infer_hps, n_rhs, n_infer_ext_rel, n_hpdefs) ->
              let n_rhs2 = Cfutil.subst_rel_def n_rhs rel_defs in
              prove_sem_ext n_infer_hps infer_pred_rels n_infer_ext_rel n_rhs2 cur_hpdef n_hpdefs i
            | None -> false, [cur_hpdef], old_split
          else
            false, [cur_hpdef], old_split
        end
      | 2 -> (*to pure ext lhs*)
        false, [cur_hpdef], old_split
      | _ ->
        let lst_hpargs = CF.get_HRels_f rhs_f in
        let n_split = (hp, args, lst_hpargs, pure_comps, lhs_hf, List.hd (CF.heap_of rhs_f), rhs_rel_pure0) in
        true,n_split_defs, n_split
  in
  (****************************************************************)
  (*************************END INTERNAL*********************)
  (****************************************************************)
  let is_valid, nhp_defs, n_split = prove_sem_ext (List.map fst comps) (List.map fst pure_comps)
      [] (CF.mkBase rhs_hf0 (MCP.mix_of_pure rhs_rel_pure0) CvpermUtils.empty_vperm_sets Cformula.TypeTrue (Cformula.mkTrueFlow ()) []  no_pos)
      cur_hpdef [] 0 in
  (is_valid, nhp_defs, n_split)

(*to do: should add ss_rels for subst_hprel_pure*)
let prove_split_cand_x iprog cprog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs
    ((hp, args, comps, pure_comps, lhs_hf, rhs_hf, rhs_rel_pure) as old_split) =
  let proc_name = "split_pred" in
  let rec look_up rest_defs rem=
    match rest_defs with
    | [] -> report_error no_pos "SAC.prove_split_cand 1"
    | ( def)::rest->
      let hp1,_ = CF.extract_HRel def.CF.def_lhs in
      if CP.eq_spec_var hp1 hp then
        def, rem@rest
      else
        look_up rest (rem@[def])
  in
  let rec comps_split comps (f,og) res=
    match comps with
    | [] -> res
    | (hp,args)::rest ->
      let f_comp = CF.drop_data_view_hrel_nodes f CF.check_nbelongsto_dnode
          CF.check_nbelongsto_vnode Sautil.check_neq_hrelnode
          args args [hp]
      in
      let () = Debug.ninfo_hprint (add_str  "f_comp " Cprinter.prtt_string_of_formula) f_comp no_pos in
      comps_split rest (f,og) (res@[(f_comp,og)])
  in
  let rec insert_para comps fs_wg res=
    match comps,fs_wg with
    | [],[] -> res
    | fs::rest_comps, f_wg::rest -> insert_para rest_comps rest (res@[(fs@[f_wg])])
    | _ -> report_error no_pos "sac.prove_split_cand: should be the same length 1"
  in
  let rec combine_comp comps1 ls_fs_wg  pos res=
    match comps1,ls_fs_wg  with
    | [],[] -> res
    | (hp, args)::rest1, fs_wg::rest2 ->
      let () = Debug.ninfo_hprint (add_str  "fs " (pr_list_ln Cprinter.prtt_string_of_formula)) (List.map fst fs_wg) no_pos in
      let fs1a_wg = Sautil.elim_useless_rec_preds cprog hp args fs_wg in
      let fs1_wg = Gen.BList.remove_dups_eq (fun (f1,_) (f2,_) ->
          Sautil.check_relaxeq_formula args f1 f2) fs1a_wg
      in
      let fs2_wg = List.filter (fun (f,_) -> not (Sautil.is_trivial f (hp,args))) fs1_wg in
      let r,paras = Sautil.find_root cprog (hp::unk_hps) args (List.map fst fs2_wg) in
      let n_hp_defs = Sautil.mk_hprel_def_wprocess cprog false [] unk_hps [] hp (args, r, paras) fs2_wg  pos in
      combine_comp rest1 rest2 pos (res@(List.map snd n_hp_defs))
    | _ -> report_error no_pos "sac.prove_split_cand: should be the same length 2"
  in
  (*res: list of disj of resulting split*)
  let subst_and_split acc (f,og)=
    (*subst*)
    let () = Debug.ninfo_hprint (add_str  "subst_and_split: f " (Cprinter.prtt_string_of_formula)) f no_pos in
    let f1 = CF.subst_hrel_f f ss_preds in
    let fs_wg = comps_split comps (f1,og) [] in
    let n_res = if acc = [] then
        List.map (fun x -> [x]) fs_wg
      else insert_para acc fs_wg []
    in
    n_res
  in
  (*shared*)
  (*END share*)
  (********END INTERNAL***********)
  let prove_syn (* (k, rel, og, f) *) def =
    (* let fs0,ogs = List.split def.CF.def_rhs in *)
    (* let fs = List.fold_left (fun r f-> r@(CF.list_of_disjs f)) [] fs0 in *)
    let n_rhs = def.CF.def_rhs in
    let ls_fs_wg = List.fold_left subst_and_split [] n_rhs in
    let split_hp_defs = combine_comp comps ls_fs_wg  no_pos [] in
    let n_hp_def = {def with CF.def_rhs = [( CF.formula_of_heap rhs_hf no_pos, None)]} in
    (* let () = Debug.info_pprint (" pred_split (syn):" ^ (!CF.print_h_formula n_hp_def.CF.def_lhs) ^ "(" ^ (CP.print_svl args) ^ ") :== " ^ *)
    (*     (Cprinter.prtt_string_of_h_formula rhs_hf)) no_pos in *)
    let () = Debug.info_pprint (" pred_split (syn):" ^ (!CF.print_h_formula n_hp_def.CF.def_lhs) ^ ":== " ^
                                (Cprinter.prtt_string_of_h_formula rhs_hf)) no_pos in
    (true, n_hp_def::split_hp_defs)
  in
  try
    let (* (k, rel, og, f) *)def, rem_hp_defs = look_up hp_defs [] in
    (*try: do the split to obtain new defs sematically*)
    let is_succ,split_hp_defs, new_split =
      if !Globals.syntatic_mode then
        (*syntactically*)
        try
          let is_valid, defs = prove_syn def in
          (is_valid,defs,old_split)
        with _ -> (false,[def], old_split)
      else (*prove_sem def*)  pred_split_ext iprog cprog proc_name ass_stk hpdef_stk
          (hp, args, comps, pure_comps, lhs_hf, rhs_hf, rhs_rel_pure) def
    in
    (is_succ,split_hp_defs@rem_hp_defs, new_split)
  with _ -> (false, hp_defs, old_split)

let prove_split_cand iprog cprog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs
    (hp, args, comps, pure_comps, lhs_hf, rhs_hf, rhs_pure)=
  let pr1 = pr_list_num Cprinter.string_of_hp_rel_def in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  let pr_comp = (pr_list (pr_pair !CP.print_sv !CP.print_svl)) in
  let pr3 = pr_hepta !CP.print_sv !CP.print_svl pr_comp pr_comp pr2 pr2 !CP.print_formula in
  Debug.no_6 "prove_split_cand" pr1 !CP.print_svl pr_comp pr_comp pr2 pr2
    (pr_triple string_of_bool pr1 pr3)
    (fun _ _ _ _ _ _ -> prove_split_cand_x iprog cprog proving_fnc ass_stk hpdef_stk
        unk_hps ss_preds hp_defs (hp, args, comps, pure_comps, lhs_hf, rhs_hf, rhs_pure))
    hp_defs args comps pure_comps lhs_hf rhs_hf

let find_closure_tuplep_hps tupled_hps hp_defs=
  let get_tupled_dep_hps tuple_deps def=
    let f = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in
    let hps = CF.get_hp_rel_name_formula f in
    let hp0, _ = CF.extract_HRel def.CF.def_lhs in
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

let seg_split prog unk_hps ass_stk hpdef_stk hp_def=
  let hp,args = CF.extract_HRel hp_def.CF.def_lhs in
  if List.length args = 2 then
    match hp_def.CF.def_cat with
    | CP.HPRelDefn (hp,r, others) ->begin
        let split_seg_opt = Sautil.norm_unfold_seg prog hp r others unk_hps hp_def.CF.def_flow
            (List.fold_left (fun r (f,og) ->
                 r@(List.map (fun f1 -> (f1,og)) (CF.split_conjuncts f))) [] hp_def.CF.def_rhs) in
        match split_seg_opt with
        | None -> ([],[hp_def])
        | Some (n_rhs, gen_hp_def) ->
          (*prove equiv*)
          let n_hp_def = {hp_def with CF.def_rhs = [(n_rhs,None)]} in
          ([hp],[n_hp_def;gen_hp_def])
      end
    | _ -> ([],[hp_def])
  else
    ([],[hp_def])

let seg_split prog unk_hps ass_stk hpdef_stk hp_def=
  let pr1 = Cprinter.string_of_hp_rel_def in
  let pr2 = pr_pair !CP.print_svl (pr_list_ln pr1) in
  Debug.no_1 "SAC.seg_split" pr1 pr2
    (fun _ -> seg_split prog unk_hps ass_stk hpdef_stk hp_def)
    hp_def

(*return new hpdefs and hp split map *)
let pred_split_hp_x iprog prog unk_hps ass_stk hpdef_stk (hp_defs0: CF.hp_rel_def list)  =
  let false_defs,hp_defs1 = List.partition (fun hp_def ->
      List.for_all (fun (f,_) -> CF.isAnyConstFalse f ) hp_def.CF.def_rhs) hp_defs0 in
  let true_defs,hp_defs = List.partition (fun hp_def ->
      List.for_all (fun (f,_) -> CF.is_unknown_f f || CF.isAnyConstTrue f ) hp_def.CF.def_rhs) hp_defs1 in
  let sing_hp_defs, tupled_hp_defs, tupled_hps = List.fold_left (fun (s_hpdefs, t_hpdefs, t_hps)  hp_def->
      match hp_def.CF.def_cat with
      | CP.HPRelDefn _ -> (s_hpdefs@[hp_def], t_hpdefs, t_hps)
      | CP.HPRelLDefn hps -> (s_hpdefs, t_hpdefs@[hp_def], t_hps@hps)
      | _ -> (s_hpdefs, t_hpdefs@[hp_def], t_hps)
    ) ([],[],[]) hp_defs
  in
  let closure_tupled_hps = find_closure_tuplep_hps tupled_hps sing_hp_defs in
  let sing_hp_defs1a, tupled_hp_defs1  = if List.length closure_tupled_hps > List.length tupled_hps then
      let sing_hp_defs2, tupled_hp_defs2 = List.partition (fun def ->
          match def.CF.def_cat with
          | CP.HPRelDefn (hp,_,_) -> not (CP.mem_svl hp closure_tupled_hps)
          | _ -> false
        ) sing_hp_defs in
      (sing_hp_defs2, tupled_hp_defs2@tupled_hp_defs)
    else
      sing_hp_defs,tupled_hp_defs
  in
  let sing_hp_defs1, sing_hp_def1b = List.partition (fun def ->
      let fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] def.CF.def_rhs in
      if List.length fs < 1 then false else true) sing_hp_defs1a in
  (*compute candidates*)
  let split_cands = pred_split_cands prog unk_hps sing_hp_defs1 in
  (*split and obtain map*)
  let split_map_hprel_subst = check_split_global iprog prog split_cands in
  let ss_preds = List.map (fun (_,_,_,_,a,b,c) -> (a,b)) split_map_hprel_subst in
  (*prove and do split*)
  let proving_fnc svl f1 = wrap_proving_kind PK_Pred_Split (x_add Sleekcore.sleek_entail_check 7 [] svl prog [] f1) in
  let sing_hp_defs2, split_map_hprel_subst1 = List.fold_left (fun (hp_defs0, r_split) split ->
      let is_succ, hp_defs1, n_split = prove_split_cand iprog prog proving_fnc ass_stk hpdef_stk unk_hps ss_preds hp_defs0 split in
      if is_succ then
        (hp_defs1, r_split@[n_split])
      else
        (hp_defs0, r_split)
    ) (sing_hp_defs1,[]) split_map_hprel_subst
  in
  (*do seg split*)
  let () = Debug.ninfo_hprint (add_str "sing_hp_defs2: " ( pr_list_ln Cprinter.string_of_hp_rel_def)) sing_hp_defs2 no_pos in
  let sing_hp_defs3 = if not !Globals.pred_seg_split then
      List.fold_left (fun r def -> let split_hps, new_defs = (seg_split prog unk_hps ass_stk hpdef_stk def) in
                       r@new_defs
                     ) [] sing_hp_defs2
    else  sing_hp_defs2
  in
  let tupled_hp_defs2 = List.map (fun def ->
      let fs,ogs = List.split def.CF.def_rhs in
      let f = CF.disj_of_list fs no_pos in
      {def with CF.def_rhs = [(CF.subst_hrel_f f ss_preds, CF.combine_guard ogs)]}) (tupled_hp_defs1@sing_hp_def1b) in
  let r = (sing_hp_defs3@tupled_hp_defs2@true_defs@false_defs,List.map (fun (a1,a2,a3,a4,a5,_,_) -> (a1,a2,a3,a4,a5)) split_map_hprel_subst1) in
  r

let pred_split_hp iprog prog unk_hps ass_stk hpdef_stk (hp_defs: CF.hp_rel_def list): (CF.hp_rel_def list *
                                                                                       (CP.spec_var*CP.spec_var list * (CP.spec_var*CP.spec_var list) list
                                                                                        * (CP.spec_var*CP.spec_var list) list *CF.h_formula) list) =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_sv in
  let pr3 = Cprinter.string_of_h_formula in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = fun (a1,a2) -> (*ignore a3*)
    let pr = pr_pair pr1 (pr_list (pr_penta pr2 !CP.print_svl pr5 pr5 pr3)) in
    pr (a1, a2)
  in
  Debug.no_2 "pred_split_hp" !CP.print_svl pr1 pr4
    (fun _ _ -> pred_split_hp_x iprog prog unk_hps ass_stk hpdef_stk hp_defs)  unk_hps hp_defs

(*
 return a triples
  - new hp_defs
  - splited_hps (to remove them on the hpdefs)
  - split_hp_defs (to transform them to hpdefs)
*)
let pred_seg_split_hp iprog prog unk_hps ass_stk hpdef_stk (hp_defs: CF.hp_rel_def list):
  (CF.hp_rel_def list * CP.spec_var list * CF.hp_rel_def list) =
  let sing_hp_defs, tupled_hp_defs, tupled_hps = List.fold_left (fun (s_hpdefs, t_hpdefs, t_hps)  hp_def->
      match hp_def.CF.def_cat with
      | CP.HPRelDefn _ -> (s_hpdefs@[hp_def], t_hpdefs, t_hps)
      | CP.HPRelLDefn hps -> (s_hpdefs, t_hpdefs@[hp_def], t_hps@hps)
      | _ -> (s_hpdefs, t_hpdefs@[hp_def], t_hps)
    ) ([],[],[]) hp_defs
  in
  let closure_tupled_hps = find_closure_tuplep_hps tupled_hps sing_hp_defs in
  let sing_hp_defs1a, tupled_hp_defs1  = if List.length closure_tupled_hps > List.length tupled_hps then
      let sing_hp_defs2, tupled_hp_defs2 = List.partition (fun def ->
          match def.CF.def_cat with
          | CP.HPRelDefn (hp,_,_) -> not (CP.mem_svl hp closure_tupled_hps)
          | _ -> false
        ) sing_hp_defs
      in
      (sing_hp_defs2, tupled_hp_defs2@tupled_hp_defs)
    else
      sing_hp_defs,tupled_hp_defs
  in
  let sing_hp_defs1, sing_hp_def1b = List.partition (fun def ->
      let fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f)) [] def.CF.def_rhs in
      if List.length fs < 1 then false else true) sing_hp_defs1a in
  let sing_hp_defs2, splited_hps, split_hp_defs = List.fold_left (fun (acc_hp_defs, acc_split_hps, split_hp_defs) def ->
      let split_hps, new_defs = (seg_split prog unk_hps ass_stk hpdef_stk def) in
      let new_split_hp_defs = match split_hps with
        | [] -> split_hp_defs
        | _ -> split_hp_defs@new_defs
      in
      (acc_hp_defs@new_defs , acc_split_hps@split_hps, new_split_hp_defs)
    ) ([],[],[]) sing_hp_defs1 in
  (sing_hp_defs2@sing_hp_def1b@tupled_hp_defs1,splited_hps, split_hp_defs)

(*=============**************************================*)
(*=============END PRED SPLIT================*)
(*=============**************************================*)


(***************************************************************)
         (*=========== NORMALIZATION FOR RAW DEF===========*)
(***************************************************************)

let pred_norm_disj_x iprog prog unk_hps hp_defs=

  (1,[])

let pred_norm_disj iprog prog unk_hps hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_sv in
  Debug.no_2 "pred_norm_disj" pr2 pr1 (pr_pair string_of_int pr1)
    (fun _ _ -> pred_norm_disj_x iprog prog unk_hps hp_defs)
    unk_hps hp_defs

(*
a pred may have a cutpoint in the middle. somehow expose this cutpoint
steps:
 1- dectect
 2- generate seg pred
 3- generate the link
*)
let pred_norm_seg_x iprog prog unk_hps hp_defs=
  (****************INTERNAL***************)
  let need_cutpoint def=
    let hp,args = CF.extract_HRel def.CF.def_lhs in
    let () = Debug.ninfo_hprint (add_str "checking for hp"  (!CP.print_sv)) hp no_pos in
    if CP.mem_svl hp unk_hps then None else
      (*split base cases and rec-cases*)
      let bfs,rfs, dep_fs = List.fold_left ( fun (acc_bfs, acc_rfs, dep_fs) (f,_) ->
          let hps = Cformula.get_hp_rel_name_formula f in
          if hps = [] then
            (acc_bfs@[f], acc_rfs, dep_fs)
          else if CP.mem_svl hp hps then
            (acc_bfs, acc_rfs@[f], dep_fs)
          else (acc_bfs, acc_rfs, dep_fs@[(f,hps)])
      ) ([],[],[]) def.CF.def_rhs in
      match bfs,dep_fs with
        | [bf],[(dep_f, dep_hps)] -> (* adhoc *) begin
            (* TODO: rfs should be progressing *)
            (* TODO: dep_f should be progressing *)
            match dep_hps with
              | [dep_hp] -> begin
                  try
                    let () = Debug.ninfo_hprint (add_str "dep_hp"  (!CP.print_sv)) dep_hp no_pos in
                    let dep_def = CF.look_up_hp_def hp_defs dep_hp in
                    (* todo: check whether dep_def == bf \/ dep_f *)
                    let dep_fs0 = List.fold_left (fun acc (f,_) -> acc@[f]) [] dep_def.CF.def_rhs in
                    (* let rec_f0 = CF.subst_hprel rec_f [hp] dep_hp in *)
                    let _,dep_args = CF.extract_HRel dep_def.CF.def_lhs in
                    let sst = List.combine args dep_args in
                    let bf1 = CF.subst sst bf in
                    let dep_f1 = CF.subst sst dep_f in
                    let is_equiv= Syn_checkeq.checkeq_formula_list_w_args dep_args [bf1;dep_f1] dep_fs0 in
                    if is_equiv then
                      Some (hp, args, bf, rfs, dep_hp, dep_f)
                    else None
                  with _ -> None
                end
              | _ -> None
          end
        | _ -> None
  in
  let extract_root hp def=
    match def.CF.def_cat with
        | CP.HPRelDefn (_,r,others) ->  r, others
        | _ -> raise Not_found
  in
  let extend_seg_arg target_hp new_hp seg_earg hf0=
    let rec recf hf= match hf with
      | CF.HRel (hp, eargs, pos) ->
            if CP.eq_spec_var target_hp hp then
              CF.HRel (new_hp, eargs@[seg_earg], pos)
            else hf
      | CF.Star({CF.h_formula_star_h1 = h1;
        CF.h_formula_star_h2 = h2;
        CF.h_formula_star_pos = pos;}) -> 
            let new_f1 =  recf h1 in
            let new_f2 = recf h2 in
            CF.mkStarH new_f1 new_f2 pos
      | _ -> hf
    in
    recf hf0
  in
  let generate_seg_pred orig_hp orig_all_args orig_root orig_args rec_fs dep_hp=
    let seg_arg = fresh_any_name Globals.seg_arg in
    let seg_sv = CP.SpecVar (CP.type_of_spec_var orig_root, seg_arg ,Unprimed) in
    let orig_hpcl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var orig_hp) in
    let seg_def_lhs0, n_hp = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog true false (orig_hpcl.Cast.hp_vars_inst@[(seg_sv,NI)]) no_pos in
    let sst0 = List.combine (List.map fst orig_hpcl.Cast.hp_vars_inst) orig_all_args in
    let seg_def_lhs = CF.h_subst sst0 seg_def_lhs0 in
    let n_hpcl = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls (CP.name_of_spec_var n_hp) in
    let todo_unk = Iast.mkhp_decl iprog n_hpcl.Cast.hp_name
          (List.map (fun (CP.SpecVar (t,id,_) ,ins) -> (t,id, ins)) n_hpcl.Cast.hp_vars_inst)
          n_hpcl.Cast.hp_part_vars n_hpcl.Cast.hp_root_pos n_hpcl.Cast.hp_is_pre (IF.mkTrue IF.n_flow no_pos)
    in
    let seg_earg = CP.mkVarNull seg_sv no_pos in
    let seg_def_rec_rhs = List.map (fun f ->
        CF.formula_map (extend_seg_arg orig_hp n_hp seg_earg) f
    ) rec_fs in
    let seg_base_rhs = CF.formula_of_pure_formula (CP.mkPtrEqn orig_root seg_sv no_pos) no_pos in
    let seg_def_rhs = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 no_pos) seg_base_rhs seg_def_rec_rhs in
    let seg_def_cat = CP.HPRelDefn (n_hp, orig_root, orig_args@[seg_sv]) in
    let seg_pred = CF.mk_hp_rel_def1 seg_def_cat seg_def_lhs [(seg_def_rhs, None)] None in
    (seg_pred, seg_def_lhs, seg_sv)
  in
  let generate_seg (orig_def,hp, args, bf, rec_fs, dep_hp,dep_f)=
    let () = Debug.ninfo_hprint (add_str "generating for hp"  (!CP.print_sv)) hp no_pos in
    try
      let orig_root, orig_args = extract_root hp orig_def in
      (* generate seg pred *)
      let (seg_def, seg_def_lhs, seg_sv) = generate_seg_pred hp args orig_root orig_args rec_fs dep_hp in
      let () = Debug.ninfo_hprint (add_str "seg_def"  Cprinter.string_of_hp_rel_def) seg_def no_pos in
      let () = Debug.ninfo_hprint (add_str "seg_def_lhs"  !CF.print_h_formula) seg_def_lhs no_pos in
      (* generate linking pred *)
      let hprels = CF.get_hprel dep_f in
      let ((ter_hp, ter_eargs,_) as hprel) = List.hd (List.filter (fun (hp,_,_) -> CP.eq_spec_var hp dep_hp) hprels) in
      let dep_root,_ = Cast.get_root_args_hprel prog.Cast.prog_hp_decls (CP.name_of_spec_var ter_hp) (List.concat (List.map CP.afv ter_eargs)) in
      let sst1 = [dep_root,seg_sv] in
      let ter_seg = CF.h_subst sst1 (CF.HRel hprel) in
      let link_rhs_f = CF.formula_of_heap (CF.mkStarH seg_def_lhs ter_seg no_pos) no_pos in
      let link_def = {orig_def with def_rhs = [(link_rhs_f, None)]} in
      let () = Debug.ninfo_hprint (add_str "link_def"  Cprinter.string_of_hp_rel_def) link_def no_pos in
      [link_def;seg_def]
    with _ -> [orig_def]
  in

  (****************END**INTERNAL***************)
  let () = Debug.ninfo_hprint (add_str " step 1" pr_id) "checking" no_pos in
  let to_norm_def, rest = List.fold_left (fun (acc_to, acc_rest) def -> begin
    try
      let need_seg_opt = need_cutpoint def in
      match need_seg_opt with
        | Some conf ->
              (acc_to@[conf], acc_rest)
        | None -> (acc_to, acc_rest@[def])
    with _ -> (acc_to, acc_rest@[def])
  end
  ) ([],[]) hp_defs in
  let () = Debug.ninfo_hprint (add_str " step 2" pr_id) "generating" no_pos in
  let seg_defs = List.fold_left (fun acc (hp, args, bf, rec_fs, dep_hp,dep_f) ->
      let orig_def = CF.look_up_hp_def hp_defs hp in
      let conf1 = (orig_def,hp, args, bf, rec_fs, dep_hp,dep_f) in
      let new_defs = generate_seg conf1 in
      acc@new_defs
  ) [] to_norm_def in
  rest@seg_defs

let pred_norm_seg iprog prog unk_hps hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = !CP.print_svl in
  Debug.no_2 "pred_norm_seg" pr2 pr1 pr1
    (fun _ _ -> pred_norm_seg_x iprog prog unk_hps hp_defs)
    unk_hps hp_defs

(***************************************************************)
         (*===========END NORMALIZATION===========*)
(***************************************************************)


(***************************************************************)
          (*=========== SIMPLIFICATION FOR RAW DEF===========*)
(***************************************************************)

(*
  x::ll<> & x=null <=> x=null
*)
let simplify_trim_unsat_view_branches cprog def=
  let unfold_ptrs f vptrs=
    List.fold_left (fun (f,ss) sv0 ->
        let sv = CP.subst_var_par ss sv0 in
        let nf,ss1 = Solver.unfold_nth 9 (cprog, None) f sv true 0 no_pos in
        (nf, ss@ss1)
      ) (f, []) vptrs
  in
  let trim_unsat_g (f,og)=
    if CF.is_trivial_f f then (f,og)
    else
      (* get view_nodes. then unfold *)
      let vptrs = CF.get_vptrs f in
      let () = Debug.ninfo_hprint (add_str "vptrs" !CP.print_svl) vptrs no_pos in
      if vptrs = [] then (f,og)
      else
        let unfolded_f,_ = unfold_ptrs f vptrs in
        let () = Debug.ninfo_hprint (add_str "unfolded_f" !CF.print_formula) unfolded_f no_pos in
        (* unfold step already does trim. this only works for base case. *)
        let unfolded_vptrs = CF.get_vptrs unfolded_f in
        let nf = if unfolded_vptrs = [] then CF.simplify_pure_f unfolded_f else f
        (* let goods,unsat_list = x_add Solver.find_unsat cprog unfolded_f in *)
        (* if unsat_list = [] then (f,og) *)
        (* else *)
        (*   let nf = match goods with *)
        (*     | x::[]-> x *)
        (*     | _ -> List.fold_left ( fun a c -> CF.mkOr c a no_pos) (CF.mkFalse (CF.mkTrueFlow ()) no_pos) goods *)
        in
        (nf,og)
  in
  let trimed_rhs = List.map trim_unsat_g def.CF.def_rhs in
  {def with CF.def_rhs = trimed_rhs}

let simplify_trim_unsat_view_branches cprog def=
  let pr1 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "simplify_trim_unsat_view_branches" pr1 pr1
      (fun _ -> simplify_trim_unsat_view_branches cprog def) def

(*
this simplify may overlap with split base case for post.
*)
let simplify_defined_pred def=
  let elim_defined_pred_g (f,og)=
    if CF.is_trivial_f f then (f,og)
    else
      let hp_rels = CF.get_HRels_f f in
      if hp_rels = [] then (f,og)
      else
        let ( _,mf,_,_,_,_) = CF.split_components f in
        let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mf) in
        if eqNulls = [] then (f,og)
        else
          let defined_hps = List.fold_left (fun acc (hp,args) -> if CP.diff_svl args eqNulls = [] then
            acc@[hp] else acc
          ) [] hp_rels in
          let nf = if defined_hps=[] then f
          else fst (CF.drop_hrel_f f defined_hps)
          in
          let () = Debug.ninfo_hprint (add_str "nf" !CF.print_formula) nf no_pos in
          (nf, og)
  in
  let elimed_rhs = List.map elim_defined_pred_g def.CF.def_rhs in
  {def with CF.def_rhs = elimed_rhs}

let simplify_defined_pred def=
  let pr1 = Cprinter.string_of_hp_rel_def in
  Debug.no_1 "simplify_defined_pred" pr1 pr1
      (fun _ -> simplify_defined_pred def) def

(*
  - this function simplifies the raw output of the synthesis
  - preserve equivalence
  - now, apply for post only
 *)
let simplify_def prog defs=
  let simplify_post def=
    (*simplify one branch, post*)
    (*post synthesis usually includes views of pre-synthesis. do trim unsat branches*)
    let def1 = simplify_trim_unsat_view_branches prog def in
    (* this simplify may overlap with split base case for post. *)
    (* simplify_defined_pred def1 *)
    def1
  in
  List.map simplify_post defs


let simplify_def prog defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "simplify_def" pr1 pr1
    (fun _ -> simplify_def prog defs) defs

(***************************************************************)
          (*===========END SIMPLIFICATION===========*)
(***************************************************************)
