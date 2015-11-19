#include "xdebug.cppo"
open VarGen
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
(* module SAU = Sautility *)

(*the stack seems more internal to the inference than anything else,*)
(* the results are never picked from the stack,*)
(* rather they are returned by the inference method however the height of the stack is used*)
(* as an indicator of the inference success*)
let rel_def_stk : CF.hprel_def Gen.stack_pr = new Gen.stack_pr "rel-def-stk"
  Cprinter.string_of_hprel_def_lib (==)

let rec elim_redundant_paras_lst_constr_x prog constrs =
  let drop_cands = List.concat (List.map (fun c -> check_dropable_paras_constr prog c) constrs) in
  let rec partition_cands_by_hp_name drops parts=
    match drops with
    | [] -> parts
    | (hp_name,ids)::xs ->
      let part,remains= List.partition (fun (hp_name1,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
      partition_cands_by_hp_name remains (parts@[[(hp_name,ids)]@part])
  in
  let intersect_cand_one_hp ls=
    let hp_names,cands = List.split ls in
    (* let () = Debug.ninfo_zprint (lazy (("   hprel: " ^ (!CP.print_svl hp_names)))) no_pos in *)
    (* let () = Debug.ninfo_zprint (lazy (("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)))) no_pos in *)
    let locs = List.fold_left (fun ls1 ls2 -> Gen.BList.intersect_eq (=) ls1 ls2) (List.hd cands) (List.tl cands) in
    if locs = [] then []
    else [(List.hd hp_names, locs)]
  in
  let rec drop_invalid_group ls res=
    match ls with
    | [] -> res
    | (hp,locs)::ss -> if locs = [-1] then drop_invalid_group ss res
      else drop_invalid_group ss (res@[(hp,locs)])
  in
  (*group cands into each hp*)
  let groups = partition_cands_by_hp_name drop_cands [] in
  (*each hp, intersect all candidate drops*)
  let drop_hp_args = List.concat (List.map intersect_cand_one_hp groups) in
  let drop_hp_args = drop_invalid_group drop_hp_args [] in
  let () = Debug.ninfo_pprint ("  drops: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                              in pr drop_hp_args)) no_pos in
  let new_constrs,ms = drop_process constrs drop_hp_args in
  (*find candidates in all assumes, if a case appears in all assmses => apply it*)
  (ms,new_constrs)

and elim_redundant_paras_lst_constr prog hp_constrs =
  let pr0 = pr_list !CP.print_exp in
  let pr = pr_list_ln Cprinter.string_of_hprel in
  let pr1 = pr_list (pr_triple !CP.print_sv pr0 pr0) in
  Debug.no_1 "elim_redundant_paras_lst_constr" pr (pr_pair pr1 pr)
    (fun _ ->  elim_redundant_paras_lst_constr_x prog hp_constrs) hp_constrs

(*each constraint, pick candidate args which can be droped in each hprel*)
and check_dropable_paras_constr prog constr:((CP.spec_var*int list) list) =
  Debug.ninfo_hprint (add_str "  assumption: " (Cprinter.string_of_hprel)) constr no_pos;
  let(lhs,rhs) = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
  let () = Debug.ninfo_pprint ("    RHS") no_pos in
  let l1 = check_dropable_paras_RHS prog rhs in
  let () = Debug.ninfo_pprint ("    LHS") no_pos in
  let l2 = check_dropable_paras_LHS prog lhs rhs constr.CF.predef_svl in
  (l1@l2)

(*each hprel: check which arg is raw defined*)
and check_dropable_paras_RHS prog f:((CP.spec_var*int list) list)=
  (*RHS: dropable if para have just partial defined or more*)
  let def_vs_wo_args, _, _, hrs, _,eqNulls = Sautil.find_defined_pointers_raw prog f in
  (* let def_vsl_wo_args = def_vs_wo_args@eqNulls in *)
  let rec helper args res index=
    match args with
    | [] -> res
    | a::ass -> if (CP.mem_svl a def_vs_wo_args) then
        helper ass (res@[index]) (index+1)
      else helper ass res (index+1)
  in
  let check_dropable_each_pred hr =
    let (svar, exps,_) = hr in
    let () = Debug.ninfo_zprint (lazy (("      hprel:  " ^ (CP.name_of_spec_var svar)))) no_pos in
    let res = helper (List.concat (List.map CP.afv exps)) [] 0 in
    let () = Debug.ninfo_zprint (lazy (("      cands: " ^ (Cprinter.string_of_list_int res)))) no_pos in
    if res = [] then [(svar,[-1])] (*renturn -1 to indicate that none is allowed to drop*)
    else [(svar,res)]
  in
  List.concat (List.map check_dropable_each_pred hrs)

(*each hprel: check which arg is either defined or not-in-used*)
and check_dropable_paras_LHS prog f1 f2 predef :((CP.spec_var*int list) list)=
  let def_vs, hp_paras, _, _, _ = Sautil.find_defined_pointers prog f1 predef in
  let rec helper args res index=
    match args with
    | [] -> res
    | a::ass -> if ((CP.mem_svl a (def_vs@predef)) || (is_not_used a (f1,f2))) then
        helper ass (res@[index]) (index+1)
      else helper ass res (index+1)
  in
  let check_dropable_each_hp (svar, args) =
    let () = Debug.ninfo_zprint (lazy (("      hprel:  " ^ (CP.name_of_spec_var svar) ^ (!CP.print_svl args)))) no_pos in
    let res = helper args [] 0 in
    let () = Debug.ninfo_zprint (lazy (("      cands: " ^ (Cprinter.string_of_list_int res)))) no_pos in
    if res = [] then [(svar,[-1])] (*renturn -1 to indicate that none is allowed to drop*)
    else [(svar, res)]
  in
  List.concat (List.map check_dropable_each_hp hp_paras)


and drop_process (constrs: CF.hprel list) (drlocs: (CP.spec_var* int list) list):
  ( CF.hprel list* (CP.spec_var*CP.exp list*CP.exp list) list) =
  let new_constrs, m = List.split(List.map (fun c -> drop_process_one_constr c drlocs) constrs) in
  (new_constrs, Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) -> CP.eq_spec_var hp1 hp2) (List.concat m))

and drop_process_one_constr (constr: CF.hprel) drlocs: CF.hprel * ((CP.spec_var*CP.exp list*CP.exp list) list) =
  let nlhs,m1 = filter_hp_rel_args_f constr.CF.hprel_lhs drlocs in
  let nrhs,m2 = (filter_hp_rel_args_f constr.CF.hprel_rhs drlocs) in
  let m = Gen.BList.remove_dups_eq (fun (hp1,_,_) (hp2,_,_) -> CP.eq_spec_var hp1 hp2) (m1@m2) in
  ({constr with
    CF.hprel_lhs = nlhs;
    CF.hprel_rhs = nrhs},m)


and filter_hp_rel_args_f (f: CF.formula) (drlocs: (CP.spec_var* int list) list)=
  (* let rels, _ = List.split drlocs in *)
  let rec helper f drlocs = match f with
    | CF.Base fb -> let nh,m= filter_hp_rel_args fb.CF.formula_base_heap drlocs in
      (CF.Base {fb with CF.formula_base_heap = nh;}),m
    | CF.Or orf ->
      let n_orf1,m1 = helper orf.CF.formula_or_f1 drlocs in
      let n_orf2,m2 = helper orf.CF.formula_or_f2 drlocs in
      (CF.Or {orf with CF.formula_or_f1 = n_orf1;
                       CF.formula_or_f2 = n_orf2;}),m1@m2
    | CF.Exists fe ->
      let nh,m=filter_hp_rel_args fe.CF.formula_exists_heap drlocs  in
      (CF.Exists {fe with CF.formula_exists_heap =  nh;}),m
  in
  helper f drlocs

and filter_hp_rel_args (hf: CF.h_formula) (drlocs: (CP.spec_var* int list) list): CF.h_formula *
                                                                                  ((CP.spec_var*CP.exp list*CP.exp list) list)=
  (* let rels, _ = List.split drlocs in *)
  let rec look_up_drop_hp hp drops=
    match drops with
    | [] -> []
    | (hp1, locs)::ss -> if CP.eq_spec_var hp hp1 then locs
      else look_up_drop_hp hp ss
  in
  let rec helper hf0=
    match hf0 with
    | CF.Star {CF.h_formula_star_h1 = hf1;
               CF.h_formula_star_h2 = hf2;
               CF.h_formula_star_pos = pos} ->
      let n_hf1,m1 = helper hf1 in
      let n_hf2,m2 = helper hf2 in
      let hf1=
        (match n_hf1,n_hf2 with
         | (CF.HEmp,CF.HEmp) -> CF.HEmp
         | (CF.HEmp,_) -> n_hf2
         | (_,CF.HEmp) -> n_hf1
         | _ -> CF.Star {CF.h_formula_star_h1 = n_hf1;
                         CF.h_formula_star_h2 = n_hf2;
                         CF.h_formula_star_pos = pos}
        )
      in hf1,m1@m2
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;
                CF.h_formula_conj_pos = pos} ->
      let n_hf1,m1 = helper hf1 in
      let n_hf2,m2 = helper hf2 in
      let hf1 = CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                          CF.h_formula_conj_h2 = n_hf2;
                          CF.h_formula_conj_pos = pos}
      in hf1,m1@m2
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;
                 CF.h_formula_phase_pos = pos} ->
      let n_hf1,m1 = helper hf1 in
      let n_hf2,m2 = helper hf2 in
      (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                  CF.h_formula_phase_rw = n_hf2;
                  CF.h_formula_phase_pos = pos}),m1@m2
    | CF.DataNode hd -> hf0,[]
    | CF.ViewNode hv -> hf0,[]
    | CF.ThreadNode ht -> hf0,[] (*TOCHECK*)
    | CF.HRel (sv, args, l) ->
      let locs =  look_up_drop_hp sv drlocs in
      if locs = [] then hf0,[]
      else
        begin
          let rec filter_args args new_args index=
            match args with
            | [] -> new_args
            | a::ss -> if List.exists (fun id -> id = index) locs then
                filter_args ss new_args (index+1)
              else filter_args ss (new_args@[a]) (index+1)
          in
          let new_args = filter_args args [] 0 in
          if((List.length new_args) == 0) then CF.HEmp,[(sv,args,[])]
          else (CF.HRel (sv, new_args, l)),[(sv,args,new_args)]
        end
    | CF.Hole _ | CF.FrmHole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp | CF.HVar _ -> hf0,[]
    | CF.StarMinus _ | CF.ConjStar _ | CF.ConjConj _ -> Error.report_no_pattern ()
  in
  helper hf

and is_not_used sv constr=
  let lhs, rhs = constr in
  (is_not_used_RHS sv rhs) && (is_not_connect_LHS sv rhs lhs)

and is_not_used_RHS (v: CP.spec_var)(f: CF.formula): bool =
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let eqNulls = match f with
    |CF.Base  ({CF.formula_base_pure = p1})
    |CF.Exists ({ CF.formula_exists_pure = p1}) -> (
        let eqNull1, eqNull2 =  List.split (MCP.ptr_equations_with_null p1) in
        CP.remove_dups_svl (eqNull1@eqNull2)
      )
    |CF.Or f  -> report_error no_pos "not handle yet"
  in
  let rhs_vs = (eqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds) @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs)  in
  let get_svars el = List.concat (List.map (fun c -> [CP.exp_to_spec_var c] ) el) in
  let rel_args =List.concat ( List.map (fun (_,el,_) -> get_svars el) hrs) in
  let rhs_vs = rhs_vs@rel_args in
  let str = List.fold_left (fun a b ->  (CP.name_of_spec_var b ^ "," ^ a )) "" rhs_vs in
  let () = Debug.ninfo_zprint (lazy (("RHS vars " ^ str))) no_pos in
  let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) rhs_vs in
  if(b) then false
  else true

and is_not_connect_LHS (v: CP.spec_var)(f: CF.formula)(f2:CF.formula): bool =
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let hds = List.filter (fun c -> not(is_not_used_RHS c.CF.h_formula_data_node f2)) hds in
  let hvs = List.filter (fun c -> not(is_not_used_RHS c.CF.h_formula_view_node f2)) hvs in
  let node_args = (List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds)) @ (List.concat(List.map (fun hv -> hv.CF.h_formula_view_arguments) hvs)) in
  let node_args = List.filter (fun c -> CP.is_node_typ c) node_args in
  let b = List.exists (fun c-> if(CP.eq_spec_var v c) then true else false) node_args in
  if(b) then false
  else true

(**************************)
(*===========SPLIT===========*)
let get_hp_split_cands_one_cs prog unk_hps lhs rhs=
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
  let lhns, lhvs, lhrs = CF.get_hp_rel_formula lhs in
  let rhns, rhvs, rhrs = CF.get_hp_rel_formula rhs in
  let ( _,lmix_f,_,_,_,_) = CF.split_components lhs in
  let leqs = (MCP.ptr_equations_without_null lmix_f) in
  let ( _,rmix_f,_,_,_,_) = CF.split_components rhs in
  let reqs = (MCP.ptr_equations_without_null rmix_f) in
  let cands = lhrs @ rhrs in
  let cands1 = List.filter (fun (hp,el,l) -> not (CP.mem_svl hp unk_hps) && (List.length el) >= 2) cands in
  let cands2 = List.map (fun (hp,el,l) ->
      let args = List.concat (List.map CP.afv el) in
      let parts = do_partition (lhns@rhns) (lhvs@rhvs) (leqs@reqs) args in
      (hp,args, parts,l)
    ) cands1
  in
  (cands2)

let get_hp_split_cands_x prog constrs=
  List.concat (List.map (fun cs -> get_hp_split_cands_one_cs prog (List.map fst cs.CF.unk_hps)
                            cs.CF.hprel_lhs cs.CF.hprel_rhs) constrs)

let get_hp_split_cands prog constrs =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln (pr_quad !CP.print_sv !CP.print_svl (pr_list !CP.print_svl) string_of_full_loc) in
  Debug.no_1 "get_hp_split_cands" pr1 pr2
    (fun _ -> get_hp_split_cands_x prog constrs) constrs

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
    let hf,new_hp_sv = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog true false args1 pos in
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
        if Sautil.eq_spec_var_order_list args1 args2 then
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
    let new_hrels_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 p0) (List.hd new_hrel_fs) (List.tl new_hrel_fs) in
    let hrel0 = Sautil.mkHRel hp args0 p0 in
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

let subst_constr_with_new_hps_x hp_constrs hprel_subst=
  let elim_two_first_arg (_,_,_,a4,a5)= (a4,a5) in
  let new_hprel_subst = List.map elim_two_first_arg hprel_subst in
  let helper cs=
    {cs with
     CF.hprel_lhs= CF.subst_hrel_f cs.CF.hprel_lhs new_hprel_subst;
     CF.hprel_rhs= CF.subst_hrel_f cs.CF.hprel_rhs new_hprel_subst;
    }
  in
  List.map helper hp_constrs

let subst_constr_with_new_hps hp_constrs hprel_subst=
  let pr1= pr_list_ln Cprinter.string_of_hprel in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr3 = pr_list_ln (pr_penta !CP.print_sv !CP.print_svl pr4 pr2 pr2) in
  Debug.no_2 "subst_constr_with_new_hps" pr1 pr3 pr1
    (fun _ _ -> subst_constr_with_new_hps_x hp_constrs hprel_subst) hp_constrs hprel_subst

(*return new contraints and hp split map *)
let split_hp_x prog (hp_constrs: CF.hprel list): (CF.hprel list *
                                                  (CP.spec_var*CP.spec_var list * (CP.spec_var*CP.spec_var list) list
                                                   * CF.h_formula) list) =
  (*get hp candidates*)
  let split_cands = get_hp_split_cands prog hp_constrs in
  (*split  and get map*)
  let split_map_hprel_subst = check_split_global prog split_cands in
  (*subs old hrel by new hrels*)
  let new_constrs = subst_constr_with_new_hps hp_constrs split_map_hprel_subst in
  (new_constrs,List.map (fun (a1,a2,a3,a4,_) -> (a1,a2,a3,a4)) split_map_hprel_subst)

let split_hp prog hp_constrs:(CF.hprel list *
                              (CP.spec_var*CP.spec_var list * (CP.spec_var*CP.spec_var list) list
                               *CF.h_formula) list) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = !CP.print_sv in
  let pr3 = Cprinter.string_of_h_formula in
  let pr5 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr4 = fun (a1,a2) -> (*ignore a3*)
    let pr = pr_pair pr1 (pr_list (pr_quad pr2 !CP.print_svl pr5 pr3)) in
    pr (a1, a2)
  in
  Debug.no_1 "split_hp" pr1 pr4
    (fun _ -> split_hp_x prog hp_constrs) hp_constrs
(*===========END SPLIT===========*)
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
        (* let () = Debug.info_zprint (lazy (("   hp: " ^ (!CP.print_sv hp_name)))) no_pos in *)
        (* let () = Debug.info_zprint (lazy (("     res: " ^ (pr1 res)))) no_pos in *)
        (* let () = Debug.info_zprint (lazy (("     largs: " ^ (!CP.print_svl largs)))) no_pos in *)
      if (List.length res) = (List.length largs) then
        ([(hp_name, res)],[(hp_name, largs,res)])
      else ([(hp_name, res)],[])
    end
  in
  get_unk_ptr known_svl (hp_name, args)

(*analysis unknown information*)
let rec analize_unk_one prog unk_hps constr =
  let () = Debug.ninfo_zprint (lazy (("   hrel: " ^ (Cprinter.string_of_hprel constr)))) no_pos in
  (*elim hrel in the formula and returns hprel_args*)
  (*lhs*)
  let lhs1,lhrels = Sautil.drop_get_hrel constr.CF.hprel_lhs in
  (*rhs*)
  let rhs1,rhrels = Sautil.drop_get_hrel constr.CF.hprel_rhs in
  (*find fv of lhs + rhs wo hrels*)
  (* let lsvl = Sautil.get_raw_defined_w_pure prog lhs1 in *)
  (* let rsvl = Sautil.get_raw_defined_w_pure prog rhs1 in *)
  let svl = Sautil.get_raw_defined_w_pure prog constr.CF.predef_svl lhs1 rhs1 in
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
    | [] -> ([])
    | (hp1,locs)::ss -> if CP.eq_spec_var hp hp1 then
        begin
          (*find unknown hprel*)
          if (List.length args) = (List.length locs) then
            (args)
          else
            ((Sautil.retrieve_args_from_locs args locs))
        end
      else retrieve_args_one_hp ss (hp,args)
  in
  let double_check_one_constr unk_hp_locs cs_hprels=
    let unk_hp_names = List.map (fun (hp, _) -> hp) unk_hp_locs in
    let cs_hp_args = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq (cs_hprels) in
    let cs_unk_hps,cs_non_unk_hps = List.partition
        (fun (hp,_) -> CP.mem_svl hp unk_hp_names) cs_hp_args in
    (* definitely non unk*)
    let cs_non_unk_svl = List.concat (List.map (fun (_, args) -> args) cs_non_unk_hps) in
    let cs_non_unk_svl1 =
      CP.remove_dups_svl (* (CF.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) *) cs_non_unk_svl
      (* ) *)
    in
    (*possible unk*)
    let unk_svl_hps = List.concat (List.map (retrieve_args_one_hp unk_hp_locs) cs_unk_hps) in
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

(*this method has the same structure with elim_redundant_paras_lst_constr_x,
  should use higher-order when stab.*)
and analize_unk prog hp_rel_unkmap constrs =
  let rec partition_cands_by_hp_name unks parts=
    match unks with
    | [] -> parts
    | (hp_name,ids)::xs ->
      let part,remains= List.partition (fun (hp_name1,_) -> CP.eq_spec_var hp_name1 hp_name) xs in
      partition_cands_by_hp_name remains (parts@[[(hp_name,ids)]@part])
  in
  let intersect_cand_one_hp ls=
    let hp_names,cands = List.split ls in
    let () = Debug.ninfo_zprint (lazy (("   hprel: " ^ (!CP.print_svl hp_names)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)))) no_pos in
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
  let unk_hps = List.fold_left (fun ls (hps,_) ->ls@(List.map fst hps)) [] hp_rel_unkmap in
  let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map (analize_unk_one prog unk_hps) constrs) in
  let unk_hp_args01,_ = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
  (*for debugging*)
  let () = Debug.ninfo_pprint ("  unks 1: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                               in pr unk_hp_args01)) no_pos
  in
  (*END for debugging*)
  (*double check across one cs*)
  let rec loop_helper unk_hp_locs0=
    let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map (double_check_unk prog unk_hp_locs0 unk_hps) constrs) in
    let unk_hp_args02,full_unk_hp_args2_locs = helper (ls_unk_cands,ls_full_unk_cands_w_args) in
    let ls_unk_cands1 = Gen.BList.remove_dups_eq Sautil.check_hp_locs_eq unk_hp_args02 in
    let () = Debug.ninfo_pprint ("  ls_unk_cands1: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                                        in pr ls_unk_cands1)) no_pos
    in
    if ls_unk_cands1 = [] then [],[] else
      let diff = Gen.BList.difference_eq Sautil.check_hp_locs_eq unk_hp_locs0 ls_unk_cands1 in
      if diff =[] then (ls_unk_cands1, full_unk_hp_args2_locs) else
        loop_helper ls_unk_cands1
  in
  let unk_hp_args02,full_unk_hp_args2_locs = loop_helper unk_hp_args01 in
  (* let ls_unk_cands,ls_full_unk_cands_w_args = List.split (List.map (double_check_unk unk_hp_args01) constrs) in *)
  (* let ls_unk_cands,ls_full_unk_cands_w_args = double_check_unk_all unk_hp_args01 constrs in *)
  (* let unk_hp_args02,full_unk_hp_args2_locs = helper (ls_unk_cands,ls_full_unk_cands_w_args) in *)
  (*********END double check ****************)
  let full_unk_hp_args2_locs = Sautil.refine_full_unk2 unk_hp_args02 full_unk_hp_args2_locs in
  (*generate equivs mapping for all full unk hps*)
  let gen_equivs_from_full_unk_hps (hp,args,locs)=
    ((hp,locs), [(hp, args)])
  in
  let equivs0 = List.map gen_equivs_from_full_unk_hps full_unk_hp_args2_locs in
  (*for debugging*)
  let () = Debug.ninfo_pprint ("  unks 2: " ^ (let pr = pr_list (pr_pair !CP.print_sv (pr_list string_of_int))
                                               in pr unk_hp_args02)) no_pos
  in
  (* let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
  (*                            (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
  (* let () = Debug.info_zprint (lazy (("  equivs0: " ^ (pr1 equivs0) ))) no_pos in *)
  (*END for debugging*)
  (*END double check*)
  let rec update_helper cs cur_full_unk_hps res_cs res_unk_hps res_equivs=
    match cs with
    | [] ->  (res_cs, res_unk_hps, res_equivs)
    | c::ss ->
      let new_c, new_unk_hps,new_full_unk_hps, new_equivs= update_unk_one_constr prog unk_hp_args02
          cur_full_unk_hps res_equivs c in
      update_helper ss new_full_unk_hps (res_cs@[new_c]) (res_unk_hps@new_unk_hps) new_equivs
  in
  (* let cs_unk_hps = List.map (update_unk_one_constr prog unk_hp_args02) constrs in *)
  (* let new_cs, unk_hps,equivs = split3 cs_unk_hps in *)
  (* (new_cs, Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq (List.concat unk_hps), *)
  (* List.concat equivs) *)
  let new_cs, unk_hps,equivs = update_helper constrs
      (List.map (fun (hp,_,_) -> hp ) full_unk_hp_args2_locs) [] [] equivs0
  in
  (new_cs, Sautil.elim_eq_shorter_hpargs unk_hps, equivs)

and update_unk_one_constr_x prog unk_hp_locs cur_full_unk_hps equivs0 constr=
  (*return: unk_args*)
  let rec retrieve_args_one_hp ls (hp,args)=
    match ls with
    | [] -> ([])
    | (hp1,locs)::ss -> if CP.eq_spec_var hp hp1 then
        begin
          (*find unknown hprel*)
          if (List.length args) = (List.length locs) then
            (args)
          else
            ((Sautil.retrieve_args_from_locs args locs))
        end
      else retrieve_args_one_hp ss (hp,args)
  in
  let look_up_equiv_x (hp,lunk_args, allargs) equivs=
    let () = DD.ninfo_zprint (lazy (("       look up hp:" ^ (!CP.print_sv hp)))) no_pos in
    let rec helper eqs done_svl res=
      match eqs with
      | [] -> res
      | ((hp1,locs1),ls)::eqss ->
        if CP.eq_spec_var hp1 hp then
          (*retrieve unk_args0*)
          let unk_args0 = Sautil.retrieve_args_from_locs allargs locs1 in
          if CP.diff_svl unk_args0 done_svl = [] then
            helper eqss done_svl res
          else
            let inter = CP.intersect_svl unk_args0 lunk_args in
            (* let () = DD.info_zprint (lazy (("       inter:" ^ (!CP.print_svl inter)))) no_pos in *)
            if inter <> [] then
              let new_ls =
                match ls with
                | [(a,_)] -> [(a,inter,inter)]
                | _ -> report_error no_pos "sa.look_up_equiv"
              in
              let new_done_svl = done_svl@inter in
              if CP.diff_svl lunk_args new_done_svl = [] then
                res@[(new_ls,inter)]
              else helper eqss new_done_svl res@[(new_ls,inter)]
            else
              helper eqss done_svl res
        else helper eqss done_svl res
    in
    helper equivs [] []
  in
  let look_up_equiv (hp,lunk_args, allargs) equivs=
    let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int))
                             (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in
    let pr2 = pr_triple !CP.print_sv !CP.print_svl !CP.print_svl in
    let pr3 = pr_list_ln (pr_pair (pr_list (pr_triple !CP.print_sv !CP.print_svl !CP.print_svl)) !CP.print_svl) in
    Debug.no_2 "look_up_equiv" pr2 pr1 pr3
      (fun _ _ -> look_up_equiv_x (hp,lunk_args, allargs) equivs) (hp,lunk_args, allargs) equivs
  in

  let gen_eqv_x cur_equivs lohp_name lunk_args_locs lunk_svl unk_hp unk_hps=
    let lunk_args,lunk_locs = List.split lunk_args_locs in
    let rec filter_fn keep_svl svl res index=
      match svl with
      | [] -> res
      | sv::ss ->
        if CP.mem_svl sv keep_svl then
          filter_fn keep_svl ss (res@[(sv,index)]) (index+1)
        else filter_fn keep_svl ss res (index+1)
    in
    let rec helper ll res=
      match ll with
      | [] -> res
      | (hp0,args0)::hpss ->
        (*check hp0,lunk_locs is mapped or not*)
        (* let pr1 = (pr_pair !CP.print_sv !CP.print_svl) in *)
        (* let () = Debug.info_zprint (lazy (("  hp0:args0: " ^ (pr1 (hp0,args0))))) no_pos in *)
        if (List.exists (fun ((hp1,locs1),_) ->
            (* let pr = (pr_pair !CP.print_sv (pr_list string_of_int)) in *)
            (* let () = Debug.info_zprint (lazy (("  hp1:locs1: " ^ (pr (hp1,locs1))))) no_pos in *)
            CP.eq_spec_var hp1 hp0 &&
            List.length lunk_locs = List.length locs1 &&
            Gen.BList.difference_eq (=) lunk_locs locs1 = [])
            cur_equivs) then
          helper hpss res
        else
          let unk_args0, unk_locs0 = List.split (filter_fn lunk_args args0 [] 0) in
          if CP.diff_svl unk_args0 lunk_args = [] &&
             List.length unk_args0 = List.length lunk_args then
            helper hpss (res@[((hp0, unk_locs0), unk_hp)])
          else helper hpss res
    in
    helper unk_hps []
  in
  let gen_eqv cur_equivs lohp_name lunk_args_locs lunk_svl unk_hp unk_hps=
    let pr1 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int))
                             (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in
    let pr2 = pr_list (pr_pair !CP.print_sv string_of_int) in
    let pr3 = !CP.print_svl in
    let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
    Debug.no_6 "gen_eqv" pr1 !CP.print_sv pr2 pr3 pr4 pr4 pr1
      (fun _ _ _ _ _ _ -> gen_eqv_x cur_equivs lohp_name lunk_args_locs lunk_svl unk_hp unk_hps)
      cur_equivs lohp_name lunk_args_locs lunk_svl unk_hp unk_hps
  in
  (*split args into 2 groups: unk_hp and remains*)
  let get_par_unk_hp cs_unk_svl cs_unk_hps cs_full_unk_hps full_unk_hps equivs (hp, args)=
    let () = DD.ninfo_pprint ("     *******partial hp *********") no_pos in
    let () = DD.ninfo_zprint (lazy (("       partial hp:" ^ (!CP.print_sv hp)))) no_pos in
    (* let pr1 = pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
    (*                           (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
    (* let () = DD.info_zprint (lazy (("   equiv:" ^ (pr1 equivs)))) no_pos in *)
    (* let () = DD.info_zprint (lazy (("       full unkhps:" ^ (!CP.print_svl full_unk_hps)))) no_pos in *)
    (*********LOCAL FUNCTION***********)
    let look_up_unk_svl_one_hp hp args=
      let rec look_up_svl lunk_hp_locs =
        match lunk_hp_locs with
        | [] -> report_error no_pos "sa.look_up_un_svl_one_hp"
        | (hp1,locs1)::ls ->
          if CP.eq_spec_var hp1 hp then
            let args2 = Sautil.retrieve_args_from_locs args locs1 in
            List.combine args2 locs1
          else
            look_up_svl ls
      in
      look_up_svl unk_hp_locs
    in
    let rec loop_eqv_hps unk_hps lunk_args cs_unk_svl res=
      match unk_hps with
      | [] -> res
      | (hp0,args0)::hpss ->
        (*skip hp because we thave tried (look-up) it previously*)
        if CP.eq_spec_var hp hp0 then loop_eqv_hps hpss lunk_args cs_unk_svl res
        else
          (*look ip all hps (including itself) have the inter unk svs*)
          let unk_args0 = List.filter (fun sv -> CP.mem_svl sv cs_unk_svl) args0 in
          (* let () = DD.info_zprint (lazy (("       hp0:" ^ (!CP.print_sv hp0)))) no_pos in *)
          (* let () = DD.info_zprint (lazy (("       unk_args0:" ^ (!CP.print_svl unk_args0)))) no_pos in *)
          let inter = CP.intersect_svl lunk_args unk_args0 in
          if inter <> [] then
            if List.length inter = List.length lunk_args then
              (res@[(hp0,inter,args0)])
            else
              loop_eqv_hps hpss lunk_args cs_unk_svl (res@[(hp0,inter,args0)])
          else loop_eqv_hps hpss lunk_args cs_unk_svl res
    in
    let rec look_up_equiv_from_hps ls_hpargs res=
      match ls_hpargs with
      | [] -> res
      | hpargs::hpss ->
        let equivs = look_up_equiv hpargs equivs in
        if equivs = [] then
          look_up_equiv_from_hps hpss res
        else equivs
    in
    (*generate new unk annotation and create corr. equivs*)
    let gen_unk_hp hp_unk_svl_locs=
      let hp_unk_svl = fst (List.split hp_unk_svl_locs) in
      let hp_unk_svl_inst = List.map (fun sv -> (sv,NI)) hp_unk_svl in
      let unk_hf, sunk_hp = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) prog true true hp_unk_svl_inst no_pos in
      (*generate all matching: hp with similar unk_svl*)
      let new_equivs = gen_eqv equivs hp hp_unk_svl_locs cs_unk_svl [(sunk_hp, hp_unk_svl)] cs_unk_hps in
      (* let pr3 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) *)
      (*                         (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in *)
      (* let () = Debug.info_zprint (lazy (("  gen_unk_h:new_equivs: " ^ (pr3 new_equivs)))) no_pos in *)
      ([(sunk_hp, hp_unk_svl)],[unk_hf], new_equivs)
    in
    (*unk has been annotated already, just add it*)
    let process_one_match_eqv (sunk_hp,unk_args1,lunk_args)=
      let () = DD.ninfo_pprint ("       process_one_match_eqv:" ^
                                (let pr = (pr_pair !CP.print_sv !CP.print_svl) in
                                 pr (sunk_hp, lunk_args)))  no_pos
      in
      let unk_hfs =
        (*check whether there exists a local unk hp with the same set of unk svl?*)
        if (CP.mem_svl sunk_hp full_unk_hps) &&
           List.exists (fun (hp1,args,_) ->
               CP.eq_spec_var sunk_hp hp1 ||
               (CP.diff_svl args lunk_args = [] && List.length args = List.length lunk_args)
             ) cs_full_unk_hps
        then
          []
        else
          [Sautil.mkHRel sunk_hp lunk_args no_pos]
      in
      ((sunk_hp,unk_args1), unk_hfs)
    in
    let recover_locs hp_unk_svl unk_svl_locs=
      let rec find_loc lsvl_locs sv=
        match lsvl_locs with
        | [] -> report_error no_pos "sa.recover_locs"
        | (sv1,loc1)::ss -> if CP.eq_spec_var sv sv1 then ((sv1,loc1))
          else find_loc ss sv
      in
      List.map (find_loc unk_svl_locs) hp_unk_svl
    in
    (****END LOCAL FUNC*********)
    begin
      let unk_args_locs = look_up_unk_svl_one_hp hp args in
      (* let () = DD.info_pprint ("       unk_args_locs:" ^ *)
      (*                                (let pr = pr_list (pr_pair !CP.print_sv string_of_int) in *)
      (*                                 pr unk_args_locs)) *)
      (*   no_pos *)
      (* in *)
      (*look up in equiv first*)
      let unk_args,unk_locs = List.split unk_args_locs in
      let eqvs,matched_svls,new_equivs =
        let own_eqvs,own_matched_svls = List.split (look_up_equiv_from_hps
                                                                     (*equiv_hpargs*) [(hp, unk_args,args)] []) in
        (*retry with neighbor hp*)
        if own_eqvs = [] then
          let equiv_hpargs = loop_eqv_hps cs_unk_hps unk_args cs_unk_svl [] in
          (* let pr = pr_list_ln (pr_triple !CP.print_sv !CP.print_svl !CP.print_svl) in *)
          (* let () = DD.info_zprint (lazy (("   equiv_hpargs:" ^ (pr equiv_hpargs)))) no_pos in *)
          let ls = (look_up_equiv_from_hps equiv_hpargs []) in
          (*generate new mapping*)
          let new_equivs = List.map (fun (m,hp_unk_svl) ->
              let hp_unk_svl_locs = recover_locs hp_unk_svl unk_args_locs in
              (*remove third args in mapping*)
              let ls =
                match m with
                | [(a,b,_)] -> [(a,b)]
                | _ -> report_error no_pos "sa.look_up_equiv"
              in
              gen_eqv equivs hp hp_unk_svl_locs cs_unk_svl ls cs_unk_hps) ls
          in
          let ms,matched = List.split ls in
          (ms,matched,List.concat new_equivs)
        else (own_eqvs,own_matched_svls,[])
      in
      (*let pr = pr_list_ln (pr_triple !CP.print_sv !CP.print_svl !CP.print_svl) in *)
      (* let () = DD.ninfo_zprint (lazy (("   equiv_hps:" ^ (pr equiv_hpargs)))) no_pos in *)
      (*add new unk hp and eqv mapping*)
      let matched_svl = CP.remove_dups_svl (List.concat matched_svls) in
      (* let () = DD.info_pprint ("    matched_svl:" ^ (!CP.print_svl matched_svl)) *)
      (*   no_pos in *)
      let rem_unk_args_locs = List.filter(fun (arg,_) -> not(CP.mem_svl arg matched_svl)) unk_args_locs in
      let r11,r12,r13 = if rem_unk_args_locs = [] then [],[],[]
        else gen_unk_hp rem_unk_args_locs
      in
      (*matched eqv*)
      let ls = List.concat eqvs in
      let unk_hpargs,unk_hfss = List.split (List.map (process_one_match_eqv) ls) in
      ((unk_hpargs@r11), (List.concat unk_hfss)@(r12), (equivs@new_equivs@r13))
    end
  in
  let get_full_unk_hps unk_svl (hp, args)=
    (* let () = DD.info_zprint (lazy (("       hp:" ^ (!CP.print_sv hp)))) no_pos in *)
    let rec look_up_full_unk unk_hp_locs =
      match unk_hp_locs with
      | [] -> [],[]
      | (hp1,locs1)::ls ->
        if CP.eq_spec_var hp1 hp then
          if (List.length locs1) = (List.length args) then
            ([(hp,args,locs1)],[])
          else
            ([],[(hp,args)])
        else
          look_up_full_unk ls
    in
    look_up_full_unk unk_hp_locs
  in
  (*===========================*)
  let rec helper1 unk_svl oneside_unk_hps cs_unk_hps cs_full_unk_hps full_unk_hps res_unks res_hfs res_equivs=
    let rec loop_helper unk_svl rem_unk_hps res_unks res_hfs lres_equivs=
      match rem_unk_hps with
      | [] -> (res_unks, res_hfs, lres_equivs)
      | unk_hps::ss ->
        let unks, new_hfs,new_equivs = get_par_unk_hp unk_svl cs_unk_hps
            cs_full_unk_hps full_unk_hps lres_equivs unk_hps
        in
        loop_helper unk_svl ss (res_unks@unks) (res_hfs@new_hfs) new_equivs
    in
    loop_helper unk_svl oneside_unk_hps res_unks res_hfs res_equivs
  in
  (*===========================*)
  let helper lhs rhs equivs unk_hp_names=
    (*lhs*)
    let lhprels = CF.get_HRels_f lhs in
    (*hps have unk slv*)
    let l_cs_unk_hps,l_cs_non_unk_hps = List.partition
        (fun (hp,_) -> CP.mem_svl hp unk_hp_names) lhprels in
    (*unk*)
    let l_unk_svl = List.concat ((List.map (retrieve_args_one_hp unk_hp_locs) l_cs_unk_hps)) in
    let l_unk_svl = CP.remove_dups_svl l_unk_svl in
    (*rhs*)
    let rhprels = CF.get_HRels_f rhs in
    (*hps have unk slv*)
    let r_cs_unk_hps,r_cs_non_unk_hps = List.partition
        (fun (hp,_) -> CP.mem_svl hp unk_hp_names) rhprels in
    (*unk*)
    let r_unk_svl = List.concat ((List.map (retrieve_args_one_hp unk_hp_locs) r_cs_unk_hps)) in
    let unk_svl = CP.remove_dups_svl (l_unk_svl@r_unk_svl) in
    (* let unks, new_hfs,new_equivs = split3 (List.map (get_unk_hp unk_svl equivs) cs_unk_hps) in *)
    (*dynamic splitting: unk and non-unk*)
    (*filter all full unk_hps and non_unk_hps first*)
    let lres1,lres2 = List.split(List.map (get_full_unk_hps unk_svl) l_cs_unk_hps) in
    let l_full_unks = List.concat lres1 in
    let l_rems = List.concat lres2 in
    (*rhs*)
    let rres1,rres2 = List.split(List.map (get_full_unk_hps unk_svl) r_cs_unk_hps) in
    let r_full_unks = List.concat rres1 in
    let r_rems = List.concat rres2 in
    (*generate eqv for new full unk hps*)
    let new_equivs = List.concat (List.map (fun (hp,args,locs) ->
        gen_eqv equivs hp (List.combine args locs) unk_svl [(hp,args)] (l_cs_unk_hps@r_cs_unk_hps)
      ) (l_full_unks@r_full_unks)) in
    (*update*)
    let cs_full_unk_hps = List.map (fun (hp,_,_) -> hp) (l_full_unks@r_full_unks) in
    let new_total_full_unks = CP.remove_dups_svl (cur_full_unk_hps @ cs_full_unk_hps) in

    let l_unks, l_hfs, lequivs = helper1 unk_svl l_rems (l_cs_unk_hps@r_cs_unk_hps)
        (l_full_unks@r_full_unks) new_total_full_unks [] [] (equivs@new_equivs)
    in
    let r_unks, r_hfs,new_equivs = helper1 unk_svl r_rems (l_cs_unk_hps@r_cs_unk_hps)
        (l_full_unks@r_full_unks) new_total_full_unks [] [] lequivs
    in
    let unks = (List.map (fun (a,b,c) -> (a,b)) (l_full_unks@r_full_unks))@
               l_unks@r_unks in
    (******************************START******************************)
    (*currently, we do not add extract dangling hps into ass*)
    (*let n_lhs =
       match l_hfs with
         | [] -> lhs
         | _ ->
         let l = CF.pos_of_formula lhs in
         let new_hfs_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 l) (List.hd l_hfs) (List.tl l_hfs) in
         (* let split_hps,_ = List.split new_equivs in *)
            (*remove old hps*)
         (* let f1,_ = CF.drop_hrel_f f (fst (List.split split_hps)) in *)
         let f1 = lhs in
         let f2 = CF.mkAnd_f_hf f1 new_hfs_comb (CF.pos_of_formula f1) in
         f2
      in
      (*remove dups from rhs*)
      let new_r_hfs = Gen.BList.difference_eq (fun hf1 hf2 ->
        let hp1,_ = CF.extract_HRel hf1 in
        let hp2,_ = CF.extract_HRel hf2 in
        CP.eq_spec_var hp1 hp2
      )
      r_hfs l_hfs in
      let n_rhs =
       match new_r_hfs with
         | [] -> rhs
         | _ ->
         let l = CF.pos_of_formula rhs in
         let new_hfs_comb = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 l) (List.hd new_r_hfs) (List.tl new_r_hfs) in
         (* let split_hps,_ = List.split new_equivs in *)
            (*remove old hps*)
         (* let f1,_ = CF.drop_hrel_f f (fst (List.split split_hps)) in *)
         let f1 = rhs in
         let f2 = CF.mkAnd_f_hf f1 new_hfs_comb (CF.pos_of_formula f1) in
         f2
      in *)
    (*WHY DONOT?*)
    let n_lhs = lhs in
    let n_rhs = rhs in
    (*************************END***********************************)
    (n_lhs, n_rhs, unks, new_total_full_unks, unk_svl, new_equivs)
  in
  (*============BODY===============*)
  let unk_hp_names =  (List.map (fun (hp, _) -> hp) unk_hp_locs) in
  (* let lhs,lunk_hps,lunk_svl, lequv = helper constr.CF.hprel_lhs equivs0 unk_hp_names in *)
  (* let rhs,runk_hps,runk_svl, requv = helper constr.CF.hprel_rhs (lequv) unk_hp_names in *)
  let lhs,rhs,new_unk_hps, new_full_unk_hps ,new_unk_svl, new_equv = helper constr.CF.hprel_lhs constr.CF.hprel_rhs equivs0 unk_hp_names in
  let new_constr = {constr with
                    CF.unk_svl = CP.remove_dups_svl (constr.CF.unk_svl@new_unk_svl);
                    CF.unk_hps = Sautil.elim_eq_shorter_hpargs (constr.CF.unk_hps@new_unk_hps);
                    CF.hprel_lhs = lhs;
                    CF.hprel_rhs = rhs;
                   }
  in
  let () = Debug.ninfo_pprint ("   new hrel: " ^
                               (Cprinter.string_of_hprel new_constr)) no_pos in
  (new_constr,new_unk_hps, new_full_unk_hps, new_equv)

and update_unk_one_constr prog unk_hp_locs cur_full_unk_hps equivs0 constr=
  let pr1 = pr_list (pr_pair !CP.print_sv (pr_list string_of_int)) in
  let pr2 =  pr_list_ln (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int))
                           (pr_list (pr_pair !CP.print_sv !CP.print_svl))) in
  let pr3 = Cprinter.string_of_hprel in
  let pr4 = !CP.print_svl in
  let pr5 = fun (a,_,_,d) -> (pr3 a) ^ " \n eqvs:" ^ (pr2 d) in
  Debug.no_4 "update_unk_one_constr" pr1 pr4 pr2 pr3 pr5
    (fun _ _ _ _ -> update_unk_one_constr_x prog unk_hp_locs cur_full_unk_hps
        equivs0 constr) unk_hp_locs cur_full_unk_hps equivs0 constr

(*=============END UNKOWN================*)
(*END first step*)
(*=======================*)
(*check_partial_def_eq: to remove duplicate and identify terminating condition*)
let check_partial_def_eq_x (hp1, args1,_, cond1, olhs1, og1, orhs1) (hp2, args2,_, cond2, olhs2, og2, orhs2)=
  if (CP.eq_spec_var hp1 hp2) then (*if not the same hp, fast return*)
    (*form a subst*)
    let subst = List.combine args1 args2 in
    let checkeq_w_option of1 of2=
      match of1, of2 with
      | None,None -> true
      | Some _, None -> false
      | None, Some _ -> false
      | Some f1, Some f2 ->
        (*subs*)
        let f1_subst = x_add CF.subst subst f1 in
        let hvars = List.map (fun c -> CP.full_name_of_spec_var c) (CF.get_hp_rel_name_formula f1_subst @ CF.get_hp_rel_name_formula f2) in
        let r,_ (*map*) =  CEQ.checkeq_formulas hvars f1_subst f2 in
        r
    in
    ((checkeq_w_option olhs1 olhs2) && (checkeq_w_option orhs1 orhs2))(*  || *)
    (* ((checkeq_w_option olhs1 orhs2) && (checkeq_w_option orhs1 olhs2)) *)
  else false

let check_partial_def_eq par_def1 par_def2=
  let pr1 = Sautil.string_of_par_def_w_name in
  Debug.no_2 "check_partial_def_eq" pr1 pr1 string_of_bool
    (fun _ _ -> check_partial_def_eq_x par_def1 par_def2) par_def1 par_def2

(*should we mkAnd f1 f2*)
let rec find_defined_pointers_two_formulas_x prog f1 f2 predef_ptrs=
  let (def_vs1, hds1, hvs1, hrs1, eqs1,eqNulls1) = Sautil.find_defined_pointers_raw prog f1 in
  let (def_vs2, hds2, hvs2, hrs2, eqs2,eqNulls2) = Sautil.find_defined_pointers_raw prog f2 in
  Sautil.find_defined_pointers_after_preprocess prog (def_vs1@def_vs2) (hds1@hds2) (hvs1@hvs2)
    (hrs2) (eqs1@eqs2) (eqNulls1@eqNulls2) predef_ptrs

and find_defined_pointers_two_formulas prog f1 f2 predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
    let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_3 "find_defined_pointers_two_formulas" Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula pr1 pr4
    (fun _ _ _ -> find_defined_pointers_two_formulas_x prog f1 f2 predef_ptrs) f1 f2 predef_ptrs

(**********************************************************)
(*********aux functions for pardef collect********)
(**********************************************************)
(*if root + next ptr is inside args: ll_all_13a: G***)
let elim_direct_root_pto_x undef_args args prog hd_nodes hv_nodes=
  let root =
    if args = [] then report_error no_pos "sa.elim_direct_root_pto: hp should have at least one arguments"
    else List.hd args
  in
  if CP.mem_svl root undef_args then
    let next_ptrs_from_root = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes [root] in
    let next_ptrs_from_root1 = (CP.remove_dups_svl next_ptrs_from_root) in
    let next_ptrs_from_root2 = CP.diff_svl next_ptrs_from_root1 [root] in
    (* let () = Debug.info_zprint (lazy (("    next_ptrs_from_root2:" ^ (!CP.print_svl next_ptrs_from_root2)))) no_pos in *)
    let add_defs =
      if (next_ptrs_from_root2 <> []) && CP.diff_svl next_ptrs_from_root2 args = [] then
        ([root]@next_ptrs_from_root1)
      else []
    in
    let undef_args1 = CP.diff_svl undef_args add_defs in
    undef_args1
  else
    undef_args

let elim_direct_root_pto undef_args args prog hd_nodes hv_nodes=
  let pr1 = !CP.print_svl in
  Debug.no_2 "elim_direct_root_pto" pr1 pr1 pr1
    (fun _ _ -> elim_direct_root_pto_x undef_args args prog hd_nodes hv_nodes) undef_args args

let add_xpure_dling_x f unk_hpargs local_unk_svl=
  (* let cur_hps = CF.get_hp_rel_name_formula f in *)
  let rec sel_helper hpargs res=
    match hpargs with
    | [] -> res
    | (hp,args)::rest ->
      if (* not(CP.mem_svl hp cur_hps) && *)
        CP.diff_svl args local_unk_svl = [] then
        sel_helper rest (res@[(hp,args)])
      else sel_helper rest res
  in
  let ls_unk_hpargs = sel_helper unk_hpargs [] in
  if ls_unk_hpargs = [] then f else
    let _, p, _ = CF.generate_xpure_view ls_unk_hpargs [] in
    CF.mkAnd_pure f (MCP.mix_of_pure p) no_pos

let add_xpure_dling f unk_hpargs local_unk_svl=
  let pr1= Cprinter.prtt_string_of_formula in
  let pr2= pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_3 "add_xpure_dling" pr1 pr2 !CP.print_svl pr1
    (fun _ _ _ -> add_xpure_dling_x f unk_hpargs local_unk_svl)
    f unk_hpargs local_unk_svl

let rec collect_par_defs_one_side_one_hp_aux_x prog f (hrel, args) def_ptrs
    eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  let refine_neq_null neqNulls=
    let neqNulls1 = CF.find_close neqNulls eqs in
    let neqNulls2 = CP.diff_svl neqNulls1 expl_ptrs in
    CP.intersect_svl neqNulls2 args
  in
  begin
    Debug.ninfo_zprint (lazy ((" hp: "^ (!CP.print_sv hrel)))) no_pos;
    let () = DD.ninfo_zprint (lazy (("   def " ^(!CP.print_svl (def_ptrs@predef@unk_svl))))) no_pos in
    let def_ptrs1 = (List.fold_left Sautil.close_def (def_ptrs@predef@unk_svl) eqs) in
    let () = DD.ninfo_zprint (lazy (("   def1 " ^(!CP.print_svl def_ptrs1)))) no_pos in
    (*find definition in both lhs and rhs*)
    let undef_args = Sautil.lookup_undef_args args [] def_ptrs1 in
    (* let () = DD.ninfo_zprint (lazy (("   undef_args " ^(!CP.print_svl undef_args)))) no_pos in *)
    (*if root + next ptr is inside args: ll_all_13a: G***)
    let undef_args1 =  elim_direct_root_pto undef_args args prog hd_nodes hv_nodes in
    (* let () = DD.ninfo_zprint (lazy (("   undef_args1 " ^(!CP.print_svl undef_args1)))) no_pos in *)
    let args_neqNull_svl = refine_neq_null (CF.get_neqNull f) in
    let undef_args2 = CP.diff_svl undef_args1 args_neqNull_svl in
    let defined_args, _, _, _, _ = Sautil.find_defined_pointers prog f def_ptrs1 in
    let test1= (List.length undef_args2) = 0  || (defined_args <> []) in
    (*case 1*)
    (*this hp is well defined, synthesize partial def*)
    if test1 then
      let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args in
      let keep_ptrs1 = (List.fold_left Sautil.close_def keep_ptrs eqs) in
      let keep_ptrs2 = keep_ptrs1@ (CP.intersect_svl undef_args1 args_neqNull_svl)in
      let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs2) unk_hps) in
      (* let keep_unk_hps = [] in *)
      let l = CF.drop_data_view_hrel_nodes f Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs2 keep_ptrs2 keep_unk_hps in
      let test2 = (not (Sautil.is_empty_f l)) (* && (not (CF.is_only_neqNull predef keep_unk_hps l)) *) in
      if test2 then
        (* let () =  DD.info_pprint ("  l: \n" ^ *)
        (*                                 (Cprinter.prtt_string_of_formula l) ) no_pos in *)
        let lhs =
          if !Globals.pred_elim_dangling then
            let inter_unk_svl = CP.intersect_svl unk_svl keep_ptrs2 in
            if inter_unk_svl = [] || (CF.is_only_neqNull args keep_unk_hps l) then l else
              add_xpure_dling l unk_hps inter_unk_svl
          else l
        in
        let l_r = (hrel, args, (* CP.intersect_svl args *) unk_svl, CF.get_pure lhs, Some lhs, None, None) in
        let () =  DD.ninfo_pprint ("  partial defs: \n" ^
                                   (let pr =  Sautil.string_of_par_def_w_name in pr l_r) ) no_pos in
        [l_r]
      else []
    else []
  end

and collect_par_defs_one_side_one_hp_aux prog f (hrel, args) def_ptrs
    eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  let pr1 = pr_pair !CP.print_sv !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "collect_par_defs_one_side_one_hp_rhs" pr1 pr2 pr3
    (fun _ _ -> collect_par_defs_one_side_one_hp_aux_x prog f (hrel, args)
        def_ptrs eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs)
    (hrel, args) f

(*collect partial def for rhs hrels. diff from lhs, rhs includes rhs formula also*)
and collect_par_defs_one_side_one_hp_rhs_x prog lhs rhs (hrel, args) def_ptrs lhrels
    eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  begin
    Debug.ninfo_pprint (" collect pardef for rhs hps: ") no_pos;
    let nlhs = CF.mkStar lhs rhs CF.Flow_combine (CF.pos_of_formula lhs) in
    let pdefs = collect_par_defs_one_side_one_hp_aux_x prog nlhs (hrel, args) def_ptrs
        eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs
    in pdefs
    (* if pdefs = [] then *)
    (*     (\*CASE2: hp1(x1,x2,x3) --> h2(x1,x2,x3)* formula: hp such that have the same set of args in both sides*\) *)
    (*   (\*matching lhs-rhs- first*\) *)
    (*   let r_ls,_ = collect_par_defs_two_side_one_hp prog lhs rhs (hrel, args) *)
    (*     (unk_svl@predef) lhrels hd_nodes hv_nodes unk_hps false in *)
    (*   r_ls *)
    (* else pdefs *)
  end

and collect_par_defs_one_side_one_hp_rhs prog lhs rhs (hrel, args) def_ptrs
    lhrels eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  let pr1 = pr_pair !CP.print_sv !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "collect_par_defs_one_side_one_hp_rhs" pr1 pr2 pr3
    (fun _ _ -> collect_par_defs_one_side_one_hp_rhs_x prog lhs rhs
        (hrel, args) def_ptrs lhrels eqs hd_nodes hv_nodes unk_hps unk_svl
        predef expl_ptrs) (hrel, args) rhs

(*collect partial def ---> hp*)
and collect_par_defs_one_side_one_hp_x prog lhs rhs (hrel, args) ldef_ptrs rdef_ptrs
    rhrels eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  begin
    let () = Debug.ninfo_pprint ("   collect pardef for lhs hps: " ^ (!CP.print_sv hrel) ^
                                 (!CP.print_svl args) ) no_pos in
    let () = Debug.ninfo_zprint (lazy ((" unk_svl: "^ (!CP.print_svl unk_svl)))) no_pos in
    let lprocess_helper def_ptrs=
      let () =  DD.ninfo_pprint ("       def ---> hp: \n" ) no_pos in
      collect_par_defs_one_side_one_hp_aux_x prog lhs (hrel, args) ldef_ptrs
        eqs hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs
    in
    let rprocess_helper def_ptrs=
      (*find definition in lhs*)
      let undef_args = Sautil.lookup_undef_args args [] def_ptrs in
      (*if root + next ptr is inside args: ll_all_13a: G***)
      let undef_args1 =  elim_direct_root_pto undef_args args prog hd_nodes hv_nodes in
      let test1= (List.length undef_args1) = 0 in
      if test1 then
        (*case 1*)
        (*this hp is well defined, synthesize partial def*)
        let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args in
        let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) unk_hps) in
        let r = CF.drop_data_view_hrel_nodes rhs
            Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode
            Sautil.check_neq_hrelnode keep_ptrs keep_ptrs keep_unk_hps
        in
        let test2 = (not (Sautil.is_empty_f r)) && (not (CF.is_only_neqNull args keep_unk_hps r)) in
        if test2 then
          (*collect partial def ---> hp*)
          let l1 =
            let l=CF.drop_data_view_hrel_nodes lhs Sautil.check_nbelongsto_dnode
                Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs
                keep_ptrs keep_unk_hps
            in
            if (Sautil.is_empty_f l) || (CF.is_only_neqNull args keep_unk_hps l)  then None else
              let lhs =
                if !Globals.pred_elim_dangling then
                  let inter_unk_svl = CP.intersect_svl unk_svl keep_ptrs in
                  if inter_unk_svl = [] then l else
                    add_xpure_dling l unk_hps inter_unk_svl
                else l
              in
              Some lhs
          in
          let l_r = (hrel, args, (* CP.intersect_svl args *) unk_svl,CF.get_pure r, l1 , None, Some r) in
          let () =  DD.ninfo_pprint ("       hp ---> def: \n" ^
                                     (let pr =  Sautil.string_of_par_def_w_name in pr l_r) ) no_pos in
          [l_r]
        else
          []
      else []
    in
    let pdefs1 = lprocess_helper ldef_ptrs in
    let pdefs2 = rprocess_helper (ldef_ptrs@rdef_ptrs) in
    let pdefs = pdefs1@pdefs2 in
    if pdefs = [] then
      (*CASE2: hp1(x1,x2,x3) --> h2(x1,x2,x3)* formula: hp such that have the same set of args in both sides*)
      (*matching lhs-rhs- first*)
      let r_r,_ = collect_par_defs_two_side_one_hp prog lhs rhs (hrel, args) (unk_svl@predef)
          rhrels hd_nodes hv_nodes unk_hps in
      r_r
    else pdefs
  end

(*matching hps between lhs and rhs, if there exists, drop them*)
and collect_par_defs_one_side_one_hp prog lhs rhs (hrel, args) ldef_ptrs
    rdef_ptrs rhrels eq hd_nodes hv_nodes unk_hps unk_svl predef expl_ptrs=
  let pr1 = pr_pair !CP.print_sv !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "collect_par_defs_one_side_one_hp" pr1 pr2 pr3
    (fun _ _ -> collect_par_defs_one_side_one_hp_x prog lhs rhs (hrel, args) ldef_ptrs rdef_ptrs rhrels eq hd_nodes hv_nodes unk_hps unk_svl predef
        expl_ptrs) (hrel, args) lhs

(*collect hp1(x1,x2,x3) ---> hp2(x1,x2,x3) * F  partial def : drop after matching*)
(*: more general form: collect hp1(x1,x2,x3) ---> hp2(x1,x2) * F:
  x3 is defined/unknown/predef  partial def
*)

and collect_par_defs_two_side_one_hp_x prog lhs rhs (hrel, args)
    predef other_side_hrels hd_nodes hv_nodes unk_hps (*is_lhs*)=
  let () =  DD.ninfo_zprint (lazy (("    lhs hrel:" ^ (!CP.print_sv hrel) ))) no_pos in
  let args0 = CP.remove_dups_svl args in
  let args01 = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args0 in
  (* let () =  DD.ninfo_zprint (lazy (("    args0:" ^ (!CP.print_svl args0) ))) no_pos in *)
  let () =  DD.ninfo_zprint (lazy (("    args01:" ^ (!CP.print_svl args01) ))) no_pos in
  let () =  DD.ninfo_zprint (lazy (("    predef:" ^ (!CP.print_svl predef) ))) no_pos in
  let unk_svl = List.fold_left (fun svl (_,svl2) -> svl@svl2) [] unk_hps in
  let rec find_hrel_w_same_set_args_one_hpargs (hp, args1) r res=
    match r with
    | [] -> [],res
    | (hps, keep_args, rem_args1)::ss ->
      let args0 = CP.remove_dups_svl rem_args1 in
      let args01 = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args0 in
      (* let () =  DD.info_zprint (lazy (("    args01:" ^ (!CP.print_svl args01) ))) no_pos in *)
      (*recompute def_ptrs *)
      (* let () =  DD.info_zprint (lazy (("    rhs hrel:" ^ (!CP.print_sv hp) ))) no_pos in *)
      (*elim recursive cases*)
      if CP.eq_spec_var hrel hp || CP.intersect args01 args1 = [] ||
         Gen.BList.difference_eq CP.eq_spec_var args1 predef = [] then
        find_hrel_w_same_set_args_one_hpargs (hp, args1) ss (res@[(hps, keep_args, rem_args1)])
      else begin
        (*find all defined pointer (null, nodes) and recursive defined parameters (HP, arg)*)
        let n_predef = CP.remove_dups_svl (predef@keep_args@args1) in
        let () =  DD.ninfo_zprint (lazy (("    n_predef:" ^ (!CP.print_svl n_predef) ))) no_pos in
        let l_def_ptrs, _,_, _,_ = Sautil.find_defined_pointers prog lhs n_predef in
        let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog lhs rhs n_predef in
        (* let () =  DD.ninfo_zprint (lazy (("    defs:" ^ (!CP.print_svl (l_def_ptrs@r_def_ptrs)) ))) no_pos in *)
        let undef_args = Sautil.lookup_undef_args args01 [] (l_def_ptrs@r_def_ptrs@n_predef) in
        (* let () =  DD.info_zprint (lazy (("    undef_args:" ^ (!CP.print_svl undef_args) ))) no_pos in *)
        if undef_args = [] then
          [(hps@[hp], CP.remove_dups_svl (keep_args@args1@rem_args1) )],[] (*collect it*)
        else
          let keep_args_in_rem = CP.diff_svl rem_args1 undef_args in
          find_hrel_w_same_set_args_one_hpargs (hp, args1) ss (r@[(hps@[hp], CP.remove_dups_svl (keep_args@args1@keep_args_in_rem), undef_args)])
      end
  in
  let rec find_hrels_w_same_set_args ls cur_par_list r=
    match ls with
    | [] -> r
    | hpargs1::ss ->
      let res,new_par_list = find_hrel_w_same_set_args_one_hpargs hpargs1 cur_par_list [] in
      if res = [] then
        find_hrels_w_same_set_args ss new_par_list r
      else res
  in
  (*find all hrel in rhs such that cover the same set of args*)
  let r_selected_hrels = find_hrels_w_same_set_args other_side_hrels [([hrel],[],args0)] [] in
  let build_par_def lhs0 (hps,args0)=
    let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args0 in
    let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) unk_hps) in
    (* if is_lhs then *)
    let pdef_rhs = CF.drop_data_view_hrel_nodes rhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs (hps@keep_unk_hps) in
    let pdef_cond = CF.drop_data_view_hrel_nodes lhs0 Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs (keep_unk_hps) in
    let lhprel = CF.get_hprel pdef_cond in
    let bf =
      if lhprel = [] then pdef_rhs else
        let lhfs = List.map (fun hprel -> CF.HRel hprel) lhprel in
        let lhf = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 no_pos) (List.hd lhfs) (List.tl lhfs) in
        let pos = (CF.pos_of_formula pdef_rhs) in
        (* Sautil.compose_subs pdef_rhs (CF.formula_of_heap lhf pos) pos *)
        CF.mkAnd_f_hf pdef_rhs lhf pos
    in
    let pdefs = if Sautil.is_trivial bf (hrel, args) then [] else
      if not (Sautil.is_empty_f pdef_cond || CF.is_only_neqNull args keep_unk_hps pdef_cond) && CF.is_HRel_f bf then
        let r_hp,r_args = CF.extract_HRel_f bf in
        let pdef = CF.drop_data_view_hrel_nodes lhs0 Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs (keep_unk_hps@[hrel]) in
        let r_svl = CF.fv pdef in
        if CP.diff_svl r_args r_svl = [] then
          [(r_hp, r_args, unk_svl, CF.get_pure pdef_cond , Some pdef, None, None)]
        else []
      else
        let r_svl = CF.fv bf in
        if CP.diff_svl args r_svl = [] then
          [(hrel, args, unk_svl, CF.get_pure pdef_cond , None, None, Some bf)]
        else []
    in
    (pdefs,lhs)
  in
  let rec loop_helper lhs1 ls res=
    match ls with
    | [] -> res,lhs1
    | r_sel_hp::ss -> let r,nlhs =  build_par_def lhs1 r_sel_hp in
      loop_helper nlhs ss (res@r)
  in
  let rs,lhs_n = loop_helper lhs r_selected_hrels [] in
  let () =  DD.ninfo_pprint ("  partial defs - two side: \n" ^
                             (let pr = pr_list_ln Sautil.string_of_par_def_w_name in pr rs) ) no_pos in
  rs,lhs_n

and collect_par_defs_two_side_one_hp prog lhs rhs (hrel, args) predef rhs_hrels hd_nodes hv_nodes unk_hps=
  let pr1 = pr_pair !CP.print_sv !CP.print_svl in
  let pr2 =  pr_list_ln pr1 in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr4 = pr_pair pr3 Cprinter.prtt_string_of_formula in
  Debug.no_2 "collect_par_defs_two_side_one_hp" pr1 pr2 pr4
    (fun _ _ -> collect_par_defs_two_side_one_hp_x prog lhs rhs (hrel, args) predef
        rhs_hrels hd_nodes hv_nodes unk_hps)
    (hrel, args) rhs_hrels

let collect_par_defs_recursive_hp_x prog lhs rhs (hrel, args) rec_args other_side_hrels def_ptrs hrel_vars eqs hd_nodes hv_nodes dir unk_hps unk_svl predef=
  let () =  DD.ninfo_zprint (lazy (("    rec hrel:" ^ (!CP.print_sv hrel) ))) no_pos in
  let () =  DD.ninfo_zprint (lazy (("    lhs:" ^ (Cprinter.string_of_formula lhs) ))) no_pos in
  let () =  DD.ninfo_zprint (lazy (("    rhs:" ^ (Cprinter.string_of_formula rhs) ))) no_pos in
  (* let () =  DD.info_zprint (lazy (("    args:" ^ (!CP.print_svl args) ))) no_pos in *)
  (* let () =  DD.info_zprint (lazy (("    rec args:" ^ (!CP.print_svl rec_args) ))) no_pos in *)
  let def_ptrs = CP.remove_dups_svl (List.fold_left Sautil.close_def (def_ptrs@predef@unk_svl) eqs) in
  let rec find_hrel_w_same_set_args_one_hpargs (hp, args1) r res=
    match r with
    | [] -> [],res
    | (hps, keep_args, rem_args1)::ss ->
      let args0 = CP.remove_dups_svl rem_args1 in
      let args01 = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes args0 in
      let () =  DD.ninfo_zprint (lazy (("    args01:" ^ (!CP.print_svl args01) ))) no_pos in
      (*recompute def_ptrs *)
      let () =  DD.ninfo_zprint (lazy (("    lhs hrel:" ^ (!CP.print_sv hp) ))) no_pos in
      (*elim recursive cases*)
      if (* CP.eq_spec_var hrel hp || *) CP.intersect args01 args1 = [] || Gen.BList.difference_eq CP.eq_spec_var args1 predef = [] then
        find_hrel_w_same_set_args_one_hpargs (hp, args1) ss (res@[(hps, keep_args, rem_args1)])
      else begin
        (*find all defined pointer (null, nodes) and recursive defined parameters (HP, arg)*)
        let n_predef = CP.remove_dups_svl (predef@keep_args@args1) in
        let () =  DD.ninfo_zprint (lazy (("    n_predef:" ^ (!CP.print_svl n_predef) ))) no_pos in
        let l_def_ptrs, _,_, _,_ = Sautil.find_defined_pointers prog lhs n_predef in
        let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog lhs rhs n_predef in
        (* let () =  DD.ninfo_zprint (lazy (("    defs:" ^ (!CP.print_svl (l_def_ptrs@r_def_ptrs)) ))) no_pos in *)
        let undef_args = Sautil.lookup_undef_args args01 [] (l_def_ptrs@r_def_ptrs@n_predef) in
        (* let () =  DD.info_zprint (lazy (("    undef_args:" ^ (!CP.print_svl undef_args) ))) no_pos in *)
        if undef_args = [] then
          [(hps@[hp], CP.remove_dups_svl (keep_args@args1@rem_args1) )],[] (*collect it*)
        else
          let keep_args_in_rem = CP.diff_svl rem_args1 undef_args in
          find_hrel_w_same_set_args_one_hpargs (hp, args1) ss (r@[(hps@[hp], CP.remove_dups_svl (keep_args@args1@keep_args_in_rem), undef_args)])
      end
  in
  let rec find_hrels_w_same_set_args ls cur_par_list r=
    match ls with
    | [] -> r
    | hpargs1::ss ->
      let res,new_par_list = find_hrel_w_same_set_args_one_hpargs hpargs1 cur_par_list [] in
      if res = [] then
        find_hrels_w_same_set_args ss new_par_list r
      else res
  in
  let build_partial_def (hps,args0)=
    let keep_ptrs = CF.look_up_reachable_ptr_args prog hd_nodes hv_nodes
        (CP.remove_dups_svl (args0@args@rec_args@unk_svl)) in
    let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) unk_hps) in
    let plhs = CF.drop_data_view_hrel_nodes lhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs (hps@keep_unk_hps) in
    let prhs = CF.drop_data_view_hrel_nodes rhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs (hps@keep_unk_hps) in
    (*find which formula contains root args*)
    let () = Debug.ninfo_zprint (lazy (("lpdef: " ^ (Cprinter.prtt_string_of_formula plhs)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("rpdef: " ^ (Cprinter.prtt_string_of_formula prhs)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("args: " ^ (!CP.print_svl args)))) no_pos in
    let () = Debug.ninfo_zprint (lazy (("rec_args: " ^ (!CP.print_svl rec_args)))) no_pos in
    let plhs1,prhs1=
      if !Globals.pred_elim_dangling then
        let inter_unk_svl = CP.intersect_svl unk_svl keep_ptrs in
        let plhs0 = add_xpure_dling plhs unk_hps inter_unk_svl in
        let prhs0 = add_xpure_dling prhs unk_hps inter_unk_svl in
        plhs0,prhs0
      else plhs,prhs
    in
    let () = Debug.ninfo_zprint (lazy ((" dir: " ^ (string_of_bool dir)))) no_pos in
    if dir then (*args in lhs*)
      begin
        let ptrs1 = CF.get_ptrs_f plhs in
        let ptrs2 = CF.find_close ptrs1 eqs in
        let () = Debug.ninfo_zprint (lazy (("ptrs2: " ^ (!CP.print_svl ptrs2)))) no_pos in
        if CP.intersect_svl args ptrs2 <> [] then
          [(hrel , args, (* CP.intersect_svl args *) unk_svl, CF.get_pure plhs, Some plhs1, None, Some prhs1)]
          (* (hrel , args, CP.intersect_svl args unk_svl ,plhs, Some prhs, Some plhs) *)
        else if CP.mem_svl (List.hd rec_args) ptrs1 then
          [(hrel , rec_args, (* CP.intersect_svl rec_args *) unk_svl , CF.get_pure plhs, Some plhs1, None, Some prhs1)]
        else []
      end
    else
      let ptrs1 = CF.get_ptrs_f prhs in
      let ptrs2 = CF.find_close ptrs1 eqs in
      let () = Debug.ninfo_zprint (lazy (("ptrs2: " ^ (!CP.print_svl ptrs2)))) no_pos in
      if CP.intersect_svl args ptrs2 <> [] then
        [(hrel , args, (* CP.intersect_svl args *) unk_svl , CF.get_pure plhs, Some plhs1, None, Some prhs1)]
      else if CP.mem_svl (List.hd rec_args) ptrs1 then
        [(hrel , rec_args, (* CP.intersect_svl args *) unk_svl ,CF.get_pure plhs, Some plhs1, None, Some prhs1)]
        (* (hrel , rec_args, CP.intersect_svl rec_args unk_svl ,plhs, Some prhs, Some plhs) *)
      else []
  in
  (* let () = Debug.info_zprint (lazy (("def_ptrs: " ^ (!CP.print_svl def_ptrs)))) no_pos in *)
  let rec_pdefs =
    let undef_args = Sautil.lookup_undef_args args [] (def_ptrs) in
    if undef_args = [] then
      let local_rec_defs = (build_partial_def ([hrel],args@rec_args)) in
      local_rec_defs
    else
      let keep_args_in_rem = CP.diff_svl (args@rec_args) undef_args in
      let ls_par_match =  [([hrel], CP.remove_dups_svl (keep_args_in_rem), undef_args)] in
      (*find all hrel in rhs such that cover the same set of args*)
      let r_selected_hrels = find_hrels_w_same_set_args other_side_hrels ls_par_match [] in
      let local_rec_pdefs = List.concat (List.map build_partial_def r_selected_hrels) in
      local_rec_pdefs
  in
  let () = DD.ninfo_pprint ("  rec partial defs: \n" ^
                            (let pr = pr_list_ln Sautil.string_of_par_def_w_name in pr (rec_pdefs)) ) no_pos in
  rec_pdefs

let collect_par_defs_recursive_hp prog lhs rhs (hrel, args) args2  other_side_hrels def_ptrs hrel_vars
    eq hd_nodes hv_nodes dir unk_hps unk_svl predef=
  let pr1 = !CP.print_svl in
  let pr2 = (pr_pair !CP.print_sv pr1) in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "collect_par_defs_recursive_hp" pr2 pr1 pr3
    (fun  _ _ -> collect_par_defs_recursive_hp_x prog lhs rhs (hrel, args)
        args2 other_side_hrels def_ptrs hrel_vars eq hd_nodes hv_nodes dir unk_hps unk_svl predef) (hrel, args) def_ptrs

let collect_par_defs_unk_hps_x lhs rhs lunk_hp_arg runk_hp_arg=
  (* let lxpures = CF.get_xpure_view lhs in *)
  (* let rxpures = CF.get_xpure_view rhs in *)
  (* let lunk_hp_arg0 = lunk_hp_arg@lxpures in *)
  (* let runk_hp_arg0 = runk_hp_arg@rxpures in *)
  let rec lhelper (hp1, args1) rls=
    match rls with
    | [] -> []
    | (hp2, args2)::ss -> if Sautil.eq_spec_var_order_list args1 args2 then
        [(hp1, args1),(hp2, args2)]
      else lhelper (hp1, args1) ss
  in
  let ls_matched = List.concat (List.map (fun lhp_args -> lhelper lhp_args runk_hp_arg) lunk_hp_arg) in
  if ls_matched = [] then ([],lhs,rhs)
  else
    begin
      let build_par_def ((lhp,largs),(rhp,rargs))=
        let plhs = CF.formula_of_heap (Sautil.mkHRel lhp largs no_pos) no_pos in
        let prhs = CF.formula_of_heap (Sautil.mkHRel rhp rargs no_pos) no_pos in
        ([(lhp,largs,largs, CF.get_pure plhs, None, None, Some prhs)],lhp,rhp)
      in
      let tr3 = List.map build_par_def ls_matched in
      let pdefs,lhps,rhps = split3 tr3 in
      let nlhs,_ = CF.drop_hrel_f lhs lhps in
      let nrhs,_ = CF.drop_hrel_f rhs rhps in
      (*for recursive, we keep exactly unkhps*)
      (* let inter = CP.intersect_svl lhps rhps in *)
      (* let rec_lhps = CP.diff_svl lhps inter in *)
      (* let rec_rhps = CP.diff_svl rhps inter in *)
      (* let rec_lhs,_ = CF.drop_hrel_f lhs rec_lhps in *)
      (* let rec_rhs,_ = CF.drop_hrel_f rhs rec_rhps in *)
      (List.concat pdefs, nlhs, nrhs)
    end

let collect_par_defs_unk_hps lhs rhs lunk_hp_arg runk_hp_arg=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv pr1) in
  let pr3 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr4 = Cprinter.prtt_string_of_formula in
  Debug.no_2 "collect_par_defs_unk_hps" pr2 pr2 (pr_triple pr3 pr4 pr4)
    (fun  _ _ -> collect_par_defs_unk_hps_x lhs rhs lunk_hp_arg runk_hp_arg) lunk_hp_arg runk_hp_arg

let rec collect_par_defs_one_constr_new_x prog callee_hps constr =
  let lhs, rhs = constr.CF.hprel_lhs, constr.CF.hprel_rhs in
  DD.ninfo_pprint ">>>>>> collect partial def for hp_rel <<<<<<" no_pos;
  DD.ninfo_zprint (lazy ((" hp_rel: " ^ (Cprinter.string_of_hprel constr)))) no_pos;
  let rec get_rec_pair_hps ls (hrel1, arg1)=
    if not (CP.mem_svl hrel1 callee_hps) then
      match ls with
      | [] -> []
      | (hrel2, arg2)::ss -> if CP.eq_spec_var hrel1 hrel2 then [((hrel1, arg1), (hrel2, arg2))]
        else get_rec_pair_hps ss (hrel1, arg1)
    else []
  in
  let cs_predef_ptrs = constr.CF.predef_svl@constr.CF.unk_svl in
  (*find all defined pointer (null, nodes) and recursive defined parameters (HP, arg)*)
  let l_def_ptrs, l_hp_args_name,l_dnodes, l_vnodes,leqs = Sautil.find_defined_pointers prog lhs cs_predef_ptrs in
  (* let () = DD.info_zprint (lazy (("   l_def_ptrs " ^(!CP.print_svl l_def_ptrs)))) no_pos in *)
  (*should mkAnd lhs*rhs?*)
  let r_def_ptrs, r_hp_args_name, r_dnodes, r_vnodes, reqs = find_defined_pointers_two_formulas prog lhs rhs cs_predef_ptrs in
  (*remove dup hp needs to be processed*)
  let filter_unk_hps unk_hpargs unk_svl (hp,args)=
    let rec helper unk_ls=
      match unk_ls with
      | [] -> true
      | (hp1,_)::hps ->
        if CP.eq_spec_var hp hp1 then false
        else
        if CP.diff_svl args unk_svl = [] then false
        else
          helper hps
    in
    helper unk_hpargs
  in
  let lhps = (Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq (l_hp_args_name)) in
  (* let lnon_unk_hps= Gen.BList.difference_eq Sautil.check_simp_hp_eq lhps constr.CF.unk_hps in *)
  let lnon_unk_hps= List.filter (filter_unk_hps constr.CF.unk_hps constr.CF.unk_svl) lhps in
  let rhps = (Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq (r_hp_args_name)) in
  (* let rnon_unk_hps= Gen.BList.difference_eq Sautil.check_simp_hp_eq rhps constr.CF.unk_hps in *)
  let rnon_unk_hps= List.filter (filter_unk_hps constr.CF.unk_hps constr.CF.unk_svl) rhps in
  let total_hps = (Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq (lhps@rhps)) in
  (*CASE 0: matching lhs-rhs: now unkown hps only*)
  let lunk_hps = Gen.BList.intersect_eq (* Sautil.check_hp_arg_eq *)Sautil.check_simp_hp_eq lhps constr.CF.unk_hps in
  let runk_hps = Gen.BList.intersect_eq (* Sautil.check_hp_arg_eq*) Sautil.check_simp_hp_eq rhps constr.CF.unk_hps in
  let unk_pdefs,nlhs,nrhs = collect_par_defs_unk_hps lhs rhs lunk_hps runk_hps in
  (*ptrs defined by h_formula_data*)
  let expl_ptrs = List.map (fun hd -> hd.CF.h_formula_data_node) (l_dnodes@r_dnodes) in
  (*CASE 1: formula --> hp*)
  let lpredef = CF.find_close (l_def_ptrs@cs_predef_ptrs) leqs in
  let rpredef = CF.find_close (r_def_ptrs) (leqs@reqs) in
  let l_unknown_hps = List.filter (fun (hp,_) -> not(CP.mem hp callee_hps)) lnon_unk_hps in
  let lpdefs = List.concat (List.map (fun hrel ->
      collect_par_defs_one_side_one_hp prog nlhs nrhs hrel lpredef rpredef rnon_unk_hps leqs (l_dnodes@r_dnodes) (l_vnodes@r_vnodes) constr.CF.unk_hps constr.CF.unk_svl constr.CF.predef_svl expl_ptrs) l_unknown_hps) in
  let r_unknown_hps = List.filter (fun (hp,_) -> not(CP.mem hp callee_hps)) rnon_unk_hps in
  let rpdefs = List.concat (List.map (fun hrel ->
      collect_par_defs_one_side_one_hp_rhs prog nlhs nrhs hrel lpredef lnon_unk_hps
        (leqs@reqs) (l_dnodes@r_dnodes) (l_vnodes@r_vnodes) constr.CF.unk_hps constr.CF.unk_svl
        constr.CF.predef_svl expl_ptrs)
      r_unknown_hps) in
  (*CASE2: hp1(x1,x2,x3) --> h2(x1,x2,x3)* formula: hp such that have the same set of args in both sides - call in side lhs*)
  (*CASE 3: recursive contraints*)
  let rec_pair_hps = List.concat (List.map (get_rec_pair_hps l_hp_args_name) r_hp_args_name) in
  let unk_hp_names = List.map (fun (hp_name,_) -> hp_name) constr.CF.unk_hps in
  let rec_pair_hps = List.filter (fun ((hp,_),_) -> not (CP.mem_svl hp unk_hp_names)) rec_pair_hps in
  (*for debugging*)
  (* let pr1 = (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let pr2 = pr_list_ln (pr_pair pr1 pr1) in *)
  (* Debug.ninfo_hprint (add_str "  recursive pair: " (pr2)) rec_pair_hps no_pos; *)
  (*END for debugging*)
  let new_constrs, rec_pdefs =
    if rec_pair_hps = [] then
      (*DONT DROP!! ll-next3.drop constraints that have one hp after collect partial def*)
      (* let new_constrs= *)
      (*   (\* let unk_hps = List.map (fun (hp,_) -> hp) (lnon_unk_hps@rnon_unk_hps) in *\) *)
      (*   if (List.length total_hps <=1) && (List.length (lnon_unk_hps@rnon_unk_hps)) = 0 then [] *)
      (*   else [constr] *)
      (* in *)
      ([constr], [])
    else
      let helper ((hp1,args1),(hp2,args2))=
        (*recompute defined ptrs*)
        let l_def_ptrs, _,_, _,_ = Sautil.find_defined_pointers prog nlhs (args2@cs_predef_ptrs) in
        (*should mkAnd lhs*rhs?*)
        let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog nlhs nrhs (args2@cs_predef_ptrs) in
        let r1 = collect_par_defs_recursive_hp prog nlhs nrhs (hp1,args1) args2 lnon_unk_hps
            (l_def_ptrs@r_def_ptrs@args2@cs_predef_ptrs) (l_hp_args_name@r_hp_args_name) (leqs@reqs)
            (l_dnodes@r_dnodes) (l_vnodes@r_vnodes) true constr.CF.unk_hps
            constr.CF.unk_svl constr.CF.predef_svl
        in
        if r1 = [] then
          (*recompute defined ptrs*)
          let l_def_ptrs, _,_, _,_ = Sautil.find_defined_pointers prog nlhs (args1@cs_predef_ptrs) in
          (*should mkAnd lhs*rhs?*)
          let r_def_ptrs, _, _, _, _ = find_defined_pointers_two_formulas prog nlhs nrhs (args1@cs_predef_ptrs) in
          collect_par_defs_recursive_hp prog nlhs nrhs (hp2,args2) args1 lnon_unk_hps
            (l_def_ptrs@r_def_ptrs@args1@cs_predef_ptrs) (l_hp_args_name@r_hp_args_name) (leqs@reqs)
            (l_dnodes@r_dnodes) (l_vnodes@r_vnodes) false constr.CF.unk_hps
            constr.CF.unk_svl constr.CF.predef_svl
        else r1
      in
      let rec_pdefs = List.concat (List.map helper rec_pair_hps) in
      (*if constr contains only one rec hp -drop it*)
      let new_constrs=
        let num_hp = (List.length (* (Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq (lnon_unk_hps@rnon_unk_hps)) *) total_hps) in
        let num_pair_rec_hp = (List.length rec_pair_hps) in
        if (num_hp - num_pair_rec_hp) < 1 then []
        else [constr]
      in
      (new_constrs, rec_pdefs)
  in
  let hppdefs = lpdefs @ rpdefs @ rec_pdefs @ unk_pdefs in
  (* let unk_hps = List.map (fun (hp,_) -> hp) constr.CF.unk_hps in *)
  (* let hppdefs1 = List.filter (fun (_,_,_,l,r)-> (Sautil.is_empty_wop l) || (Sautil.is_empty_wop r)) hppdefs in *)
  (new_constrs,hppdefs)

and collect_par_defs_one_constr_new prog callee_hps constr =
  let pr1 = Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr4 = pr_list_ln pr1 in
  let pr3 = (pr_pair pr4 pr2) in
  Debug.no_1 "collect_par_defs_one_constr_new" pr1 pr3
    (fun _ -> collect_par_defs_one_constr_new_x prog callee_hps constr) constr

(* - collect partial def
   - simplify: remove constaints which have <= 1 hp
*)
let rec collect_partial_definitions_x prog callee_hps constrs: (CF.hprel list * Sautil.par_def_w_name list) =
  let simpl_constrs, par_defs = List.split (List.map (collect_par_defs_one_constr_new prog callee_hps) constrs) in
  (List.concat simpl_constrs, List.concat par_defs)

and collect_partial_definitions prog callee_hps constrs: (CF.hprel list * Sautil.par_def_w_name list) =
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 =  pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_1 "collect_partial_definitions" pr1 (pr_pair pr1 pr2)
    (fun _ -> collect_partial_definitions_x prog callee_hps constrs) constrs


(*========SIMPLIFICATION============*)
let rec simplify_one_constr prog unk_hps constr=
  begin
    let (lhs, rhs) = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
    let qvars1, f1 = CF.split_quantifiers lhs in
    let qvars2, f2 = CF.split_quantifiers rhs in
    match f1,f2 with
    | CF.Base lhs_b, CF.Base rhs_b ->
      begin
        let l,r,matched = Sautil.simplify_one_constr_b prog unk_hps lhs_b rhs_b in
        (* if l.CF.formula_base_heap = CF.HEmp && *)
        (*   (MCP.isConstMTrue l.CF.formula_base_pure) then *)
        if CF.is_unknown_f (CF.Base l) || CF.is_unknown_f (CF.Base r) ||
           (Sautil.is_empty_f (CF.Base l) && Sautil.is_empty_f (CF.Base r)) then
          let () = DD.ninfo_pprint (" input: " ^(Cprinter.prtt_string_of_formula_base lhs_b) ^ " ==> " ^
                                    (Cprinter.prtt_string_of_formula_base rhs_b)) no_pos in
          let () =  DD.ninfo_pprint (" output: drop") no_pos in
          []
        else
          (*it may subst into some unk_hps, should detect it*)
          let hp_args = (CF.get_HRels l.CF.formula_base_heap)@
                        (CF.get_HRels r.CF.formula_base_heap) in
          let hp_args1 = Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq
              hp_args in
          (*get hp that all args are unk*)
          let unk_hp_args = List.filter (fun (hp,args) ->
              (Gen.BList.difference_eq CP.eq_spec_var args constr.CF.unk_svl) = []) hp_args1 in
          let new_constr = {constr with CF.predef_svl = constr.CF.predef_svl@matched;
                                        CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq
                                            (constr.CF.unk_hps@unk_hp_args);
                                        CF.hprel_lhs = CF.Base l;
                                        CF.hprel_rhs = CF.Base r;
                           }
          in
          let () =  DD.ninfo_zprint (lazy ((" simplify: new cs:" ^ ( Cprinter.string_of_hprel new_constr)))) no_pos in
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
(*===========END SIMPLIFICATION===========*)

(*========subst==============*)
(*****************)
let rec check_unsat_x f0=
  let rec helper f=
    match f with
    | CF.Base fb -> check_inconsistency fb.CF.formula_base_heap fb.CF.formula_base_pure
    | CF.Or orf -> (helper orf.CF.formula_or_f1) || (helper orf.CF.formula_or_f2)
    | CF.Exists fe ->
      (*may not correct*)
      check_inconsistency fe.CF.formula_exists_heap fe.CF.formula_exists_pure
  in
  helper f0

and check_unsat f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = string_of_bool in
  Debug.no_1 "check_unsat" pr1 pr2
    (fun _ -> check_unsat_x f) f

and check_inconsistency hf mixf=
  let new_mf = CF.xpure_for_hnodes hf in
  let cmb_mf = MCP.merge_mems mixf new_mf true in
  not (TP.is_sat_raw cmb_mf)

let check_heap_inconsistency unk_hpargs f0=
  let do_check hf=
    let hpargs = CF.get_HRels hf in
    (*remove dangling*)
    let hpargs1 = List.filter
        (fun (hp0,args0) ->
           not(Gen.BList.mem_eq Sautil.check_hp_arg_eq (hp0,args0) unk_hpargs))
        hpargs
    in
    Gen.BList.check_dups_eq Sautil.eq_spec_var_order_list (List.map snd hpargs1)
  in
  let rec helper f=
    match f with
    | CF.Base fb -> do_check fb.CF.formula_base_heap
    | CF.Or orf -> (helper orf.CF.formula_or_f1) || (helper orf.CF.formula_or_f2)
    | CF.Exists fe ->
      (*may not correct*)
      do_check fe.CF.formula_exists_heap
  in
  helper f0

(* let get_dups_hprel f0 f1= *)
(*   let hpargs0 =CF.get_HRels_f f0 in *)
(*   let hpargs1 =CF.get_HRels_f f1 in *)
(*   let ls_args0 = List.map snd hpargs0 in *)
(*   let dups_hps = List.concat (List.map (fun (hp,args) -> *)
(*       if Gen.BList.mem_eq Sautil.eq_spec_var_order_list  args ls_args0 then [hp] else []) *)
(*                                   hpargs1) *)
(*   in *)
(*   dups_hps *)

(*****************)
(*
x::node<a,b> .... ===> x::node<c,d> === ss={a/c;b/d} and
subst into rhs
*)
let do_simpl_nodes_match_x lhs rhs =
  let check_eq_data_node dn1 dn2=
    CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node
  in
  let sort_data_node_by_name dn1 dn2=
    String.compare (CP.name_of_spec_var dn1.CF.h_formula_data_node)
      (CP.name_of_spec_var dn2.CF.h_formula_data_node)
  in
  let rec get_subst lhds rhds res=
    match rhds,lhds with
    | [],_ -> res
    | _, [] -> res
    | dn2::rest2,dn1::rest1 ->
      let ss=
        if CP.eq_spec_var dn1.CF.h_formula_data_node dn2.CF.h_formula_data_node then
          List.combine dn2.CF.h_formula_data_arguments dn1.CF.h_formula_data_arguments
        else []
      in
      get_subst rest1 rest2 (res@ss)
  in
  let l_hds, _, _ = CF.get_hp_rel_formula lhs in
  let r_hds, _, _ = CF.get_hp_rel_formula rhs in
  let matched_data_nodes = Gen.BList.intersect_eq check_eq_data_node l_hds r_hds in
  let l_hds = Gen.BList.intersect_eq check_eq_data_node l_hds matched_data_nodes in
  let r_hds = Gen.BList.intersect_eq check_eq_data_node r_hds matched_data_nodes in
  let sl_hds = List.sort sort_data_node_by_name l_hds in
  let sr_hds = List.sort sort_data_node_by_name r_hds in
  let ss = get_subst sl_hds sr_hds [] in
  let n_rhs =
    if ss = [] then rhs
    else x_add CF.subst ss rhs
  in
  n_rhs

let do_simpl_nodes_match lhs rhs =
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "do_simpl_nodes_match" pr1 pr1 pr1
    (fun _ _ -> do_simpl_nodes_match_x lhs rhs) lhs rhs

let subst_one_cs_w_one_partial_def cs_unk_hps olhs f (hp_name, args,unk_svl, def_f)=
  (*drop hrel and get current args*)
  let new_f, argsl = CF.drop_hrel_f f [hp_name] in
  let do_subst newf eargs=
    (*generate a susbst*)
    let args2= (List.fold_left List.append [] (List.map CP.afv eargs)) in
    DD.ninfo_pprint ("   subst " ^ (Cprinter.prtt_string_of_formula def_f) ^ " ==> " ^ (!CP.print_sv hp_name)
                     ^ (!CP.print_svl args)) no_pos;
    DD.ninfo_zprint (lazy (("   into " ^ (Cprinter.prtt_string_of_formula f)))) no_pos;
    let subst = (List.combine args args2) in
    let def_f_subst = x_add CF.subst subst def_f in
    let unk_svl_subst = CP.subst_var_list subst unk_svl in
    DD.ninfo_zprint (lazy (("   body after subst " ^ (Cprinter.prtt_string_of_formula def_f_subst)))) no_pos;
    (*should remove duplicate*)
    let svl1 = CF.get_ptrs_f (* CF.get_all_sv_f *) newf in
    let svl2 = CF.get_ptrs_f (* CF.get_all_sv_f *) def_f_subst in
    let intersect = CP.intersect svl1 svl2 in
    DD.ninfo_zprint (lazy (("   intersect: " ^ (!CP.print_svl intersect)))) no_pos;
    (*node points to itself*)
    let def_f_hnodes = Sautil.get_hdnodes def_f_subst in
    let svl3 = List.fold_left (fun res hd -> if CP.intersect_svl [hd.CF.h_formula_data_node]
                                  hd.CF.h_formula_data_arguments <> [] then (res@[hd.CF.h_formula_data_node]) else res)
        [] def_f_hnodes in
    let elim_dnodes = CP.remove_dups_svl (intersect@svl3) in
    let def_f1 =
      if elim_dnodes = [] then def_f_subst else
        (* let diff = Gen.BList.difference_eq CP.eq_spec_var svl2 svl1 in *)
        match def_f_subst with
        | CF.Base fb ->
          CF.Base {fb with CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf fb.CF.formula_base_heap
                               Sautil.select_dnode Sautil.select_vnode
                               Sautil.select_hrel elim_dnodes elim_dnodes (intersect(* @(get_dups_hprel newf def_f_subst) *) )}
        | _ -> report_error no_pos "sa.subst_one_cs_w_one_partial_def"
    in
    (*combi def_f_subst into newf*)
    let newf1 = CF.mkStar newf def_f1 CF.Flow_combine (CF.pos_of_formula newf) in
    (*check contradiction*)
    let subst_f=
      if check_unsat newf1 || check_heap_inconsistency cs_unk_hps newf1 then
        let () = DD.ninfo_pprint ("     contradiction found after subst.") no_pos in
        f
      else newf1
    in
    DD.ninfo_zprint (lazy (("   subst out: " ^ (Cprinter.prtt_string_of_formula subst_f)))) no_pos;
    (*match with lhs if this is rhs*)
    (subst_f,unk_svl_subst)
  in
  match argsl with
  | [] -> (f,[])
  | (*[eargs]*) ls_eargs ->
    let new_f1,new_unk_svl =  List.fold_left (
        fun (f,ls) args ->  let nf, nunk_slv = do_subst f args in
          (nf, ls@nunk_slv)
      ) (new_f,[]) ls_eargs in
    begin
      match olhs with
      | None -> (new_f1,new_unk_svl)
      | Some lhs -> (do_simpl_nodes_match lhs new_f1,new_unk_svl)
    end

let elim_irr_rhs_hps_x lhs rhs=
  let l_svl = CF.fv lhs in
  let rhs0 = rhs in
  let r_hpargs = CF.get_HRels_f rhs0 in
  (*get hps in rhs*)
  let r_hps = List.map fst r_hpargs in
  let rhs1,_ =  CF.drop_hrel_f rhs r_hps in
  let r_svl = CF.fv rhs1 in
  let used_svl = (l_svl@r_svl) in
  let keep_hps = List.concat (List.map (Sautil.get_intersect_hps used_svl) r_hpargs) in
  let rhs2,_ =  CF.drop_hrel_f rhs0 (CP.diff_svl (CP.remove_dups_svl r_hps) (CP.remove_dups_svl keep_hps)) in
  rhs2

let elim_irr_rhs_hps lhs rhs=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "elim_irr_rhs_hps" pr1 pr1 pr1
    (fun _ _ -> elim_irr_rhs_hps_x lhs rhs) lhs rhs

(*
each constraints, apply lhs and rhs. each partial def in one side ==> generate new constraint

 ldef --> hp: subst all hp in lhs with ldef
 hp --> rdef: subst all hp in rhs with rdef
*)
let subst_one_cs_w_partial_defs ldefs rdefs constr=
  let lhs,rhs = constr.CF.hprel_lhs,constr.CF.hprel_rhs in
  DD.ninfo_zprint (lazy (("    input: " ^ (Cprinter.string_of_hprel constr)))) no_pos;
  let l_one_hps = CF.check_and_get_one_hpargs lhs in
  let r_one_hps = CF.check_and_get_one_hpargs rhs in
  match l_one_hps,r_one_hps with
  | [_],[_] -> [constr]
  | _ ->
    (*subst lhs*)
    let subst_one_side olhs (f,ls_unk_svl) pdef=
      let new_f,new_unk_svl = subst_one_cs_w_one_partial_def constr.CF.unk_hps olhs f pdef in
      (new_f,ls_unk_svl@new_unk_svl)
    in
    DD.ninfo_pprint "  subst lhs" no_pos;
    let lhs1,new_lunk_svl = List.fold_left (subst_one_side None) (lhs,[]) ldefs in
    (*subst rhs*)
    DD.ninfo_pprint "  subst rhs" no_pos;
    let rhs1,new_runk_svl = List.fold_left (subst_one_side (Some lhs1)) (rhs,[]) rdefs in
    (*rhs contradict with lhs?*)
    let cmbf = CF.mkStar lhs1 rhs1 CF.Flow_combine no_pos in
    let is_constra,lhs2,rhs2 =
      if check_unsat cmbf then
        let () = DD.ninfo_pprint ("      contradiction found between lhs and rhs") no_pos in
        (true,lhs,rhs)
      else
        (*remove redudant*)
        (false,lhs1,elim_irr_rhs_hps lhs1 rhs1)
    in
    (* let () = DD.info_pprint ("    out: " ^(Cprinter.prtt_string_of_formula lhs2) ^ " ==> " ^ *)
    (*                                (Cprinter.prtt_string_of_formula rhs2)) no_pos in *)
    if is_constra then [constr] else
      let new_cs ={constr with
                   CF.unk_svl = CP.remove_dups_svl (constr.CF.unk_svl@new_lunk_svl@new_runk_svl) ;
                   CF.hprel_lhs = lhs2;
                   CF.hprel_rhs = rhs2} in
      let () = DD.ninfo_zprint (lazy (("    output: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
      [new_cs]

let subst_cs_w_partial_defs_x hp_constrs par_defs=
  (*partition non-recursive partial defs: lhs set and rhs set*)
  let rec partition_par_defs pdefs lpdefs rpdefs=
    match pdefs with
    | [] -> (lpdefs, rpdefs)
    | (hp_name, hp_args,unk_svl, _, oldef, og,ordef)::ps ->
      (
        match oldef, ordef with
        | Some _ ,Some _ -> (*recursive par def -->currently omit*)
          partition_par_defs ps lpdefs rpdefs
        | Some f1, None -> (*lhs case*)
          let new_lpdef = if Cfutil.is_empty_heap_f f1 then [] else
              [(hp_name, hp_args,unk_svl, f1)] in
          partition_par_defs ps (lpdefs@new_lpdef) rpdefs
        | None, Some f2 -> (*rhs case*)
          let new_rpdef = if Cfutil.is_empty_heap_f f2 then [] else
              [(hp_name, hp_args,unk_svl, f2)] in
          partition_par_defs ps lpdefs (rpdefs@new_rpdef)
        | None, None -> (*can not happen*)
          report_error no_pos "sa.partition_par_defs: can not happen"
      )
  in
  let (ldefs, rdefs) = partition_par_defs par_defs [] [] in
  List.fold_left
    (fun ls cs -> let new_cs = subst_one_cs_w_partial_defs ldefs rdefs cs in
      ls@new_cs
    )
    [] hp_constrs

let subst_cs_w_partial_defs hp_constrs par_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "subst_cs_w_partial_defs" pr1 pr2 pr1
    (fun _ _ -> subst_cs_w_partial_defs_x hp_constrs par_defs) hp_constrs par_defs

(*
sth ====> A*HP1*HPn
substituted by HP1*HPn ====> b
(currently we only support HP1*HPn, we can enhance with
more general formula and use imply )
result is sth ====> A*b
*)
(* let subst_cs_w_other_cs_x constrs= *)
(*   (\* find all constraints which have lhs is a HP1*HPn ====> b *\) *)
(*   let check_lhs_hps_only constr= *)
(*     let lhs = constr.CF.hprel_lhs in *)
(*     let rhs = constr.CF.hprel_rhs in *)
(*     DD.ninfo_zprint (lazy (("      LHS: " ^ (Cprinter.prtt_string_of_formula lhs)))) no_pos; *)
(*     match lhs with *)
(*       | CF.Base fb -> if (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure)) then *)
(*             let r = (CF.get_HRel fb.CF.formula_base_heap) in *)
(*             (match r with *)
(*               | None -> [] *)
(*               | Some (hp, args) -> [(hp, args, rhs)] *)
(*             ) *)
(*           else [] *)
(*       | _ -> report_error no_pos "sa.subst_cs_w_other_cs: not handle yet" *)
(*   in *)
(*   let cs_substs = List.concat (List.map check_lhs_hps_only constrs) in *)
(*   (\* let () = if cs_substs = [] then DD.ninfo_pprint ("      EMPTY") no_pos else *\) *)
(*   (\*       DD.ninfo_pprint ("      NOT EMPTY") no_pos *\) *)
(*   (\* in *\) *)
(*   List.map (subst_one_cs_w_partial_defs [] cs_substs) constrs *)

(* let rec subst_cs_w_other_cs constrs= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hprel in *)
(*    Debug.no_1 "subst_cs_w_other_cs" pr1 pr1 *)
(*        (fun _ -> subst_cs_w_other_cs_x constrs) constrs *)

(*======================*)
(*
each lhs1, check rhs2 of other cs:
 - remove irrelevant svl of rhs2 (wrt. lhs1)
 - checkeq lhs1,rhs2: if yes
  - get susbt
  - form new cs (after subst): lhs2 -> rhs1
*)

(*input in fb
  output: true,susbs: can subst
*)

(*
dn is current node, it is one node of ldns
ss: subst from ldns -> ldns
*)
(* let rec get_closed_ptrs_one rdn ldns rdns rcur_match ss= *)
(*   (\* let () =  DD.info_zprint (lazy (("    rdn: " ^ (!CP.print_sv rdn) ))) no_pos in *\) *)
(*   let rec find_args_subst largs rargs lm rm= *)
(*     match largs, rargs with *)
(*       | [],[] -> (lm,rm) *)
(*       | la::ls,ra::rs -> if CP.mem_svl ra rcur_match then *)
(*             (\*find all matched previously. one lhs can match many rhs*\) *)
(*             let l_ss = fst (List.split (List.filter (fun (_,r) -> CP.eq_spec_var r ra) ss)) in *)
(*             let () =  DD.ninfo_zprint (lazy (("    l_ss: " ^ (!CP.print_svl l_ss) ))) no_pos in *)
(*             if CP.mem_svl la l_ss then *)
(*                let () =  DD.ninfo_zprint (lazy (("    la: " ^ (!CP.print_sv la) ))) no_pos in *)
(*                let () =  DD.ninfo_zprint (lazy (("    ra: " ^ (!CP.print_sv ra) ))) no_pos in *)
(*               find_args_subst ls rs lm rm (\*matched already*\) *)
(*             else find_args_subst ls rs (lm@[la]) (rm@[ra]) *)
(*           else find_args_subst ls rs (lm@[la]) (rm@[ra]) *)
(*       | _ -> report_error no_pos "sa.get_closed_ptrs: 1" *)
(*   in *)
(*   let rec look_up_rdn m_dn rdns res= *)
(*     match rdns with *)
(*       | [] -> res *)
(*       | (data_name,node_name,args)::rest -> *)
(*           let r= *)
(*             if CP.mem_svl m_dn (node_name::args) then *)
(*               [(data_name,node_name,args)] *)
(*             else [] *)
(*           in *)
(*           look_up_rdn m_dn rest (res@r) *)
(*   in *)
(*   if ldns = [] || rdns = [] then *)
(*     ([],[]) (\*either lhs1 or rhs2 does not have any node*\) *)
(*   else *)
(*     begin *)
(*         (\* let (ld_name, lsv, largs) = List.hd ldn_match in *\) *)
(*         (\* let (rd_name, rsv, rargs) = List.hd rdn_match in *\) *)
(*         let rec helper1 (ld_name, lsv, largs) rdn_m = *)
(*           match rdn_m with *)
(*             | [] -> [] *)
(*             | (rd_name, rsv, rargs)::rs -> *)
(*                 let () =  DD.ninfo_zprint (lazy (("    lsv: " ^ (!CP.print_sv lsv)))) no_pos in *)
(*                 let () =  DD.ninfo_zprint (lazy (("    rsv: " ^ (!CP.print_sv rsv)))) no_pos in *)
(*                 if (String.compare ld_name rd_name=0) && ((CP.eq_spec_var lsv rsv) || CP.intersect_svl rargs largs <> [])then *)
(*                   rsv::rargs *)
(*                 else helper1 (ld_name, lsv, largs) rs *)
(*         in *)
(*         let rec helper2 ldn_m= *)
(*           match ldn_m with *)
(*             | [] -> ([],[]) (\*all node intersected are diff in type*\) *)
(*             | (ld_name, lsv, largs):: ls -> *)
(*                 let lsv1 = CP.subs_one ss lsv in *)
(*                 (\* if CP.mem_svl lsv1 rcur_match then helper2 ls *\) *)
(*                 (\* else *\) *)
(*                   begin *)
(*                       let largs1 = List.map (CP.subs_one ss) largs in *)
(*                       (\*look_up rdn in rdns*\) *)
(*                       let cur_rdns = look_up_rdn rdn rdns [] in *)
(*                       let rargs = helper1 (ld_name, lsv1, largs1) cur_rdns in *)
(*                       if rargs = [] then helper2 ls *)
(*                       else *)
(*                         let () =  DD.ninfo_zprint (lazy (("    largs: " ^ (!CP.print_svl (lsv::largs))))) no_pos in *)
(*                         let () =  DD.ninfo_zprint (lazy (("    largs1: " ^ (!CP.print_svl (lsv1::largs1))))) no_pos in *)
(*                         let () =  DD.ninfo_zprint (lazy (("    rargs: " ^ (!CP.print_svl (rargs))))) no_pos in *)
(*                         find_args_subst (lsv::largs) rargs [] [] *)
(*                   end *)
(*         in *)
(*         let lm,rm = helper2 ldns in *)
(*         let () =  DD.ninfo_zprint (lazy (("    lm " ^ (!CP.print_svl (lm))))) no_pos in *)
(*         let () =  DD.ninfo_zprint (lazy (("    rm " ^ (!CP.print_svl (rm))))) no_pos in *)
(*         if lm = [] then ([],[]) (\*all node intersected are diff in type*\) *)
(*         else (rm, List.combine lm rm) *)
(*     end *)

(* and get_closed_matched_ptrs ldns rdns rcur_match ss= *)
(*   let rec helper old_m old_ss inc_m= *)
(*     let () =  DD.ninfo_zprint (lazy (("    old_m " ^ (!CP.print_svl old_m)))) no_pos in *)
(*     (\*find matching ldns and rdns*\) *)
(*     let r = List.map (fun m -> get_closed_ptrs_one m ldns rdns old_m old_ss) inc_m in *)
(*     let incr_match, incr_ss = List.split r in *)
(*     if incr_match = [] then *)
(*       old_m, old_ss *)
(*     else *)
(*       let n_incr_m = (List.concat incr_match) in *)
(*       helper (CP.remove_dups_svl (old_m@n_incr_m)) (old_ss@(List.concat incr_ss)) n_incr_m *)
(*   in *)
(*   helper rcur_match ss rcur_match *)

(* (\* *)
(*  lhs1 ==> rhs1 *)
(* find all constraints lhs2 ==> rhs2 such that *)
(*  rhs2 |- lhs1 --> l,r. *)
(* Note *)
(* - rhs2 may have more hps + hnode than lhs1 *)
(* - should return a subst from lhs1 to rhs2 since at the end *)
(* we have to combine rhs1 into r to form a new cs: *)
(*       lhs2*l ===> r*subst(rhs1) *)
(* *\) *)
(* and find_imply prog lunk_hps runk_hps lhs1 rhs1 lhs2 rhs2= *)
(*   let sort_hps_x hps = List.sort (fun (CP.SpecVar (_, id1,_),_) *)
(*       (CP.SpecVar (_, id2, _),_)-> String.compare id1 id2) hps *)
(*   in *)
(*   let sort_hps hps= *)
(*     let pr1 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
(*     Debug.no_1 "sort_hps" pr1 pr1 *)
(*         (fun _ ->  sort_hps_x hps) hps *)
(*   in *)
(* (\* *)
(*   let check_equiv_chains largs rargs ldns rdns= *)
(*     let rec find_root arg dns r= *)
(*       match dns with *)
(*         | [] -> false, r *)
(*         | dn::rest -> *)
(*             if CP.eq_spec_var dn.CF.h_formula_data_node arg then *)
(*               true,arg *)
(*             else if CP.mem_svl arg dn.CF.h_formula_data_arguments then *)
(*               let rs = List.filter (fun sv -> (CP.is_node_typ sv) && not(CP.eq_spec_var sv arg)) dn.CF.h_formula_data_arguments in *)
(*               if rs=[] then (false,r) else *)
(*                 find_root arg rest (List.hd rs) *)
(*             else *)
(*               find_root arg rest r *)
(*     in *)
(*     if List.length largs = 1 && List.length rargs = 1 then *)
(*       let is_node1,r1 = find_root (List.hd largs) ldns (List.hd largs) in *)
(*       let is_node2,r2 = find_root (List.hd rargs) rdns (List.hd rargs) in *)
(*       if is_node1 && is_node2 then *)
(*         let svl1 = CF.look_up_reachable_ptr_args prog ldns [] [r1] in *)
(*         let svl2 = CF.look_up_reachable_ptr_args prog rdns [] [r2] in *)
(*         (List.length svl1)=(List.length svl2) *)
(*       else *)
(*         false *)
(*     else *)
(*       false *)
(*   in *)
(*   *\) *)
(*   (\*precondition: ls1 and ls2 are sorted*\) *)
(*   (\*we may enhance here, ls1, ls2 are not necessary the same: ls2 >= ls1*\) *)
(*   let rec check_hrels_imply ls1 ls2 ldns rdns lhs_hps subst matched args res_rename= *)
(*     match ls1,ls2 with *)
(*       | [],[] -> (subst,matched,args,res_rename) *)
(*       | (id1, args1)::ss1,(id2, args2)::ss2 -> *)
(*           if CP.eq_spec_var id1 id2 then *)
(*             begin *)
(*                 (\* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *\) *)
(*                 (\*   !Globals.sa_equiv_chain && not(check_equiv_chains args1 args2 ldns rdns) then *\) *)
(*                 (\*   check_hrels_imply ls1 ss2 ldns rdns lhs_hps *\) *)
(*                 (\*     (subst) (matched) (args) res_rename *\) *)
(*                 (\* else *\) *)
(*                   check_hrels_imply ss1 ss2 ldns rdns lhs_hps *)
(*                     (subst@(List.combine args1 args2)) (matched@[id2]) (args@args2) res_rename *)
(*             end *)
(*           else (\* begin *\) *)
(*               (\* (\\*unk hps*\\) *\) *)
(*               (\* if CP.mem_svl id1 lunk_hps && CP.mem_svl id2 runk_hps && *\) *)
(*               (\*   List.length args1 = List.length args2 && not (List.mem id2 lhs_hps) then *\) *)
(*               (\*   check_hrels_imply ss1 ss2 lhs_hps (subst@(List.combine args1 args2)) *\) *)
(*               (\*       (matched@[id1]) (args@args2) (res_rename@[(id1,(id2,args2))]) *\) *)
(*               (\* else *\) *)
(*             check_hrels_imply ls1 ss2 ldns rdns lhs_hps subst matched args res_rename *)
(*           (\* end *\) *)
(*       | [], _ -> (subst,matched,args,res_rename) *)
(*       | _ -> ([],[],[],[]) *)
(*   in *)
(*   let transform_hrel (hp,eargs,_)= (hp, List.concat (List.map CP.afv eargs)) in *)
(*   let transform_dn dn= (dn.CF.h_formula_data_name, dn.CF.h_formula_data_node, *)
(*                         List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t ) dn.CF. h_formula_data_arguments) in *)
(*   let rec is_inconsistent_x ss done_ss= *)
(*     match ss with *)
(*       | [] -> false *)
(*       | (sv1,sv2)::rest-> *)
(*           try *)
(*               let sv22 = List.assoc sv1 (rest@done_ss) in *)
(*               if CP.eq_spec_var sv2 sv22 then *)
(*                 is_inconsistent_x rest (done_ss@[(sv1,sv2)]) *)
(*               else true *)
(*           with Not_found -> is_inconsistent_x rest (done_ss@[(sv1,sv2)]) *)
(*   in *)
(*   let rec is_inconsistent ss done_ss= *)
(*     let pr1= pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*     Debug.no_1 "is_inconsistent" pr1 string_of_bool *)
(*         (fun _ -> is_inconsistent_x ss done_ss) ss *)
(*   in *)
(*   (\*matching hprels and return subst*\) *)
(*   let ldns,lvns,lhrels = CF.get_hp_rel_bformula lhs1 in *)
(*   let rdns,_,rhrels = CF.get_hp_rel_bformula rhs2 in *)
(*   let l_rhrels = sort_hps (List.map transform_hrel lhrels) in *)
(*   let r_rhrels = sort_hps (List.map transform_hrel rhrels) in *)
(*   (\*m_args2: matched svl of rhs2*\) *)
(*   let subst,matched_hps, m_args2,rhs_hps_rename = check_hrels_imply l_rhrels r_rhrels ldns rdns (List.map fst l_rhrels) [] [] [] [] in *)
(*   let r= *)
(*     if matched_hps = [] then None *)
(*     else *)
(*       begin *)
(*           (\*for debugging*\) *)
(*           let () = Debug.ninfo_zprint (lazy (("     m_args2: " ^ (!CP.print_svl  m_args2)))) no_pos in *)
(*           let pr_ss = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
(*           let () =  Debug.ninfo_zprint (lazy (("     subst: " ^ (pr_ss subst)))) no_pos in *)
(*           (\*END for debugging*\) *)
(*       (\*matching hnodes (in matched_hps) and return subst*\) *)
(*           let lhns1 = List.map transform_dn ldns in *)
(*           let rhns1 = List.map transform_dn rdns in *)
(*           (\*all_matched_svl2: all matched slv of rhs2*\) *)
(*           let all_matched_svl2,subst1 =  get_closed_matched_ptrs lhns1 rhns1 m_args2 subst in *)
(*           let () = Debug.ninfo_zprint (lazy (("    all matched: " ^ (!CP.print_svl all_matched_svl2)))) no_pos in *)
(*           let () =  Debug.ninfo_zprint (lazy (("     subst1: " ^ (pr_ss subst1)))) no_pos in *)
(*           if  (is_inconsistent subst1 []) then None else *)
(*       (\*subst in lhs1*\) *)
(*           let n_lhs1 = CF.subst_b subst1 lhs1 in *)
(*           (\*check pure implication*\) *)
(*           let nldns,nlvns,_ = CF.get_hp_rel_bformula n_lhs1 in *)
(*           let lmf = CP.filter_var_new (MCP.pure_of_mix n_lhs1.CF.formula_base_pure) *)
(*             (CF.look_up_reachable_ptr_args prog nldns nlvns all_matched_svl2) in *)
(*           let rmf = (MCP.pure_of_mix rhs2.CF.formula_base_pure) in *)
(*           (\* let () = Debug.info_zprint (lazy (("    n_lhs1: " ^ (Cprinter.string_of_formula_base n_lhs1)))) no_pos in *\) *)
(*           let () = Debug.ninfo_zprint (lazy (("    lmf: " ^ (!CP.print_formula lmf)))) no_pos in *)
(*           let () = Debug.ninfo_zprint (lazy (("    rmf: " ^ (!CP.print_formula rmf)))) no_pos in *)
(*           let b,_,_ = x_add TP.imply_one 21 rmf lmf "sa:check_hrels_imply" true None in *)
(*           let lpos = (CF.pos_of_formula lhs2) in *)
(*           if b then *)
(*             let l_res = {n_lhs1 with *)
(*               CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf *)
(*                   n_lhs1.CF.formula_base_heap Sautil.select_dnode *)
(*                   Sautil.select_vnode Sautil.select_hrel  all_matched_svl2  all_matched_svl2 matched_hps} *)
(*             in *)
(*             (\*drop hps and matched svl in n_rhs2*\) *)
(*             let r_res = {rhs2 with *)
(*                 CF.formula_base_heap = CF.drop_data_view_hrel_nodes_hf *)
(*                     rhs2.CF.formula_base_heap Sautil.select_dnode *)
(*                     Sautil.select_vnode Sautil.select_hrel all_matched_svl2 all_matched_svl2 matched_hps; *)
(*                 CF.formula_base_pure = MCP.mix_of_pure *)
(*                     (CP.filter_var_new *)
(*                          (MCP.pure_of_mix rhs2.CF.formula_base_pure) all_matched_svl2)} *)
(*             in *)
(*             (\*avoid clashing --> should refresh remain svl of lhs2*\) *)
(*             let slv2 = CP.remove_dups_svl ((CF.fv lhs2)@ *)
(*                                                   (CF.fv (CF.Base rhs2))) in *)
(*             (\*do not rename HP names*\) *)
(*             let hp_names = CP.remove_dups_svl ((CF.get_hp_rel_name_formula lhs2)@(CF.get_hp_rel_name_bformula rhs2)) in *)
(*             (\*remove hp name*\) *)
(*             let diff1 = Gen.BList.difference_eq CP.eq_spec_var slv2 hp_names in *)
(*             let () = Debug.ninfo_zprint (lazy (("    diff1: " ^ (!CP.print_svl diff1)))) no_pos in *)
(*             (\*elim matched svl*\) *)
(*             let diff2 = Gen.BList.difference_eq CP.eq_spec_var diff1 all_matched_svl2 in *)
(*             let () = Debug.ninfo_zprint (lazy (("    diff2: " ^ (!CP.print_svl diff2)))) no_pos in *)
(*             (\*refresh it*\) *)
(*             let fresh_diff2 = CP.fresh_spec_vars diff2 in *)
(*             let ss2 = List.combine diff2 fresh_diff2 in *)
(*             let n_lhs2 = x_add CF.subst ss2 lhs2 in *)
(*             (\*end refresh*\) *)
(*             (\*combine l_res into lhs2*\) *)
(*             let l =  CF.mkStar n_lhs2 (CF.Base l_res) CF.Flow_combine lpos in *)
(*             let n_rhs1 = x_add CF.subst subst1 rhs1 in *)
(*             (\*avoid clashing --> should refresh remain svl of r_res*\) *)
(*             let r_res1 = x_add CF.subst ss2 (CF.Base r_res) in *)
(*             (\*elim duplicate hprel in r_res1 and n_rhs1*\) *)
(*             let nr_hprel = CF.get_HRels_f n_rhs1 in *)
(*             let nrest_hprel = CF.get_HRels_f r_res1 in *)
(*             let diff3 = Gen.BList.intersect_eq Sautil.check_hp_arg_eq nr_hprel nrest_hprel in *)
(*             let r_res2,_ = CF.drop_hrel_f r_res1 (List.map (fun (hp,_) -> hp) diff3) in *)
(*             let r = CF.mkStar n_rhs1 r_res2 CF.Flow_combine (CF.pos_of_formula n_rhs1) in *)
(*             (Some (l, r,subst1, ss2)) *)
(*           else None *)
(*       end *)
(*   in *)
(*   r *)

let rec find_imply_subst_x prog constrs=
  let rec check_constr_duplicate (lhs,rhs) constrs=
    match constrs with
    | [] -> false
    | cs::ss -> if Sautil.checkeq_pair_formula (lhs,rhs)
        (cs.CF.hprel_lhs,cs.CF.hprel_rhs) then
        true
      else check_constr_duplicate (lhs,rhs) ss
  in
  let find_imply_one cs1 cs2=
    let () = Debug.ninfo_zprint (lazy (("    rhs: " ^ (Cprinter.string_of_hprel cs2)))) no_pos in
    match cs1.CF.hprel_lhs,cs2.CF.hprel_rhs with
    | CF.Base lhs1, CF.Base rhs2 ->
      let r = Sautil.find_imply prog (List.map fst cs1.CF.unk_hps) (List.map fst cs2.CF.unk_hps) lhs1 cs1.CF.hprel_rhs cs2.CF.hprel_lhs rhs2 None [] [] in
      begin
        match r with
        | Some (l,r,lhs_ss, rhs_ss,_) ->
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
                            CF.unk_hps = Gen.BList.remove_dups_eq Sautil.check_hp_arg_eq
                                ((List.map (fun (hp,args) -> (hp,CP.subst_var_list lhs_ss args)) cs1.CF.unk_hps)@
                                 (List.map (fun (hp,args) -> (hp,CP.subst_var_list rhs_ss args)) cs2.CF.unk_hps));
                            CF.hprel_lhs = l;
                            CF.hprel_rhs = r;
                           }
              in
              let () = Debug.ninfo_zprint (lazy (("    new cs: " ^ (Cprinter.string_of_hprel new_cs)))) no_pos in
              [new_cs]
            end
        | None -> []
      end
    | _ -> report_error no_pos "sa.find_imply_one"
  in
  let rec helper don rest res=
    match rest with
    | [] -> res
    | cs::ss ->  (* let () = Debug.ninfo_zprint (lazy (("    ss size1: " ^ (string_of_int (List.length ss))))) no_pos in *)
      let () = Debug.ninfo_zprint (lazy (("    lhs: " ^ (Cprinter.string_of_hprel cs)))) no_pos in
      let r = List.concat (List.map (find_imply_one cs) (don@ss@res)) in
      (helper (don@[cs]) ss (res@r))
  in
  helper [] constrs []

and find_imply_subst prog constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "find_imply_subst" pr1 pr1
    (fun _ -> find_imply_subst_x prog constrs) constrs
and is_non_recursive_cs dang_hps constr=
  let lhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_lhs in
  let rhrel_svl = CF.get_hp_rel_name_formula constr.CF.hprel_rhs in
  ((CP.intersect lhrel_svl rhrel_svl) = [])

and subst_cs_w_other_cs_new_x prog dang_hps constrs=
  (*remove recursive cs*)
  let constrs1 = List.filter (is_non_recursive_cs dang_hps) constrs in
  (* let cs_susbsts = List.concat (List.map check_lhs_hps_only constrs) in *)
  (* List.concat (List.map (subst_one_cs_w_hps cs_susbsts) constrs) *)
  find_imply_subst prog constrs1
(*=========END============*)

let rec subst_cs_w_other_cs_new prog dang_hps constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "subst_cs_w_other_cs_new" pr1 pr1
    (fun _ -> subst_cs_w_other_cs_new_x prog dang_hps constrs) constrs

let simple_unk_info_check_x prog dang_hps constrs=
  (****************INTERNAL*****************)
  let rec update_other_cs non_unk_hps ls_non_unk_hp_locs ls_cs res=
    match ls_cs with
    | [] -> res
    | cs::rest ->
      let hpargs = Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq ((CF.get_HRels_f cs.CF.hprel_lhs)@(CF.get_HRels_f cs.CF.hprel_rhs)) in
      let non_unk_svl = CP.remove_dups_svl (List.fold_left (fun ls (hp,locs) ->
          try
            let args = List.assoc hp hpargs in
            let l_non_unk_svl = Sautil.retrieve_args_from_locs args locs in
            (ls@l_non_unk_svl)
          with Not_found -> ls
        ) [] ls_non_unk_hp_locs) in
      let cs1 = {cs with
                 CF.unk_hps = List.filter (fun (hp,_) -> not (CP.mem_svl hp  non_unk_hps)) cs.CF.unk_hps;
                 CF.unk_svl = CP.diff_svl cs.CF.unk_svl non_unk_svl}
      in
      update_other_cs non_unk_hps ls_non_unk_hp_locs rest (res@[cs1])
  in
  let rec helper1 args res index=
    match args with
    | [] -> res
    | a::ass -> helper1 ass (res@[index]) (index+1)
  in
  let process_one_cs rem cs=
    if cs.CF.unk_svl = [] then (rem,cs,[]) else
      let cur_cs_unk_hps = List.map fst cs.CF.unk_hps in
      let unk_hp_locs,unk_hp_args_locs = x_add analize_unk_one prog [] cs in
      let non_unk_hps,ls_non_unk_hp_locs,non_unk_svl =
        if unk_hp_locs = [] then
          let non_unk_hp_locs = List.map (fun (hp,args) -> (hp, helper1 args [] 0)) cs.CF.unk_hps in
          (cur_cs_unk_hps,non_unk_hp_locs,cs.CF.unk_svl)
        else
          (* let unk_hp_locs1 = List.filter (fun (hp,_) -> not(CP.mem_svl hp dang_hps) && *)
          (*     CP.mem_svl hp cur_cs_unk_hps) unk_hp_locs in *)
          let unk_hp_args_locs1 = List.filter (fun (hp,_,_) -> not(CP.mem_svl hp dang_hps) &&
                                                               CP.mem_svl hp cur_cs_unk_hps) unk_hp_args_locs in
          let non_unk_hp_args_locs = List.fold_left
              (fun ls (hp,args,locs) ->
                 let cmb = List.combine args locs in
                 let non_svl,non_locs = List.fold_left
                     (fun (ls1,ls2) (a,l) -> if CP.mem_svl a cs.CF.unk_svl
                       then (ls1,ls2) else
                         (ls1@[a],ls2@[l])
                     ) ([],[]) cmb in
                 if non_svl = [] then ls else
                   (ls@[(hp,non_svl,non_locs)])
              ) [] unk_hp_args_locs1
          in
          List.fold_left
            ( fun (ls1,ls2,ls3) (hp,non_unk_svl,non_unk_locs) ->
               (ls1@[hp],ls2@[(hp,non_unk_locs)],ls3@non_unk_svl)
            ) ([],[],[]) non_unk_hp_args_locs
      in
      (*update other cs*)
      let rem1 = if ls_non_unk_hp_locs = [] then rem else
          update_other_cs non_unk_hps ls_non_unk_hp_locs rem []
      in
      let cs1 = {cs with
                 CF.unk_hps = List.filter (fun (hp,_) -> not (CP.mem_svl hp  non_unk_hps)) cs.CF.unk_hps;
                 CF.unk_svl = CP.diff_svl cs.CF.unk_svl non_unk_svl}
      in
      (* let () = DD.info_zprint (lazy (("\n non_unk_svl: " ^ (!CP.print_svl non_unk_svl)))) no_pos in *)
      (* let () = DD.info_zprint (lazy (("\n non_unk_hps: " ^ (!CP.print_svl non_unk_hps)))) no_pos in *)
      (rem1,cs1,non_unk_hps)
  in
  let rec loop_helper ls_cs res_cs res_non_unk_hps=
    match ls_cs with
    | [] -> (res_cs, res_non_unk_hps)
    | cs::rest -> let rest1,cs1,non_unk_hps=process_one_cs rest cs in
      loop_helper rest1 (res_cs@[cs1]) (res_non_unk_hps@non_unk_hps)
  in
  loop_helper constrs [] []

let simple_unk_info_check prog dang_hps constrs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  Debug.no_1 "simple_unk_info_check" pr1 (pr_pair pr1 !CP.print_svl)
    (fun _  -> simple_unk_info_check_x prog dang_hps constrs)
    constrs

let subst_cs_x prog dang_hps hp_constrs par_defs =
  (*subst by constrs*)
  DD.ninfo_pprint "\n subst with other assumptions" no_pos;
  let new_cs =
    if (List.length hp_constrs) > 1 then
      subst_cs_w_other_cs_new prog dang_hps hp_constrs
    else []
  in
  (* let nonrec_new_cs,rec_new_cs= List.partition (is_non_recursive_cs dang_hps) new_cs in *)
  (*subst by partial defs*)
  DD.ninfo_pprint "\n subst with partial defs" no_pos;
  let constrs1 = subst_cs_w_partial_defs ((* nonrec_new_cs@ *)hp_constrs) par_defs in
  (*for each cs in new_cs, check unk*)
  let constrs2,non_unk_hps =  simple_unk_info_check prog dang_hps constrs1 in
  (constrs2@new_cs,non_unk_hps)

let subst_cs prog dang_hps hp_constrs par_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in
  Debug.no_2 "subst_cs" pr1 pr2 (pr_pair pr1 !CP.print_svl)
    (fun _ _ -> subst_cs_x prog dang_hps hp_constrs par_defs) hp_constrs par_defs

(*===========end subst============*)
(*========generalization==========*)
(*for par_defs*)
let generalize_one_hp_x prog hpdefs non_ptr_unk_hps unk_hps par_defs=
  (*collect definition for each partial definition*)
  let obtain_and_norm_def hp args0 (a1,args,og,f,unk_args)=
    (*normalize args*)
    let subst = List.combine args args0 in
    let f1 = (x_add CF.subst subst f) in
    let f2 =
      if !Globals.pred_elim_dangling then
        CF.annotate_dl f1 (List.filter (fun hp1 -> not (CP.eq_spec_var hp hp1)) unk_hps)
      else f1
    in
    let unk_args1 = List.map (CP.subs_one subst) unk_args in
    (* (\*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *\) *)
    (* (\*make explicit root*\) *)
    (* let r = *)
    (*   if args0 = [] then report_error no_pos "sa.obtain_and_norm_def: hp has at least one arg" *)
    (*   else (List.hd args0) *)
    (* in *)
    (* let f2 = Sautil.mk_expl_root r f1 in *)
    (f2,CF.subst_opt subst og, unk_args1)
  in
  (* let have_roots args f= *)
  (*   let svl = CF.fv f in *)
  (*   CP.intersect_svl args svl <> [] *)
  (* in *)
  DD.ninfo_pprint ">>>>>> generalize_one_hp: <<<<<<" no_pos;
  if par_defs = [] then ([],[]) else
    begin
      let hp, args,_, _,_ = (List.hd par_defs) in
      (*find the root: ins2,ins3: root is the second, not the first*)
      let args0 = List.map (CP.fresh_spec_var) args in
      (* DD.ninfo_zprint (lazy (((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")"))) no_pos; *)
      let defs,ogs,ls_unk_args = split3 (List.map (obtain_and_norm_def hp args0) par_defs) in
      let r,non_r_args = Sautil.find_root prog (hp::unk_hps) args0 defs in
      (*make explicit root*)
      let defs0 = List.map (Sautil.mk_expl_root r) defs in
      let unk_svl = CP.remove_dups_svl (List.concat (ls_unk_args)) in
      (*normalize linked ptrs*)
      let defs1,_ = List.split (Sautil.norm_hnodes_wg args0 (List.map (fun f -> (f, None)) defs0)) in
      (* let defs1 = Sautil.norm_hnodes args0 defs0 in *)
      (*remove unkhp of non-node*)
      let defs2 = (* List.map remove_non_ptr_unk_hp *) defs1 in
      (*remove duplicate*)
      let defs3 = Gen.BList.remove_dups_eq (fun f1 f2 -> Sautil.check_relaxeq_formula args f1 f2) defs2 in
      if CP.mem_svl hp unk_hps then
        (Sautil.mk_unk_hprel_def hp args0 defs3 no_pos,[])
      else
        let defs4,_ = List.split (Sautil.remove_equiv_wo_unkhps_wg hp args unk_hps (List.map (fun f -> (f, None)) defs3)) in
        (*remove duplicate with self-recursive*)
        (* let base_case_exist,defs4 = Sautil.remove_dups_recursive hp args0 unk_hps defs3 in *)
        (*find longest hnodes common for more than 2 formulas*)
        (*each hds of hdss is def of a next_root*)
        (* let defs5 = List.filter (fun f -> have_roots args0 f) defs4 in *)
        let defs,elim_ss = Sautil.get_longest_common_hnodes_list prog false hpdefs unk_hps unk_svl hp r non_r_args args0
            (List.map (fun f -> (f,None)) defs4) in
        if defs <> [] then (defs,elim_ss) else
          report_error no_pos "shape analysis: FAIL"
    end

let generalize_one_hp prog defs non_ptr_unk_hps unk_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  let pr3 = pr_list (pr_pair Cprinter.prtt_string_of_h_formula Cprinter.prtt_string_of_h_formula) in
  Debug.no_1 "generalize_one_hp" pr1 (pr_pair pr2 pr3)
    (fun _ -> generalize_one_hp_x prog defs non_ptr_unk_hps unk_hps par_defs) par_defs

let get_pdef_body unk_hps post_hps (a1,args,unk_args,a3,olf,og,orf)=
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

(* let get_pdef_body unk_hps post_hps (a1,args,unk_args,a3,olf,og,orf)= *)
(*   let pr1 = Sautil.string_of_par_def_w_name in *)
(*   let pr2 = pr_list (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl) in *)
(*   Debug.no_1 "get_pdef_body" pr1 pr2 *)
(*       (fun _ -> get_pdef_body unk_hps post_hps (a1,args,unk_args,a3,olf,og,orf) )(a1,args,unk_args,a3,olf,og,orf) *)

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

(*=========SUBST DEF FIX==========*)
(*
  divide hp into three groups:
  - independent - ready for genalizing
  - dependent:
      - depend on non-recursive groups: susbst
      - depend on recusive groups: wait
*)
let def_subst_fix prog unk_hps hpdefs=
  (*remove dups*)
  (* let unk_hps = CP.remove_dups_svl unk_hps in *)
  let is_rec_hpdef d=
    let (a1,_,_,f) = CF.flatten_hp_rel_def d in
    let hp = CF.get_hpdef_name a1 in
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_hpdef d=
    let (a1,_,_,f) = CF.flatten_hp_rel_def d in
    let hp = CF.get_hpdef_name a1 in
    let hps = CF.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_zprint (lazy (("       rec hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let _,rems = List.partition (fun hp1 -> CP.eq_spec_var hp hp1) hps in
    (* DD.ninfo_zprint (lazy (("       rec rems: " ^ (!CP.print_svl rems)))) no_pos; *)
    (rems = [])
  in
  let process_dep_hpdef hpdef rec_hps nrec_hpdefs=
    let (a1,hprel,g,f) = CF.flatten_hp_rel_def hpdef in
    let hp = CF.get_hpdef_name a1 in
    let fs = CF.list_of_disjs f in
    (* DD.ninfo_zprint (lazy (("       process_dep_group hp: " ^ (!CP.print_sv hp)))) no_pos; *)
    let succ_hp_args =  List.concat (List.map CF.get_HRels_f fs) in
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
      let ters,new_fs = List.split (List.map (fun f1 -> Sautil.succ_subst_hpdef prog [] nrec_hpdefs succ_hps1 (hp,args,g,f1)) fs) in
      (*check all is false*)
      (* let pr = pr_list string_of_bool in *)
      (* DD.ninfo_zprint (lazy (("       bool: " ^ (pr ters)))) no_pos; *)
      let new_fs = List.map fst (List.concat new_fs) in
      let ter = List.for_all (fun b -> not b) ters in
      let fs1  = Sautil.remove_longer_common_prefix_w_unk unk_hps new_fs in
      (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
      (* let () = DD.info_zprint (lazy (("       fs1: " ^ (pr1 fs1)))) no_pos in *)
      let b =
        if not ter then
          not (Sautil.checkeq_formula_list fs fs1)
        else false
      in
      (* let fs2 = Sautil.remove_subset new_fs1 in *)
      (*may be wrong: should reevauate root*)
      (b , CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args )) hprel [(CF.disj_of_list fs1 no_pos,g )] None)
    else
      (*return*)
      (false,hpdef)
  in
  let subst_first_dep_hpdef deps rec_hps nrec_hpdefs=
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
        (fun d -> CF.get_hpdef_name d.CF.def_cat)
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
    else (new_cur@new_rec_indps@new_nrec_indps)
  in
  let hpdefs = List.map (fun (a,b,c) -> CF.mk_hp_rel_def1 a b [(c,None)] None) hpdefs  in
  let res = helper_fix hpdefs [] [] in
  List.map (fun def -> (def.CF.def_cat,def.CF.def_lhs, def.CF.def_rhs)) res

(*this subst is to elim intermediate hps in final inferred hprel def
*)
(* let def_subst_fix prog unk_hps hpdefs= *)
(*   let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in *)
(*   Debug.no_1 "def_subst_fix" pr1 pr1 *)
(*       (fun _ -> def_subst_fix prog unk_hps hpdefs) hpdefs *)

(*=========END SUBST FIX==========*)

let subst_lhs_pdefs_w_impl hppdefs=
  let classify (hp1,args1,unk_args,a3,olf,orf)=
    match olf,orf with
    | Some f, None ->
      (*currently we just subst for recursive cases*)
      ([(hp1,args1,unk_args,a3,olf,orf)],[],[])
    | None, Some f ->
      if CF.is_HRel_f f then
        let hp2,args2 = CF.extract_HRel_f f in
        if Sautil.eq_spec_var_order_list args1 args2 then
          ([], [], [(hp2,hp1,(hp1,args1,unk_args,a3,olf,orf))])
        else ([(hp1,args1,unk_args,a3,olf,orf)], [], [])
      else ([(hp1,args1,unk_args,a3,olf,orf)], [], [])
    | Some f1, Some f2 -> ([],[(hp1,args1,unk_args,a3,f1,f2)],[])
    | None, None -> report_error no_pos "sa.add_hpdef_equiv_form: can't happen 2"
  in
  (* let rec partition_subst_by_to_hp subst parts= *)
  (*  match subst with *)
  (*    | [] -> parts *)
  (*    | (from_hp,to_hp)::xs -> *)
  (*        let part,remains= List.partition (fun (_,to_hp1) -> CP.eq_spec_var to_hp1 to_hp) xs in *)
  (*        partition_subst_by_to_hp remains (parts@[[(from_hp,to_hp)]@part]) *)
  (* in *)
  let subst_impl subst (hp1,args1,unk_args,a3,f1,f2)=
    let rec subst_helper ls to_hp0=
      match ls with
      | [] -> f1,[]
      | (from_hp,to_hp,_)::tl -> if CP.eq_spec_var to_hp to_hp0 then
          (CF.subst_hprel f1 [from_hp] to_hp,[(from_hp,to_hp)])
        else subst_helper tl to_hp0
    in
    let new_f1,matched=
      if CF.is_HRel_f f2 then
        let to_hp,_ = CF.extract_HRel_f f2 in
        subst_helper subst to_hp
      else (f1,[])
    in
    ((hp1,args1,unk_args,a3,Some new_f1, Some f2),matched)
  in
  let get_remain_from_subst subst subst_matched =
    let ls_pdefs = List.map
        (
          fun (fr_hp0,to_hp0,pdef) ->
            if List.exists (fun
                             (fr_hp1,to_hp1) ->
                             CP.eq_spec_var fr_hp0 fr_hp1 &&
                             CP.eq_spec_var to_hp0 to_hp1) subst_matched
            then [] else [pdef]
        )
        subst
    in
    List.concat ls_pdefs
  in
  let ls_pdefs0,ls_to_be_substed,ls_subst = split3 (List.map classify hppdefs) in
  let to_be_substed = List.concat ls_to_be_substed in
  let subst = List.concat ls_subst in
  (*START debugging*)
  (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
  (* let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in *)
  (* let tmp1 = List.map (fun (a1,a2,_) -> (a1,a2)) subst in *)
  (* let () = DD.info_zprint (lazy (("       subst: " ^ (pr1 tmp1)))) no_pos in *)
  (* let tmp = List.map (fun (a1,a2,a3,a4,a5,a6) -> (a1,a2,a3,a4,Some a5,Some a6)) to_be_substed in *)
  (* let () = DD.info_zprint (lazy (("       to_be_substed: " ^ (pr2 tmp)))) no_pos in *)
  (*END debugging*)
  (* let subst_grp = partition_subst_by_to_hp subst [] in *)
  let new_to_be_substed,ls_matched = List.split (List.map (subst_impl subst) to_be_substed) in
  let not_subst = get_remain_from_subst subst (List.concat ls_matched) in
  ((List.concat ls_pdefs0)@( new_to_be_substed)@not_subst)

(* let subst_lhs_pdefs_w_impl hppdefs= *)
(*   let pr1 = pr_list_ln Sautil.string_of_par_def_w_name in *)
(*   Debug.no_1 "subst_lhs_pdefs_w_impl" pr1 pr1 *)
(*       (fun _ -> subst_lhs_pdefs_w_impl hppdefs) hppdefs *)

let is_valid_pardef (_,args,_,f,_)=
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

(*remove neqNUll redundant*)
let remove_neqNull_helper (hp,args,og,f,unk_svl)=
  let f1 = CF.remove_neqNulls_f f in
  if Sautil.is_empty_f f1 then [] else [(hp,args,og,f1,unk_svl)]

let remove_neqNull_grp_helper grp=
  List.fold_left (fun r pdef-> let new_pdef = remove_neqNull_helper pdef in
                   r@new_pdef) [] grp

let generalize_hps_par_def_x prog non_ptr_unk_hps unk_hpargs post_hps par_defs=
  (*partition the set by hp_name*)
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
    | [] -> parts
    | (a1,a2,og,a3,a4)::xs ->
      let part,remains= List.partition (fun (hp_name,_,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
      partition_pdefs_by_hp_name remains (parts@[[(a1,a2,og,a3,a4)]@part])
  in
  let unk_hps = (List.map fst unk_hpargs) in
  (* let par_defs0 = subst_lhs_pdefs_w_impl par_defs in *)
  let par_defs1 = List.concat (List.map (get_pdef_body unk_hps post_hps) par_defs) in
  let par_defs2 = List.filter is_valid_pardef par_defs1 in
  let groups = partition_pdefs_by_hp_name par_defs2 [] in
  (*remove dups in each group*)
  let groups1 = List.map Sautil.remove_dups_pardefs_w_neqNull groups in
  (*remove neqNull*)
  (* let groups1a = (List.map remove_neqNull_grp_helper groups1) in *)
  (*
    subst such that each partial def does not contain other hps
    dont subst recursively
    search_largest_matching between two formulas
  *)
  (* let pr1 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl)) in *)
  (* let () = DD.info_zprint (lazy (("      groups1: " ^ (pr1 groups1)))) no_pos in *)
  (* let groups1b = Sautil.generate_equiv_pdefs unk_hps groups1 in *)
  let groups2 = pardef_subst_fix prog unk_hps groups1 in
  (* let () = Debug.info_pprint ("     END: " ) no_pos in *)
  (*remove empty*)
  let groups3 = List.filter (fun grp -> grp <> []) groups2 in
  (*each group, do union partial definition*)
  let hpdefs,elim_ss = List.fold_left (fun (hpdefs,elim_ss) pdefs->
      let new_defs,ss = generalize_one_hp prog hpdefs non_ptr_unk_hps unk_hps pdefs in
      ((hpdefs@new_defs), elim_ss@ss)
    ) ([],[]) groups3
  in
  let hpdefs1 =
    if !Globals.pred_elim_useless then
      List.map (fun (hp,def) ->
          (hp, {def with CF.def_rhs = List.map (fun (f, g) -> (CF.subst_hrel_f f elim_ss,g)) def.CF.def_rhs})) hpdefs
    else
      hpdefs
  in
  hpdefs1

let generalize_hps_par_def prog non_ptr_unk_hps unk_hpargs post_hps par_defs=
  let pr1 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr2 = Cprinter.string_of_hp_rel_def in
  let pr3 = fun (_,a)-> pr2 a in
  Debug.no_2 "generalize_hps_par_def" !CP.print_svl pr1 (pr_list_ln pr3)
    (fun _ _ -> generalize_hps_par_def_x prog non_ptr_unk_hps unk_hpargs post_hps par_defs) post_hps par_defs

let drop_unk_hps unk_hp_args cs=
  let unk_hps,_ = List.split unk_hp_args in
  (*get all cs hp_args*)
  let cs_hp_args = (CF.get_HRels_f cs.CF.hprel_lhs)@(CF.get_HRels_f cs.CF.hprel_rhs) in
  let cs_unk_hps = List.concat (List.map (fun (hp,_) -> if (CP.mem_svl hp unk_hps) then [hp] else []) cs_hp_args) in
  let cs_unk_hps =  CP.remove_dups_svl cs_unk_hps in
  (*drop them*)
  if cs_unk_hps = [] then
    cs
  else
    let n_lhs,_ = CF.drop_hrel_f cs.CF.hprel_lhs  cs_unk_hps in
    let n_rhs,_ = CF.drop_hrel_f cs.CF.hprel_rhs  cs_unk_hps in
    {cs with CF.hprel_lhs = n_lhs;
             CF.hprel_rhs = n_rhs;
    }

let generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs=
  let generalize_hps_one_cs constr=
    (* let () = DD.info_zprint (lazy (("         cs:" ^ (Cprinter.string_of_hprel constr)))) no_pos in *)
    (* let () = DD.info_zprint (lazy (("         hpdefs:" ^ (!CP.print_svl hpdefs)))) no_pos in *)
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
          let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
          let () = DD.ninfo_zprint (lazy (("         " ^ (!CP.print_sv hp) ^ " is defined already: drop the constraint"))) no_pos in
          ([constr],[])
        else if CP.mem_svl hp unk_hps then
          let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
          let () = DD.ninfo_zprint (lazy (("         " ^ (!CP.print_sv hp) ^ " is unknown. pass to next step"))) no_pos in
          ([constr],[])
        else
          let keep_ptrs = CF.look_up_reachable_ptr_args prog (lhds@rhds) (lhvs@rhvs) args in
          let p = CF.pos_of_formula lhs in
          (* let rhsp = match rhs with *)
          (*   | CF.Base fb -> fb.CF.formula_base_pure *)
          (*   | CF.Exists fe -> fe.CF.formula_exists_pure *)
          (*   | _ -> report_error no_pos "sa.collect_par_defs_one_side_one_hp_rhs_x: not handle yet" *)
          (* in *)
          let nlhs = CF.mkStar lhs rhs  CF.Flow_combine p in
          let hpargs = CF.get_HRels_f nlhs in
          let hpdefs1 =
            let lhps = CF.get_hp_rel_name_formula lhs in
            let rhps = CF.get_hp_rel_name_formula rhs in
            if (CP.intersect_svl lhps rhps) = [] then hpdefs else hpdefs@[hp]
          in
          let hpargs1 = List.filter (fun (hp1,_) -> CP.mem_svl hp1 hpdefs1) hpargs in
          let keep_def_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) hpargs1) in
          let r = CF.drop_data_view_hrel_nodes nlhs Sautil.check_nbelongsto_dnode Sautil.check_nbelongsto_vnode Sautil.check_neq_hrelnode keep_ptrs keep_ptrs keep_def_hps in
          if (not (Sautil.is_empty_f r)) then
            let () = DD.ninfo_pprint ">>>>>> generalize_one_cs_hp: <<<<<<" no_pos in
            (*should identify root. Now, root is the first, it may be wrong*)
            let () = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")=" ^
                                      (Cprinter.prtt_string_of_formula r) ) no_pos in
            ([],[CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args, List.tl args)) (*CF.formula_of_heap*)
                   (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, p)) [( r,None)] None ])
          else
            ([constr],[])
      end
    | _ -> ([constr],[]) (*keep constraint, no new definition*)
  in
  let r = List.map generalize_hps_one_cs cs in
  let cs1, hp_defs = List.split r in
  (*combine hp_defs*)
  let hpdefs = Sautil.combine_hpdefs (List.concat hp_defs) in
  (List.concat cs1, hpdefs)

let generalize_hps_cs prog callee_hps hpdefs unk_hps cs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr3  = pr_list Cprinter.string_of_hp_rel_def in
  let pr4 (_,b) = pr3 b in
  Debug.no_3 "generalize_hps_cs" pr1 !CP.print_svl !CP.print_svl pr4
    (fun _ _ _ -> generalize_hps_cs_x prog callee_hps hpdefs unk_hps cs) cs  callee_hps hpdefs

let get_unk_hps_relation_x prog callee_hps defined_hps post_hps hpdefs cs=
  let () = DD.ninfo_zprint (lazy (("         cs:" ^ (Cprinter.string_of_hprel cs)))) no_pos in
  let lhns, lhvs, lhrels = CF.get_hp_rel_formula cs.CF.hprel_lhs in
  let rhns, rhvs, rhrels = CF.get_hp_rel_formula cs.CF.hprel_rhs in
  let lhp_args = List.map (fun (hp,eargs, _) -> (hp, List.concat (List.map CP.afv eargs))) lhrels in
  let rhp_args = List.map (fun (hp,eargs, _) -> (hp, List.concat (List.map CP.afv eargs))) rhrels in
  let hp_args = Gen.BList.remove_dups_eq Sautil.check_simp_hp_eq (lhp_args@rhp_args) in
  let helper d= fst (List.split (CF.get_HRels d.CF.def_lhs)) in
  (*lookup all unk_hp of current cs*)
  let cs_unk_hps = (List.map (fun (hp,_) -> hp) cs.CF.unk_hps) in
  let cs_def_hps = List.concat (List.map helper hpdefs) in
  let def_hps, remains = List.partition (fun (hp,_) -> CP.mem_svl hp cs_def_hps) hp_args in
  let unk_hps, undef = List.partition (fun (hp,_) -> CP.mem_svl hp cs_unk_hps) remains in
  (* (\*for debugging*\) *)
  (* let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () = Debug.ninfo_zprint (lazy (("     lhps: " ^ (pr lhp_args)))) no_pos in *)
  (* let () = Debug.ninfo_zprint (lazy (("     rhps: " ^ (pr rhp_args)))) no_pos in *)
  (* let () = Debug.ninfo_zprint (lazy (("     all hps: " ^ (pr hp_args)))) no_pos in *)
  (* let () = Debug.ninfo_zprint (lazy (("     defs: " ^ (pr def_hps)))) no_pos in *)
  (* let () = Debug.info_zprint (lazy (("     unks1: " ^ (pr unk_hps)))) no_pos in *)
  (* let () = Debug.info_zprint (lazy (("     unks2: " ^ (pr cs.CF.unk_hps)))) no_pos in *)
  (* let () = Debug.info_zprint (lazy (("     undef: " ^ (pr undef)))) no_pos in *)
  (* (\*end for debugging*\) *)
  let new_defs1,rem_cs1=
    match undef with
    | [] -> [],[]
    | [(hp,args)] ->
      let hds = (lhns@rhns) in
      let hvs = (lhvs@rhvs) in
      let keep_ptrs = CF.look_up_reachable_ptr_args prog hds hvs args in
      let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_hps keep_ptrs) unk_hps) in
      let lhs = Sautil.keep_data_view_hrel_nodes prog cs.CF.hprel_lhs hds hvs keep_ptrs (keep_unk_hps) in
      let rhs = Sautil.keep_data_view_hrel_nodes prog cs.CF.hprel_rhs hds hvs keep_ptrs (keep_unk_hps) in
      let ltest = Sautil.is_empty_f lhs in
      let rtest = Sautil.is_empty_f rhs in
      if ltest && rtest then [], [cs]
      else
        let def_body =  CF.mkStar lhs rhs  CF.Flow_combine (CF.pos_of_formula lhs) in
        (
          (*  match def_body with *)
          (* | [] -> [], [cs] *)
          (* | [f] -> *)
          let f = def_body in
          begin
            DD.ninfo_pprint ">>>>>> from assumption to def: <<<<<<" no_pos;
            DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")=" ^
                             (Cprinter.prtt_string_of_formula f) ) no_pos;
            ([CF.mk_hp_rel_def1 (CP.HPRelDefn (hp, List.hd args,List.tl args))
                (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos)) [( f,None)] None],[])
          end
          (* | _ -> report_error no_pos "sa.get_unk_hps_relation" *)
        )
    | _ -> [],[cs]
  in
  (*should lunk_hps ---> runk_hps *)
  let lunk_hps, _ = List.partition (fun (hp,_) -> CP.mem_svl hp cs_unk_hps) lhp_args in
  let runk_hps, _ = List.partition (fun (hp,_) -> CP.mem_svl hp cs_unk_hps) rhp_args in
  (* (\*for debugging*\) *)
  (* let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let () = Debug.ninfo_zprint (lazy (("     l unk_hps: " ^ (pr lunk_hps)))) no_pos in *)
  (* let () = Debug.ninfo_zprint (lazy (("     r unk hps: " ^ (pr runk_hps)))) no_pos in *)
  (* (\*end for debugging*\) *)
  (*local helper*)
  let new_defs2,rem_cs2=
    if lunk_hps = [] || runk_hps = [] then ([],[cs])
    else
      let rels = List.concat (List.map
                                (fun (hp1,args1) -> List.map (fun (hp2,args2) ->
                                     if CP.intersect_svl args1 args2 = [] then []
                                     else
                                     if not(CP.mem_svl hp1 post_hps) && (CP.mem_svl hp2 post_hps) then
                                       (*hp2 is defined?*)
                                       if (CP.mem_svl hp2 (cs_def_hps@callee_hps)) then []
                                       else [((hp2,args2),(hp1,args1))]
                                     else
                                       [((hp1,args1),(hp2,args2))]) runk_hps)
                                lunk_hps)
      in
      (List.concat rels,[cs])
  in
  let cs3=
    if (rem_cs1@rem_cs2) = [] then []
    else [(List.hd (rem_cs1@rem_cs2))]
  in
  (cs3, new_defs1,new_defs2)

let get_unk_hps_relation prog callee_hps defined_hps post_hps hpdefs cs=
  let pr1 = Cprinter.string_of_hprel in
  let pr3 = pr_list_ln ( Cprinter.string_of_hp_rel_def) in
  let pr4 = pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) (pr_pair !CP.print_sv !CP.print_svl)) in
  Debug.no_4 "get_unk_hps_relation" pr1 pr3 !CP.print_svl !CP.print_svl (pr_triple (pr_list_ln pr1) pr3 pr4)
    (fun _ _ _ _-> get_unk_hps_relation_x prog callee_hps defined_hps post_hps hpdefs cs) cs hpdefs callee_hps defined_hps

let generate_defs_from_unk_rels prog unk_rels=
  let () = DD.ninfo_pprint ">>>>>> unk hps equivalent: <<<<<<" no_pos in
  let generate_unkhps_relation (hp1,args1) (hp2,args2) =
    let () = Debug.ninfo_zprint (lazy (("     candidate unks: " ^ (!CP.print_svl [hp1;hp2])))) no_pos in
    (* let pr = (pr_pair !CP.print_sv !CP.print_svl) in *)
    (* let () = Debug.info_zprint (lazy (("     l unk_hp: " ^ (pr (hp1,args1))))) no_pos in *)
    (* let () = Debug.info_zprint (lazy (("     r unk_hp: " ^ (pr (hp2,args2))))) no_pos in *)
    if CP.eq_spec_var hp1 hp2 || (List.length args1) <> (List.length args2) ||
       (CP.diff_svl args2 args1) <> []
    then []
    else
      begin
        let () = Debug.ninfo_zprint (lazy (("     unks: " ^ (!CP.print_svl [hp1;hp2])))) no_pos in
        let args = CP.remove_dups_svl (args1@args2) in
        (* let keep_unk_hps = List.concat (List.map (Sautil.get_intersect_unk_hps args) unk_hps) in *)
        let rhs = CF.formula_of_heap (CF.HRel (hp2, List.map (fun x -> CP.mkVar x no_pos) args2, no_pos)) no_pos in
        (* let () = Debug.ninfo_zprint (lazy (("      rhs: " ^ (Cprinter.prtt_string_of_formula rhs)))) no_pos in *)
        begin
          DD.ninfo_pprint ((!CP.print_sv hp1)^"(" ^(!CP.print_svl args) ^ ")=" ^
                           (Cprinter.prtt_string_of_formula rhs) ) no_pos;
          [CF.mk_hp_rel_def1 (CP.HPRelDefn (hp1, List.hd args1, List.tl args1)) (CF.HRel (hp1, List.map (fun x -> CP.mkVar x no_pos) args1, no_pos)) [(rhs,None)] None ]
        end
      end
  in
  let helper ((hp11,args11),(hp12,args12)) ((hp21,args21),(hp22,args22))=
    let b = Sautil.check_hp_arg_eq (hp11,args11) (hp21,args21) &&
            Sautil.check_hp_arg_eq (hp12,args12) (hp22,args22) in
    if b then true
    else
      Sautil.check_hp_arg_eq (hp11,args11) (hp22,args22) &&
      Sautil.check_hp_arg_eq (hp12,args12) (hp21,args21)
  in
  let unk_rels = Gen.BList.remove_dups_eq helper unk_rels in
  let lunk_hps,runk_hps = List.split unk_rels in
  let new_defs=
    if lunk_hps = [] || runk_hps = [] then []
    else
      let rels = List.concat (List.map
                                (fun lhp -> List.concat (List.map
                                                           (fun rhp -> generate_unkhps_relation lhp rhp) runk_hps)) lunk_hps) in
      rels
  in
  new_defs

let generalize_pure_def_from_hpunk_x prog hp_def_names cs=
  let mk_pure_def p pos (hp,args)=
    if CP.mem_svl hp hp_def_names then [] else
      let def1 = CP.filter_var_new p args in
      let def2,_ = Sautil.remove_irr_eqs args def1 in
      if not (CP.isConstTrue def2) then
        let d = Sautil.mk_hprel_def_wprocess prog false [] [hp] args hp (args,List.hd args, List.tl args) [(CF.formula_of_pure_formula def2 pos, None)]
            pos
        in d
      else []
  in
  let _, mxlhs, _, _,_,_ = (CF.split_components cs.CF.hprel_lhs) in
  let _, prhs, _, _,_,_ = (CF.split_components cs.CF.hprel_rhs) in
  let plhs = (MCP.pure_of_mix mxlhs) in
  let pos = (CP.pos_of_formula plhs) in
  let p = CP.mkAnd  plhs (MCP.pure_of_mix prhs) pos in
  List.concat (List.map (mk_pure_def p pos) cs.CF.unk_hps)

let generalize_pure_def_from_hpunk prog hp_def_names cs=
  let pr1 = Cprinter.string_of_hprel in
  let pr2 =  pr_list (pr_pair !CP.print_sv Cprinter.string_of_hp_rel_def) in
  Debug.no_1 "generalize_pure_def_from_hpunk" pr1 pr2
    (fun _ -> generalize_pure_def_from_hpunk_x prog hp_def_names cs) cs

let generalize_hps_x prog callee_hps unk_hps sel_post_hps cs par_defs=
  DD.ninfo_pprint ">>>>>> step 6: generalization <<<<<<" no_pos;
  (*for consistency, we should handle partially unk_hp first*)
  (* let new_unk_hps, new_par_defs = Sautil.ann_unk_svl prog par_defs in *)
  (* let total_unk_hps = unk_hps @ new_unk_hps in *)
  (*general par_defs*)
  let non_ptr_unk_hps = List.concat (List.map (fun (hp,args) -> if List.exists (fun a -> not ( CP.is_node_typ a)) args
                                                then [hp] else []) unk_hps) in
  let pair_names_defs = generalize_hps_par_def prog non_ptr_unk_hps unk_hps sel_post_hps par_defs in
  let hp_names,hp_defs = List.split pair_names_defs in
  (*for each constraints, we may pick more definitions*)
  (* let cs1 = List.map (drop_unk_hps unk_hps) cs in *)
  let remain_constr, hp_def1 = generalize_hps_cs prog callee_hps hp_names (List.map (fun (hp,_) -> hp) unk_hps) cs in
  let remain_constr0,hp_def2,ls_unk_rels = split3 (List.map (get_unk_hps_relation prog callee_hps hp_names sel_post_hps
                                                               (hp_defs@hp_def1)) remain_constr) in
  let hpdef21 = (List.concat hp_def2) in
  let unk_rels = (List.concat ls_unk_rels) in
  let hpdefs3 = generate_defs_from_unk_rels prog unk_rels in
  let hpdef22 = Sautil.combine_hpdefs (hpdef21@hpdefs3) in
  let get_unk_rel r ((hp1,args1),(hp2,args2))=
    if List.length args1 = List.length args2 then r@[(hp1,hp2)] else r
  in
  (List.concat remain_constr0, (hp_defs@hp_def1)@hpdef22,unk_hps,
   List.fold_left get_unk_rel [] unk_rels)

let generalize_hps prog callee_hps unk_hps sel_post_hps cs par_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Sautil.string_of_par_def_w_name in
  let pr3 = pr_list Cprinter.string_of_hp_rel_def in
  let pr4 = pr_list(pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var_list) in
  let pr5 = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in
  Debug.no_3 "generalize_hp" !CP.print_svl pr1 pr2 (pr_quad pr1 pr3 pr4 pr5)
    (fun _ _ _ -> generalize_hps_x prog callee_hps unk_hps sel_post_hps cs par_defs) callee_hps cs par_defs

(*========END generalization==========*)
(*===========fix point==============*)
let infer_hps_fix prog callee_hps hp_rel_unkmap unk_hps (constrs: CF.hprel list) =
  let dang_hps = List.fold_left (fun ls (hps,_)-> ls@ (List.map fst hps)) [] hp_rel_unkmap in
  let rec helper (constrs: CF.hprel list) par_defs non_unk_hps=
    DD.ninfo_pprint ">>>>>> step 3: simplification <<<<<<" no_pos;
    let constrs1 = simplify_constrs prog unk_hps constrs in
    Debug.ninfo_hprint (add_str "constr each LOOP: " (pr_list_ln Cprinter.string_of_hprel)) constrs1 no_pos;
    (*step 3: pick partial definition*)
    DD.ninfo_pprint ">>>>>> step 4: pick partial definitions <<<<<<" no_pos;
    let constrs2, new_par_defs = collect_partial_definitions prog callee_hps constrs1 in
    (*remove duplicate*)
    let new_par_defs = Gen.BList.remove_dups_eq check_partial_def_eq new_par_defs in
    let par_defs_diff = Gen.BList.difference_eq
        check_partial_def_eq new_par_defs par_defs in
    if par_defs_diff = [] then
      (*teminating condition*)
      (constrs2, par_defs,non_unk_hps)
    else
      begin
        (*step 4: pick complete def*)
        let constrs3 = constrs2 in
        DD.ninfo_pprint ">>>>>> step 5: subst new partial def into constrs <<<<<<" no_pos;
        (*step 5: subst new partial def into constrs*)
        let constrs4,new_non_unk_hps = subst_cs prog dang_hps constrs3 (par_defs@par_defs_diff) in
        (*for debugging*)
        (* let helper (constrs: CF.hprel list) par_defs non_unk_hps= *)
        (*   let pr = pr_list_ln Sautil.string_of_par_def_w_name in *)
        (*   Debug.no_1 "infer_hps_fix" pr (fun (_,pdefs) -> pr pdefs) *)
        (*       (fun _ -> helper constrs par_defs non_unk_hps) par_defs *)
        (* in *)
        (*END for debugging*)
        let norm_constrs, par_defs,non_unk_hps1 = helper constrs4 (par_defs@par_defs_diff) (non_unk_hps@new_non_unk_hps) in
        ((* simplify_constrs prog *) norm_constrs,  par_defs, CP.remove_dups_svl non_unk_hps1)
      end
  in
  helper constrs [] []

let generate_hp_def_from_split_x prog hpdefs hp_defs_split unk_hpargs=
  let is_rec_hpdef hp f=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let rec look_up_hp_def hp args0 hpdefs=
    match hpdefs with
    | [] -> (false,[Sautil.mkHRel_f hp args0 no_pos])
    | d::defss ->
      let (_,hrel1,_,f) = CF.flatten_hp_rel_def d in
      let hp1,args1 = CF.extract_HRel hrel1 in
      if CP.eq_spec_var hp1 hp then
        if is_rec_hpdef hp f then (true,[]) else
          let ss = List.combine args1 args0 in
          let nf = x_add CF.subst ss f in
          (false,CF.list_of_disjs nf)
      else look_up_hp_def hp args0 defss
  in
  let rec look_up_hp_defs hp_args hpdefs res=
    match hp_args with
    | [] -> false,res
    | (hp1, args1)::tl ->
      let is_rec,fs = look_up_hp_def hp1 args1 hpdefs in
      if is_rec then (true,res)
      else look_up_hp_defs tl hpdefs (res@[fs])
  in
  let rec combine_def lls pos res=
    match lls with
    | [] -> res
    | fs::ss ->
      (*mkAnd each f1 of fs with each f2 of res*)
      let f_cmbs = List.concat (List.map (fun f1 -> List.map (fun f2 -> CF.mkStar f1 f2 CF.Flow_combine pos) res) fs) in
      combine_def ss pos f_cmbs
  in
  let unk_hps = List.map (fun (hp,_) -> hp) unk_hpargs in
  let unk_svl = List.fold_left (fun svl (_,svl1) -> svl@svl1) [] unk_hpargs in
  let generate_def (hp0,args0, hp_args,hrel0)=
    let exists_rec,fss = look_up_hp_defs hp_args hpdefs []  in
    let fs=
      if exists_rec then
        (* let () = DD.info_pprint ">>>>>> a <<<<<<" no_pos in *)
        let hrels = List.map (fun (hp,args) -> Sautil.mkHRel hp args no_pos) hp_args in
        let hf = List.fold_left (fun hf0 hf1 -> CF.mkStarH hf0 hf1 no_pos)
            (List.hd hrels) (List.tl hrels) in
        (* let () = DD.info_pprint ("hf: " ^ (Cprinter.string_of_h_formula hf) )no_pos in *)
        [CF.formula_of_heap hf no_pos]
      else
        (* let () = DD.info_pprint ">>>>>> b <<<<<<" no_pos in *)
        let nfs =
          if fss = [] then
            report_error no_pos "sa.generate_def"
          else combine_def (List.tl fss) no_pos (List.hd fss)
        in nfs
    in
    Sautil.mk_hprel_def_wprocess prog false [] unk_hps unk_svl hp0 (args0, List.hd args0, List.tl args0)
      (List.map (fun f -> (f, None)) fs) no_pos
  in
  let () = DD.ninfo_pprint ">>>>>> equivalent hps: <<<<<<" no_pos in
  let new_hpdefs = snd (List.split (List.concat (List.map generate_def hp_defs_split))) in
  new_hpdefs

let generate_hp_def_from_split prog hpdefs hp_defs_split unk_hpargs=
  let pr1 =  pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 =  pr_list_ln (pr_quad !CP.print_sv !CP.print_svl pr3 Cprinter.string_of_h_formula) in
  Debug.no_2 "generate_hp_def_from_split" pr1 pr2 pr1
    (fun _ _ -> generate_hp_def_from_split_x prog hpdefs hp_defs_split unk_hpargs) hpdefs hp_defs_split


let generate_init_unk_hpdefs_x ls_unk_hpargs=
  let unk_defs =
    if !Globals.pred_elim_dangling then [] else
      List.fold_left (fun ls (hp,args)  ->
          let _, defs = List.split (Sautil.mk_unk_hprel_def hp args [(CF.mkHTrue_nf no_pos)] no_pos) in
          ls@defs) [] ls_unk_hpargs
  in
  unk_defs

let generate_init_unk_hpdefs ls_unk_hpargs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_1 "generate_init_unk_hpdefs" pr2 pr1
    (fun _ -> generate_init_unk_hpdefs_x ls_unk_hpargs) ls_unk_hpargs

let unify_branches_hpdef_x unk_hps hp_defs =
  (*move unk hps into the first position*)
  let rec swap_map ss r=
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
        swap_map tl (r@new_ss)
      end
  in
  let rec list_partition ss r=
    match ss with
    | [] -> r
    | (sv1,sv2)::tl ->
      let part,rem = List.partition (fun (_, sv4) -> CP.eq_spec_var sv2 sv4) tl in
      let part_svl = fst (List.split part) in
      list_partition rem r@[(sv1::part_svl, sv2)]
  in
  let rec check_eq_one args fs f done_fs=
    match fs with
    | [] -> done_fs,[f]
    | f1::tl ->
      let b,m = CEQ.checkeq_formulas args f f1 in
      if b then
        let ss = swap_map (List.hd m) [] in
        let parts = list_partition ss [] in
        (* let pr = pr_list (pr_pair !CP.print_svl !CP.print_sv) in *)
        (* let () = DD.info_zprint (lazy (("  parts: " ^ (pr parts)))) no_pos in *)
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
  let process_one_hpdef d=
    let hp,args = CF.extract_HRel d.CF.def_lhs in
    if CP.mem_svl hp unk_hps then
      d
    else
      let (a,hrel,og,f) = CF.flatten_hp_rel_def d in
      let fs = CF.list_of_disjs f in
      let fs1 = check_eq [] fs [] in
      let p = CF.pos_of_formula f in
      let new_f = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 p)
          (List.hd fs1) (List.tl fs1) in
      {d with CF.def_rhs = [(new_f, og)]}
  in
  DD.ninfo_pprint ">>>>>> unify: <<<<<<" no_pos;
  let r = List.map process_one_hpdef hp_defs in
  r

let unify_branches_hpdef unk_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_2 "unify_branches_hpdef" !CP.print_svl pr1 pr1
    (fun _ _ -> unify_branches_hpdef_x unk_hps hp_defs) unk_hps hp_defs

let check_eq_hpdef_x unk_hpargs post_hps hp_defs =
  let unk_hps = List.map fst unk_hpargs in

  (**************** internal methods**********************)
  let rec lookup_equiv_hpdef hpdefs hp args f=
    match hpdefs with
    | [] -> (f,[])
    | d1::tl ->
      let  (a1,hrel1,og,f1) = CF.flatten_hp_rel_def d1 in
      let hp1,eargs1,p1 = CF.extract_HRel_orig hrel1 in
      if CP.mem_svl hp1 post_hps then
        lookup_equiv_hpdef tl hp args f
      else
        let args1 = List.concat (List.map CP.afv eargs1) in
        if CP.eq_spec_var hp hp1 || CP.mem_svl hp1 unk_hps ||
           (List.length args <> List.length args1) then
          lookup_equiv_hpdef tl hp args f
        else
          let ss = List.combine args1 args in
          let f10 = x_add CF.subst ss f1 in
          let f11 = CF.subst_hprel f10 [hp1] hp in
          if Sautil.checkeq_formula_list (CF.list_of_disjs f) (CF.list_of_disjs f11) then
            (* if fst (CEQ.checkeq_formulas (List.map CP.name_of_spec_var args) f f11) then *)
            let new_f = Sautil.mkHRel_f hp1 args p1 in
            (new_f,[(hp,hp1)])
          else lookup_equiv_hpdef tl hp args f
  in
  let process_one_hpdef all_hpdefs post_hps (eq_pairs,r_hpdefs) d=
    let (a,hrel,og,f) = CF.flatten_hp_rel_def d in
    let hp,args = CF.extract_HRel hrel in
    if not (CP.mem_svl hp post_hps) || CP.mem_svl hp unk_hps then
      (eq_pairs,r_hpdefs@[d])
    else
      let new_f,new_eq_pairs = lookup_equiv_hpdef all_hpdefs hp args f in
      let new_f1 = List.fold_left (fun f (hp1,hp) -> CF.subst_hprel f [hp1] hp) new_f (eq_pairs) in
      ((eq_pairs@new_eq_pairs),r_hpdefs@[{d with CF.def_rhs = [(new_f1, og)]}])
  in
  let get_post_hps_depend cur_depend d=
    let (a,hrel,og,f) = CF.flatten_hp_rel_def d in
    let hp,_ = CF.extract_HRel hrel in
    if not (CP.mem_svl hp post_hps) || CP.mem_svl hp unk_hps then
      cur_depend
    else
      let hps = CF.get_hp_rel_name_formula f in
      let hps1 = CP.remove_dups_svl hps in
      let dep_hps = List.filter (fun hp1 -> not ((CP.eq_spec_var hp hp1) ||
                                                 (CP.mem_svl hp1 unk_hps))) hps1 in
      (cur_depend@dep_hps)
  in
  let rec move_post_hps_depend hp_defs post_hps_depend res=
    match hp_defs with
    | [] -> res
    | d::rest -> let (a,hrel,og,f) = CF.flatten_hp_rel_def d in
      let hp,_ = CF.extract_HRel hrel in
      if not (CP.mem_svl hp post_hps_depend) then
        move_post_hps_depend rest post_hps_depend (res@[d])
      else
        move_post_hps_depend rest post_hps_depend (d::res)
  in
  (****************END internal methods**********************)

  let post_hps_depend = List.fold_left get_post_hps_depend [] hp_defs in
  (* let () = Debug.info_zprint (lazy (("     post_hps: " ^ (!CP.print_svl post_hps)))) no_pos in *)
  (* let () = Debug.info_zprint (lazy (("     post_hps_depend: " ^ (!CP.print_svl post_hps_depend)))) no_pos in *)
  (*move post_hps_depend in the top: to be processed first*)
  let hp_defs1 = move_post_hps_depend hp_defs post_hps_depend [] in
  let _,res_hp_defs = List.fold_left (process_one_hpdef hp_defs (post_hps@post_hps_depend))
      ([],[]) hp_defs1 in
  res_hp_defs

let check_eq_hpdef unk_hpargs post_hps hp_defs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_2 "check_eq_hpdef" !CP.print_svl pr1 pr1
    (fun _ _ -> check_eq_hpdef_x unk_hpargs post_hps hp_defs) post_hps hp_defs

(************************************************************)
(****************(*MATCHING w view decls*)*****************)
(************************************************************)
(*========= matching=========*)
let match_hps_views_x iprog prog (hp_defs: CF.hp_rel_def list) (vdcls: CA.view_decl list):
  (CP.spec_var* CF.h_formula list) list=
  let m = List.map (Sautil.match_one_hp_views iprog prog [] vdcls) hp_defs in
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

(*END matching*)
(************************************************************)
(****************(*END MATCHING w view decls*)*****************)
(************************************************************)

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
  let mk_hprel_def kind hprel og opf opflib=
    let libs = match opflib with
      | None -> []
      | Some f -> [(f, None)]
    in
    {
      CF.hprel_def_kind = kind;
      CF.hprel_def_hrel = hprel;
      CF.hprel_def_guard = og;
      CF.hprel_def_body = [([], opf, None)];
      CF.hprel_def_body_lib = libs;
      Cformula.hprel_def_flow = None;
    }
  in
  let compute_def_w_lib (hp,d)= let (a,hprel,og,f) = CF.flatten_hp_rel_def d in
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
      (mk_hprel_def a hprel og (Some f) (Some f1))
    end
  in
  let look_up_depend cur_hp_sel f=
    let hps = CF.get_hp_rel_name_formula f in
    let dep_hps =CP.diff_svl hps (cur_hp_sel(* @unk_hps *)) in
    (CP.remove_dups_svl dep_hps)
  in
  let look_up_hp_def new_sel_hps non_sel_hp_def=
    List.partition (fun (hp,_) -> CP.mem_svl hp new_sel_hps) non_sel_hp_def
  in
  let rec find_closed_sel cur_sel cur_sel_hpdef non_sel_hp_def incr=
    let rec helper1 ls res=
      match ls with
      | [] -> res
      | (hp,d)::lss -> let (a,hf,_,f) = CF.flatten_hp_rel_def d in
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
  let defsw = List.map (fun d -> let (a,hf,og,f) = CF.flatten_hp_rel_def d in
                         (List.hd (CF.get_hp_rel_name_h_formula hf), d)) defs in
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

let prtt_string_of_par_def_w_name (a1,args,unk_args,a3,olf,og,orf)=
  let str_hrel= (!CP.print_sv a1) ^ "(" ^ (String.concat "," (List.map !CP.print_sv args)) ^ ")" in
  match olf,orf with
  | Some f, None ->
    let str_f = Cprinter.prtt_string_of_formula f in
    (str_f ^ " --> " ^ str_hrel)
  | None, Some f ->
    let str_f = Cprinter.prtt_string_of_formula f in
    ( str_hrel ^ " --> " ^ str_f )
  | Some f1, Some f2 ->
    let f_body=
      let hps1 = CF.get_hp_rel_name_formula f1 in
      let hps2 = CF.get_hp_rel_name_formula f2 in
      if CP.intersect_svl hps1 hps2 <> [] then
        (*recurive case*)
        if CF.is_HRel_f f1 then f2 else f1
      else Sautil.compose_subs f2 f1 (CF.pos_of_formula f2)
    in
    let str_f = Cprinter.prtt_string_of_formula f_body in
    ( str_hrel ^ " --> " ^ str_f )
  | None, None -> report_error no_pos "sa.obtain_def: can't happen 2"

(*
  input: constrs: (formula * formula) list
  output: definitions: (formula * formula) list
*)
let infer_hps_x iprog prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hps
    (hp_rel_unkmap: ((CP.spec_var * int) list * CP.xpure_view) list) preprocess:
  (CF.hprel list * CF.hp_rel_def list* (CP.spec_var*CP.exp list * CP.exp list) list) =
  DD.ninfo_pprint "\n\n>>>>>> norm_hp_rel <<<<<<" no_pos;
  DD.ninfo_pprint ">>>>>> step 1a: drop arguments<<<<<<" no_pos;
  let callee_hpdefs =
    try
      Cast.look_up_callee_hpdefs_proc prog.Cast.new_proc_decls proc_name
    with _ -> []
  in
  let callee_hps = List.map (fun d-> CF.get_hpdef_name d.CF.def_cat) callee_hpdefs in
  (* let () = DD.info_zprint (lazy ((" callee_hps: " ^ (!CP.print_svl callee_hps)))) no_pos in *)
  let _ =
    if !VarGen.sap then
      let () =  print_endline_quiet "" in
      let () = print_endline_quiet "*********************************************************************" in
      let () = print_endline_quiet "*******pre-process (split/unknown analyze) hprel assumptions ********" in
      let () = print_endline_quiet "**********************************************************************" in
      ()
    else ()
  in
  (* step 1: drop irr parameters *)
  (* let drop_hp_args,constrs = elim_redundant_paras_lst_constr prog hp_constrs in *)
  (* Debug.ninfo_hprint (add_str "   AFTER DROP: " (pr_list_ln Cprinter.string_of_hprel)) constrs no_pos; *)
  DD.ninfo_pprint ">>>>>> step 1b: split arguments: currently omitted <<<<<<" no_pos;
  (* step 1': split HP *)
  let constrs1b, split_tb_hp_defs_split =
    if !Globals.sa_en_split then
      split_hp prog hp_constrs
    else (hp_constrs,[])
  in
  DD.ninfo_pprint ">>>>>> step 1c: find unknown ptrs<<<<<<" no_pos;
  let constrs1c,unk_hps,hp_defs_split = x_add analize_unk prog hp_rel_unkmap constrs1b in
  (*rhs should be <= 1 hp*)
  (*for temporal*)
  let constrs1d = List.concat (List.map (Sautil.split_rhs prog) constrs1c)  in
  let constrs2 = constrs1d in
  let _ =
    if !VarGen.sap then
      let () = print_string "\n\n*******relational assumptions (2) ********" in
      let () = DD.info_pprint
          ((let pr = pr_list_ln Cprinter.string_of_hprel in pr constrs2) ) no_pos in
      ()
    else ()
  in
  (* let split_tb_hp_defs_split = [] in *)
  (*END for temporal*)
  let _ =
    if !VarGen.sap then
      let () =  print_endline_quiet "" in
      let () = print_endline_quiet "**************************************************************************" in
      let () = print_endline_quiet "*******loop: collect partial defs, substition, simplification ********" in
      let () = print_endline_quiet "**************************************************************************" in
      ()
    else ()
  in
  let cs, par_defs,non_unk_hps = infer_hps_fix prog
      callee_hps hp_rel_unkmap (List.map fst unk_hps) constrs2 in
  let unk_hpargs0 = List.filter (fun (hp,_) -> not (CP.mem_svl hp non_unk_hps)) unk_hps in
  let _ =
    if !VarGen.sap then
      let () = print_string "\n\n*******relational assumptions (3) ********\n" in
      let () = DD.info_pprint
          ((let pr = pr_list_ln Cprinter.string_of_hprel_short in pr cs) ) no_pos in
      let () = print_endline_quiet "\n\n*******partial definitions ********" in
      let pdef_sort_fn (hp1,_,_,_,_,_,_) (hp2,_,_,_,_,_,_)=
        let n1 = CP.name_of_spec_var hp1 in
        let n2 = CP.name_of_spec_var hp2 in
        String.compare n1 n2
      in
      let par_defs1 = List.sort pdef_sort_fn par_defs in
      let () = print_endline
          ((let pr = pr_list_ln prtt_string_of_par_def_w_name in pr par_defs1) )  in
      ()
    else ()
  in
  (*step 6: over-approximate to generate hp def*)
  let _ =
    if !VarGen.sap then
      let () =  print_endline_quiet "" in
      let () = print_endline_quiet "*********************************************************************" in
      let () = print_endline_quiet "*******subst, join, combine split, transfrom unknown ********" in
      let () = print_endline_quiet "**********************************************************************" in
      ()
    else ()
  in
  let constr3, hp_defs, new_unk_hps,unk_rels = generalize_hps prog callee_hps unk_hpargs0 sel_post_hps cs par_defs in
  let hp_def_names =  List.map (fun d -> CF.get_hpdef_name d.CF.def_cat) hp_defs in
  let unk_hps1 = (* List.filter (fun (hp,_) -> not (CP.mem_svl hp hp_def_names)) *) new_unk_hps in
  let unk_hp_svl = (List.map (fun (hp,_) -> hp) unk_hps1) in
  (*get unk_hps def from constraints*)
  let unk_hp_pures, unk_hp_pure_def = List.split (List.concat
                                                    (List.map (generalize_pure_def_from_hpunk prog hp_def_names) constr3))
  in
  let unk_hps2 = List.filter (fun (hp,_) -> not(CP.mem_svl hp unk_hp_pures)) unk_hps1 in
  let unk_hp_svl1 = List.filter (fun hp -> not(CP.mem_svl hp unk_hp_pures)) unk_hp_svl in
  DD.ninfo_pprint (" remains: " ^
                   (let pr1 = pr_list_ln Cprinter.string_of_hprel in pr1 constr3) ) no_pos;
  let hp_defs1 =  (Gen.BList.remove_dups_eq (fun d1 d2 ->
      let hp1 = CF.get_hpdef_name d1.CF.def_cat in
      let hp2 = CF.get_hpdef_name d2.CF.def_cat in
      CP.eq_spec_var hp1 hp2) (hp_defs))
  in
  let hp_defs2 = (* (def_subst_fix prog unk_hp_svl (hp_defs1)) *) hp_defs1 in
  (*init unk_hp = true*)
  let init_unk_hpdefs = generate_init_unk_hpdefs (List.filter (fun (hp,_) -> (CP.mem_svl hp unk_hp_svl) && not (CP.mem_svl hp (hp_def_names@callee_hps))) new_unk_hps) in
  let hp_defs22 = Sautil.combine_hpdefs (hp_defs2@unk_hp_pure_def@init_unk_hpdefs) in
  let hp_def_from_split =
    if !Globals.sa_en_split then
      generate_hp_def_from_split prog hp_defs22 split_tb_hp_defs_split unk_hpargs0
    else []
  in
  let hp_defs3 = hp_defs22@hp_def_from_split in
  (*currently, we discard all non-node unk hp*)
  (* unk_hps3: all non-node unk hps *)
  (* let non_node_unk_hps = List.filter (fun (_,args) -> *)
  (*     List.for_all (fun a -> not (CP.is_node_typ a)) args) unk_hps2 *)
  (* in *)
  (* let hp_defs21 = Sautil.drop_non_node_unk_hps hp_defs2 non_node_unk_hps in *)
  let hp_defs4=
    if !Globals.pred_elim_dangling then
      let () = print_endline_quiet "\n*******relational definitions (wo elim-dangling) ********" in
      let () = print_endline
          ((let pr = pr_list_ln  Cprinter.string_of_hp_rel_def_short in pr hp_defs3) )
      in
      let hp_defs3a,unk_rel_hpdefs, unk_hp_defs,unk_hp_frargs,unk_rels3 = Sautil.generate_hp_def_from_unk_hps hp_def_names unk_hps2 hp_defs3 sel_post_hps [](* unk_rels *) in
      if !Globals.pred_elim_dangling then
        let unk_hpdefs_from_rel = Sautil.rel_helper sel_post_hps unk_rels3 unk_hp_frargs in
        let all_unk_hpdefs = Sautil.combine_hpdefs (unk_hp_defs@unk_hpdefs_from_rel) in
        let hp_defs3b = hp_defs3a@all_unk_hpdefs in
        Sautil.transform_unk_hps_to_pure (hp_defs3b) unk_hp_frargs
      else (hp_defs3a@unk_hp_defs@unk_rel_hpdefs)
    else (hp_defs3)
  in
  (*unify inside on hp*)
  let unk_hps0 = List.map fst unk_hpargs0 in
  let hp_defs4a = check_eq_hpdef unk_hpargs0 sel_post_hps hp_defs4 in
  let hp_defs4b =
    if !Globals.sa_unify_dangling then
      unify_branches_hpdef unk_hps0 hp_defs4a
    else hp_defs4a
  in
  let hp_defs5 =
    if !Globals.sa_tree_simp then
      Sautil.simp_tree unk_hps0 hp_defs4b
    else hp_defs4b
  in
  (****************************************************)
  let _ =
    if !VarGen.sap then
      let () = print_endline_quiet "\n*******relational definitions ********" in
      let () = print_endline_quiet
          ((let pr = pr_list_ln Cprinter.string_of_hp_rel_def_short in pr hp_defs5) )  in
      ()
    else ()
  in
  DD.ninfo_pprint ">>>>>> step 7: mathching with predefined predicates <<<<<<" no_pos;
  let _ =
    if !VarGen.sap then
      let () =  print_endline_quiet "" in
      let () = print_endline_quiet "*********************************************************************" in
      let () = print_endline_quiet "*******post-process: predefined predicates matching  ********" in
      let () = print_endline_quiet "**********************************************************************" in
      ()
    else ()
  in
  let m = match_hps_views iprog prog hp_defs5 prog.CA.prog_view_decls in
  let () = DD.ninfo_zprint (lazy (("        sel_hp_rel:" ^ (!CP.print_svl sel_hp_rels)))) no_pos in
  (* let () =  DD.info_pprint (" matching: " ^ *)
  (*   (let pr = pr_list_ln (fun (hp,view_names) -> (!CP.print_sv hp) ^ " === " ^ *)
  (*     ( String.concat " OR " view_names)) in pr m)) no_pos in *)
  let sel_hpdefs, rems = List.partition
      (fun d ->
         let hp = CF.get_hpdef_name d.CF.def_cat in
         CP.mem_svl hp sel_hp_rels
      ) hp_defs5 in
  let sel_hpdefs1 = (* Sautil.recover_dropped_args drop_hp_args *) sel_hpdefs in
  let hp_defs6 = rems@sel_hpdefs1 in
  let sel_hp_defs = collect_sel_hp_def hp_defs6 sel_hp_rels unk_hp_svl1 m in
  let () = List.iter (fun hp_def -> rel_def_stk # push hp_def) sel_hp_defs in
  (*for cp*)
  let dropped_hps = (* List.filter (fun (hp,_,_) -> not(CP.mem_svl hp sel_hp_rels)) drop_hp_args *)[] in
  (constr3, hp_defs6@callee_hpdefs, dropped_hps) (*return for cp*)

(*(pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula)*)
let infer_hps iprog prog proc_name (hp_constrs: CF.hprel list) sel_hp_rels sel_post_hp_rels 
    (hp_rel_unkmap: ((CP.spec_var * int) list * CP.xpure_view) list) preprocess:
  (CF.hprel list * CF.hp_rel_def list*(CP.spec_var*CP.exp list * CP.exp list) list) =
  let pr0 = pr_list !CP.print_exp in
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr3 = pr_list (pr_triple !CP.print_sv pr0 pr0) in
  let pr4 = pr_list (pr_pair  (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in
  Debug.no_4 "infer_hps" pr_id pr1 !CP.print_svl pr4 (pr_triple pr1 pr2 pr3)
    (fun _ _ _ _ -> infer_hps_x iprog prog proc_name hp_constrs sel_hp_rels sel_post_hp_rels hp_rel_unkmap preprocess)
    proc_name hp_constrs sel_post_hp_rels hp_rel_unkmap

(**===============**********************==============**)
(******************END of NORMALIZATION**************)
(**===============**********************==============**)

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
