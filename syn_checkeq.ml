#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cformula

(* module DD = Debug *)
(* module CF = Cformula *)
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

(************************************************************)
(******************CHECKEQ************************)
(************************************************************)
(*==========check_relaxeq=============*)
(*currently we do not submit exists*)
let check_stricteq_hnodes_x stricted_eq hns1 hns2=
  (*allow dangl ptrs have diff names*)
  let all_ptrs =
    if stricted_eq then [] else
      let ptrs1 = List.map (fun hd -> hd.Cformula.h_formula_data_node) hns1 in
      let ptrs2 = List.map (fun hd -> hd.Cformula.h_formula_data_node) hns2 in
      CP.remove_dups_svl (ptrs1@ptrs2)
  in
  let check_stricteq_hnode hn1 hn2=
    let arg_ptrs1 = (* List.filter CP.is_node_typ *) hn1.Cformula.h_formula_data_arguments in
    let arg_ptrs2 = (* List.filter CP.is_node_typ *)  hn2.Cformula.h_formula_data_arguments in
    if (hn1.Cformula.h_formula_data_name = hn2.Cformula.h_formula_data_name) &&
       (CP.eq_spec_var hn1.Cformula.h_formula_data_node hn2.Cformula.h_formula_data_node) then
      let b = CP.eq_spec_var_order_list arg_ptrs1 arg_ptrs2 in
      (*bt-left2: may false if we check set eq as below*)
      let diff1 = (Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2) in
      (* (\*for debugging*\) *)
      (* let () = Debug.info_zprint  (lazy  ("     arg_ptrs1: " ^ (!CP.print_svl arg_ptrs1))) no_pos in *)
      (* let () = Debug.info_zprint  (lazy  ("     arg_ptrs2: " ^ (!CP.print_svl arg_ptrs2))) no_pos in *)
      (* let () = Debug.info_zprint  (lazy  ("     diff1: " ^ (!CP.print_svl diff1)) no_pos in *)
      (*END for debugging*)
      if stricted_eq then (* (diff1=[]) *)(b,[]) else
        (*allow dangl ptrs have diff names*)
        let diff2 = CP.intersect_svl diff1 all_ptrs in
        let ss = List.combine arg_ptrs1 arg_ptrs2 in
        (diff2 = [], (* List.filter (fun (sv1, sv2) -> not(CP.eq_spec_var sv1 sv2)) *) ss)
    else
      (false,[])
  in
  let rec helper hn hns2 rest2=
    match hns2 with
    | [] -> (false,[], rest2)
    | hn1::hss ->
      let r,ss1 =  check_stricteq_hnode hn hn1 in
      if r then
        (true, ss1, rest2@hss)
      else helper hn hss (rest2@[hn1])
  in
  let rec helper2 hns1 hns2 ss0=
    match hns1 with
    | [] -> if hns2 = [] then (true,ss0) else (false,ss0)
    | hn1::rest1 ->
      let r,ss1, rest2 = helper hn1 hns2 [] in
      if r then
        let n_rest1 = if ss1 = [] then rest1 else List.map (fun dn -> Cformula.dn_subst ss1 dn) rest1 in
        helper2 n_rest1 rest2 (ss0@ss1)
      else (false,ss0)
  in
  if (List.length hns1) <= (List.length hns2) then
    helper2 hns1 hns2 []
  else (false,[])

let check_stricteq_hnodes stricted_eq hns1 hns2=
  let pr1 hd = Cprinter.prtt_string_of_h_formula (Cformula.DataNode hd) in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "check_stricteq_hnodes" string_of_bool pr2 pr2 (pr_pair string_of_bool pr3)
    (fun _ _ _ -> check_stricteq_hnodes_x stricted_eq hns1 hns2)  stricted_eq hns1 hns2

let check_stricteq_vnodes_x stricted_eq vns1 vns2=
  (*allow dangl ptrs have diff names*)
  let all_ptrs =
    if stricted_eq then [] else
      let ptrs1 = List.map (fun hd -> hd.Cformula.h_formula_view_node) vns1 in
      let ptrs2 = List.map (fun hd -> hd.Cformula.h_formula_view_node) vns2 in
      CP.remove_dups_svl (ptrs1@ptrs2)
  in
  let check_stricteq_vnode hn1 hn2=
    let arg_ptrs1 = (* List.filter CP.is_node_typ *) hn1.Cformula.h_formula_view_arguments in
    let arg_ptrs2 = (* List.filter CP.is_node_typ *)  hn2.Cformula.h_formula_view_arguments in
    if (hn1.Cformula.h_formula_view_name = hn2.Cformula.h_formula_view_name) &&
       (CP.eq_spec_var hn1.Cformula.h_formula_view_node hn2.Cformula.h_formula_view_node) then
      let b = CP.eq_spec_var_order_list arg_ptrs1 arg_ptrs2 in
      (*bt-left2: may false if we check set eq as below*)
      let diff1 = (Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2) in
      (* (\*for debugging*\) *)
      (* let () = Debug.info_zprint  (lazy  ("     arg_ptrs1: " ^ (!CP.print_svl arg_ptrs1))) no_pos in *)
      (* let () = Debug.info_zprint  (lazy  ("     arg_ptrs2: " ^ (!CP.print_svl arg_ptrs2))) no_pos in *)
      (* let () = Debug.info_zprint  (lazy  ("     diff1: " ^ (!CP.print_svl diff1)) no_pos in *)
      (*END for debugging*)
      if stricted_eq then (* (diff1=[]) *)(b,[]) else
        (*allow dangl ptrs have diff names*)
        let diff2 = CP.intersect_svl diff1 all_ptrs in
        let ss = List.combine arg_ptrs1 arg_ptrs2 in
        (diff2 = [], (* List.filter (fun (sv1, sv2) -> not(CP.eq_spec_var sv1 sv2)) *) ss)
    else
      (false,[])
  in
  let rec helper vn vns2 rest2=
    match vns2 with
    | [] -> (false,[], rest2)
    | vn1::vss ->
      let r,ss1 = check_stricteq_vnode vn vn1 in
      if r then
        (true, ss1, rest2@vss)
      else helper vn vss (rest2@[vn1])
  in
  let rec helper2 vns1 vns2 ss0=
    match vns1 with
    | [] -> if vns2 = [] then (true,ss0) else (false,ss0)
    | vn1::rest1 ->
      let r,ss1, rest2 = helper vn1 vns2 [] in
      if r then
        let n_rest1 = if ss1 = [] then rest1 else List.map (fun dn -> Cformula.vn_subst ss1 dn) rest1 in
        helper2 n_rest1 rest2 (ss0@ss1)
      else (false,ss0)
  in
  if (List.length vns1) <= (List.length vns2) then
    helper2 vns1 vns2 []
  else (false,[])

let check_stricteq_vnodes stricted_eq vns1 vns2=
  let pr1 vn = Cprinter.prtt_string_of_h_formula (Cformula.ViewNode vn) in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "check_stricteq_vnodes" string_of_bool pr2 pr2 (pr_pair string_of_bool pr3)
    (fun _ _ _ -> check_stricteq_vnodes_x stricted_eq vns1 vns2)  stricted_eq vns1 vns2

let check_stricteq_hrels_x hrels1 hrels2=
  let check_stricteq_hr (hp1, eargs1, _) (hp2, eargs2, _)=
    let r = (CP.eq_spec_var hp1 hp2) in
    (* ((Gen.BList.difference_eq CP.eq_exp_no_aset *)
    (*     eargs1 eargs2)=[]) *)
    if r then
      let ls1 = List.concat (List.map CP.afv eargs1) in
      let ls2 = List.concat (List.map CP.afv eargs2) in
      (true, List.combine ls1 ls2)
    else (false,[])
  in
  let rec helper hr hrs2 rest2=
    match hrs2 with
    | [] -> (false,[],rest2)
    | hr1::hss ->
      let r,ss1= check_stricteq_hr hr hr1 in
      if r then
        (true,ss1,rest2@hss)
      else helper hr hss (rest2@[hr1])
  in
  let rec helper2 hrs1 hrs2 ss0=
    match hrs1 with
    | [] -> if hrs2 = [] then (true,ss0) else (false,ss0)
    | hr1::rest1 ->
      let r,ss, rest2 = helper hr1 hrs2 [] in
      if r then
        helper2 rest1 rest2 (ss0@ss)
      else (false,ss0)
  in
  (* let rec check_inconsistency (sv1,sv2) rest= *)
  (*   match rest with *)
  (*     | [] -> false *)
  (*     | a:: rest1 -> *)
  (*           if List.exists (fun (sv3,sv4) -> CP.eq_spec_var sv1 sv4 && CP.eq_spec_var sv2 sv3) rest then *)
  (*             true *)
  (*           else check_inconsistency a rest1 *)
  (* in *)
  let leng1 = List.length hrels1 in
  if leng1 = (List.length hrels2) then
    if leng1 = 0 then (true,[]) else
      let b, ss = helper2 hrels1 hrels2 [] in
      (*inconsistence: (x1,x2) and (x2,x1)*)
      (* if b && ss != [] then *)
      (*   if check_inconsistency (List.hd ss) (List.tl ss) then (false,[]) else *)
      (*     (b,ss) *)
      (* else *) (b,ss)
  else (false,[])

let check_stricteq_hrels hrels1 hrels2=
  let pr1 vn = Cprinter.prtt_string_of_h_formula (Cformula.HRel vn) in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "check_stricteq_hrels" pr2 pr2 (pr_pair string_of_bool pr3)
    (fun _ _ -> check_stricteq_hrels_x hrels1 hrels2) hrels1 hrels2

let check_stricteq_h_fomula_x stricted_eq hf1 hf2=
  let hnodes1, vnodes1, hrels1 = Cformula.get_hp_rel_h_formula hf1 in
  let hnodes2, vnodes2, hrels2 = Cformula.get_hp_rel_h_formula hf2 in
  (* if vnodes1 <> [] || vnodes2 <> [] then (false,[]) else *)
  let r,ss = check_stricteq_hrels hrels1 hrels2 in
  let data_helper hn=
    let n_hn = Cformula.h_subst ss (Cformula.DataNode hn) in
    match n_hn with
    | Cformula.DataNode hn -> hn
    | _ -> report_error no_pos "sau.check_stricteq_h_fomula 1"
  in
  let view_helper ss0 vn=
    let n_vn = Cformula.h_subst ss0 (Cformula.ViewNode vn) in
    match n_vn with
    | Cformula.ViewNode vn -> vn
    | _ -> report_error no_pos "sau.check_stricteq_h_fomula 2"
  in
  if r then begin
    let n_hnodes1 = List.map data_helper hnodes1 in
    let n_hnodes2 = List.map data_helper hnodes2 in
    let r1,ss1 =
      if (List.length n_hnodes1) <= (List.length n_hnodes2) then
        check_stricteq_hnodes stricted_eq n_hnodes1 n_hnodes2
      else
        check_stricteq_hnodes stricted_eq n_hnodes2 n_hnodes1
    in
    let ss1a = ss@ss1 in
    if not r1 then (false,[]) else
      let n_vnodes1 = List.map (view_helper ss1a) vnodes1 in
      let n_vnodes2 = List.map (view_helper ss1a) vnodes2 in
      let r2,ss2 =
        if (List.length n_vnodes1) <= (List.length n_vnodes2) then
          check_stricteq_vnodes stricted_eq n_vnodes1 n_vnodes2
        else
          check_stricteq_vnodes stricted_eq n_vnodes2 n_vnodes1
      in
      (r2,ss@ss1@ss2)
  end
  else (false,[])

let check_stricteq_h_fomula stricted_eq hf1 hf2=
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 " check_stricteq_h_fomula" string_of_bool pr1 pr1 (pr_pair string_of_bool pr2)
    (fun _ _ _ ->  check_stricteq_h_fomula_x stricted_eq hf1 hf2) stricted_eq hf1 hf2

let checkeq_pure_x qvars1 qvars2 p1 p2=
  if CP.equalFormula p1 p2 then true else
    let p2 = CP.mkExists qvars2 p2 None no_pos in
    let b1,_,_ = x_add TP.imply_one 3 p1 p2 "sa:checkeq_pure" true None in
    if b1 then
      let p1 = CP.mkExists qvars1 p1 None no_pos in
      let b2,_,_ = x_add TP.imply_one 4 p2 p1 "sa:checkeq_pure" true None in
      b2
    else false

let checkeq_pure qvars1 qvars2 p1 p2=
  let pr1 = !CP.print_formula in
  Debug.no_2 "checkeq_pure" pr1 pr1 string_of_bool
    (fun _ _ -> checkeq_pure_x qvars1 qvars2 p1 p2) p1 p2

let rec check_eq_formula args is_strict f10 f20=
  let rec is_cyc_subst sst=
    match sst with
      | [] -> false
      | [x] -> false
      | (sv1,sv2)::rest -> if List.exists (fun (sv3,sv4) ->
            CP.eq_spec_var sv1 sv4 && CP.eq_spec_var sv2 sv3
        ) rest then true else
          is_cyc_subst rest
  in
  (********REMOVE dup branches**********)
  let fs11 = Cformula.list_of_disjs f10 in
  let fs12 = Gen.BList.remove_dups_eq (check_eq_formula args is_strict) fs11 in
  let f1 = Cformula.disj_of_list fs12 (Cformula.pos_of_formula f10) in
  let fs21 = Cformula.list_of_disjs f20 in
  let fs22 = Gen.BList.remove_dups_eq (check_eq_formula args is_strict) fs21 in
  let f2 = Cformula.disj_of_list fs22 (Cformula.pos_of_formula f20) in
  (********END********)
  try
    let qvars1, base_f1 = Cformula.split_quantifiers f1 in
    let qvars2, base_f2 = Cformula.split_quantifiers f2 in
    let hf1,mf1,_,_,_,_ = Cformula.split_components base_f1 in
    let hf2,mf2,_,_,_,_ = Cformula.split_components base_f2 in
    Debug.ninfo_zprint  (lazy  ("   mf1: " ^(Cprinter.string_of_mix_formula mf1))) no_pos;
    Debug.ninfo_zprint  (lazy  ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2))) no_pos;
    (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
    let r1,ss = check_stricteq_h_fomula is_strict hf1 hf2 in
    if r1 && not (is_cyc_subst ss) then
      let r2 = if !Globals.pred_elim_dangling then
          List.for_all (fun ((CP.SpecVar (_,id1,_)), (CP.SpecVar (_,id2,_))) ->
              try
                let pre1 = String.sub id1 0 5 in
                let pre2 = String.sub id2 0 5 in
                let b1 = string_eq pre1 dang_hp_default_prefix_name in
                let b2 = string_eq pre2 dang_hp_default_prefix_name in
                (b1 && b2) || (not b1 && not b2)
              with _ -> true
            ) ss
        else true in
      if not r2 then false
      else
        (* let new_mf1 = xpure_for_hnodes hf1 in *)
        (* let cmb_mf1 = MCP.merge_mems mf1 new_mf1 true in *)
        (* let new_mf2 = xpure_for_hnodes hf2 in *)
        (* let cmb_mf2 = MCP.merge_mems mf2 new_mf2 true in *)
        (* (\*remove dups*\) *)
        (* let np1 = CP.remove_redundant (MCP.pure_of_mix cmb_mf1) in *)
        (* let np2 = CP.remove_redundant (MCP.pure_of_mix cmb_mf2) in *)
        let np1 = Cformula.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
        let np2 = Cformula.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
        (* Debug.info_zprint  (lazy  ("   f1: " ^(!CP.print_formula np1))) no_pos; *)
        (* Debug.info_zprint  (lazy  ("   f2: " ^ (!CP.print_formula np2))) no_pos; *)
        (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
        let diff2 = List.map snd ss in
        let () = Debug.ninfo_zprint  (lazy  ("   diff: " ^ (!CP.print_svl diff2))) no_pos in
        let np11 = (* CP.mkExists qvars1 np1 None no_pos *) np1 in
        let np21 = (* CP.mkExists qvars2 np2 None no_pos *) np2 in
        let np12 = CP.subst ss np11 in
        (* let _, bare_f2 = CP.split_ex_quantifiers np2 in *)
        let svl1 = CP.fv np12 in
        let svl2 = CP.fv np21 in
        Debug.ninfo_zprint  (lazy  ("   np12: " ^(!CP.print_formula np12))) no_pos;
        Debug.ninfo_zprint  (lazy  ("   np21: " ^ (!CP.print_formula np21))) no_pos;
        let qvars1 = CP.remove_dups_svl ((CP.diff_svl svl1 (args@diff2))) in
        let qvars2 = CP.remove_dups_svl ((CP.diff_svl svl2 (args@diff2))) in
        let r2 = checkeq_pure qvars1 qvars2 np12 np21 in
        let () = Debug.ninfo_zprint  (lazy  ("   eq: " ^ (string_of_bool r2))) no_pos in
        r2
    else
      false
  with _ -> false

and check_relaxeq_formula_x args f1 f2=
  check_eq_formula args false f1 f2

and check_relaxeq_formula args f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_relaxeq_formula" pr1 pr1 string_of_bool
    (fun _ _ -> check_relaxeq_formula_x args f1 f2) f1 f2

and check_stricteq_formula args f1 f2=
  check_eq_formula args true f1 f2

(*exactly eq*)
let checkeq_pair_formula (f11,f12) (f21,f22)=
  (check_relaxeq_formula [] f11 f21)&&(check_relaxeq_formula [] f12 f22)

let rec checkeq_formula_list_x fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
    | [] -> (false, fs1)
    | f1::fss -> if (check_relaxeq_formula [] f f1) then
        (true,fs1@fss)
      else look_up_f f fss (fs1@[f1])
  in
  if List.length fs1 = List.length fs2 then
    match fs1 with
    | [] -> true
    | f1::fss1 ->
      begin
        let r,fss2 = look_up_f f1 fs2 [] in
        if r then
          checkeq_formula_list fss1 fss2
        else false
      end
  else false

and checkeq_formula_list fs1 fs2=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "checkeq_formula_list" pr1 pr1 string_of_bool
    (fun _ _ -> checkeq_formula_list_x fs1 fs2) fs1 fs2

let rec checkeq_formula_list_w_args_x args fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
    | [] -> (false, fs1)
    | f1::fss -> if (check_relaxeq_formula args f f1) then
        (true,fs1@fss)
      else look_up_f f fss (fs1@[f1])
  in
  if List.length fs1 = List.length fs2 then
    match fs1 with
    | [] -> true
    | f1::fss1 ->
      begin
        let r,fss2 = look_up_f f1 fs2 [] in
        if r then
          checkeq_formula_list_w_args args fss1 fss2
        else false
      end
  else false

and checkeq_formula_list_w_args args fs1 fs2=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "checkeq_formula_list" pr1 pr1 string_of_bool
    (fun _ _ -> checkeq_formula_list_w_args_x args fs1 fs2) fs1 fs2


let check_exists_cyclic_proofs_x es (ante,conseq)=
  let collect_vnode hf=
    match hf with
    | Cformula.ViewNode vn -> [vn]
    | _ -> []
  in
  let rec look_up_vn l_vns vn=
    match l_vns with
    | [] -> None
    | vn1::rest -> if String.compare vn vn1.Cformula.h_formula_view_name = 0 then
        Some (vn1.Cformula.h_formula_view_node::vn1.Cformula.h_formula_view_arguments)
      else look_up_vn rest vn
  in
  let rec build_subst ss vns1 vns2=
    match vns1 with
    | [] -> ss
    | vn::rest -> begin
        let args_opt = look_up_vn vns2 vn.Cformula.h_formula_view_name in
        match args_opt with
        | None -> build_subst ss rest vns2
        | Some args2 -> let ss1 = List.combine (vn.Cformula.h_formula_view_node::vn.Cformula.h_formula_view_arguments) args2 in
          build_subst (ss@(List.filter (fun (sv1,sv2) -> not (CP.eq_spec_var sv1 sv2)) ss1)) rest vns2
      end
  in
  let check_one l_vns r_vns (a1,c1)=
    let vn_a1 = Cformula.map_heap_1 collect_vnode a1 in
    let vn_c1 = Cformula.map_heap_1 collect_vnode c1 in
    if List.length l_vns != List.length vn_a1 || List.length r_vns != List.length vn_c1 then
      let () = Debug.ninfo_hprint (add_str " xxxx" pr_id) "1" no_pos in
      false
    else
      let l_ss = build_subst [] vn_a1 l_vns in
      let r_ss = build_subst [] vn_c1 r_vns in
      let a11 = if l_ss = [] then a1 else x_add Cformula.subst l_ss a1 in
      let c11 = if r_ss = [] then c1 else x_add Cformula.subst r_ss c1 in
      (* (check_relaxeq_formula [] ante a11) && (check_relaxeq_formula [] conseq c11) *)
      (fst (Checkeq.checkeq_formulas [] ante a11)) && (fst(Checkeq.checkeq_formulas [] conseq c11))
  in
  let l_vns = Cformula.map_heap_1 collect_vnode ante in
  let r_vns = Cformula.map_heap_1 collect_vnode conseq in
  List.exists (check_one l_vns r_vns) es.Cformula.es_proof_traces

let check_exists_cyclic_proofs es (ante,conseq)=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr3 es = (pr_list_ln pr2) es.Cformula.es_proof_traces in
  Debug.no_2 "SY_CEQ.check_exists_cyclic_proofs" pr3 pr2 string_of_bool
    (fun _ _ -> check_exists_cyclic_proofs_x es (ante,conseq))
    es (ante,conseq)

(*******************************************************************************)
(**********************HEAP GRAPH*************************************)
(*******************************************************************************)

let syntax_nodes_match_x lhs0 rhs0 =
  (******************************************************)
  let check_exact_eq_data_node dn1 dn2=
    CP.eq_spec_var dn1.Cformula.h_formula_data_node dn2.Cformula.h_formula_data_node &&
    List.length dn1.Cformula.h_formula_data_arguments = List.length dn2.Cformula.h_formula_data_arguments &&
    CP.diff_svl dn1.Cformula.h_formula_data_arguments dn2.Cformula.h_formula_data_arguments = []
  in
  let check_eq_data_node dn1 dn2=
    CP.eq_spec_var dn1.Cformula.h_formula_data_node dn2.Cformula.h_formula_data_node
  in
  let xpure_dnode pos dn=
    let sv1 = dn.Cformula.h_formula_data_node in
    let ps = List.map (fun sv2 ->
        CP.mkPtrNeqEqn sv1 sv2 pos
      ) dn.Cformula.h_formula_data_arguments in
    let neqNull = CP.mkNeqNull sv1 pos in
    CP.conj_of_list (neqNull::ps) pos
  in
  let hn_drop_matched matched_svl hf=
    match hf with
    | Cformula.DataNode hn -> if CP.mem_svl hn.Cformula.h_formula_data_node matched_svl then Cformula.HEmp else hf
    | _ -> hf
  in
  let rec check_inconsistent dns=
    match dns with
    | [] -> false
    | dn::rest -> if List.exists (fun dn1 ->
        CP.eq_spec_var dn.Cformula.h_formula_data_node dn1.Cformula.h_formula_data_node
      ) rest then true else
        check_inconsistent rest
  in
  let check_pure_inconsistent f=
    let p = (Cformula.get_pure f) in
    CP.isConstFalse p || Cpgraph.inconsisten_neq p
  in
  (******************************************************)
  (* let l_hds,_,_ = Cformula.get_hp_rel_formula lhs in *)
  let l_hds = Cformula.get_datas lhs0 in
  let r_hds0, r_hvs,_ = Cformula.get_hp_rel_formula rhs0 in
  let lhs_unsat = check_inconsistent l_hds || check_pure_inconsistent lhs0 in
  let rhs_unsat = check_inconsistent r_hds0 || check_pure_inconsistent rhs0 in
  let lhs = if lhs_unsat then Cformula.mkFalse_nf no_pos else lhs0 in
  let rhs = if rhs_unsat then Cformula.mkFalse_nf no_pos else rhs0 in
  if lhs_unsat || rhs_unsat then
    (lhs, rhs, lhs_unsat, rhs_unsat)
  else
    let root_ptrs1 = List.map (fun hd -> hd.Cformula.h_formula_data_node) r_hds0 in
    let root_ptrs = (List.map (fun hv -> hv.Cformula.h_formula_view_node) r_hvs)@root_ptrs1 in
    (*data nodes that not in a cicle*)
    let r_hds = List.filter (fun hd ->
        try
          let todo_unk = List.find (fun sv -> CP.mem_svl sv root_ptrs) hd.Cformula.h_formula_data_arguments in
          false
        with _ -> true
      ) r_hds0 in
    let matched_data_nodes = Gen.BList.intersect_eq check_exact_eq_data_node l_hds r_hds in
    (* let l_hds = Gen.BList.intersect_eq check_eq_data_node l_hds matched_data_nodes in *)
    (* let r_hds = Gen.BList.intersect_eq check_eq_data_node r_hds matched_data_nodes in *)
    let matched_svl = (List.map (fun hn -> hn.Cformula.h_formula_data_node) matched_data_nodes) in
    let n_lhs, n_rhs =
      if matched_svl = [] then (lhs, rhs)
      else
        (*drop matched, add pure constraints (footprints) to the lhs*)
        let xpure_ps = List.map (xpure_dnode no_pos) matched_data_nodes in
        let xpure_p = CP.conj_of_list xpure_ps no_pos in
        let droped_lhs = Cformula.formula_trans_heap_node (hn_drop_matched matched_svl) lhs in
        (Cformula.mkAnd_pure droped_lhs (Mcpure.mix_of_pure xpure_p) no_pos,
         Cformula.formula_trans_heap_node (hn_drop_matched matched_svl) rhs)
    in
    (n_lhs, n_rhs, lhs_unsat, rhs_unsat)

let syntax_nodes_match lhs rhs =
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "syntax_nodes_match" pr1 pr1 (pr_quad pr1 pr1 string_of_bool string_of_bool)
    (fun _ _ -> syntax_nodes_match_x lhs rhs) lhs rhs

let hview_drop_matched matched_svl hf=
  match hf with
  | Cformula.ViewNode vn -> if CP.mem_svl vn.Cformula.h_formula_view_node matched_svl then Cformula.HEmp else hf
  | _ -> hf


let syntax_vnodes_match_x lhs0 rhs0 =
  (******************************************************)
  let check_exact_eq_view_node vn1 vn2=
    CP.eq_spec_var vn1.Cformula.h_formula_view_node vn2.Cformula.h_formula_view_node &&
    List.length vn1.Cformula.h_formula_view_arguments = List.length vn2.Cformula.h_formula_view_arguments &&
    CP.diff_svl vn1.Cformula.h_formula_view_arguments vn2.Cformula.h_formula_view_arguments = []
  in
  let check_eq_view_node vn1 vn2=
    CP.eq_spec_var vn1.Cformula.h_formula_view_node vn2.Cformula.h_formula_view_node
  in
  (******************************************************)
  let l_hvs = Cformula.get_views lhs0 in
  let r_hvs = Cformula.get_views rhs0 in
  let matched_view_nodes = Gen.BList.intersect_eq check_exact_eq_view_node l_hvs r_hvs in
  let l_hvs = Gen.BList.intersect_eq check_eq_view_node l_hvs matched_view_nodes in
  let r_hvs = Gen.BList.intersect_eq check_eq_view_node r_hvs matched_view_nodes in
  let matched_svl = (List.map (fun hv -> hv.Cformula.h_formula_view_node) matched_view_nodes) in
  if matched_svl = [] then (false, lhs0, rhs0)
  else
    (*drop matched, add pure constraints (footprints) to the lhs*)
    let droped_lhs = Cformula.formula_trans_heap_node (hview_drop_matched matched_svl) lhs0 in
    (true, droped_lhs, Cformula.formula_trans_heap_node (hview_drop_matched matched_svl) rhs0)

let syntax_vnodes_match lhs rhs =
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "syntax_vnodes_match" pr1 pr1 (pr_triple string_of_bool pr1 pr1)
    (fun _ _ -> syntax_vnodes_match_x lhs rhs) lhs rhs

let syntax_contrb_lemma_end_null_x prog lhs rhs=
  (*****************************************)
  let all_args_null l_hvs leqnulls ptr=
    try
      let vn = List.find (fun hv -> CP.eq_spec_var ptr hv.Cformula.h_formula_view_node) l_hvs in
      CP.diff_svl (List.filter CP.is_node_typ vn.Cformula.h_formula_view_arguments) leqnulls = []
    with _ -> false
  in
  let fold_lemma_end_null l_hns l_hvs leqnulls (cur_rhs_null_ptrs, cur_l_vns, cur_r_vns) r_vn=
    let reach_ptrs = Cformula.look_up_reachable_ptr_args prog l_hns l_hvs [r_vn.Cformula.h_formula_view_node] in
    if List.exists (all_args_null l_hvs leqnulls) reach_ptrs then
      (cur_rhs_null_ptrs@r_vn.Cformula.h_formula_view_arguments, cur_l_vns@reach_ptrs, cur_r_vns@[r_vn.Cformula.h_formula_view_node])
    else (cur_rhs_null_ptrs, cur_l_vns, cur_r_vns)
  in
  let heap_drop_matched matched_svl hf= match hf with
    | Cformula.ViewNode vn -> if CP.mem_svl vn.Cformula.h_formula_view_node matched_svl then Cformula.HEmp else hf
    | Cformula.DataNode dn -> if CP.mem_svl dn.Cformula.h_formula_data_node matched_svl then Cformula.HEmp else hf
    | _ -> hf
  in
  (*****************************************)
  let ( _,rmf,_,_,_,_) = Cformula.split_components rhs in
  let r_eqnull_svl =  MCP.get_null_ptrs rmf in
  if r_eqnull_svl = [] then
    (lhs, rhs)
  else
    let ( _,lmf,_,_,_,_) = Cformula.split_components lhs in
    let l_eqnull_svl =  MCP.get_null_ptrs lmf in
    if l_eqnull_svl = [] then
      (lhs, rhs)
    else
      let l_hns, l_hvs,_ = Cformula.get_hp_rel_formula lhs in
      let r_hvs = Cformula.get_views rhs in
      let r_hvs_end_null = List.filter (fun vn -> CP.diff_svl (List.filter CP.is_node_typ vn.Cformula.h_formula_view_arguments) r_eqnull_svl = []) r_hvs in
      let rhs_null_ptrs, drop_l_hvs, drop_r_hvs = List.fold_left (fold_lemma_end_null l_hns l_hvs l_eqnull_svl) ([],[],[]) r_hvs_end_null in
      let cl_drop_r_hvs = Cformula.look_up_rev_reachable_ptr_args prog [] r_hvs  drop_r_hvs in
      let cl_drop_l_hvs = if List.length cl_drop_r_hvs = List.length drop_r_hvs then drop_l_hvs
        else Cformula.look_up_rev_reachable_ptr_args prog l_hns l_hvs drop_l_hvs
      in
      let droped_lhs = if drop_l_hvs = [] then
          lhs
        else
          Cformula.formula_trans_heap_node (heap_drop_matched cl_drop_l_hvs) lhs
      in
      let droped_rhs = if drop_r_hvs = [] then rhs else
          let () = Debug.ninfo_hprint (add_str "drop_r_hvs" Cprinter.string_of_spec_var_list)  drop_r_hvs no_pos in
          let () = Debug.ninfo_hprint (add_str "cl_drop_r_hvs" Cprinter.string_of_spec_var_list) cl_drop_r_hvs no_pos in
          (* Cformula.formula_trans_heap_node (hn_drop_matched drop_r_hvs) rhs *)
          Cfutil.elim_eqnull (Cformula.heap_trans_heap_node (hview_drop_matched cl_drop_r_hvs)) rhs_null_ptrs rhs
      in
      (droped_lhs, droped_rhs)

(* x::ls<p> * p::ls<null> <-> x::ls<null> *)
let syntax_contrb_lemma_end_null prog lhs rhs=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "syntax_contrb_lemma_end_null" pr1 pr1 (pr_pair pr1 pr1)
    (fun _ _ -> syntax_contrb_lemma_end_null_x prog lhs rhs) lhs rhs

(*******************************************************************************)
(**********************END HEAP GRAPH**********************************)
(*******************************************************************************)
(*******************************************************************************)
