open Globals
open Gen

module DD = Debug
module CF = Cformula
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
    let ptrs1 = List.map (fun hd -> hd.CF.h_formula_data_node) hns1 in
    let ptrs2 = List.map (fun hd -> hd.CF.h_formula_data_node) hns2 in
    CP.remove_dups_svl (ptrs1@ptrs2)
  in
  let check_stricteq_hnode hn1 hn2=
    let arg_ptrs1 = (* List.filter CP.is_node_typ *) hn1.CF.h_formula_data_arguments in
    let arg_ptrs2 = (* List.filter CP.is_node_typ *)  hn2.CF.h_formula_data_arguments in
    if (hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name) &&
        (CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node) then
      let b = CP.eq_spec_var_order_list arg_ptrs1 arg_ptrs2 in
      (*bt-left2: may false if we check set eq as below*)
      let diff1 = (Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2) in
      (* (\*for debugging*\) *)
      (* let _ = Debug.info_pprint ("     arg_ptrs1: " ^ (!CP.print_svl arg_ptrs1)) no_pos in *)
      (* let _ = Debug.info_pprint ("     arg_ptrs2: " ^ (!CP.print_svl arg_ptrs2)) no_pos in *)
      (* let _ = Debug.info_pprint ("     diff1: " ^ (!CP.print_svl diff1)) no_pos in *)
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
            let n_rest1 = if ss1 = [] then rest1 else List.map (fun dn -> CF.dn_subst ss1 dn) rest1 in
            helper2 n_rest1 rest2 (ss0@ss1)
          else (false,ss0)
  in
  if (List.length hns1) <= (List.length hns2) then
    helper2 hns1 hns2 []
  else (false,[])

let check_stricteq_hnodes stricted_eq hns1 hns2=
  let pr1 hd = Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  let pr2 = pr_list_ln pr1 in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "check_stricteq_hnodes" string_of_bool pr2 pr2 (pr_pair string_of_bool pr3)
      (fun _ _ _ -> check_stricteq_hnodes_x stricted_eq hns1 hns2)  stricted_eq hns1 hns2


let check_stricteq_hrels hrels1 hrels2=
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
  if (List.length hrels1) = (List.length hrels2) then
    helper2 hrels1 hrels2 []
  else (false,[])

let check_stricteq_h_fomula_x stricted_eq hf1 hf2=
  let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in
  let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in
  let r,ss = check_stricteq_hrels hrels1 hrels2 in
  let helper hn=
    let n_hn = CF.h_subst ss (CF.DataNode hn) in
    match n_hn with
      | CF.DataNode hn -> hn
      | _ -> report_error no_pos "sau.check_stricteq_h_fomula"
  in
  if r then begin
      let n_hnodes1 = List.map helper hnodes1 in
      let n_hnodes2 = List.map helper hnodes2 in
      let r,ss1 =
        if (List.length n_hnodes1) <= (List.length n_hnodes2) then
          check_stricteq_hnodes stricted_eq n_hnodes1 n_hnodes2
        else
          check_stricteq_hnodes stricted_eq n_hnodes2 n_hnodes1
      in
      (r,ss@ss1)
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
     let b1,_,_ = TP.imply_one 3 p1 p2 "sa:checkeq_pure" true None in
    if b1 then
      let p1 = CP.mkExists qvars1 p1 None no_pos in
      let b2,_,_ = TP.imply_one 4 p2 p1 "sa:checkeq_pure" true None in
      b2
    else false

let checkeq_pure qvars1 qvars2 p1 p2=
  let pr1 = !CP.print_formula in
  Debug.no_2 "checkeq_pure" pr1 pr1 string_of_bool
      (fun _ _ -> checkeq_pure_x qvars1 qvars2 p1 p2) p1 p2

let check_relaxeq_formula_x args f1 f2=
  let qvars1, base_f1 = CF.split_quantifiers f1 in
  let qvars2, base_f2 = CF.split_quantifiers f2 in
  let hf1,mf1,_,_,_ = CF.split_components base_f1 in
  let hf2,mf2,_,_,_ = CF.split_components base_f2 in
  DD.ninfo_pprint ("   mf1: " ^(Cprinter.string_of_mix_formula mf1)) no_pos;
  DD.ninfo_pprint ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1,ss = check_stricteq_h_fomula false hf1 hf2 in
  if r1 then
    (* let new_mf1 = xpure_for_hnodes hf1 in *)
    (* let cmb_mf1 = MCP.merge_mems mf1 new_mf1 true in *)
    (* let new_mf2 = xpure_for_hnodes hf2 in *)
    (* let cmb_mf2 = MCP.merge_mems mf2 new_mf2 true in *)
    (* (\*remove dups*\) *)
    (* let np1 = CP.remove_redundant (MCP.pure_of_mix cmb_mf1) in *)
    (* let np2 = CP.remove_redundant (MCP.pure_of_mix cmb_mf2) in *)
    let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
    let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
    (* DD.info_pprint ("   f1: " ^(!CP.print_formula np1)) no_pos; *)
    (* DD.info_pprint ("   f2: " ^ (!CP.print_formula np2)) no_pos; *)
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    let diff2 = List.map snd ss in
    let _ = DD.ninfo_pprint ("   diff: " ^ (!CP.print_svl diff2)) no_pos in
    let np11 = (* CP.mkExists qvars1 np1 None no_pos *) np1 in
    let np21 = (* CP.mkExists qvars2 np2 None no_pos *) np2 in
    let np12 = CP.subst ss np11 in
    (* let _, bare_f2 = CP.split_ex_quantifiers np2 in *)
    let svl1 = CP.fv np12 in
    let svl2 = CP.fv np21 in
    DD.ninfo_pprint ("   np12: " ^(!CP.print_formula np12)) no_pos;
    DD.ninfo_pprint ("   np21: " ^ (!CP.print_formula np21)) no_pos;
    let qvars1 = CP.remove_dups_svl ((CP.diff_svl svl1 (args@diff2))) in
    let qvars2 = CP.remove_dups_svl ((CP.diff_svl svl2 (args@diff2))) in
    let r2 = checkeq_pure qvars1 qvars2 np12 np21 in
    let _ = DD.ninfo_pprint ("   eq: " ^ (string_of_bool r2)) no_pos in
    r2
  else
    false

let check_relaxeq_formula args f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_relaxeq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_relaxeq_formula_x args f1 f2) f1 f2

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


let check_exists_cyclic_proofs_x es (ante,conseq)=
  let collect_vnode hf=
    match hf with
      | CF.ViewNode vn -> [vn]
      | _ -> []
  in
  let rec look_up_vn l_vns vn=
    match l_vns with
      | [] -> None
      | vn1::rest -> if String.compare vn vn1.CF.h_formula_view_name = 0 then
          Some (vn1.CF.h_formula_view_node::vn1.CF.h_formula_view_arguments)
        else look_up_vn rest vn
  in
  let rec build_subst ss vns1 vns2=
    match vns1 with
      | [] -> ss
      | vn::rest -> begin
          let args_opt = look_up_vn vns2 vn.CF.h_formula_view_name in
          match args_opt with
            | None -> build_subst ss rest vns2
            | Some args2 -> let ss1 = List.combine (vn.CF.h_formula_view_node::vn.CF.h_formula_view_arguments) args2 in
              build_subst (ss@(List.filter (fun (sv1,sv2) -> not (CP.eq_spec_var sv1 sv2)) ss1)) rest vns2
        end
  in
  let check_one l_vns r_vns (a1,c1)=
    let vn_a1 = CF.map_heap_1 collect_vnode a1 in
    let vn_c1 = CF.map_heap_1 collect_vnode c1 in
    if List.length l_vns != List.length vn_a1 || List.length r_vns != List.length vn_c1 then false
    else
      let l_ss = build_subst [] vn_a1 l_vns in
      let r_ss = build_subst [] vn_c1 r_vns in
      let a11 = if l_ss = [] then a1 else CF.subst l_ss a1 in
      let c11 = if r_ss = [] then c1 else CF.subst r_ss c1 in
      (check_relaxeq_formula [] ante a11) && (check_relaxeq_formula [] conseq c11)
  in
  let l_vns = CF.map_heap_1 collect_vnode ante in
  let r_vns = CF.map_heap_1 collect_vnode conseq in
  List.exists (check_one l_vns r_vns) es.CF.es_proof_traces

let check_exists_cyclic_proofs es (ante,conseq)=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair pr1 pr1 in
  let pr3 es = (pr_list_ln pr2) es.CF.es_proof_traces in
  Debug.no_2 "SY_CEQ.check_exists_cyclic_proofs" pr3 pr2 string_of_bool
      (fun _ _ -> check_exists_cyclic_proofs_x es (ante,conseq))
      es (ante,conseq)
