#include "xdebug.cppo"
open VarGen
(* module CP = Cpure    *)
(* module CF = Cformula *)
(* module MCP = Mcpure  *)

open Cprinter
open Globals
open Gen
open Tid
open Ti2
open Ti3

(*******************************)   
(* Temporal Relation at Return *)
(*******************************)
(* let ret_trel_stk: ret_trel Gen.stack = new Gen.stack *)

let add_ret_trel_stk prog ctx lhs rhs pos =
  let params = params_of_term_ann prog rhs in
  let trel = {
    ret_ctx = MCP.pure_of_mix ctx;
    termr_fname = CP.fn_of_term_ann rhs;
    termr_rhs_params = params;
    termr_lhs = lhs;
    termr_rhs = rhs; 
    termr_pos = pos; } in 
  let () = y_tinfo_hp (add_str "ret_trel" print_ret_trel) trel in
  Log.current_tntrel_ass_stk # push (Ret trel);
  ret_trel_stk # push trel;
  trel

(* Only merge relations split by post *)
let merge_trrels rec_trrels = 
  let same_flow_path r1 r2 =
    eq_path_formula r1.ret_ctx r2.ret_ctx
  in
  let same_cond_path r1 r2 = CP.eq_term_ann r1.termr_rhs r2.termr_rhs in
  let grp_trrels = partition_eq (fun r1 r2 -> 
      (same_cond_path r1 r2) && (same_flow_path r1 r2)) rec_trrels in
  (* let () = List.iter (fun trrels -> print_endline_quiet (pr_list print_ret_trel trrels)) grp_trrels in *)
  let merge_trrels = List.map (fun grp ->
      let conds = List.map (fun r -> r.ret_ctx) grp in
      match grp with
      | [] -> report_error no_pos "[TNT Inference]: Group of returned temporal assumptions is empty."
      | r::_ -> { r with ret_ctx = CP.join_disjunctions conds }) grp_trrels in
  merge_trrels

let solve_rec_trrel rtr conds = 
  let rec_cond = x_add simplify rtr.ret_ctx rtr.termr_rhs_params in
  let rec_cond =
    if CP.is_disjunct rec_cond
    then pairwisecheck rec_cond
    else rec_cond
  in
  let rec_cond, conds = List.fold_left (fun (rc, ca) cond ->
      match cond with
      | Base bc -> 
        let oc = mkAnd bc rc in
        if is_sat oc then (* Recursive case and base case are overlapping *)
          let nbc = mkAnd bc (mkNot rc) in
          if is_sat nbc then (mkAnd (mkNot bc) rc, (Base nbc)::(MayTerm oc)::ca)
          else (mkAnd (mkNot bc) rc, (MayTerm oc)::ca)
        else (rc, cond::ca)
      | MayTerm mc -> 
        let oc = mkAnd mc rc in
        if is_sat oc then (mkAnd (mkNot mc) rc, cond::ca)
        else (rc, cond::ca)
      | Rec other_rc ->
        let oc = mkAnd other_rc rc in
        if is_sat oc then 
          let nrc = mkAnd other_rc (mkNot rc) in
          if is_sat nrc then (mkAnd (mkNot other_rc) rc, (Rec oc)::(Rec nrc)::ca)
          else (mkAnd (mkNot other_rc) rc, (Rec oc)::ca)
        else (rc, cond::ca)
    ) (rec_cond, []) conds in
  if is_sat rec_cond then (Rec rec_cond)::conds
  else conds 

let solve_base_trrel btr turels =
  let base_cond = x_add simplify btr.ret_ctx btr.termr_rhs_params in
  let base_cond =
    if CP.is_disjunct base_cond
    then pairwisecheck base_cond
    else base_cond
  in
  (* There is at least one method call in the base case is not terminating or unknown *)
  if List.exists (fun r -> is_sat (mkAnd base_cond r.call_ctx)) turels 
  then MayTerm base_cond
  else Base base_cond

let solve_base_trrels params base_trrels turels =
  let base_ctx = List.map (fun btr ->
      x_add simplify btr.ret_ctx btr.termr_rhs_params) base_trrels in
  let not_term_cond = List.fold_left (fun ac tu ->
      let ctx = x_add simplify tu.call_ctx params in
      (* let () = print_endline_quiet ("ctx: " ^ (!CP.print_formula ctx)) in *)
      mkOr ac ctx) (CP.mkFalse no_pos) turels in
  let not_term_cond = om_simplify not_term_cond in
  let term_cond = mkNot not_term_cond in

  (* let () = print_endline_quiet ("term_cond: " ^ (!CP.print_formula term_cond)) in         *)
  (* let () = print_endline_quiet ("not_term_cond: " ^ (!CP.print_formula not_term_cond)) in *)
  (* let () = print_endline_quite ("base_ctx: " ^ (pr_list !CP.print_formula base_ctx)) in   *)

  let base_cond = List.fold_left (fun ac bctx ->
      mkOr ac (mkAnd bctx term_cond)) (CP.mkFalse no_pos) base_ctx in
  (* let base_conds = simplify_and_slit_disj base_cond in *)
  let base_cond = simplify_disj base_cond in
  let base_cond = if is_sat base_cond then [Base base_cond] else [] in
  base_cond  
(* if !Globals.tnt_infer_lex then base_cond                                *)
(* else                                                                    *)
(*   let may_cond = List.fold_left (fun ac bctx ->                         *)
(*     mkOr ac (mkAnd bctx not_term_cond)) (CP.mkFalse no_pos) base_ctx in *)
(*   (* let may_conds = simplify_and_slit_disj may_cond in *)              *)
(*   let may_cond = simplify_disj may_cond in                              *)
(*   let may_cond = if is_sat may_cond then [MayTerm may_cond] else [] in  *)
(*   base_cond @ may_cond                                                  *)

let solve_base_trrels params base_trrels turels =
  Debug.no_1 "solve_base_trrels" (!CP.print_svl) (pr_list print_trrel_sol)
    (fun _ -> solve_base_trrels params base_trrels turels) params

let solve_trrel_list params trrels turels = 
  (* let params = remove_nondet_vars params in *)
  let base_trrels, rec_trrels = List.partition (fun trrel -> trrel.termr_lhs == []) trrels in
  (* let base_conds = List.map (fun btr -> solve_base_trrel btr turels) base_trrels in *)
  let base_conds = solve_base_trrels params base_trrels turels in
  let rec_trrels = merge_trrels rec_trrels in

  (* let conds = List.fold_left (fun conds rtr -> solve_rec_trrel rtr conds) base_conds rec_trrels in  *)
  let not_rec_conds = List.map (fun s ->
      match s with
      | Base bc -> bc
      | MayTerm mc -> mc
      | _ -> CP.mkFalse no_pos) base_conds in
  let not_rec_cond = 
    if is_empty not_rec_conds 
    then CP.mkFalse no_pos 
    else CP.join_disjunctions not_rec_conds 
  in

  (* let () = print_endline_quiet ("not_rec_cond: " ^ (!CP.print_formula not_rec_cond)) in *)

  let rec_conds = List.fold_left (fun acc rtr ->
      let rec_cond = x_add simplify rtr.ret_ctx ((* remove_nondet_vars *) rtr.termr_rhs_params) in
      let rec_cond =
        if CP.is_disjunct rec_cond
        then pairwisecheck rec_cond
        else rec_cond
      in
      let rec_cond = mkAnd rec_cond (mkNot not_rec_cond) in
      if is_sat rec_cond then acc @ [rec_cond] else acc) [] rec_trrels 
  in

  let loop_conds = List.fold_left (fun acc tu ->
      match tu.termu_rhs with
      | Loop _ ->
        let loop_cond = x_add simplify tu.call_ctx params in
        let loop_cond = mkAnd loop_cond (mkNot not_rec_cond) in
        if is_sat loop_cond then acc @ [loop_cond] else acc
      | _ -> acc) [] turels 
  in
  let rec_conds = rec_conds @ loop_conds in

  let rec_conds = 
    if is_empty rec_conds then [] 
    else
      let rec_conds = om_simplify (CP.join_disjunctions rec_conds) in
      List.map (fun c -> Rec c) (CP.split_disjunctions rec_conds)
  in

  let conds = base_conds @ rec_conds in

  (* let may_cond = om_simplify (mkNot (join_disjs (List.map get_cond conds))) in *)
  (* if (is_sat may_cond) && not !Globals.tnt_infer_lex then                      *)
  (*   conds @ [MayTerm may_cond]                                                 *)
  (* else conds                                                                   *)
  let rem_cond = om_simplify (mkNot (join_disjs (List.map get_cond conds))) in
  let pre_cond = CP.join_conjunctions (List.fold_left (fun acc tu ->
      let cond = x_add simplify tu.call_ctx params in
      acc @ [cond]) [] turels) in
  let unk_cond = om_simplify (mkAnd pre_cond rem_cond) in
  let may_cond = om_simplify (mkAnd rem_cond (mkNot unk_cond)) in 
  conds @ 
  (if is_sat unk_cond then [Rec unk_cond] else []) @
  (if is_sat may_cond then [Rec may_cond] else [])

(* let conds = List.map simplify_trrel_sol conds in                 *)
(* let conds = List.concat (List.map split_disj_trrel_sol conds) in *)
(* conds                                                            *)

let pr_cond_w_ids f =
  let pr_cond (i, c) = "[" ^ (string_of_int i) ^ "]" ^ (print_trrel_sol c) in 
  (pr_list (fun ((fn, _), s) -> 
      "\t" ^ (if fn = "" then "" else fn ^ ": ") ^ 
          (pr_list pr_cond s) ^ "\n")) f

let case_split_init prog trrels turels = 
  let fn_rels = partition_trels_by_proc trrels turels in
  let fn_cond_w_ids = List.map (fun (fn, trrels, turels) ->
      let params = snd fn in
      (fn, List.map (fun c -> tnt_fresh_int (), c) (solve_trrel_list params trrels turels))) fn_rels in
  let () = 
    print_endline_quiet ("\nBase/Rec Case Splitting:\n" ^ 
                         (pr_cond_w_ids fn_cond_w_ids))
  in fn_cond_w_ids 

let case_split_init prog trrels turels = 
  Debug.no_2 "case_split_init" 
      pr_none pr_none pr_cond_w_ids 
      (fun _ _ -> case_split_init prog trrels turels) trrels turels
  
(*****************************)
(* Temporal Relation at Call *)
(*****************************)
(* let call_trel_stk: call_trel Gen.stack = new Gen.stack *)

let add_call_trel_stk prog ctx lhs rhs callee args pos =
  let params = params_of_term_ann prog rhs in
  let trel = {
    trel_id = tnt_fresh_int ();
    call_ctx = MCP.pure_of_mix ctx;
    termu_fname = CP.fn_of_term_ann lhs;
    termu_lhs = lhs;
    termu_rhs = rhs; 
    termu_rhs_params = params; 
    termu_cle = callee;
    termu_rhs_args = args; 
    termu_pos = pos; } in 
  let () = y_tinfo_hp (add_str "call_trel" print_call_trel) trel in
  Log.current_tntrel_ass_stk # push (Call trel);
  call_trel_stk # push trel;
  trel

(* Initial instantiation of temporal relation *)      
let inst_lhs_trel_base rel fn_cond_w_ids =  
  let lhs_ann = rel.termu_lhs in
  let inst_lhs = match lhs_ann with
    | CP.TermU uid -> 
      begin try
          let fn = uid.CP.tu_fname in
          let _, cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
          let rcond_w_ids = List.filter (fun (_, c) -> is_rec c) cond_w_ids in
          let rcond_w_ids = List.map (fun (i, c) -> (i, get_cond c)) rcond_w_ids in
          let tuc = uid.CP.tu_cond in
          let eh_ctx = mkAnd rel.call_ctx tuc in
          let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx c)) rcond_w_ids in
          List.map (fun (i, c) -> CP.TermU { uid with 
                                             CP.tu_id = cantor_pair uid.CP.tu_id i; 
                                             CP.tu_cond = mkAnd tuc c; 
                                             (* Update condition of interest for abduction *)
                                             CP.tu_icond = c; }) fs_rconds
        with Not_found -> [lhs_ann] end
    | _ -> [lhs_ann] 
  in inst_lhs

let inst_rhs_trel_base inst_lhs rel fn_cond_w_ids = 
  let rhs_ann = rel.termu_rhs in
  let cond_lhs = CP.cond_of_term_ann inst_lhs in
  let ctx = mkAnd rel.call_ctx cond_lhs in
  let inst_rhs = match rhs_ann with
    | CP.TermU uid -> 
      begin try
          let fn = uid.CP.tu_fname in
          let rhs_args = uid.CP.tu_args in
          let (_, fparams), cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
          let tuc = uid.CP.tu_cond in
          let eh_ctx = mkAnd ctx tuc in
          let sst = List.combine fparams rhs_args in
          let subst_cond_w_ids = List.map (fun (i, c) -> 
              (i, trans_trrel_sol (CP.subst_term_avoid_capture sst) c)) cond_w_ids in 
          let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx (get_cond c))) subst_cond_w_ids in
          List.map (fun (i, c) -> 
              let cond = get_cond c in
              CP.TermU { uid with 
                         CP.tu_id = cantor_pair uid.CP.tu_id i; 
                         CP.tu_cond = mkAnd tuc cond; 
                         CP.tu_icond = cond;
                         CP.tu_sol = match c with 
                           | Base _ -> Some (CP.Term, [])
                           | MayTerm _ -> Some (CP.MayLoop None, [])
                           | _ -> uid.CP.tu_sol }) fs_rconds
        with Not_found -> [rhs_ann] end
    | _ -> [rhs_ann] 
  in List.map (fun irhs -> update_call_trel rel inst_lhs irhs) inst_rhs

let inst_call_trel_base rel fn_cond_w_ids =
  let inst_lhs = inst_lhs_trel_base rel fn_cond_w_ids in
  let inst_rels = List.concat (List.map (fun ilhs -> 
      inst_rhs_trel_base ilhs rel fn_cond_w_ids) inst_lhs) in
  inst_rels

(* End of Temporal Relation at Call *)

(******************)
(* Main algorithm *)
(******************)
(* Only analyze unknown scc *)
let solve_turel_one_unknown_scc prog trrels tg scc =
  let outside_scc_succ = outside_succ_scc tg scc in

  let update = 
    (* We assume that all nodes in scc are unknown *)
    if List.for_all (fun (_, v) -> CP.is_Loop v) outside_scc_succ then
      if (outside_scc_succ = []) && (is_acyclic_scc tg scc)
      (* Term with phase number or MayLoop *)
      then update_ann scc (subst (CP.Term, [CP.mkIConst (scc_fresh_int ()) no_pos]))
      else
        try
          (* Loop with nondet *)
          let nd_trrel = List.find (fun rel -> CP.has_nondet_cond rel.ret_ctx) trrels in
          let nd_pos = nd_trrel.termr_pos in
          update_ann scc (subst (CP.MayLoop (Some { CP.tcex_trace = [CP.TCall nd_pos] }), []))
        with _ ->
          (* update_ann scc (subst (CP.Loop None, [])) (* Loop without nondet *) *)
          proving_non_termination_scc prog trrels tg scc

    (* match outside_scc_succ with                                                      *)
    (* | [] ->                                                                          *)
    (*   if is_acyclic_scc tg scc                                                       *)
    (*   (* Term with phase number or MayLoop *)                                        *)
    (*   then update_ann scc (subst (CP.Term, [CP.mkIConst (scc_fresh_int ()) no_pos])) *)
    (*   else                                                                           *)
    (*     update_ann scc (subst (CP.Loop None, [])) (* Loop *)                         *)
    (* | s::_ -> update_ann scc (subst (CP.Loop None, [])) (* Loop *)                   *)

    else if List.for_all (fun (_, v) -> CP.is_Term v) outside_scc_succ then
      if is_acyclic_scc tg scc 
      then update_ann scc (subst (CP.Term, [CP.mkIConst (scc_fresh_int ()) no_pos])) (* Term *)
      else proving_termination_scc prog trrels tg scc

    else if (List.exists (fun (_, v) -> CP.is_Loop v) outside_scc_succ)
    then proving_non_termination_scc prog trrels tg scc

    (* else if (List.exists (fun (_, v) -> CP.is_MayLoop v) outside_scc_succ) then           *)
    (*   if is_acyclic_scc tg scc                                                            *)
    (*   then update_ann scc (subst (CP.MayLoop None, [])) (* MayLoop *)                     *)
    (*   else proving_non_termination_scc prog trrels tg scc                                 *)

    (* else (* Error: One of scc's succ is Unknown *)                                        *)
    (*   report_error no_pos "[TNT Inference]: One of analyzed scc's successors is Unknown." *)

    else
      let mayloop_lst = List.find_all (fun (_, v) -> CP.is_MayLoop v) outside_scc_succ in
      if is_empty mayloop_lst then
        report_error no_pos "[TNT Inference]: One of analyzed scc's successors is Unknown."
      else if is_acyclic_scc tg scc then
        let cex = CP.cex_of_term_ann_list (List.map snd mayloop_lst) in
        update_ann scc (subst (CP.MayLoop cex, [])) (* MayLoop *)
      else proving_non_termination_scc prog trrels tg scc

  in
  let ntg = map_ann_scc tg scc update in
  ntg

let solve_turel_one_scc prog trrels tg scc =
  if is_unknown_scc tg scc then 
    solve_turel_one_unknown_scc prog trrels tg scc
  else tg

let solve_turel_one_scc prog trrels tg scc =
  let pr = print_graph_by_rel in
  Debug.no_1 "solve_turel_one_scc" pr pr
    (fun _ -> solve_turel_one_scc prog trrels tg scc) tg

let finalize_turel_graph prog tg =
  print_web_mode "Termination Inference Result:";
  (* let () = print_endline (print_graph_by_rel tg) in *)
  pr_proc_case_specs prog

(* let rec solve_turel_graph iter_num prog trrels tg =                                         *)
(*   if iter_num < !Globals.tnt_thres then                                                     *)
(*     try                                                                                     *)
(*       let scc_list = Array.to_list (TGC.scc_array tg) in                                    *)
(*       let scc_groups = partition_scc_list tg scc_list in                                    *)
(*       (* let () =                                                            *)             *)
(*       (*   print_endline_quiet ("GRAPH @ ITER " ^ (string_of_int iter_num)); *)             *)
(*       (*   print_endline_quiet (print_graph_by_rel tg)                       *)             *)
(*       (* in                                                                  *)             *)
(*       (* let () = print_endline_quiet (print_scc_list_num scc_list) in       *)             *)
(*       let tg = List.fold_left (fun tg -> solve_turel_one_scc prog trrels tg) tg scc_list in *)
(*       finalize_turel_graph prog tg                                                          *)
(*     with                                                                                    *)
(*     | Restart_with_Cond tg ->                                                               *)
(*       solve_turel_graph (iter_num + 1) prog trrels tg                                       *)
(*     | _ -> finalize_turel_graph prog tg                                                     *)
(*   else finalize_turel_graph prog tg                                                         *)

let rec solve_turel_graph iter_num prog trrels tg =
  let scc_list = Array.to_list (TGC.scc_array tg) in
  let scc_groups = partition_scc_list tg scc_list in
  List.iter (fun scc_group ->
      solve_turel_graph_one_group iter_num prog trrels tg scc_group) scc_groups

and solve_turel_graph_one_group iter_num prog trrels tg scc_list =
  if iter_num < !Globals.tnt_thres then
    try
      let () = pr_im_case_specs iter_num in
      let tg = sub_graph_of_scc_list tg scc_list in
      (* let () =                                                            *)
      (*   print_endline_quiet ("GRAPH @ ITER " ^ (string_of_int iter_num)); *)
      (*   print_endline_quiet (print_graph_by_rel tg)                       *)
      (* in                                                                  *)
      (* let () = print_endline_quiet (print_scc_list_num scc_list) in       *)
      let tg = List.fold_left (fun tg scc -> 
          try solve_turel_one_scc prog trrels tg scc
          with Should_Finalize -> tg) tg scc_list in
      ()
    with
    | Restart_with_Cond (_, tg) -> solve_turel_graph (iter_num + 1) prog trrels tg
    | _ -> ()
  else ()

let solve_turel_graph_init prog trrels tg =
  let () = solve_turel_graph 0 prog trrels tg in
  finalize_turel_graph prog tg

let solve_trel_init prog trrels turels =
  (* (* Transform nondet relations into vars *)                       *)
  (* Unsound: termination-crafted/NonTermination2_false-termination.c *)
  (* let trrels, turels = trans_nondet_trels prog trrels turels in    *)
  let fn_cond_w_ids = case_split_init prog trrels turels in 
  (* Update TNT case spec with base condition *)
  let () = List.iter (add_case_spec_of_trrel_sol_proc prog)
      (List.map (fun ((fn, _), sl) -> (fn, List.map snd sl)) fn_cond_w_ids) in
  (* let () =                                      *)
  (*   print_endline_quiet ("Initial Case Spec:"); *)
  (*   pr_proc_case_specs prog                     *)
  (* in                                            *)

  let irels = List.concat (List.map (fun rel -> 
      inst_call_trel_base rel fn_cond_w_ids) turels) in
  (* let () = print_endline_quiet ("Initial Inst Assumption:\n" ^        *)
  (*   (pr_list (fun ir -> (print_call_trel_debug ir) ^ "\n") irels)) in *)

  let tg = graph_of_trels irels in
  (* let rec_trrels = List.filter (fun tr -> List.length tr.termr_lhs > 0) trrels in *)
  (* solve_turel_graph_init prog rec_trrels tg                                       *)
  solve_turel_graph_init prog trrels tg

let finalize () =
  reset_seq_num ();
  reset_scc_num ();
  ret_trel_stk # reset;
  call_trel_stk # reset;
  Hashtbl.reset proc_case_specs

(* Main Inference Function *)
let solve no_verification_errors should_infer_tnt prog =
  if not should_infer_tnt then ()
  else
    let trrels = ret_trel_stk # get_stk in
    let turels = call_trel_stk # get_stk in
  
    if not no_verification_errors then
      x_winfo_pp ("\nTermination Inference is not performed due to errors in verification process.\n") no_pos
    (* If turels is empty then there is no *)
    (* unknown termination behaviors       *)
    else if turels = [] && trrels = [] then 
      x_winfo_pp ("\nTermination Inference is not performed due to empty set of relational assumptions.\n") no_pos
    else
      let () = print_endline_quiet "\n\n*****************************" in
      let () = print_endline_quiet     "*** TERMINATION INFERENCE ***" in
      let () = print_endline_quiet     "*****************************" in
  
      (* Temporarily disable template assumption printing *)
      let pr_templassume = !print_relassume in
      let () = print_relassume := false in
  
      let () = print_endline_quiet "Temporal Assumptions:" in
      let () = List.iter (fun trrel -> print_endline_quiet ((print_ret_trel trrel) ^ "\n")) trrels in
      let () = List.iter (fun turel -> print_endline_quiet ((print_call_trel turel) ^ "\n")) turels in
  
      let () = solve_trel_init prog trrels turels in
  
      let () = print_relassume := pr_templassume in
      ()




