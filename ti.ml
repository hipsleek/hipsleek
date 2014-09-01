module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Cprinter
open Globals
open Gen
open Ti2
open Ti3

(*******************************)
(* Temporal Relation at Return *)
(*******************************)
let ret_trel_stk: ret_trel Gen.stack = new Gen.stack

let add_ret_trel_stk prog ctx lhs rhs =
  (* let params = List.concat (List.map CP.afv (CP.args_of_term_ann rhs)) in *)
  let params = params_of_term_ann prog rhs in
  let trel = {
    ret_ctx = ctx;
    termr_fname = CP.fn_of_term_ann rhs;
    termr_params = params;
    termr_lhs = lhs;
    termr_rhs = rhs; } in 
  (* let _ = print_endline (print_ret_trel trel) in *)
  Log.current_tntrel_ass_stk # push (Ret trel);
  ret_trel_stk # push trel
  
let rec solve_rec_trrel rtr conds = 
  let rec_cond = simplify (MCP.pure_of_mix rtr.ret_ctx) rtr.termr_params in
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

let solve_base_trrel btr = 
  Base (simplify (MCP.pure_of_mix btr.ret_ctx) btr.termr_params)

let solve_trrel_list trrels = 
  (* print_endline (pr_list print_ret_trel trrel) *)
  let base_trrels, rec_trrels = List.partition (fun trrel -> trrel.termr_lhs == []) trrels in
  let base_conds = List.map solve_base_trrel base_trrels in
  let conds = List.fold_left (fun conds rtr -> solve_rec_trrel rtr conds) base_conds rec_trrels in 
  let conds = List.map simplify_trrel_sol conds in
  let conds = List.concat (List.map split_disj_trrel_sol conds) in
  conds
  
let case_split_init trrels = 
  let fn_trrels = 
    let key_of r = (r.termr_fname, r.termr_params) in
    let key_eq (k1, _) (k2, _) = String.compare k1 k2 == 0 in  
    partition_by_key key_of key_eq trrels 
  in
  let fn_cond_w_ids = List.map (fun (fn, trrels) -> 
    (fn, List.map (fun c -> tnt_fresh_int (), c) (solve_trrel_list trrels))) fn_trrels in
  let _ = 
    let pr_cond (i, c) = "[" ^ (string_of_int i) ^ "]" ^ (print_trrel_sol c) in 
    print_endline ("\nBase/Rec Case Splitting:\n" ^ 
      (pr_list (fun ((fn, _), s) -> 
        "\t" ^ (if fn = "" then "" else fn ^ ": ") ^ 
        (pr_list pr_cond s) ^ "\n") fn_cond_w_ids))
  in fn_cond_w_ids 
  
(*****************************)
(* Temporal Relation at Call *)
(*****************************)
let call_trel_stk: call_trel Gen.stack = new Gen.stack

let add_call_trel_stk ctx lhs rhs =
  let trel = {
    call_ctx = ctx;
    trel_id = tnt_fresh_int ();
    termu_lhs = lhs;
    termu_rhs = rhs; } in 
  (* let _ = print_endline (print_call_trel trel) in *)
  Log.current_tntrel_ass_stk # push (Call trel);
  call_trel_stk # push trel
  
(* Initial instantiation of temporal relation *)      
let inst_lhs_trel_base rel fn_cond_w_ids =  
  let lhs_ann = rel.termu_lhs in
  let inst_lhs = match lhs_ann with
    | CP.TermU uid -> 
      let fn = uid.CP.tu_fname in
      let _, cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
      let rcond_w_ids = List.filter (fun (_, c) -> is_rec c) cond_w_ids in
      let rcond_w_ids = List.map (fun (i, c) -> (i, get_cond c)) rcond_w_ids in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) tuc in
      let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx c)) rcond_w_ids in
      List.map (fun (i, c) -> CP.TermU { uid with 
        CP.tu_id = cantor_pair uid.CP.tu_id i; 
        CP.tu_cond = mkAnd tuc c; 
        (* Update condition of interest for abduction *)
        CP.tu_icond = c; }) fs_rconds
    | _ -> [lhs_ann] 
  in inst_lhs

let inst_rhs_trel_base inst_lhs rel fn_cond_w_ids = 
  let rhs_ann = rel.termu_rhs in
  let cond_lhs = CP.cond_of_term_ann inst_lhs in
  let ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) cond_lhs in
  let inst_rhs = match rhs_ann with
    | CP.TermU uid -> 
      let fn = uid.CP.tu_fname in
      let rhs_args = uid.CP.tu_args in
      let (_, fparams), cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd ctx tuc in
      let sst = List.combine fparams rhs_args in
      let subst_cond_w_ids = List.map (fun (i, c) -> 
        (i, trans_trrel_sol (CP.subst_term_avoid_capture sst) c)) cond_w_ids in 
      let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx (get_cond c))) subst_cond_w_ids in
      List.map (fun (i, c) -> CP.TermU { uid with 
        CP.tu_id = cantor_pair uid.CP.tu_id i; 
        CP.tu_cond = mkAnd tuc (get_cond c); 
        CP.tu_sol = match c with 
          | Base _ -> Some (Term, [])
          | MayTerm _ -> Some (MayLoop, [])
          | _ -> uid.CP.tu_sol }) fs_rconds
    | _ -> [rhs_ann] 
  in List.map (fun irhs -> update_call_trel rel inst_lhs irhs) inst_rhs
  
let inst_call_trel_base rel fn_cond_w_ids =
  let inst_lhs = inst_lhs_trel_base rel fn_cond_w_ids in
  let inst_rels = List.concat (List.map (fun ilhs -> 
    inst_rhs_trel_base ilhs rel fn_cond_w_ids) inst_lhs) in
  inst_rels

(* Main algorithm *)
exception Restart_with_Cond of TG.t
       
let solve_turel_one_scc prog tg scc =
  let update_ann scc f ann = (* Only update nodes in scc *)
    let ann_id = CP.id_of_term_ann ann in
    if Gen.BList.mem_eq (==) ann_id scc 
    then f ann
    else ann
  in
  
  let subst sol ann =
    let fn = CP.fn_of_term_ann ann in
    let cond = CP.cond_of_term_ann ann in
    (* Add call number into the result *)
    (* let call_num = CP.call_num_of_term_ann ann in                    *)
    (* let sol = (fst sol, (CP.mkIConst call_num no_pos)::(snd sol)) in *)
    (* Update TNT case spec with solution *)
    let _ = add_sol_case_spec_proc fn cond sol in
    (* let _ = print_endline ("Case spec @ scc " ^ (print_scc_num scc)) in *)
    (* let _ = pr_proc_case_specs () in                                    *)
    
    subst_sol_term_ann sol ann
  in 
  
  let outside_scc_succ = outside_succ_scc tg scc in
  
  let update = 
    (* We assume that all nodes in scc are unknown *)
    if List.for_all (fun v -> CP.is_Loop v) outside_scc_succ then
      if (outside_scc_succ = []) && (is_acyclic_scc tg scc) 
           (* Term with phase number or MayLoop *)
      then update_ann scc (subst (CP.Term, [CP.mkIConst (scc_fresh_int ()) no_pos]))
      else update_ann scc (subst (CP.Loop, [])) (* Loop *)
    
    else if (List.exists (fun v -> CP.is_Loop v) outside_scc_succ) ||
            (List.exists (fun v -> CP.is_MayLoop v) outside_scc_succ) 
    then update_ann scc (subst (CP.MayLoop, [])) (* MayLoop *)
  
    else if List.for_all (fun v -> CP.is_Term v) outside_scc_succ then
      if is_acyclic_scc tg scc 
      then update_ann scc (subst (CP.Term, [CP.mkIConst (scc_fresh_int ()) no_pos])) (* Term *)
      else (* Term with a ranking function for each scc's node *)
        let res = infer_ranking_function_scc prog tg scc in
        match res with
        | Some rank_of_ann -> 
          let scc_num = CP.mkIConst (scc_fresh_int ()) no_pos in
          update_ann scc (fun ann -> 
            let res = (CP.Term, scc_num::(rank_of_ann ann)) in 
            subst res ann)
        | None ->
          let abd_cond = infer_abductive_icond prog tg scc in 
          let tg = update_graph_with_icond tg scc abd_cond in
          (* let _ = print_endline (print_graph_by_rel tg) in *)
          raise (Restart_with_Cond tg)
  
    else (* Error: One of scc's succ is Unknown *)
      report_error no_pos "[TNT Inference]: One of analyzed scc's successors is Unknown."
  in
  let ntg = map_ann_scc tg scc update in
  ntg
  
let finalize_turel_graph prog tg = 
  let _ = print_endline "Termination Inference Result:" in
  (* let _ = print_endline (print_graph_by_rel tg) in *)
  pr_proc_case_specs ()
  
let rec solve_turel_graph iter_num prog tg = 
  if iter_num < !Globals.tnt_thres then
    try
      let scc_list = Array.to_list (TGC.scc_array tg) in
      (* let _ =                                                       *)
      (*   print_endline ("GRAPH @ ITER " ^ (string_of_int iter_num)); *)
      (*   print_endline (print_graph_by_rel tg)                       *)
      (* in                                                            *)
      (* let _ = print_endline (print_scc_list_num scc_list) in *)
      let tg = List.fold_left (fun tg -> solve_turel_one_scc prog tg) tg scc_list in
      finalize_turel_graph prog tg
    with Restart_with_Cond tg -> 
      (* TODO: Duplicate on nodes that have been analyzed *)
      solve_turel_graph (iter_num + 1) prog tg
  else finalize_turel_graph prog tg

let solve_turel_init prog turels fn_cond_w_ids = 
  (* Update TNT case spec with base condition *)
  let _ = List.iter add_case_spec_of_trrel_sol_proc
    (List.map (fun ((fn, _), sl) -> (fn, List.map snd sl)) fn_cond_w_ids) in
  (* let _ =                                  *)
  (*   print_endline ("Initial Case Spec:");  *)
  (*   pr_proc_case_specs ()                  *)
  (* in                                       *)
  
  let irels = List.concat (List.map (fun rel -> 
    inst_call_trel_base rel fn_cond_w_ids) turels) in
  (* let _ = print_endline ("Initial Inst Assumption:\n" ^               *)
  (*   (pr_list (fun ir -> (print_call_trel_debug ir) ^ "\n") irels)) in *)
    
  let tg = graph_of_trels irels in
  solve_turel_graph 0 prog tg

let finalize () =
  ret_trel_stk # reset;
  call_trel_stk # reset;
  Hashtbl.reset proc_case_specs

(* Main Inference Function *)  
let solve should_infer prog = 
  let trrels = ret_trel_stk # get_stk in
  let turels = call_trel_stk # get_stk in

  if trrels = [] && turels = [] then ()
  else if not should_infer then
    print_endline ("\n\n!!! Termination Inference is not performed due to errors in verification process.\n\n")
  else
    let _ = print_endline "\n\n*************************" in
    let _ = print_endline "* TERMINATION INFERENCE *" in
    let _ = print_endline "*************************" in

    (* Temporarily disable template assumption printing *)
    let pr_templassume = !print_relassume in
    let _ = print_relassume := false in

    let _ = print_endline "Temporal Assumptions:" in
    let _ = List.iter (fun trrel -> print_endline ((print_ret_trel trrel) ^ "\n")) trrels in
    let _ = List.iter (fun turel -> print_endline ((print_call_trel turel) ^ "\n")) turels in
  
    let fn_cond_w_ids = case_split_init trrels in
    let _ = solve_turel_init prog turels fn_cond_w_ids in
  
    let _ = print_relassume := pr_templassume in
    ()
  
  
  
  
