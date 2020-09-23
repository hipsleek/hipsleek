#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals

module C = Cast
module CP = Cpure
module CF = Cformula
module Syn = Synthesis
module I = Iast
module LO2 = Label_only.Lab2_List
module MutR = Mutation_repair
module RP = Repairpure

let filter_cand buggy_loc cand =
  match buggy_loc with
  | Some b_loc ->
    let cand_pos = Iast.get_exp_pos cand in
    let () = x_tinfo_hp (add_str "buggy pos" RP.pr_pos) b_loc no_pos in
    let () = x_tinfo_hp (add_str "cand pos" RP.pr_pos) cand_pos no_pos in
    let b_lnum = b_loc.start_pos.Lexing.pos_lnum in
    let cand_lnum = cand_pos.start_pos.Lexing.pos_lnum in
    b_lnum = cand_lnum
  | None ->
    let cand_pos = Iast.get_exp_pos cand in
    let b_loc = VarGen.proving_loc#get in
    let b_lnum = b_loc.start_pos.Lexing.pos_lnum in
    let cand_lnum = cand_pos.start_pos.Lexing.pos_lnum in
    b_lnum >= cand_lnum

let mk_candidate_proc (iproc:I.proc_decl) args candidate num =
  let body = Gen.unsome iproc.I.proc_body in
  let loc = I.get_exp_pos candidate in
  let helper sv = (CP.type_of_sv sv, CP.name_of_sv sv) in
  let decl_vars = RP.get_var_decls loc body |> List.map helper in
  let args = args @ decl_vars |> List.map (fun (x, y) -> CP.mk_typed_sv x y) in
  let args = args |> CP.remove_dups_svl
             |> List.map (fun x -> (CP.type_of_sv x, CP.name_of_sv x)) in
  let fcode = RP.create_fcode_exp args num in
  let n_body = Some (RP.replace_exp body fcode candidate) in
  ({iproc with proc_body = n_body}, args)

let rec helper args = match args with
  | [] -> ""
  | [(typ, name)] -> (string_of_typ typ) ^ " " ^ name
  | h::t -> let tail = helper t in
    let head = string_of_typ (fst h) ^ " " ^ (snd h) in
    head ^ "," ^ tail

let mutating_proc iprog (iproc: I.proc_decl): bool =
  let n_proc_list = match iproc.I.proc_body with
    | None -> []
    | Some proc_body ->
      let n_exp_list = MutR.mutate_iast_exp iprog iproc proc_body in
      let () = x_tinfo_hp (add_str "mutated_body" (pr_list RP.pr_exp)) n_exp_list no_pos in
      let n_proc_list =
        n_exp_list |> List.map (fun x -> {iproc with I.proc_body = Some x}) in
      n_proc_list in
  let aux_repair curr_res mutated_proc =
    if curr_res then true
    else
      let aux_map i_proc =
        if Syn.contains mutated_proc.I.proc_name i_proc.I.proc_name
        then mutated_proc else i_proc in
      let n_procedures = iprog.I.prog_proc_decls |> List.map aux_map in
      let n_iprog = {iprog with I.prog_proc_decls = n_procedures} in
      try
        let cprog, _ = Astsimp.trans_prog n_iprog in
        let () = Typechecker.check_prog_wrapper n_iprog cprog in
        let () = x_binfo_pp " MUTATION STRATEGY" no_pos in
        let () = x_binfo_hp (add_str "mutated_proc" RP.pr_proc) mutated_proc no_pos in
        true
      with _ -> false in
  List.fold_left aux_repair false n_proc_list

let repair_iprog_by_mutation (iprog: I.prog_decl) repair_proc =
  let () = x_binfo_pp "START USING MUTATION" no_pos in
    let p_name = Cast.unmingle_name repair_proc in
    let procs = iprog.I.prog_proc_decls in
    let r_iproc = List.find (fun x -> eq_str x.I.proc_name p_name) procs in
    mutating_proc iprog r_iproc

let mk_candidate_iprog iprog (iproc:I.proc_decl) args candidate num =
  let () = x_binfo_hp (add_str "candidate" RP.pr_exp) candidate no_pos in
  let n_iproc, args = mk_candidate_proc iproc args candidate num in
  let () = x_binfo_hp (add_str "proc" RP.pr_proc) n_iproc no_pos in
  let () = Syn.repair_pos := Some (I.get_exp_pos candidate) in
  let decl_vars = List.map (fun (x,y) -> CP.mk_typed_sv x y) args in
  let () = Syn.block_var_decls := decl_vars in
  let names = args |> List.map snd in
  let arg_str = helper args in
  let arg_names = pr_idents_wo_brackets names "," in
  let typ = RP.type_of_exp candidate [] [] in
  let fc_str = fcode_str ^ (RP.pr_int num) in
  let fcode = hp_str ^ " P" ^ (RP.pr_int num) ^ "(" ^ arg_str ^ ").\n" ^
              hp_str ^ " Q" ^ (RP.pr_int num) ^ "(" ^ arg_str ^ ").\n" ^
              (string_of_typ typ) ^  " " ^ fc_str ^ "(" ^ arg_str ^ ")\n" ^
              "requires P" ^ (RP.pr_int num) ^ "(" ^ arg_names ^ ")\n" ^
              "ensures Q" ^ (RP.pr_int num) ^ "(" ^ arg_names ^ ");" in
  let () = x_tinfo_hp (add_str "fcode" pr_id) fcode no_pos in
  let n_prog = Parser.parse_hip_string "fcode" fcode in
  (* let procs = n_prog.I.prog_proc_decls in *)
  let hps = n_prog.I.prog_hp_decls in
  let () = x_tinfo_hp (add_str "hp" RP.pr_hps) hps no_pos in
  let helper_proc proc = if proc.I.proc_name = iproc.I.proc_name
                           then n_iproc else proc in
  let n_procs = List.map helper_proc iprog.I.prog_proc_decls in
  let n_procs = n_prog.I.prog_proc_decls @ n_procs in
  let n_hps = n_prog.I.prog_hp_decls @ iprog.I.prog_hp_decls in
  {iprog with prog_hp_decls = n_hps;
              prog_proc_decls = n_procs}

let repair_heap_template () =
  let () = x_binfo_pp "start synthesis process in template" no_pos in
  let ents = !Synthesis.entailments |> List.rev in
  let pr_ents = pr_list_mln (pr_pair RP.pr_formula RP.pr_formula) in
  let () = x_binfo_hp (add_str "ents" pr_ents) ents no_pos in
  let iprog = !Syn.syn_iprog |> Gen.unsome in
  let prog = !Syn.syn_cprog |> Gen.unsome in
  let proc_name = !Syn.tmpl_proc_name |> Gen.unsome in
  let proc = C.find_proc prog proc_name in
  let () = x_binfo_hp (add_str "proc_name" pr_id) proc_name no_pos in
  let _ = Synthesizer.synthesize_entailments_one iprog prog proc [] in
  (* let res = !Synthesis.repair_res in *)
  ()

let repair_one_candidate (proc_name: string) (iprog: I.prog_decl)
    (r_iproc: I.proc_decl) args (candidate: I.exp) =
  if !Syn.repair_res != None then None
  else
    let rec aux_typ (e: I.exp) = match e with
      | I.CallRecv _
      | I.CallNRecv _ -> true
      | I.Return ret_e ->
        begin
          match ret_e.I.exp_return_val with
          | None -> false
          | Some return_e -> aux_typ return_e
        end
      | _ -> false in
    let candidate_type = aux_typ candidate in
    let iprog = mk_candidate_iprog iprog r_iproc args candidate 1 in
    let () = Syn.entailments := [] in
    let () = Syn.syn_is_call_stmt := candidate_type in
    let () = Syn.rel_num := 0 in
    let () = Syn.res_num := 0 in
    let () = Syn.repair_res := None in
    let () = if RP.is_return_exp candidate then
        Syn.is_return_cand := true
      else Syn.is_return_cand := false in
    let () = verified_procs := [] in
    let () = Syn.syn_pre := None in
    let cprog, _ = Astsimp.trans_prog iprog in
    let () = Syn.unk_hps := cprog.Cast.prog_hp_decls in
    try
      let () = repair_collect_constraint := true in
      let () = Typechecker.check_prog_wrapper iprog cprog in
      let () = repair_collect_constraint := false in
      let () = x_binfo_pp "start synthesis process" no_pos in
      let iprog = !Syn.syn_iprog |> Gen.unsome in
      let prog = !Syn.syn_cprog |> Gen.unsome in
      let proc = C.find_proc prog proc_name in
      let () = x_tinfo_hp (add_str "procs" RP.pr_cproc) proc no_pos in
      let () = Syn.repair_pos := Some (I.get_exp_pos candidate) in
      let proc_names = RP.get_all_func r_iproc in
      let () = x_binfo_hp (add_str "procs" (pr_list pr_id)) proc_names no_pos in
      let patch = Synthesizer.synthesize_entailments_one iprog prog
          proc proc_names in
      begin
        match patch with
        | None -> None
        | Some pt -> Some [(candidate, pt)]
      end
    with _ -> None

let compare_exp_return_vs_other e1 exp2 =
  match e1.I.exp_return_val with
  | None -> Syn.PriLow
  | Some r_e ->
    begin
      match r_e with
      | I.VarDecl _ -> Syn.PriLow
      | _ -> Syn.PriHigh
    end

let compare_exp (exp1: I.exp) (exp2: I.exp) =
  match exp1 with
  | I.Return e1 -> compare_exp_return_vs_other e1 exp2
  | _ ->
    let pos1 = I.get_exp_pos exp1 in
    let pos1 = pos1.start_pos in
    (* let (l1, c1) = (pos1.Lexing.pos_lnum, pos1.Lexing.pos_num) in *)
    let l1 = pos1.Lexing.pos_lnum in
    let pos2 = I.get_exp_pos exp2 in
    let pos2 = pos2.start_pos in
    let l2 = pos2.Lexing.pos_lnum in
    if l1 < l2 then Syn.PriLow
    else if l1 > l2 then Syn.PriHigh
    else Syn.PriEqual

let ranking_suspicious_exp (candidates: I.exp list) =
  let cmp_exp exp1 exp2 =
    let prio = compare_exp exp1 exp2 in
    match prio with
    | Syn.PriEqual -> 0
    | Syn.PriLow -> +1
    | Syn.PriHigh -> -1 in
  List.sort cmp_exp candidates

let repair_level_one (iprog: I.prog_decl) repair_proc (r_iproc: I.proc_decl) =
  let i_tree = RP.get_ast_traces (Gen.unsome r_iproc.proc_body) in
  let () = x_tinfo_hp (add_str "traces" RP.pr_bck) i_tree no_pos in
  let i_traces = RP.get_iast_traces i_tree in
  let check_post = !Syn.check_post_list in
  let () = x_binfo_hp (add_str "check_post" (pr_list string_of_bool)) check_post no_pos in
  let pr_traces = pr_list (pr_list (pr_list RP.pr_exp)) in
  let traces =
    if List.length check_post = List.length i_traces then
      let pairs = List.combine check_post i_traces in
      let traces = pairs |> List.filter (fun (x, _) -> x) |> List.map snd in
      traces |> List.filter (fun x -> x != [])
    else i_traces in
  let () = x_tinfo_hp (add_str "traces" pr_traces) traces no_pos in
  let stmts = traces |> List.concat |> List.concat in
  let eq_stmt s1 s2 = VarGen.eq_loc (I.get_exp_pos s1) (I.get_exp_pos s2) in
  let cands = stmts |> Gen.BList.remove_dups_eq eq_stmt in
  let not_var_decl (exp: I.exp) = match (exp:I.exp) with
    | I.VarDecl _ -> false
    | I.Return e_return ->
      begin
        match e_return.I.exp_return_val with
        | Some (I.CallNRecv call_fun) ->
          if eq_str call_fun.I.exp_call_nrecv_method "node_error" then false
          else true
        | _ -> true
      end
    | _ -> true in
  let () = x_binfo_hp (add_str "candidates: " RP.pr_exps) cands no_pos in
  let cands = cands |> List.filter not_var_decl in
  let () = x_binfo_hp (add_str "candidates: " RP.pr_exps) cands no_pos in
  let cands, others = List.partition (filter_cand !repair_loc) cands in
  let cands = ranking_suspicious_exp cands in
  let () = x_binfo_hp (add_str "candidates: " RP.pr_exps) cands no_pos in
  (* failwith "stop to debug" *)

  let locs = cands |> List.map I.get_exp_pos in
  let () = x_tinfo_hp (add_str "locs" (pr_list string_of_loc)) locs no_pos in
  let cproc = !Syn.repair_proc |> Gen.unsome in
  let specs = (cproc.Cast.proc_stk_of_static_specs # top) in
  let res_vars = Syn.get_pre_post specs |> List.map snd |> List.map CF.fv
                 |> List.concat |> List.filter CP.is_res_sv
                 |> CP.remove_dups_svl in
  (* let ref_vars = cproc.C.proc_by_name_params |> List.map CP.to_primed in *)
  let () = x_tinfo_hp (add_str "res_vars" RP.pr_vars) res_vars no_pos in
  (* let () = Syn.syn_ref_vars := ref_vars in *)
  let () = Syn.syn_res_vars := res_vars in
  let args = cproc.C.proc_args in
  let aux cand = repair_one_candidate repair_proc iprog r_iproc args cand in
  let rec aux_list cur_res list =
    if cur_res != None then cur_res
    else match list with
      | [] -> cur_res
      | head:: tail ->
        let res = aux head in
        if res != None then res
        else aux_list cur_res tail in
  let res = aux_list None cands in
  if res != None then
    let () = x_binfo_hp (add_str "failed branches" RP.pr_int) !Syn.fail_branch_num
        no_pos in
    res
  else
    aux_list None others

let map_stmt_with_level (bck_tree : RP.bck_tree) =
  let calculate_level traces =
    let rec aux_node traces = match traces with
    | RP.BckEmp -> 0
    | RP.BckNode node ->
      let l1 = aux_node node.bck_left in
      let l2 = aux_node node.bck_right in
      if l1 > l2 then l1 + 1 else l2 + 1 in
    aux_node traces in
  let rec aux traces bck_list = match traces with
    | RP.BckEmp -> bck_list
    | RP.BckNode node ->
      let level = calculate_level traces in
      let bck_list = (node.bck_statements, level)::bck_list in
      let bck_list = aux node.bck_left bck_list in
      aux node.bck_right bck_list in
  let aux_bck (bck_tree: RP.bck_tree) bck_list =
    let level_l = calculate_level bck_tree.RP.bck_left in
    let level_r = calculate_level bck_tree.RP.bck_right in
    let level = 1 + max level_l level_r in
    let bck_list = (bck_tree.RP.bck_statements, level)::bck_list in
    let bck_list = aux bck_tree.RP.bck_left bck_list in
    aux bck_tree.RP.bck_right bck_list in
  aux_bck bck_tree []

let get_candidate_pairs pairs level =
  let pairs = pairs |> List.filter (fun (_, x) -> x = 1) in
  let rec aux list num =
    if num <= 1 then
      List.map (fun x -> [x]) list
    else
      let l1 = aux list (num-1) in
      let aux_a x =
        let aux_b y =
          if List.mem x y then []
          else x::y in
        l1 |> List.map aux_b |> List.filter (fun x -> x != [])
        |> List.concat in
      list |> List.map aux_a |> List.filter (fun x -> x != []) in
  aux pairs level |> List.filter (fun x -> x != []) |> List.concat

let get_level_two_cand pairs =
  let pairs = pairs |> List.filter (fun (_, x) -> x = 1) in
  let blocks = pairs |> List.map fst in
  if List.length pairs < 2 then []
  else
    let firsts = blocks in
    let aux list block =
      let seconds = List.filter (fun x -> x!= block) blocks in
      let n_list = seconds |> List.map (fun y -> (block, y)) in
      let n_list = List.filter (fun (x,y) -> not(List.mem (y,x) list)) n_list in
      n_list @ list in
    List.fold_left aux [] firsts

let mk_pair_candidate_iprog iprog iproc (fst_cand, snd_cand) =
  let args = iproc.I.proc_args in
  let args = args |> List.map
               (fun x -> (x.I.param_type, x.I.param_name)) in
  let aux iprog iproc candidate num =
    let n_iproc, args = mk_candidate_proc iproc args candidate num in
    let () = x_tinfo_hp (add_str "proc" RP.pr_proc) n_iproc no_pos in
    let decl_vars = List.map (fun (x,y) -> CP.mk_typed_sv x y) args in
    let () = if num = 1 then
        Syn.block_var_decls := decl_vars
      else Syn.block_var_decls_snd := decl_vars in
    let names = args |> List.map snd in
    let arg_str = helper args in
    let arg_names = pr_idents_wo_brackets names "," in
    let typ = RP.type_of_exp candidate [] [] in
    let fc_str = fcode_str ^ (RP.pr_int num) in
    let fcode = hp_str ^ " P" ^ (RP.pr_int num) ^ "(" ^ arg_str ^ ").\n" ^
              hp_str ^ " Q" ^ (RP.pr_int num) ^ "(" ^ arg_str ^ ").\n" ^
              (string_of_typ typ) ^  " " ^ fc_str ^ "(" ^ arg_str ^ ")\n" ^
              "requires P" ^ (RP.pr_int num) ^ "(" ^ arg_names ^ ")\n" ^
              "ensures Q" ^ (RP.pr_int num) ^ "(" ^ arg_names ^ ");" in

    let () = x_tinfo_hp (add_str "fcode" pr_id) fcode no_pos in
    let n_prog = Parser.parse_hip_string "fcode" fcode in
    (* let procs = n_prog.I.prog_proc_decls in *)
    let hps = n_prog.I.prog_hp_decls in
    let () = x_tinfo_hp (add_str "hp" RP.pr_hps) hps no_pos in
    let helper_proc proc = if proc.I.proc_name = iproc.I.proc_name
      then n_iproc else proc in
    let n_procs = List.map helper_proc iprog.I.prog_proc_decls in
    let n_procs = n_prog.I.prog_proc_decls @ n_procs in
    let n_hps = n_prog.I.prog_hp_decls @ iprog.I.prog_hp_decls in
    let n_prog = {iprog with prog_hp_decls = n_hps;
                             prog_proc_decls = n_procs} in
    (n_prog, n_iproc) in
  let (n_prog, n_iproc) = aux iprog iproc fst_cand 1 in
  let (n_prog, n_iproc) = aux n_prog n_iproc snd_cand 2 in
  let () = x_binfo_hp (add_str "level2_proc" RP.pr_proc) n_iproc no_pos in
  n_prog

let repair_one_pair proc_name iprog r_iproc (fst_cand, snd_cand) =
  let tp_iprog = mk_pair_candidate_iprog
      iprog r_iproc (fst_cand, snd_cand) in
  let () = Syn.entailments := [] in
  let () = Syn.rel_num := 0 in
  let () = Syn.res_num := 0 in
  let () = Syn.repair_res := None in
  let () = if RP.is_return_exp fst_cand then
      Syn.is_return_fst := true
    else Syn.is_return_fst := false in
  let () = if RP.is_return_exp snd_cand then
      Syn.is_return_snd := true
    else Syn.is_return_snd := false in
  let () = verified_procs := [] in
  let () = Syn.syn_pre := None in
  let cprog, _ = Astsimp.trans_prog tp_iprog in
  let () = Syn.unk_hps := cprog.Cast.prog_hp_decls in
  try
    let () = repair_collect_constraint := true in
    let () = Typechecker.check_prog_wrapper iprog cprog in
    let () = repair_collect_constraint := false in
    let () = x_binfo_pp "start synthesis process" no_pos in
    let iprog = !Syn.syn_iprog |> Gen.unsome in
    let prog = !Syn.syn_cprog |> Gen.unsome in
    let proc = C.find_proc prog proc_name in
    let () = x_tinfo_hp (add_str "proc" RP.pr_cproc) proc no_pos in
    let () = Syn.repair_pos_fst := Some (I.get_exp_pos fst_cand) in
    let () = Syn.repair_pos_snd := Some (I.get_exp_pos snd_cand) in
    let proc_names = RP.get_all_func r_iproc in
    let res = Synthesizer.synthesize_entailments_two iprog prog
        proc proc_names in
    begin
      match res with
      | Some (fst_patch, snd_patch) ->
        let () = x_binfo_hp (add_str "fst patch" Iprinter.string_of_exp) fst_patch no_pos in
        let () = x_binfo_hp (add_str "snd patch" Iprinter.string_of_exp) snd_patch no_pos in
        let iprocs = tp_iprog.I.prog_proc_decls in
        let iproc = List.find (fun x -> contains r_iproc.I.proc_name x.I.proc_name) iprocs in
        let n_proc = Syn.replace_exp_proc fst_patch iproc 1 in
        let n_proc = Syn.replace_exp_proc snd_patch n_proc 2 in
        let n_iprocs = List.map (fun x -> if contains r_iproc.I.proc_name x.I.proc_name
                                  then n_proc else x) iprocs in
        let n_iprog = {tp_iprog with I.prog_proc_decls = n_iprocs} in
        begin
          try
            let cprog, _ = Astsimp.trans_prog n_iprog in
            let () = Typechecker.check_prog_wrapper n_iprog cprog in
            Some [(fst_cand, fst_patch); (snd_cand, snd_patch)]
          with _ -> None
        end
      | _ -> None
    end
  with _ -> None

let repair_level_two (iprog: I.prog_decl) repair_proc (r_iproc: I.proc_decl) =
  let body = r_iproc.I.proc_body |> Gen.unsome in
  let traces = RP.get_ast_traces body in
  let () = x_tinfo_hp (add_str "traces" RP.pr_bck) traces no_pos in
  let blocks = map_stmt_with_level traces in
  let candidates = get_level_two_cand blocks in
  let aux_pair (fst,snd) =
    fst |> List.map (fun x ->
        snd |> List.map (fun y -> (x,y))) |> List.concat in
  let pairs = List.map aux_pair candidates |> List.concat in
  let pr_pairs = pr_list (pr_pair RP.pr_exp RP.pr_exp) in
  let () = x_binfo_hp (add_str "candidates" pr_pairs) pairs no_pos in
  let cproc = !Syn.repair_proc |> Gen.unsome in
  let specs = (cproc.Cast.proc_stk_of_static_specs # top) in
  let res_vars = specs |> Syn.get_pre_post |> List.map snd
                 |> List.map CF.fv |> List.concat
                 |> List.filter CP.is_res_sv |> CP.remove_dups_svl in
  let () = Syn.syn_res_vars := res_vars in
  (* let () = RP.is_repair_pair := false in *)
  let rec aux_list cur_res list =
    if cur_res != None then cur_res
    else match list with
      | [] -> cur_res
      | head:: tail ->
        let res = repair_one_pair repair_proc iprog r_iproc head in
        (* restart *)
        let () = Syn.is_return_fst := false in
        let () = Syn.is_return_snd := false in
        if res != None then res
        else aux_list cur_res tail in
  aux_list None pairs
(* let r_list = pairs |> List.map (repair_one_pair repair_proc iprog r_iproc) in
 * let r_list = List.filter (fun x -> x != None) r_list in
 * let () = RP.is_repair_pair := false in
 * if r_list != [] then
 *   List.hd r_list
 * else
 *   None *)

let repair_iprog (iprog:I.prog_decl) repair_proc =
  let p_name = Cast.unmingle_name repair_proc in
  let () = x_binfo_hp (add_str "proc_name: " pr_id) p_name no_pos in
  let () = start_repair := true in
  let procs = iprog.I.prog_proc_decls in
  let r_iproc = List.find (fun x -> eq_str x.I.proc_name p_name) procs in
  let res = repair_level_one iprog repair_proc r_iproc in
  if res == None then
    let () = Syn.is_return_cand := false in
    repair_level_two iprog repair_proc r_iproc
  else res

(* let repair_straight_line (iprog:I.prog_decl) (n_prog:C.prog_decl)
 *     trace orig_proc proc block (specs:CF.formula * CF.formula) =
 *   let block_specs = RP.mk_specs specs in
 *   let helper t = match t with
 *     | Named _ | Int -> true
 *     | _ -> false in
 *   let () = x_binfo_hp (add_str "block" RP.pr_c_exps) block no_pos in
 *   let sub_blocks = RP.create_sub_blocks block in
 *   let aux sub_block =
 *     let () = x_binfo_hp (add_str "sub_block" RP.pr_c_exps) sub_block no_pos in
 *     (\* let block_exp = create_block_exp block in *\)
 *     let replace_pos = List.map C.pos_of_exp sub_block |> List.hd in
 *     (\* let body = proc.C.proc_body |> Gen.unsome in *\)
 *     (\* let orig_body = orig_proc.C.proc_body |> Gen.unsome in *\)
 *     (\* let var_decls = get_block_var_decls replace_pos orig_body in *\)
 *     let var_decls = RP.get_trace_var_decls replace_pos trace in
 *     let var_decls = var_decls @ (orig_proc.C.proc_args)
 *                     |> List.filter (fun (x, _) -> helper x) in
 *     let fcode_cprocs = RP.mk_fcode_cprocs iprog var_decls in
 *     let n_block_body = RP.create_tmpl_body_stmt block var_decls sub_block in
 *     let () = x_binfo_hp (add_str "block body" RP.pr_c_exp) n_block_body no_pos in
 *     let block_proc = RP.mk_block_proc proc n_block_body block_specs in
 *     let all_procs = C.list_of_procs n_prog in
 *     let all_procs = all_procs @ fcode_cprocs in
 *     let all_procs = block_proc::all_procs in
 *     let n_hashtbl = C.create_proc_decls_hashtbl all_procs in
 *     let n_prog = {n_prog with new_proc_decls = n_hashtbl} in
 *     let var_decls = List.map (fun (x,y) -> CP.mk_typed_sv x y) var_decls in
 *     let var_decls = var_decls |> List.filter Syn.is_node_or_int_var in
 *     let () = RP.reset_repair_straight_line var_decls replace_pos in
 *     let () = if RP.is_return_block sub_block then
 *         let res_vars = specs |> snd |> CF.fv |> List.filter CP.is_res_sv
 *                        |> CP.remove_dups_svl in
 *         let () = Syn.syn_res_vars := res_vars in
 *         Syn.is_return_cand := true
 *       else
 *         let () = Syn.syn_res_vars := [] in
 *         Syn.is_return_cand := false in
 *     begin
 *       try
 *         let _ = Typechecker.check_proc iprog n_prog block_proc None [] in
 *         let () = x_binfo_pp "START SYNTHESIS REPAIR-BLOCK SOLUTION" no_pos in
 *         Synthesizer.synthesize_block_statements iprog n_prog proc
 *           block_proc var_decls
 *       with _ -> None
 *     end in
 *   let repair_block_stmt cur_res statement =
 *     if cur_res != None then cur_res
 *     else aux statement in
 *   List.fold_left repair_block_stmt None sub_blocks *)

(* let repair_one_block (iprog: I.prog_decl) (prog : C.prog_decl) trace
 *     (proc : C.proc_decl) (block: C.exp list) =
 *   let orig_proc = proc in
 *   let () = x_binfo_hp (add_str "block" RP.pr_c_exps) block no_pos in
 *   let (n_iprog, n_prog, n_proc) = RP.create_tmpl_proc iprog prog proc trace block in
 *   let () = RP.reset_repair_block() in
 *   try
 *     let () = x_tinfo_hp (add_str "n_proc" RP.pr_cproc) n_proc no_pos in
 *     let _ = Typechecker.check_proc_wrapper n_iprog n_prog n_proc None [] in
 *     let specs = Synthesizer.infer_block_specs n_iprog n_prog n_proc in
 *     if specs = None then None
 *     else
 *       let specs_list = specs |> Gen.unsome in
 *       if specs_list = [] then None
 *       else
 *         let pr_specs = (pr_list (pr_pair RP.pr_formula RP.pr_formula)) in
 *         let () = x_binfo_hp (add_str "specs" pr_specs) specs_list no_pos in
 *         let specs = specs_list |> List.hd in
 *         repair_straight_line n_iprog n_prog trace orig_proc n_proc block specs
 *   (\* let helper cur_res specs =
 *    *   if cur_res = None then
 *    *     repair_straight_line n_iprog n_prog orig_proc n_proc block specs
 *    *   else cur_res in
 *    * List.fold_left helper None specs_list *\)
 *   with _ -> None *)

(* let repair_cproc iprog =
 *   match !Typechecker.repair_proc with
 *   | Some r_proc_name ->
 *     let () = x_binfo_pp "marking" no_pos in
 *     let () = start_repair := true in
 *     let cprog, _ = Astsimp.trans_prog iprog in
 *     let cproc = !Syn.repair_proc |> Gen.unsome in
 *     let blocks = RP.get_block_traces cproc in
 *     let () = x_tinfo_hp (add_str "blocks" RP.pr_bt) blocks no_pos in
 *     let check_post = !Syn.check_post_list in
 *     let traces = RP.get_statement_traces blocks in
 *     let pr_traces = pr_list (pr_list RP.pr_c_exps) in
 *     let traces =
 *       if List.length check_post = List.length traces then
 *         let pairs = List.combine traces check_post in
 *         let blocks = pairs |> List.filter (fun (_, x) -> x) |> List.map fst in
 *         let blocks = List.filter (fun x -> x != []) blocks in
 *         blocks
 *       else if !repair_loc != None then
 *         let repair_pos = !repair_loc |> Gen.unsome in
 *         let helper pos exp_list =
 *           let pos_list = exp_list |> List.map C.pos_of_exp in
 *           List.exists (RP.eq_loc_ln pos) pos_list in
 *         let helper2 trace = trace |> List.exists (helper repair_pos) in
 *         let traces = traces |> List.filter helper2 in
 *         traces
 *       else [] in
 *     let () = x_binfo_hp (add_str "traces" pr_traces) traces no_pos in
 *     let helper cur_res trace =
 *       if cur_res = None then
 *         let trace = List.rev trace in
 *         let aux cur_res block =
 *           if cur_res = None then
 *             repair_one_block iprog cprog trace cproc block
 *           else cur_res in
 *         List.fold_left aux None trace
 *       else cur_res in
 *     List.fold_left helper None traces
 *   | _ -> None *)

let buggy_level_one body var_decls data_decls =
  let n_body_list = [] in
  let rec aux1 body num list =
    let n_body, r_num, pos_list = RP.modify_num_infestor body num in
    if r_num = 0 then
      let level = RP.find_infest_level n_body pos_list in
      let n_list = (n_body, level)::list in
      aux1 body (num+1) n_list
    else list in
  let n_body_list = n_body_list @ (aux1 body 1 []) in
  let rec aux2 body num list =
    let n_body, r_num, pos_list = RP.remove_field_infestor body num var_decls
        data_decls in
    if r_num = 0 then
      let () = x_tinfo_hp (add_str "body" RP.pr_exp) body no_pos in
      let () = x_tinfo_hp (add_str "n_body" RP.pr_exp) n_body no_pos in
      let level = RP.find_infest_level n_body pos_list in
      let () = x_tinfo_hp (add_str "level" RP.pr_int) level no_pos in
      let n_list = (n_body, level)::list in
      aux2 body (num+1) n_list
    else list in
  let n_body_list =
    if List.length n_body_list >= 10 then n_body_list
    else n_body_list @ (aux2 body 1 []) in
  let rec aux3 body num list =
    let n_body, r_num, pos_list = RP.add_field_infestor body num var_decls
        data_decls in
    if r_num = 0 then
      let level = RP.find_infest_level n_body pos_list in
      let n_list = (n_body, level)::list in
      aux3 body (num+1) n_list
    else list in
  let n_body_list =
    if List.length n_body_list >= 10 then n_body_list
    else n_body_list @ (aux3 body 1 []) in
  let rec aux4 body num list =
    let n_body, r_num, pos_list = RP.modify_operator_infestor body num in
    if r_num = 0 then
      let level = RP.find_infest_level n_body pos_list in
      let n_list = (n_body, level)::list in
      aux4 body (num+1) n_list
    else list in
  let n_body_list =
    if List.length n_body_list >= 10 then n_body_list
    else n_body_list @ (aux4 body 1 []) in
  n_body_list

let buggy_level_two body var_decls data_decls =
  let rec aux (body: I.exp) = match body with
    | I.Block block ->
      let n_blocks = aux block.I.exp_block_body in
      let aux_a (x,y) =
        (I.Block {block with I.exp_block_body = x}, y) in
      let n_blocks = n_blocks |> List.map aux_a in
      n_blocks
    | I.Label (a, l) ->
      let n_labels = aux l in
      let aux_f (x,y) = (I.Label (a, x), y) in
      n_labels |> List.map aux_f
    | I.Cond cond ->
      let t_arm = cond.I.exp_cond_then_arm in
      let e_arm = cond.I.exp_cond_else_arm in
      let left = buggy_level_one t_arm var_decls data_decls
                 |> List.filter (fun (_, x) -> x == 1) in
      let right = buggy_level_one e_arm var_decls data_decls
          |> List.filter (fun (_, x) -> x == 1) in
      if left != [] && right != [] then
        let aux_lelf (lf, l1) =
          right |> List.map (fun (rt, l2) -> (lf, rt, l1 + l2)) in
        let triples = left |> List.map aux_lelf |> List.concat in
        let aux_triple (x,y,z) =
          let n_cond = I.Cond { cond with I.exp_cond_then_arm = x;
                                          I.exp_cond_else_arm = y} in
          (n_cond, z) in
        triples |> List.map aux_triple
      else []
    | _ -> [] in
  aux body

let get_num_cases num list =
  let rec aux list cur_list =
    match list with
    | [] -> cur_list
    | head::tail ->
      if List.length cur_list >= num then cur_list
      else aux tail (head::cur_list) in
  aux list []

let create_buggy_proc_wrapper (body : I.exp) var_decls data_decls =
  let n_body_w_level_one = buggy_level_one body var_decls data_decls in
  let n_body_w_level_one = List.map (fun (x,_) -> (x,1)) n_body_w_level_one in
  let n_body_w_level_two = buggy_level_two body var_decls data_decls in
  let n_body_w_level_two = List.map (fun (x,_) -> (x,2)) n_body_w_level_two in
  let () = x_binfo_hp (add_str "level_one: " RP.pr_int)
      (List.length n_body_w_level_one) no_pos in
  let () = x_binfo_hp (add_str "level_two: " RP.pr_int)
      (List.length n_body_w_level_two) no_pos in
  let all_cases = n_body_w_level_one @ n_body_w_level_two in
  all_cases

let create_buggy_proc (iprog: I.prog_decl) (proc : I.proc_decl) =
  let body = proc.I.proc_body |> Gen.unsome in
  let var_decls = proc.I.proc_args |> List.map
                    (fun x -> (x.I.param_type, x.I.param_name)) in
  let data_decls = iprog.I.prog_data_decls in
  let n_body_list = create_buggy_proc_wrapper body var_decls data_decls in
  n_body_list |> List.map (fun (x, y) -> ({proc with I.proc_body = Some x}, y))

let output_infestor_prog (src: string) (iprog : I.prog_decl) _level : string =
  let file_name = Filename.basename src in
  (* let dir = Filename.dirname src in *)
  let dir = Sys.getcwd() in
  let suffix = Filename.extension file_name in
  let f_name = Filename.chop_suffix file_name suffix in
  let b_file = f_name ^ "_buggy_" ^ (RP.pr_int !RP.infestor_num) ^ suffix in
  (* let b_file = f_name ^ "_buggy_" ^ (RP.pr_int level) ^ "_" ^ (RP.pr_int !infestor_num) ^ suffix in *)
  let to_saved_file = dir ^ Filename.dir_sep ^ b_file in
  let () = RP.infestor_num := !RP.infestor_num + 1 in
  let view_decls = iprog.I.prog_view_decls in
  let pre_views = ["WFSegN"; "WFSeg"; "WSSN"; "WSS"; "MEM"; "memLoc"; "size"] in
  let pre_datas = ["barrier"; "phase"; "thrd"; "__RET"; "__ArrBoundErr"; "lock";
                   "__DivByZeroErr"; "char_star"; "int_ptr_ptr"; "int_ptr"] in
  let negate x = not x in
  let filter_fun proc = match proc.I.proc_body with
    | None ->
      if eq_str proc.I.proc_name "node_error"
      then true else false
    | _ -> true in
  let view_decls = view_decls |> List.filter
                     (fun x -> List.mem x.I.view_name pre_views |> negate) in
  let data_decls = iprog.I.prog_data_decls |> List.filter
                     (fun x -> List.mem x.I.data_name pre_datas |> negate) in
  let procs = iprog.I.prog_proc_decls |> List.filter filter_fun in
  let n_prog = {iprog with I.prog_view_decls = view_decls;
                           I.prog_proc_decls = procs;
                           I.prog_data_decls = data_decls} in
  let output = RP.pr_iprog n_prog in
  let () = x_binfo_hp (add_str "STORING: " pr_id) to_saved_file no_pos in
  let oc = open_out to_saved_file in
  fprintf oc "%s\n" output; close_out oc;
  to_saved_file

let create_buggy_prog src (iprog : I.prog_decl)=
  let procs = iprog.I.prog_proc_decls in
  let b_procs = procs |> List.filter (fun x -> x.I.proc_body != None) in
  if b_procs = [] then report_error no_pos "NO PROC WITH THE UN-EMPTY BODY"
  else
    let b_proc =
      match !Globals.infest_fun with
      | Some fun_name ->
        begin
          try
            List.find (fun x -> eq_str x.I.proc_name fun_name) b_procs
          with _ -> failwith "wrong proc_name, choose another one"
        end
      | None -> b_procs |> List.rev |> List.hd in
    let buggy_procs = create_buggy_proc iprog b_proc in
    let aux_fun (b_proc, level) =
      let n_procs = procs |> List.map (fun x ->
          if eq_str x.I.proc_name b_proc.I.proc_name then b_proc
          else x) in
      ({iprog with I.prog_proc_decls = n_procs}, level) in
    let n_progs = List.map aux_fun buggy_procs in
    n_progs

let start_repair_wrapper (iprog: I.prog_decl) start_time =
  match (!Typechecker.repair_proc) with
  | Some repair_proc_name ->
    let start_time = get_time () in
    let res = repair_iprog iprog repair_proc_name in
    if res != None then
      let duration = get_time() -. start_time in
      let () = x_binfo_hp (add_str "TOTAL REPAIR TIME: " RP.pr_float)
          duration no_pos in
      let () = x_binfo_pp "REPAIRING SUCCESSFUL" no_pos in
      true
    else
      let mutated_res = repair_iprog_by_mutation iprog repair_proc_name in
      if mutated_res then
        let duration = get_time() -. start_time in
        let () = x_binfo_hp (add_str "TOTAL REPAIR TIME: " RP.pr_float) duration no_pos in
        let () = x_binfo_pp "REPAIRING SUCCESSFUL" no_pos in
        mutated_res
      else
        let () = x_binfo_pp "REPAIRING FAIL" no_pos in
        false
  | _ -> false

let infest_and_output src (iprog: I.prog_decl) =
  let filter_prog i_prog =
    try
      let cprog, _ = Astsimp.trans_prog i_prog in
      let _ = Typechecker.check_prog_wrapper i_prog cprog in
      false
    with _ -> true in
  let file_name = Filename.basename src in
  let suffix = Filename.extension file_name in
  let () = if eq_str suffix ".ss"
    then repairing_ss_file := true in
  let () = x_binfo_pp ("suffix: " ^ suffix) no_pos in
  let buggy_progs = create_buggy_prog src iprog in
  let () = x_tinfo_hp (add_str "input_prog: " Iprinter.string_of_program) iprog no_pos in
  (* buggy program with one location*)
  let level_one_progs = buggy_progs
                        |> List.filter (fun (_, y) -> y = 1)
                        |> List.map fst
                        |> List.filter filter_prog
                        |> get_num_cases 10 in
  let level_two_progs = buggy_progs
                        |> List.filter (fun (_, y) -> y = 2)
                        |> List.map fst
                        |> List.filter filter_prog
                        |> get_num_cases 10 in
  let _ = level_one_progs |> List.map (fun buggy_prog ->
      output_infestor_prog src buggy_prog 1) in
  let _ = level_two_progs |> List.map (fun buggy_prog ->
      output_infestor_prog src buggy_prog 2) in
  let injected_programs = List.length level_one_progs in
  let () = x_binfo_hp (add_str "TOTAL INJECTED PROGRAMS: " RP.pr_int)
      injected_programs no_pos in
  x_binfo_pp "END INJECTING FAULT TO CORRECT PROGRAM" no_pos


(* let infest_and_repair src (iprog : I.prog_decl) start_time =
 *   let buggy_progs = create_buggy_prog src iprog in
 *   let () = enable_repair := true in
 *   let () = RP.infestor_num := 0 in
 *   let repair_time = ref 0.0 in
 *   let aux_one (buggy_prog, level) =
 *     let () = Syn.repair_res := None in
 *     let cprog, _ = Astsimp.trans_prog buggy_prog in
 *     try
 *       let _ = Typechecker.check_prog_wrapper buggy_prog cprog in
 *       let () = Syn.check_post_list := [] in
 *       let () = Z3.stop () in
 *       let () = x_binfo_pp "INFESTED PROGRAM IS NOT BUGGY W.R.T THE SPECIFICATION" no_pos in
 *       (0, 0)
 *     with _ ->
 *       (\* let start_time = get_time () in *\)
 *       let r_iprog = start_repair_wrapper buggy_prog start_time in
 *       let () = Syn.check_post_list := [] in
 *       let duration = get_time () -. start_time in
 *       (\* to kill process *\)
 *       let () = Z3.stop () in
 *       let () = repair_time := (!repair_time) +. duration in
 *       let s_file = output_infestor_prog src buggy_prog level in
 *       if r_iprog then
 *         let () = x_binfo_pp ("REPAIRING " ^ s_file ^ " SUCCESSFULLY") no_pos in
 *         (1, 1)
 *       else
 *         let () = x_binfo_pp ("REPAIRING " ^ s_file ^ " FAIL") no_pos in
 *         (1, 0) in
 *   let reset_timing () =
 *     let () = Syn.inference_time := 0.0 in
 *     let () = Syn.synthesis_time := 0.0 in
 *     let () = repair_time := 0.0 in
 *     () in
 *   let aux level =
 *     let level1 = List.filter (fun (_, x) -> x = level) buggy_progs in
 *     let res_level1 = level1 |> List.map aux_one in
 *     let b_sum = res_level1 |> List.map fst |> RP.sum_list in
 *     let r_sum = res_level1 |> List.map snd |> RP.sum_list in
 *     let b_sum = float_of_int b_sum in
 *     let r_sum = float_of_int r_sum in
 *     let r_time = !repair_time /. b_sum in
 *     let inference_t = !Syn.inference_time/. b_sum in
 *     let r_time = r_time/. b_sum in
 *     let syn_t = !Syn.synthesis_time/. b_sum in
 *     let l1_stats = [b_sum; r_sum; inference_t; syn_t; r_time] in
 *     l1_stats in
 *   let l1_stats = aux 1 in
 *   let () = reset_timing () in
 *   let l2_stats = aux 2 in
 *   let () = x_binfo_hp (add_str "L1 STATS" (pr_list_mln RP.pr_float)) l1_stats no_pos in
 *   let () = x_binfo_hp (add_str "L2 STATS" (pr_list_mln RP.pr_float)) l2_stats no_pos in
 *   x_binfo_pp "ENDING INFESTING AND REPAIRING" no_pos *)
