#include "xdebug.cppo"
open VarGen
open Printf
open Gen.Basic
open Globals
open Repairpure

module C = Cast
module CP = Cpure
module CF = Cformula
module Syn = Synthesis
module I = Iast
module LO2 = Label_only.Lab2_List

let filter_cand buggy_loc cand =
  match buggy_loc with
  | Some b_loc ->
    let cand_pos = Iast.get_exp_pos cand in
    let () = x_tinfo_hp (add_str "buggy pos" (Cprinter.string_of_pos)) b_loc
        no_pos in
    let () = x_tinfo_hp (add_str "cand pos" (Cprinter.string_of_pos)) cand_pos
        no_pos in
    let b_lnum = b_loc.start_pos.Lexing.pos_lnum in
    let cand_lnum = cand_pos.start_pos.Lexing.pos_lnum in
    b_lnum = cand_lnum
  | None ->
    let cand_pos = Iast.get_exp_pos cand in
    let b_loc = VarGen.proving_loc#get in
    let b_lnum = b_loc.start_pos.Lexing.pos_lnum in
    let cand_lnum = cand_pos.start_pos.Lexing.pos_lnum in
    b_lnum >= cand_lnum

let mk_candidate_proc (iproc:I.proc_decl) args candidate =
  match iproc.I.proc_body with
    | None -> (iproc, args)
    | Some exp ->
      let loc = I.get_exp_pos candidate in
      let helper sv = let CP.SpecVar (a, b, _) = sv in
        (a,b) in
      let decl_vars = Synthesis.get_var_decls loc exp
                      |> List.map helper in
      let args = args @ decl_vars in
      let fcode = create_fcode_exp args in
      let n_body = Some (replace_exp exp fcode candidate) in
      ({iproc with proc_body = n_body}, args)

let mk_candidate_iprog iprog (iproc:I.proc_decl) args candidate =
  let n_iproc, args = mk_candidate_proc iproc args candidate in
  let () = x_binfo_hp (add_str "proc" pr_proc) n_iproc no_pos in
  let () = Syn.repair_pos := Some (I.get_exp_pos candidate) in
  let rec helper args = match args with
    | [] -> ""
    | [(typ, name)] -> (string_of_typ typ) ^ " " ^ name
    | h::t -> let tail = helper t in
      let head = string_of_typ (fst h) ^ " " ^ (snd h) in
      head ^ "," ^ tail in
  let names = args |> List.map snd in
  let arg_str = helper args in
  let arg_names = pr_idents_wo_brackets names "," in
  let typ = type_of_exp candidate in
  let fcode = hp_str ^ " P(" ^ arg_str ^ ").\n" ^
              hp_str ^ " Q(" ^ arg_str ^ ").\n" ^
              (string_of_typ typ) ^  " " ^ fcode_str ^ "(" ^ arg_str ^ ")\n" ^
              "requires P(" ^ arg_names ^ ")\n" ^
              "ensures Q(" ^ arg_names ^ ");" in
  let () = x_tinfo_hp (add_str "fcode" pr_id) fcode no_pos in
  let n_prog = Parser.parse_hip_string "fcode" fcode in
  let procs = n_prog.I.prog_proc_decls in
  let hps = n_prog.I.prog_hp_decls in
  let () = x_tinfo_hp (add_str "hp" pr_hps) hps no_pos in
  let helper_proc proc = if proc.I.proc_name = iproc.I.proc_name
                           then n_iproc else proc in
  let n_procs = List.map helper_proc iprog.I.prog_proc_decls in
  let n_procs = n_prog.I.prog_proc_decls @ n_procs in
  let n_hps = n_prog.I.prog_hp_decls @ iprog.I.prog_hp_decls in
  {iprog with prog_hp_decls = n_hps;
              prog_proc_decls = n_procs}

let repair_heap_template () =
  let () = x_binfo_pp "start synthesis process in template" no_pos in
  let iprog = !Syn.syn_iprog |> Gen.unsome in
  let prog = !Syn.syn_cprog |> Gen.unsome in
  let proc_name = !Syn.tmpl_proc_name |> Gen.unsome in
  let proc = C.find_proc prog proc_name in
  let _ = Synthesizer.synthesize_entailments iprog prog proc in
  let res = !Synthesis.repair_res in
  ()

let repair_one_candidate (proc_name: string) (iprog: I.prog_decl)
    (r_iproc: I.proc_decl) args candidate =
  if !Syn.repair_res != None then None
  else
    let iprog = mk_candidate_iprog iprog r_iproc args candidate in
    let () = x_tinfo_pp "marking" no_pos in
    let () = Syn.entailments := [] in
    let () = Syn.rel_num := 0 in
    let () = Syn.res_num := 0 in
    let () = Syn.repair_res := None in
    let () = if is_return_exp candidate then
        Syn.is_return_cand := true
      else Syn.is_return_cand := false in
    let () = verified_procs := [] in
    let () = Syn.syn_pre := None in
    let cprog, _ = Astsimp.trans_prog iprog in
    let () = Syn.unk_hps := cprog.Cast.prog_hp_decls in
    try
      let () = Typechecker.check_prog_wrapper iprog cprog in
      let () = x_binfo_pp "start synthesis process" no_pos in
      let iprog = !Syn.syn_iprog |> Gen.unsome in
      let prog = !Syn.syn_cprog |> Gen.unsome in
      let proc = C.find_proc prog proc_name in
      let () = Syn.repair_pos := Some (I.get_exp_pos candidate) in
      let _ = Synthesizer.synthesize_entailments iprog prog proc in
      !Synthesis.repair_res
    with _ -> None

let repair_iprog (iprog:I.prog_decl) : bool =
  let start_time = get_time () in
  match (!Typechecker.repair_proc) with
  | (Some repair_proc) ->
    let p_name = Cast.unmingle_name repair_proc in
    let () = x_tinfo_hp (add_str "proc_name: " pr_id) p_name no_pos in
    let () = start_repair := true in
    let procs = iprog.I.prog_proc_decls in
    let r_iproc = List.find (fun x -> eq_str x.I.proc_name p_name) procs in
    let cands = get_stmt_candidates (Gen.unsome r_iproc.proc_body) in
    let () = x_tinfo_hp (add_str "candidates: " pr_exps) cands no_pos in
    let cands = List.filter (filter_cand !repair_loc) cands (* |> List.rev *) in
    let () = x_binfo_hp (add_str "candidates: " pr_exps) cands no_pos in
    let locs = cands |> List.map I.get_exp_pos in
    let () = x_tinfo_hp (add_str "locs" (pr_list string_of_loc)) locs no_pos in
    let cproc = !Syn.repair_proc |> Gen.unsome in
    let specs = (cproc.Cast.proc_stk_of_static_specs # top) in
    let post_proc = specs |> Syn.get_post_cond |> Syn.rm_emp_formula in
    let res_vars = CF.fv post_proc |> List.filter CP.is_res_sv
                   |> CP.remove_dups_svl in
    let () = Syn.syn_res_vars := res_vars in
    let args = cproc.C.proc_args in
    let aux cand = repair_one_candidate repair_proc iprog r_iproc args cand in
    let res = cands |> List.map aux |> List.filter (fun x -> x != None) in
    if res = [] then
      let () = x_binfo_pp "REPAIRING FAILED\n" no_pos in
      false
    else
      let r_time = get_time() -. start_time in
      let () = x_binfo_pp "REPAIRING SUCCESSFUL\n" no_pos in
      let () = x_binfo_hp (add_str "repair time" string_of_float)
          r_time no_pos in
      let () = x_binfo_hp (add_str "failed branches" string_of_int)
          !Syn.fail_branch_num no_pos in
      let () = x_binfo_hp (add_str "check_entail" string_of_int)
          !Syn.check_entail_num no_pos in
      let _ = List.hd res in
      true
  | _ -> false

let repair_straight_line (iprog:I.prog_decl) (n_prog:C.prog_decl)
    trace orig_proc proc block (specs:CF.formula * CF.formula) =
  let block_specs = mk_specs specs in
  let helper t = match t with
    | Named _ | Int -> true
    | _ -> false in
  let () = x_binfo_hp (add_str "block" pr_c_exps) block no_pos in
  let sub_blocks = create_sub_blocks block in
  let aux sub_block =
    let () = x_binfo_hp (add_str "sub_block" pr_c_exps) sub_block no_pos in
    let block_exp = create_block_exp block in
    let replace_pos = List.map C.pos_of_exp sub_block |> List.hd in
    let body = proc.C.proc_body |> Gen.unsome in
    let orig_body = orig_proc.C.proc_body |> Gen.unsome in
    (* let var_decls = get_block_var_decls replace_pos orig_body in *)
    let var_decls = get_trace_var_decls replace_pos trace in
    let var_decls = var_decls @ (orig_proc.C.proc_args)
                    |> List.filter (fun (x, _) -> helper x) in
    let fcode_cprocs = mk_fcode_cprocs iprog var_decls in
    let n_block_body = create_tmpl_body_stmt block var_decls sub_block in
    let () = x_binfo_hp (add_str "block body" pr_c_exp) n_block_body no_pos in
    (* report_error no_pos "to debug" in *)
    let block_proc = mk_block_proc proc n_block_body block_specs in
    let all_procs = C.list_of_procs n_prog in
    let all_procs = all_procs @ fcode_cprocs in
    let all_procs = block_proc::all_procs in
    let n_hashtbl = C.create_proc_decls_hashtbl all_procs in
    let n_prog = {n_prog with new_proc_decls = n_hashtbl} in
    let var_decls = List.map (fun (x,y) -> CP.mk_typed_sv x y) var_decls in
    let var_decls = var_decls |> List.filter Syn.is_node_or_int_var in
    let () = reset_repair_straight_line var_decls replace_pos in
    let () = if is_return_block sub_block then
        let res_vars = specs |> snd |> CF.fv |> List.filter CP.is_res_sv
                       |> CP.remove_dups_svl in
        let () = Syn.syn_res_vars := res_vars in
        Syn.is_return_cand := true
      else
        let () = Syn.syn_res_vars := [] in
        Syn.is_return_cand := false in
    begin
      try
        let _ = Typechecker.check_proc iprog n_prog block_proc None [] in
        let () = x_binfo_pp "START SYNTHESIS REPAIR-BLOCK SOLUTION" no_pos in
        Synthesizer.synthesize_block_statements iprog n_prog proc
          block_proc var_decls
      with _ -> None
    end in
  let repair_block_stmt cur_res statement =
    if cur_res != None then cur_res
    else aux statement in
  List.fold_left repair_block_stmt None sub_blocks

let repair_one_block (iprog: I.prog_decl) (prog : C.prog_decl) trace
    (proc : C.proc_decl) (block: C.exp list) =
  let orig_proc = proc in
  let () = x_binfo_hp (add_str "block" pr_c_exps) block no_pos in
  (* report_error no_pos "to debug" *)
  let (n_iprog, n_prog, n_proc) = create_tmpl_proc iprog prog proc trace block in
  let () = reset_repair_block() in
  try
    let () = x_tinfo_hp (add_str "n_proc" pr_cproc) n_proc no_pos in
    let _ = Typechecker.check_proc_wrapper n_iprog n_prog n_proc None [] in
    let specs = Synthesizer.infer_block_specs n_iprog n_prog n_proc in
    if specs = None then None
    else
      let specs_list = specs |> Gen.unsome in
      if specs_list = [] then None
      else
        let pr_specs = (pr_list (pr_pair pr_formula pr_formula)) in
        let () = x_binfo_hp (add_str "specs" pr_specs) specs_list no_pos in
        let specs = specs_list |> List.hd in
        repair_straight_line n_iprog n_prog trace orig_proc n_proc block specs
      (* let helper cur_res specs =
       *   if cur_res = None then
       *     repair_straight_line n_iprog n_prog orig_proc n_proc block specs
       *   else cur_res in
       * List.fold_left helper None specs_list *)
  with _ -> None

let repair_cproc iprog =
  match !Typechecker.repair_proc with
  | Some r_proc_name ->
    let () = x_binfo_pp "marking" no_pos in
    let () = start_repair := true in
    let cprog, _ = Astsimp.trans_prog iprog in
    let cproc = !Syn.repair_proc |> Gen.unsome in
    let blocks = get_block_traces cproc in
    let () = x_tinfo_hp (add_str "blocks" pr_bt) blocks no_pos in
    (* failwith "to debug" *)
    let check_post = !Syn.check_post_list in
    let traces = get_statement_traces blocks in
    let pr_traces = pr_list (pr_list pr_c_exps) in
    let traces =
      if List.length check_post = List.length traces then
        let pairs = List.combine traces check_post in
        let blocks = pairs |> List.filter (fun (_, x) -> x) |> List.map fst in
        let blocks = List.filter (fun x -> x != []) blocks in
        blocks
      else if !repair_loc != None then
        let repair_pos = !repair_loc |> Gen.unsome in
        let helper pos exp_list =
          let pos_list = exp_list |> List.map C.pos_of_exp in
          let eq_loc_ln p1 p2 = p1.start_pos.Lexing.pos_lnum
                                = p2.start_pos.Lexing.pos_lnum in
          List.exists (eq_loc_ln pos) pos_list in
        let helper2 trace = trace |> List.exists (helper repair_pos) in
        let traces = traces |> List.filter helper2 in
                     (* |> List.filter (fun x -> x != []) in *)
        traces
      else [] in
    let () = x_binfo_hp (add_str "traces" pr_traces) traces no_pos in
    let helper cur_res trace =
      if cur_res = None then
        let trace = List.rev trace in
        let aux cur_res block =
          if cur_res = None then
            repair_one_block iprog cprog trace cproc block
          else cur_res in
        List.fold_left aux None trace
      else cur_res in
    List.fold_left helper None traces
  | _ -> None

let create_buggy_proc_wrapper (body : I.exp) =
  let list = [] in
  let () = x_binfo_hp (add_str "body" pr_exp) body no_pos in
  let list = (buggy_num_dif_pos body 1)::list in
  let list = (buggy_num_dif_pos body 2)::list in
  let list = (buggy_mem_dif_pos body 1)::list in
  let list = (buggy_mem_dif_pos body 2)::list in
  let list = (buggy_mem_dif_pos body 3)::list in
  (* let list = (buggy_boolean_exp body 1)::list in *)
  (* let list = (delete_one_branch body 1)::list in *)
  list |> List.filter (fun (_, y) -> y = 0) |> List.map fst |> List.rev

let create_buggy_proc (proc : I.proc_decl) =
  let body = proc.I.proc_body |> Gen.unsome in
  let n_body_list = create_buggy_proc_wrapper body in
  let () = x_tinfo_hp (add_str "proc" (pr_list_nl pr_exp)) n_body_list no_pos in
  n_body_list |> List.map (fun x -> {proc with I.proc_body = Some x})

let output_infestor_prog (src: string) (iprog : I.prog_decl) =
  let file_name, dir = Filename.basename src, Filename.dirname src in
  let suffix = Filename.extension file_name in
  let f_name = Filename.chop_suffix file_name suffix in
  (* let r_file = "buggy_" ^ (string_of_int !infestor_num)^ "_" ^ file_name in *)
  let b_file = f_name ^ "_buggy_" ^ (string_of_int !infestor_num) ^ suffix in
  let to_saved_file = dir ^ Filename.dir_sep ^ b_file in
  let () = infestor_num := !infestor_num + 1 in

  let view_decls = iprog.I.prog_view_decls in
  let pre_views = ["WFSegN"; "WFSeg"; "WSSN"; "WSS"; "MEM"; "memLoc"; "size"] in
  let pre_datas = ["barrier"; "phase"; "thrd"; "__RET"; "__ArrBoundErr"; "lock";
                  "__DivByZeroErr"; "char_star"; "int_ptr_ptr"; "int_ptr"] in
  let negate x = not x in
  let view_decls = view_decls |> List.filter
                     (fun x -> List.mem x.I.view_name pre_views |> negate) in
  let data_decls = iprog.I.prog_data_decls |> List.filter
                     (fun x -> List.mem x.I.data_name pre_datas |> negate) in
  let n_prog = {iprog with I.prog_view_decls = view_decls;
                           I.prog_data_decls = data_decls} in
  let output = pr_iprog n_prog in
  let oc = open_out to_saved_file in
  fprintf oc "%s\n" output; close_out oc;
  let () = x_binfo_hp (add_str "prog" pr_iprog) n_prog no_pos in
  ()

let create_buggy_progs src (iprog : I.prog_decl) =
  let procs = iprog.I.prog_proc_decls in
  let procs = procs |> List.filter (fun x -> x.I.proc_body != None) in
  let helper_buggy buggy_proc =
    List.map (fun x -> if eq_str x.I.proc_name buggy_proc.I.proc_name
               then buggy_proc else x) procs in
  let n_procs_list = List.fold_left (fun res_list cur_proc ->
      let buggy_procs = create_buggy_proc cur_proc in
      let n_procs = buggy_procs |> List.map helper_buggy in
      n_procs @ res_list) [] procs in
  let helper n_procs =
    let n_prog = {iprog with I.prog_proc_decls = n_procs} in
    n_prog in
  let () = infestor_num := 0 in
  let filter iprog =
    let cprog, _ = Astsimp.trans_prog iprog in
    try
      let () = Typechecker.check_prog_wrapper iprog cprog in
      false
    with _ -> true in
  let _ = n_procs_list |> List.map helper
          |> List.map (output_infestor_prog src) in
  ()

let rec start_repair_wrapper (iprog: I.prog_decl) =
  (* let tmp = repair_iprog iprog in *)
  let start_time = get_time () in
  let tmp = repair_cproc iprog in
  if tmp != None then
    let r_time = get_time() -. start_time in
    let () = x_binfo_pp "REPAIRING SUCCESSFUL\n" no_pos in
    let () = x_binfo_hp (add_str "repair time" string_of_float)
        r_time no_pos in
    true
  else
    let () = x_binfo_pp "REPAIRING FAILED\n" no_pos in
    false
