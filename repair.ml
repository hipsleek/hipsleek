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

let pr_proc = Iprinter.string_of_proc_decl_repair
let pr_cproc = Cprinter.string_of_proc_decl 1
let pr_iprog = Iprinter.string_of_program
let pr_ctx = Cprinter.string_of_list_failesc_context
let pr_formula = Cprinter.string_of_formula
let pr_struc_f = Cprinter.string_of_struc_formula
let pr_hps = pr_list Iprinter.string_of_hp_decl
let pr_exps = pr_list Iprinter.string_of_exp
let pr_c_exps = pr_list Cprinter.string_of_exp

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

let repair_iprog (iprog:I.prog_decl) =
  let start_time = get_time () in
  match (!Typechecker.repair_proc) with
  | (Some repair_proc) ->
    let p_name = Cast.unmingle_name repair_proc in
    let () = x_tinfo_hp (add_str "proc_name: " pr_id) p_name no_pos in
    let () = Globals.start_repair := true in
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
      let () = x_binfo_pp "REPAIRING FAILED\n" no_pos in None
    else
      let r_time = get_time() -. start_time in
      let () = x_binfo_pp "REPAIRING SUCCESSFUL\n" no_pos in
      let () = x_binfo_hp (add_str "repair time" string_of_float)
          r_time no_pos in
      let () = x_binfo_hp (add_str "failed branches" string_of_int)
          !Syn.fail_branch_num no_pos in
      let () = x_binfo_hp (add_str "check_entail" string_of_int)
          !Syn.check_entail_num no_pos in
      List.hd res
  | _ -> None

let create_tmpl_body (body : C.exp) replace_pos pos_list var_decls =
  let pr_pos = string_of_loc in
  let fcode = create_cast_fcode var_decls replace_pos in
  let () = x_binfo_hp (add_str "fcode" Cprinter.string_of_exp) fcode no_pos in
  let rec aux exp = match exp with
    | C.Block e ->
      let n_e = aux e.C.exp_block_body in
      C.Block {e with exp_block_body = n_e}
    | C.Seq e ->
      let e1 = e.C.exp_seq_exp1 in
      let e1_pos = e1 |> C.pos_of_exp in
      if List.mem e1_pos pos_list then aux e.C.exp_seq_exp2
      else
        let e2 = e.C.exp_seq_exp2 in
        let e2_pos = e2 |> C.pos_of_exp in
        if List.mem e2_pos pos_list then aux e1
        else C.Seq {e with exp_seq_exp1 = aux e1;
                           exp_seq_exp2 = aux e2}
    | C.Assign e ->
      let loc = e.C.exp_assign_pos in
      if VarGen.eq_loc e.C.exp_assign_pos replace_pos then fcode
      else exp
    | Label e ->
      let n_e = aux e.C.exp_label_exp in
      Label {e with exp_label_exp = n_e}
    | C.Cond e ->
      let e1 = aux e.C.exp_cond_then_arm in
      let e2 = aux e.C.exp_cond_else_arm in
      C.Cond {e with exp_cond_then_arm = e1;
                     exp_cond_else_arm = e2}
    | _ -> exp in
  aux body

let create_block_template (proc : C.proc_decl) (blocks: C.exp list) =
  let is_var_decl (exp: C.exp) = match exp with
    | C.VarDecl _ -> true
    | _ -> false in
  let blocks = List.filter (fun x -> not(is_var_decl x)) blocks in
  if blocks = [] then None
  else
    let () = x_binfo_hp (add_str "blocks" pr_c_exps) blocks no_pos in
    let pos_list = blocks |> List.map C.pos_of_exp in
    let replace_pos = List.hd pos_list in
    let pos_list = List.tl pos_list in
    let n_body = match proc.C.proc_body with
      | None -> None
      | Some exp ->
        let proc_args = proc.C.proc_args in
        let var_decls = get_var_decls replace_pos exp in
        let var_decls = proc_args @ var_decls in
        Some (create_tmpl_body exp replace_pos pos_list var_decls) in
    let n_proc = {proc with C.proc_body = n_body} in
    let () = x_binfo_hp (add_str "n_proc" pr_cproc) n_proc no_pos in
    Some n_proc

let repair_cproc iprog =
  match !Typechecker.repair_proc with
  | Some r_proc_name ->
    let cproc = !Syn.repair_proc |> Gen.unsome in
    let blocks = create_blocks cproc in
    let () = x_tinfo_hp (add_str "blocks" pr_bt) blocks no_pos in
    let check_post = !Syn.check_post_list in
    let leaf_nodes = get_leaf_nodes blocks in
    let pr_leaves = pr_list pr_c_exps in
    let () = x_tinfo_hp (add_str "leaves" pr_leaves) leaf_nodes no_pos in
    let pr_cp = pr_list string_of_bool in
    let () = x_tinfo_hp (add_str "check_post" pr_cp) check_post no_pos in
    let pairs = List.combine leaf_nodes check_post in
    let blocks = pairs |> List.filter (fun (_, x) -> x) |> List.map fst in
    let () = x_binfo_hp (add_str "blocks" pr_leaves) blocks no_pos in
    (* to generate all traces leading to the error *)
    (* BUT, first try all leave blocks first *)
    let _ = blocks |> List.map (create_block_template cproc) in
    None
  | _ -> None

let rec start_repair_wrapper iprog =
  (* let tmp = repair_iprog iprog in *)
  let tmp = repair_cproc iprog in
  tmp
