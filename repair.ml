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

let pr_proc = Iprinter.string_of_proc_decl
let pr_ctx = Cprinter.string_of_list_failesc_context
let pr_formula = Cprinter.string_of_formula
let pr_struc_f = Cprinter.string_of_struc_formula

let filter_cand buggy_loc cand =
  match buggy_loc with
  | Some b_loc ->
    let cand_pos = Iast.get_exp_pos cand in
    let () = x_tinfo_hp (add_str "buggy pos" (Cprinter.string_of_pos)) b_loc no_pos in
    let () = x_tinfo_hp (add_str "cand pos" (Cprinter.string_of_pos)) cand_pos no_pos in
    let b_lnum = b_loc.start_pos.Lexing.pos_lnum in
    let cand_lnum = cand_pos.start_pos.Lexing.pos_lnum in
    b_lnum = cand_lnum
  | None -> true

let find_pre_cond ctx prog = match ctx with
  | Some r_ctx ->
    let () = x_tinfo_hp (add_str "ctx" pr_ctx) r_ctx no_pos in
    let ctx_f = CF.formula_of_list_failesc_context r_ctx in
    let pf = CF.get_pure ctx_f in
    let eq_vars = CP.pure_ptr_equations_aux false pf in
    let eq_vars_w_null = CP.pure_ptr_equations_aux true pf in
    let eq_null = List.filter (fun x -> not(List.mem x eq_vars)) eq_vars_w_null in
    let unfold_vars = List.map fst eq_null in
    let n_ctx = List.fold_left (fun ctx var ->
        Solver.unfold_failesc_context (prog, None) ctx var true no_pos
      ) r_ctx unfold_vars in
    let () = x_binfo_hp (add_str "n_ctx" pr_ctx) n_ctx no_pos in
    let n_ctx_f = CF.formula_of_list_failesc_context n_ctx in
    Some n_ctx_f
  | None -> None

let mk_candidate_iproc iproc candidate =
  iproc

let start_repair (iprog:I.prog_decl) =
  let pr_exps = pr_list Iprinter.string_of_exp in
  match (!Typechecker.proc_to_repair) with
  | (Some repair_proc) ->
    let repair_proc = Cast.unmingle_name repair_proc in
    let () = x_binfo_hp (add_str "proc_name: " pr_id) repair_proc no_pos in
    let () = Globals.start_repair := true in
    let r_iproc = List.find (fun x -> eq_str x.I.proc_name repair_proc) iprog.prog_proc_decls in
    let () = x_tinfo_hp (add_str "proc: " pr_proc) r_iproc no_pos in
    let cands = I.get_stmt_candidates (Gen.unsome r_iproc.proc_body) in
    let cands = List.filter (filter_cand !Typechecker.repair_loc) cands in
    let () = x_binfo_hp (add_str "candidates: " pr_exps) cands no_pos in
    let n_iprocs = cands |> List.map (fun x -> mk_candidate_iproc r_iproc x) in
    (* let cprog = !Typechecker.repair_prog |> Gen.unsome in
     * let pre_cond = find_pre_cond !Typechecker.repair_pre_ctx cprog in
     * let cproc = !Syn.repair_proc |> Gen.unsome in
     * let specs = (cproc.Cast.proc_stk_of_static_specs # top) in
     * let post_cond = specs |> Syn.get_post_cond |> Syn.rm_emp_formula in
     * let () = x_binfo_hp (add_str "post_cond " pr_formula) post_cond no_pos in
     * let args = cproc.Cast.proc_args |>
     *            List.map (fun (x,y) -> CP.mk_typed_sv x y) in
     * let vars = args in
     * if pre_cond = None then None
     * else
     *   let pre = pre_cond |> Gen.unsome in
     *   let goal = Syn.mk_goal_w_procs cprog [cproc] pre post_cond vars in
     *   let c_exp = Synthesizer.synthesize_program goal in
     *   let a_exp = match c_exp with
     *     | None -> None
     *     | Some exp ->
     *       let i_exp = Syn.c2iast_exp exp in
     *       let () = x_tinfo_hp (add_str "iast_exp" Iprinter.string_of_exp) i_exp no_pos in
     *       Some i_exp in
     *   let n_iproc = mk_candidate_iproc repairing_iproc a_exp cands in *)
    None
  | _ ->
    let () = next_proc := false in
    None

let rec start_repair_wrapper iprog =
  let tmp = start_repair iprog in
  tmp
  (* let () = x_tinfo_hp (add_str "next_proc: " string_of_bool) (!next_proc) no_pos in
   * if (!next_proc) then
   *   let () = stop := false in
   *   let () = Globals.start_repair := false in
   *   start_repair_wrapper iprog
   * else tmp *)
