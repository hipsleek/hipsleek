#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Exc.GTable

module C = Cast
module I = Iast
module CF = Cformula
module CP = Cpure
module Syn = Synthesis

type search_goal = {
  search_prog : I.prog_decl;
  search_cprog : C.prog_decl;
  search_proc : C.proc_decl;
  search_triples : (CF.formula * CF.formula * CF.formula) list;
  search_known_hps : C.hp_decl list;
}

let mk_search_goal iprog cprog cproc triples =
  {
    search_prog = iprog;
    search_cprog = cprog;
    search_proc = cproc;
    search_triples = triples;
    search_known_hps = [];
  }

type s_derivation = {
  s_drv_kind : s_derivation_kind;
  s_drv_goal : search_goal;
}

and s_derivation_kind =
    | SDrvStatus of bool
    | SDrvSubGoal of search_goal list

let mk_search_fail s_goal =
  {
    s_drv_kind = SDrvStatus false;
    s_drv_goal = s_goal;
  }

let mk_list_failesc_context (formula:CF.formula) =
  let ctx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ctx formula no_pos in
  let ctx = CF.add_path_id ctx (None, 0) 0 in
  let tmp = {
    CF.formula_flow_interval = !norm_flow_int;
    CF.formula_flow_link = None } in
  let ctx = CF.set_flow_in_context_override tmp ctx in
  let init_esc = [((0, ""), [])] in
  let fctx = [CF.mk_failesc_context ctx [] init_esc] in
  fctx

let find_post_pred s_goal candidate pre =
  let init_ctx = mk_list_failesc_context pre in
  let label = (-2, "f_post") in
  let prog = s_goal.search_cprog in
  let proc = s_goal.search_proc in
  let n_ctx = Typechecker.check_exp prog proc init_ctx candidate label in
  CF.formula_of_list_failesc_context n_ctx

let process_one_triple s_goal candidate triple =
  let (pre, post, residue) = triple in
  let hps = !Syn.unk_hps in
  let hp_names = List.map (fun x -> x.C.hp_name) hps in
  if Syn.check_hp_formula hp_names pre && Syn.check_hp_formula hp_names post
  then false
  else if Syn.check_hp_formula hp_names post then
    let post_state = find_post_pred s_goal candidate pre in
    x_binfo_hp (add_str "post_state" Syn.pr_formula) post_state no_pos;
    false
  else false

let process_one_cand s_goal candidate =
  let triples = s_goal.search_triples in
  match triples with
  | triple::others ->
    let _ = process_one_triple s_goal candidate triple in
    false
  | [] -> true

let solve_unknown_hp s_goal candidates =
  let rec process candidates =
    match candidates with
    | candidate::others ->
      let s_drv = process_one_cand s_goal candidate in
      if s_drv then
        true
      else
        process others
    | _ -> false in
  process candidates
