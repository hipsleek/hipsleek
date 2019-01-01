open Globals
open VarGen
open Gen
open Mcpure
open Cformula

open Synthesis

module CA = Cast


(*********************************************************************
 * Data structures and exceptions
 *********************************************************************)

exception EStree of synthesis_tree

let raise_stree st = raise (EStree st)

(*********************************************************************
 * Choosing rules
 *********************************************************************)

let choose_rule_func_call goal : rule list =
  []

let choose_synthesis_rules goal : rule list =
  let rs = choose_rule_func_call goal in
  rs

(*********************************************************************
 * Processing rules
 *********************************************************************)

let process_rule_func_call goal rcore : derivation =
  mk_derivation_sub_goals goal (RlFuncCall rcore) []


let process_one_rule goal rule : derivation =
  match rule with
  | RlFuncCall rcore -> process_rule_func_call goal rcore


(*********************************************************************
 * The search procedure
 *********************************************************************)

let rec synthesize_one_goal goal : synthesis_tree =
  let rules = choose_synthesis_rules goal in
  process_all_rules goal rules

and process_all_rules goal rules : synthesis_tree =
  try
    List.iter (fun rule ->
      let drv = process_one_rule goal rule in
      let stree = process_one_derivation drv in
      if is_synthesis_tree_success stree then raise_stree stree
    ) rules;
    (* no rule can be applied *)
    mk_synthesis_tree_fail goal "no rule"
  with EStree st -> st

and process_conjunctive_subgoals goal rule sub_goals : synthesis_tree =
  (* TODO *)
  mk_synthesis_tree_success goal rule

and process_one_derivation drv : synthesis_tree =
  let goal, rule = drv.drv_goal, drv.drv_rule in
  match drv.drv_kind with
  | DrvStatus false -> mk_synthesis_tree_fail goal "unknown"
  | DrvStatus true -> mk_synthesis_tree_success goal rule
  | DrvSubgoals gs -> process_conjunctive_subgoals goal rule gs


(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)

let synthesize_program goal : CA.exp option =
  None

let foo = ()
