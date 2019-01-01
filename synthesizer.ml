open Globals
open VarGen
open Gen
open Mcpure
open Cformula

open Synthesis

module CA = Cast

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

let synthesize_one_goal goal : synthesis_tree =
  let rules = choose_synthesis_rules goal in
  ()

(*********************************************************************
 * The main synthesis algorithm
 *********************************************************************)

let synthesize_program goal : CA.exp option =
  None

let foo = ()
