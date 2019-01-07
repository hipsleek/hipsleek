#include "xdebug.cppo"

open Globals
open VarGen
open Gen
open Cpure
open Mcpure
open Cformula

(*********************************************************************
 * Data structures
 *********************************************************************)

(* goal *)
type goal = {
  gl_prog : Cast.prog_decl;
  gl_pre_cond : formula;
  gl_post_cond : formula;
  gl_vars: CP.spec_var list;
}

(* Synthesis rules
 * TODO: add more synthesis rules here *)
type rule =
  | RlFuncCall of rule_func_call
  | RlAssign of rule_assign

and rule_func_call = {
  rfc_func_name : string;
  rfc_params : exp list;
}

and rule_assign = {
  ra_exp : Cast.exp_assign;
}

(* AssignPure *)
(* {x = a} {x = b} --> {x = b} if b \in varSet*)

(* AssignPureSymb *)
(* {x = a & b = t} {x = b} --> x = t when varSet = {x, t} *)

(* Atomic derivation *)
type derivation = {
  drv_kind : derivation_kind;
  drv_rule : rule;
  drv_goal : goal;
}

and derivation_kind =
  | DrvStatus of bool
  | DrvSubgoals of goal list

(* Synthesis tree *)
type synthesis_tree =
  | StSearch of synthesis_tree_search
  | StDerive of synthesis_tree_derive

and synthesis_tree_search = {
  sts_goal : goal;
  sts_sub_trees : synthesis_tree list;
  sts_status : synthesis_tree_status;
}

and synthesis_tree_derive = {
  std_goal : goal;
  std_rule : rule;
  std_sub_trees : synthesis_tree list;
  std_status : synthesis_tree_status;
}

and synthesis_tree_core = {
  stc_goal : goal;
  stc_rule : rule;
  stc_sub_trees : synthesis_tree_core list;
}

and synthesis_tree_status =
  | StValid of synthesis_tree_core
  | StUnkn of string


(*********************************************************************
 * Constructors
 *********************************************************************)

let mk_goal cprog pre post vars =
  { gl_prog = cprog;
    gl_pre_cond = pre;
    gl_post_cond = post;
    gl_vars = vars;  }

let mk_derivation_sub_goals goal rule subgoals =
  { drv_kind = DrvSubgoals subgoals;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_success goal rule =
  { drv_kind = DrvStatus true;
    drv_rule = rule;
    drv_goal = goal; }

let mk_derivation_fail goal rule =
  { drv_kind = DrvStatus false;
    drv_rule = rule;
    drv_goal = goal; }

let mk_synthesis_tree_search goal sub_trees status : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = sub_trees;
    sts_status = status; }

let mk_synthesis_tree_derive goal rule sub_trees status : synthesis_tree =
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = sub_trees;
    std_status = status; }

let mk_synthesis_tree_core goal rule sub_trees : synthesis_tree_core =
  { stc_goal = goal;
    stc_rule = rule;
    stc_sub_trees = sub_trees; }

let mk_synthesis_tree_success goal rule : synthesis_tree =
  let stcore = mk_synthesis_tree_core goal rule [] in
  StDerive {
    std_goal = goal;
    std_rule = rule;
    std_sub_trees = [];
    std_status = StValid stcore; }

let mk_synthesis_tree_fail goal msg : synthesis_tree =
  StSearch {
    sts_goal = goal;
    sts_sub_trees = [];
    sts_status = StUnkn msg; }

(*********************************************************************
 * Queries
 *********************************************************************)

let get_synthesis_tree_status stree : synthesis_tree_status =
  match stree with
  | StDerive std -> std.std_status
  | StSearch sts -> sts.sts_status

let is_synthesis_tree_success stree : bool =
  let status = get_synthesis_tree_status stree in
  match status with
  | StValid _ -> true
  | StUnkn _ -> false


(*********************************************************************
 * Printing
 *********************************************************************)

let pr_assign_rule rule =
  let exp = rule.ra_exp in
  Cprinter.string_of_exp (Cast.Assign exp)

let pr_rule rule = match rule with
  | RlFuncCall fc -> "RlFuncCal"
  | RlAssign rule -> "RlAssign " ^ "(" ^ (pr_assign_rule rule) ^ ")"
