(*
 1. this file provides interfaces and implementations for
   - must/may errors
2. IMPORTANT (AVOID REDUNDANT): before implement new method, please go through
  interfaces and UNUSED module to check whether your need is there.
*)

open Globals
open Gen
open Exc.GTable
(* open Perm *)
(* module Err = Error *)
(* module CP = Cpure *)
(* module MCP = Mcpure *)


type steps = string list

(*implementation of must/may is moved to musterr.ml*)
 
(*      MAY

 VALID       MUST

        BOT
*)

type fail_context = {
    fc_prior_steps : steps; (* prior steps in reverse order *)
    fc_message : string;          (* error message *)
    (* fc_current_lhs : entail_state;     (\* LHS context with success points *\) *)
    (* fc_orig_conseq : struc_formula;     (\* RHS conseq at the point of failure *\) *)
    fc_failure_pts : Globals.formula_label list;     (* failure points in conseq *)
    (* fc_current_conseq : formula; *)
}

and fail_type =
  | Basic_Reason of (fail_context * fail_explaining)
  | Trivial_Reason of fail_explaining
  | Or_Reason of (fail_type * fail_type)
  | And_Reason of (fail_type * fail_type)
  | Union_Reason of (fail_type * fail_type)
  | ContinuationErr of fail_context
  | Or_Continuation of (fail_type * fail_type)

and failure_kind =
  | Failure_May of string
  | Failure_Must of string
  | Failure_Bot of string
  | Failure_Valid

and fail_explaining = {
    fe_kind: failure_kind; (*may/must*)
    fe_name: string;
    fe_locs: Globals.loc list;
    (* fe_explain: string;  *)
    (* string explaining must failure *)
    (*  fe_sugg = struc_formula *)
}



