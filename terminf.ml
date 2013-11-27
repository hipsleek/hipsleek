open Globals
open Cpure

module MCP = Mcpure
module CP = Cpure

type rel_type =
  | RR_DEC
  | RR_BND

(**** TERMINATION RANKING INFERENCE ****)
type rrel = {
  rrel_type: rel_type;
  rrel_ctx: MCP.mix_formula;
  rrel_ctr: MCP.mix_formula;
}

(* Functions for creating ID *)
let view_rank_id view_id =
  "r_" ^ view_id

let view_rank_sv view_id =
  SpecVar (Int, view_rank_id view_id, Unprimed)

let view_rank_sv_opt view_id =
  if !en_term_inf then [view_rank_sv view_id] else []

let view_rarg_id view_id =
  "r_" ^ view_id ^ "_" ^ (string_of_int (fresh_int ()))

let view_base_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_const rarg_id

let view_var_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_var rarg_id

let solve_rrel rrel = 
  let ctx = MCP.pure_of_mix rrel.rrel_ctx in
  let ctr = MCP.pure_of_mix rrel.rrel_ctr in
  Redlog.solve_rrel ctx ctr

let rec solve_rrel_list rrel_list =
  let c_constrs, is_raw = List.split (List.map solve_rrel rrel_list) in
  let is_linear = List.for_all Redlog.is_linear_formula c_constrs in
  let fv = Gen.BList.remove_dups_eq eq_spec_var 
    (List.concat (List.map CP.fv c_constrs)) in
  let model = Smtsolver.get_model is_linear fv c_constrs in 
  (model, List.exists (fun b -> b) is_raw)

