open Globals
open Cpure

type rel_type =
  | RR_DEC
  | RR_BND

(* Functions for creating ID *)
let view_rank_id view_id =
  "r_" ^ view_id

let view_rank_sv view_id =
  SpecVar (Int, view_rank_id view_id, Unprimed)

let view_rarg_id view_id =
  "r_" ^ view_id ^ "_" ^ (string_of_int (fresh_int ()))

let view_base_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_const rarg_id

let view_var_ragr view_id =
  let rarg_id = SpecVar (Int, view_rarg_id view_id, Unprimed) in
  mkRArg_var rarg_id





