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

let view_base_id rank_id =
  rank_id ^ "_0"

let view_base_sv view_id =
  SpecVar (Int, view_base_id view_id, Unprimed)

let viewnode_rank_id view_id =
  "r_" ^ view_id ^ "_" ^ (string_of_int (fresh_int ()))

let viewnode_rank_sv view_id =
  SpecVar (Int, viewnode_rank_id view_id, Unprimed)




