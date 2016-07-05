#include "xdebug.cppo"
open VarGen
open Globals
open Others
open Gen

open Cformula
module CP = Cpure

(* Loc: to implement*)
let check_sat_uo ante_uo conseq_uo=
  let is_sat = true in
  mk_cex is_sat

(* Loc: to implement*)
let check_sat_with_uo ante conseq=
  let is_sat = true in
  mk_cex is_sat

(* Loc: to implement*)
let check_sat_empty_rhs_with_uo_x es ante (conseq_p:CP.formula) matched_svl=
  let ante_pos = ante.formula_base_pos in
  let ante_w_fp = mkStar (Base ante) (formula_of_heap es.es_heap ante_pos) (Flow_combine) ante_pos in
  let is_sat = match ante.formula_base_heap with
    | HEmp -> true
    | _ -> false (* to implement*)
  in
  let is_sat = false in
  mk_cex is_sat

let check_sat_empty_rhs_with_uo es ante (conseq_p:CP.formula) matched_set=
  let pr1 = !print_formula_base in
  let pr2 = !CP.print_formula in
  Debug.no_4 "check_sat_empty_rhs_with_uo" Cprinter.string_of_entail_state pr1 pr2 !CP.print_svl Cprinter.string_of_failure_cex
      (fun _ _ _ _ -> check_sat_empty_rhs_with_uo_x es ante (conseq_p:CP.formula) matched_set)
      es ante conseq_p matched_set
