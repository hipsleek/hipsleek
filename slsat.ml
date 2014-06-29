open Globals
open Others
open Gen

open Cformula
module CP = Cpure

let check_sat_empty_rhs_with_uo lhs (rhs:CP.formula)=
  let is_sat = true in
  mk_cex is_sat
