#include "xdebug.cppo"
open VarGen
module DD = Debug
open Globals
open Gen
(* open Exc.GTable *)
(* open Label_only *)
(* open Label *)
open Cast
open Cformula

module CP = Cpure

let heap_entail_rhs_htrue_x prog es h_ante h_conseq rhs_h_matched_set=
  let nh_ante = HEmp in
  let quans,base = split_quantifiers es.es_formula in
  let h1, p1, vp1, fl1, t1, a1 = split_components base in
  let es_f = mkExists quans nh_ante p1 vp1 t1 fl1 a1 (pos_of_formula base) in
  let n_es = {es with es_formula = es_f} in
  ( nh_ante, HEmp, n_es, rhs_h_matched_set@(get_ptrs h1))

let heap_entail_rhs_htrue prog es h_ante h_conseq rhs_h_matched_set=
  let pr1 = Cprinter.prtt_string_of_h_formula in
  let pr2 = Cprinter.string_of_entail_state in
  Debug.no_2 "heap_entail_rhs_htrue" pr1 pr1 (pr_quad pr1 pr1 pr2 !CP.print_svl)
    (fun _ _ -> heap_entail_rhs_htrue_x prog es h_ante h_conseq rhs_h_matched_set)
    h_ante h_conseq
