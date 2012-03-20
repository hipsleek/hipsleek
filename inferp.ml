open Globals
open Sleekcommons
open Gen.Basic
open Exc.GTable

module I = Iast
module C = Cast
module IF = Iformula
module CF = Cformula
module IP = Ipure
module CP = Cpure
module LP = Lemproving
module AS = Astsimp
module DD = Debug

let synthesize_neg_view_def_x vd_u vd=
  (*partition into base_case and inductive case*)

  (*base case*)
  (*CF.data_of_h_formula*)
  (*inductive case*)
  (*partition into data_formula and view_formula*)
  vd

let synthesize_neg_view_def vd_u vd=
  let pr1 = Cprinter.string_of_view_decl in
   Debug.ho_2 "synthesize_neg_view_def" pr1 pr1 pr1
       (fun _ _ -> synthesize_neg_view_def_x vd_u vd) vd_u vd
