#include "xdebug.cppo"

(* extension of cpure, focused on imm related operations  *)

open Globals
open VarGen
open Gen.Basic

module CF = Cformula
module CP = Cpure

(* below should preserve the old annotation, and only set NoAnn to Mutable *)
let ann_heap_with_m = function
  | CF.DataNode hp -> 
    if not(Immutils.isNoAnn hp.CF.h_formula_data_imm) then None
    else Some (CF.DataNode { hp with h_formula_data_imm = CP.ConstAnn(Mutable) })
  | CF.ViewNode hp -> 
    if not(Immutils.isNoAnn hp.CF.h_formula_view_imm) then None
    else Some (CF.ViewNode { hp with h_formula_view_imm = CP.ConstAnn(Mutable) })
  | _ -> None

let annotate_imm_struc_formula (constr: CF.struc_formula) : CF.struc_formula =
  CF.transform_struc_formula (nonef, nonef, ann_heap_with_m, (somef, somef, somef, somef, somef)) constr

let annotate_imm_formula (constr: CF.formula) : CF.formula =
  CF.transform_formula (nonef, nonef, ann_heap_with_m, (somef, somef, somef, somef, somef)) constr
