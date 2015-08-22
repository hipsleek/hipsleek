#include "xdebug.cppo"

(* extension of cformula, focused on imm related operations  *)

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

let is_heap_abs ?pure:(p = CP.mkTrue no_pos) h = 
  let emap = Immutils.build_eset_of_imm_formula p in
  let f_h_helper h = 
    match h with
    | CF.DataNode hp -> 
      if (!Globals.allow_field_ann) then Immutils.is_abs_list ~emap:emap (CF.get_node_param_imm h)
      else Immutils.is_abs ~emap:emap  hp.CF.h_formula_data_imm
    | CF.ViewNode hp -> 
      if (!Globals.allow_field_ann) then Immutils.is_abs_list ~emap:emap (CF.get_node_param_imm h)
      else Immutils.is_abs ~emap:emap hp.CF.h_formula_view_imm
    | _ -> false
  in CF.foldheap f_h_helper (List.for_all (fun a -> a)) h

let is_imm_subtype ?pure:(p = CP.mkTrue no_pos) h1 h2 =
  let emap = Immutils.build_eset_of_imm_formula p in
  match h1, h2 with
  | CF.DataNode _, CF.DataNode _  
  | CF.ViewNode _, CF.ViewNode _ ->
    if (!Globals.allow_field_ann) then 
      let subtp, _, _, _ = Immutable.subtype_ann_list ~emap_lhs:emap [] [] (CF.get_node_param_imm h1) (CF.get_node_param_imm h2) in
      subtp
    else fst (Immutable.subtype_ann_pair ~emap_lhs:emap (CF.get_node_imm h1) (CF.get_node_imm h2))
  | _ -> true
