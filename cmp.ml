open Globals

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure

(*for testing-compare two formulas*)

(*	
and formula =
  | Base of formula_base
  | Or of formula_or
  | Exists of formula_exists

and list_formula = formula list

and formula_base = {  formula_base_heap : h_formula;
                      formula_base_pure : MCP.mix_formula;
                      formula_base_type : t_formula; (* a collection ot subtype information *)
                      formula_base_and : one_formula list; (*to capture concurrent flows*)
                      formula_base_flow : flow_formula;
                      formula_base_label : formula_label option;
                      formula_base_pos : loc }*)

let cmp_formulas (f1: CF.formula) (f2: CF.formula): bool=
  let _ = print_endline ("\n Compare formulas") in
  match f1 with
    | CF.Base b -> true
    | CF.Or b -> true
    | CF.Exists -> true 

let cmp_formulas_base (b1: MCP.mix_formula) (b2: MCP.mix_formula): bool=
let _ = print_endline ("\n Compare pure formulas") in
true
