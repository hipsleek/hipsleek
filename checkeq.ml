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

let checkeq_formulas (hvars: ident list) (f1: CF.formula) (f2: CF.formula): bool=
  let _ = print_endline ("\n Compare formulas") in
  match f1 with
    |CF.Base b1 ->(match f2 with 
	|CF.Base b2 -> checkeq_formulas_base b1 b2 
	|_ -> false)
    |_ ->  false

let checkeq_formulas_base (hvars: ident list)(b1: CF.formula_base) (b2: CF.formula_base): bool=
(*let _ = print_endline ("\n Compare base formulas") in
let h1 = b1.formula_base_heap in
let h2 
|CF.Base ({CF.formula_base_heap = h1;
	    CF.formula_base_pure = p1}) -> match f2 with
      |CF.Base ({CF.formula_base_heap = h2;
	    CF.formula_base_pure = p2}) -> *)
true
