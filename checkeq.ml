open Globals
open Gen

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

let rec checkeq_formulas (hvars: ident list) (f1: CF.formula) (f2: CF.formula): bool=
  let _ = Debug.info_pprint ("Compare formulas ") no_pos in
  match f1 with
    |CF.Base({CF.formula_base_heap = h1;
	      CF.formula_base_pure = p1}) ->(match f2 with 
	|CF.Base ({CF.formula_base_heap = h2;
	      CF.formula_base_pure = p2}) -> checkeq_h_formulas hvars h1 h2 
	|_ -> report_error no_pos "not handle not base f2 yet")
    |CF.Exists({CF.formula_exists_heap = h1;
		CF.formula_exists_pure = p1})->(match f2 with 
	|CF.Exists ({CF.formula_exists_heap = h2;
	      CF.formula_exists_pure = p2}) -> checkeq_h_formulas hvars h1 h2 
	|_ -> report_error no_pos "not handle not exists f2 yet")
    |CF.Or b1 ->  report_error no_pos "not handle Or f1 yet"
  
(*and checkeq_formulas_base (hvars: ident list)(b1: CF.formula_base) (b2: CF.formula_base): bool=
  let _ = Debug.info_pprint ("Compare base formulas ") no_pos in
  let hf1 = b1.CF.formula_base_heap in
  let p1 = b1.CF.formula_base_pure in
  let hf2 = b2.CF.formula_base_heap in
  let p2 = b2.CF.formula_base_pure in
  checkeq_h_formulas hvars hf1 hf2*)

and checkeq_h_formulas (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula): bool=
  let _ = Debug.info_pprint ("Compare heap formulas ") no_pos in
(*create list*)
  match hf1 with  
    | CF.Star ({CF.h_formula_star_h1 = h1;
	    CF.h_formula_star_h2 = h2}) 
    | CF.Phase  ({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2}) 
    | CF.Conj  ({CF.h_formula_conj_h1 = h1;
	    CF.h_formula_conj_h2 = h2})  ->
      let ph1 = checkeq_h_formulas hvars h1 hf2 in
      let ph2 = checkeq_h_formulas hvars h2 hf2 in
      ph1 && ph2 
    | CF.DataNode n -> 
      if(List.mem (CP.name_of_spec_var n.CF.h_formula_data_node) hvars) 
      then match_equiv_node n hf2 true 
      else match_equiv_node n hf2 false
    | CF.ViewNode n ->  report_error no_pos "not handle vnode yet"
    | CF.Hole _ ->  report_error no_pos "not handle hole yet"
    | CF.HRel _  ->  report_error no_pos "not handle hrelyet"
    | CF.HTrue  ->  report_error no_pos "not handle true yet"
    | CF.HFalse ->  report_error no_pos "not handle false yet"
    | CF.HEmp   ->  report_error no_pos "not handle emp yet"

and match_equiv_node (n: CF.h_formula_data) (hf2: CF.h_formula) (hard: bool): bool=
 let _ = if(hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in
true
