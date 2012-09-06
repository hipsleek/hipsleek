open Globals
open Gen

module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure

(*for testing-compare two formulas*)

let rec checkeq_formulas (hvars: ident list) (f1: CF.formula) (f2: CF.formula): bool=
 (* let _ = Debug.info_pprint ("Compare formulas ") no_pos in*)
  match f1 with
    |CF.Base({CF.formula_base_heap = h1;
	      CF.formula_base_pure = p1}) ->(match f2 with 
	|CF.Base ({CF.formula_base_heap = h2;
	      CF.formula_base_pure = p2}) -> checkeq_h_formulas hvars h1 h2 
	|_ -> false)
    |CF.Exists({CF.formula_exists_heap = h1;
		CF.formula_exists_pure = p1})->(match f2 with 
	|CF.Exists ({CF.formula_exists_heap = h2;
	      CF.formula_exists_pure = p2}) -> checkeq_h_formulas hvars h1 h2 
	|_ -> false)
    |CF.Or b1 ->  report_error no_pos "not handle Or f1 yet"
  
and checkeq_h_formulas (hvars: ident list)(hf1: CF.h_formula) (hf2: CF.h_formula): bool=
 (* let _ = Debug.info_pprint ("Compare heap formulas ") no_pos in*)
(*create list*)
  let check_false_hf1 = check_false_formula hf1 in
  let check_false_hf2 = check_false_formula hf2 in
  if(check_false_hf1 && check_false_hf2) then true
  else if(check_false_hf1 || check_false_hf2) then false
  else(
    match hf1 with  
      | CF.Star ({CF.h_formula_star_h1 = h1;
		  CF.h_formula_star_h2 = h2}) 
      | CF.Phase  ({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2}) 
      | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2})  ->
	let ph1 = checkeq_h_formulas hvars h1 hf2 in
	if(ph1) then checkeq_h_formulas hvars h2 hf2 else false
      | CF.DataNode n -> match_equiv_node hvars n hf2 
      | CF.ViewNode n -> match_equiv_view_node hvars n hf2
      | CF.Hole h1 -> ( match hf2 with
	  |CF.Hole h2 -> h1 = h2
	  |_ -> false
      )
      | CF.HRel r  ->  match_equiv_rel hvars r hf2
      | CF.HTrue  ->  true
      | CF.HFalse ->  report_error no_pos "not a case"
      | CF.HEmp   ->  match_equiv_emp hf2
  )

and check_false_formula(hf: CF.h_formula): bool =
 match hf with  
      | CF.Star ({CF.h_formula_star_h1 = h1;
		  CF.h_formula_star_h2 = h2}) 
      | CF.Phase  ({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2}) 
      | CF.Conj  ({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2})  ->
	let ph1 = check_false_formula h1 in
	if(not ph1) then check_false_formula h2 else true
      | CF.HFalse -> true
      | CF.DataNode _ 
      | CF.ViewNode _ 
      | CF.Hole _ 
      | CF.HRel _ 
      | CF.HTrue  
      | CF.HEmp   ->  false
 

and match_equiv_node (hvars: ident list) (n: CF.h_formula_data) (hf2: CF.h_formula): bool=
 (* let _ = if(is_hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in*)
 match hf2 with 
   | CF.Star ({CF.h_formula_star_h1 = h1;
	    CF.h_formula_star_h2 = h2}) 
   | CF.Phase  ({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2}) 
   | CF.Conj  ({CF.h_formula_conj_h1 = h1;
	    CF.h_formula_conj_h2 = h2})  ->
      let ph1 =  match_equiv_node hvars n h1  in
      let ph2 =  match_equiv_node hvars n h2  in
      ph1 || ph2 
   | CF.DataNode n2 -> check_node_equiv hvars n n2 
   | CF.ViewNode _
   | CF.Hole _
   | CF.HRel _ 
   | CF.HTrue -> false
   | CF.HFalse -> report_error no_pos "not a case"
   | CF.HEmp   -> false

and check_node_equiv (hvars: ident list)(n1: CF.h_formula_data) (n2:  CF.h_formula_data): bool=
  let var1 = n1.CF.h_formula_data_node in
  let name1 = n1.CF.h_formula_data_name in
  let ann1 = n1.CF.h_formula_data_imm in
  let args1 = n1.CF.h_formula_data_arguments in
  let is_hard_n1 = (List.mem (CP.name_of_spec_var n1.CF.h_formula_data_node) hvars) in
  let var2 = n2.CF.h_formula_data_node in
  let name2 = n2.CF.h_formula_data_name in
  let ann2 = n2.CF.h_formula_data_imm in
  let args2 = n2.CF.h_formula_data_arguments in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_data_node) hvars) in
  let is_hard = is_hard_n1 || is_hard_n2 in
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2))) 
  then( 
    (*let _ = Debug.info_pprint ("diff node diff name diff ann ") no_pos in *)
    false 
  )
  else check_spec_var_list_equiv hvars args1 args2
(*translation has ensured well-typedness. *)

and check_spec_var_list_equiv  (hvars: ident list)(args1: CP.spec_var list)(args2: CP.spec_var list):bool =
(*do not check type*) 
  if((List.length args1) == 0 && (List.length args2) == 0) then true
  else (
    let check_head = check_spec_var_equiv hvars (List.hd args1) (List.hd args2) in
    if(check_head) then check_spec_var_list_equiv hvars (List.tl args1) (List.tl args2) else check_head
  )

and check_spec_var_equiv (hvars: ident list)(v1: CP.spec_var) (v2: CP.spec_var):bool=
(*do not check type*) 
  let is_hard_v1 = (List.mem (CP.name_of_spec_var v1) hvars) in
  if((CP.is_null_const v1) || (CP.is_int_const v1) || is_hard_v1) 
  then( 
    (*let _ = Debug.info_pprint ("maybe diff spec ") no_pos in *)
    CP.eq_spec_var v1 v2
  )
  else true  

and match_equiv_view_node (hvars: ident list) (n: CF.h_formula_view) (hf2: CF.h_formula): bool=
 (* let _ = if(is_hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in*)
 match hf2 with 
   | CF.Star ({CF.h_formula_star_h1 = h1;
	    CF.h_formula_star_h2 = h2}) 
   | CF.Phase  ({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2}) 
   | CF.Conj  ({CF.h_formula_conj_h1 = h1;
	    CF.h_formula_conj_h2 = h2})  ->
      let ph1 =  match_equiv_view_node hvars n h1  in
      let ph2 =  match_equiv_view_node hvars n h2  in
      ph1 || ph2 
   | CF.DataNode n2 -> false 
   | CF.ViewNode n2 -> check_view_node_equiv hvars n n2 
   | CF.Hole _
   | CF.HRel _ 
   | CF.HTrue -> false
   | CF.HFalse -> report_error no_pos "not a case"
   | CF.HEmp   -> false

and check_view_node_equiv (hvars: ident list)(n1: CF.h_formula_view) (n2:  CF.h_formula_view): bool=
  let var1 = n1.CF.h_formula_view_node in
  let name1 = n1.CF.h_formula_view_name in
  let ann1 = n1.CF.h_formula_view_imm in
  let args1 = n1.CF.h_formula_view_arguments in
  let is_hard_n1 = (List.mem (CP.name_of_spec_var n1.CF.h_formula_view_node) hvars) in
  let var2 = n2.CF.h_formula_view_node in
  let name2 = n2.CF.h_formula_view_name in
  let ann2 = n2.CF.h_formula_view_imm in
  let args2 = n2.CF.h_formula_view_arguments in
  let is_hard_n2 = (List.mem (CP.name_of_spec_var n2.CF.h_formula_view_node) hvars) in
  let is_hard = is_hard_n1 || is_hard_n2 in
  if((not (CF.is_eq_node_name name1 name2)) || (is_hard && (not (CP.eq_spec_var var1 var2))) || (not (CF.is_eq_data_ann ann1 ann2))) 
  then( 
    (*let _ = Debug.info_pprint ("diff node diff name diff ann ") no_pos in *)
    false 
  )
  else check_spec_var_list_equiv hvars args1 args2
(*translation has ensured well-typedness. *)

and match_equiv_rel (hvars: ident list) (r: (CP.spec_var * (CP.exp list) * loc)) (hf2: CF.h_formula): bool=
 (* let _ = if(is_hard) then Debug.info_pprint ("check hard node ") no_pos else  Debug.info_pprint ("check soft node ") no_pos in*)
 match hf2 with 
   | CF.Star ({CF.h_formula_star_h1 = h1;
	    CF.h_formula_star_h2 = h2}) 

   | CF.Phase  ({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2}) 
   | CF.Conj  ({CF.h_formula_conj_h1 = h1;
	    CF.h_formula_conj_h2 = h2})  ->
      let ph1 =  match_equiv_rel hvars r h1  in
      let ph2 =  match_equiv_rel hvars r h2  in
      ph1 || ph2 
   | CF.DataNode n2 -> false
   | CF.ViewNode n2  -> false
   | CF.Hole _ -> false
   | CF.HRel r2  ->  check_rel_equiv hvars r r2
   | CF.HTrue  -> false
   | CF.HFalse ->  report_error no_pos "not a case"
   | CF.HEmp   ->  false

and check_rel_equiv (hvars: ident list) (r1:  (CP.spec_var * (CP.exp list) * loc)) (r2:  (CP.spec_var * (CP.exp list) * loc)): bool=
  let (n1,el1,l1) = r1 in
  let (n2,el2,l2) = r2 in
  (*let is_hard_r1 = (List.mem (CP.name_of_spec_var n1) hvars) in *)
  let spec_var_equiv = CP.eq_spec_var n1 n2 in (*eq_spec_var means same relation*)
  if(spec_var_equiv) then check_exp_list_equiv hvars el1 el2 (*check hard var in relation*)
  else false

and check_exp_list_equiv (hvars: ident list) (el1: CP.exp list) (el2: CP.exp list) : bool=
  if((List.length el1) == 0 && (List.length el2) == 0) then true
  else(
    let head1 = List.hd el1 in 
    let head2 = List.hd el2 in
    let check_head = match head1 with
      |CP.Var(sv1,_)-> (
	let is_hard = (List.mem (CP.name_of_spec_var sv1) hvars) in
	if(not is_hard) then true
	else match head2 with
	  |CP.Var(sv2,_) -> CP.eq_spec_var sv1 sv2
	  |_ -> false
      ) 
      |_ -> true (*scale down: process only spec var as relation arguments*)
     in
     if(check_head) then check_exp_list_equiv hvars (List.tl el1) (List.tl el2) 
     else false
  )
  

and match_equiv_emp (hf2: CF.h_formula): bool=
 match hf2 with 
   | CF.Star ({CF.h_formula_star_h1 = h1;
	    CF.h_formula_star_h2 = h2}) 
   | CF.Phase  ({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2}) 
   | CF.Conj  ({CF.h_formula_conj_h1 = h1;
	    CF.h_formula_conj_h2 = h2})  ->
      let ph1 =  match_equiv_emp h1  in
      if(not ph1) then  match_equiv_emp h2 else true
   | CF.DataNode _ 
   | CF.ViewNode _
   | CF.Hole _
   | CF.HRel _ 
   | CF.HTrue 
   | CF.HFalse -> false
   | CF.HEmp   -> true
