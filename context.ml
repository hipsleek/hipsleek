(*
	Created 05.06.2009
*)
open Cformula
open Cast

type context = (h_formula * match_type * h_formula list * h_formula)
(* 
	Given a context C[hole1][hole2]:
	first component: hole1 (the matching node);
	second component: a flag telling if a match happens at the root pointer or at a materialized argument, such as the tail pointer of a list with tail pointer;
	third component: hole2 (dependent on the type of the context) - it is represented by a list of h_formulas;
	forth component: the remaining of the heap after the holes have been taken away. 
*)

and match_type =
  | Root
  | MaterializedArg
  | Arg


(* 
	the context procedure corresponding to the previous entailment mechanism
*)
(* 
	returns a list of contexts, where the first hole of each context corresponds to a node from the heap lhs_h that appears in the alias set aset. 
	The flag associated with each node lets us know if the match is at the root pointer,  materialized arg, arg.
 *)  
let rec context_old prog lhs_h (lhs_p:MCP.memo_pure) (p : CP.spec_var) pos : context list =
	let lhs_fv = (h_fv lhs_h) @ (MCP.mfv lhs_p) in
	let eqns' = MCP.ptr_equations false lhs_p in
	let eqns = (p, p) :: eqns' in
	let asets = alias eqns in
	let paset = get_aset asets p in (* find the alias set containing p *)
		if U.empty paset then 
		begin (* can this case happen *)
		  failwith ("context_old: Error in getting aliases for " ^ (Cprinter.string_of_spec_var p))
		end 
		else
		begin
			if not(CP.mem p lhs_fv) || (!Globals.enable_syn_base_case && (CP.mem CP.null_var paset))
			then begin
				Debug.devel_pprint ("context_old: " ^ (Cprinter.string_of_spec_var p) ^ " is not mentioned in lhs\n\n") pos;
				[]
			end
			else
			let anodes = context_get_aliased_node prog lhs_h paset in
				anodes
		end	

and context_get_aliased_node prog (f0 : h_formula) (aset : CP.spec_var list) : context list  =
  let rec alias_helper f = match f with
	| HTrue 
	| HFalse -> []
	| DataNode ({h_formula_data_node = p1}) ->
		if CP.mem p1 aset then 
			[(f, Root, [], HTrue)]
		else 
			[]
	| ViewNode ({h_formula_view_node = p1;
				 h_formula_view_arguments = vs1;
				 h_formula_view_name = c}) ->
		if CP.mem p1 aset then
			[(f, Root, [], HTrue)]
		else
		  let vdef = look_up_view_def_raw prog.prog_view_decls c in
		  let mvs = CP.subst_var_list_avoid_capture vdef.view_vars vs1
			vdef.view_materialized_vars
		  in
			if List.exists (fun v -> CP.mem v aset) mvs then
			  [(f, MaterializedArg, [], HTrue)]
			else if List.exists (fun v -> CP.mem v aset) vs1 then
			  [(f, Arg, [], HTrue)]
			else
				[]
	| Star ({h_formula_star_h1 = f1;
			 h_formula_star_h2 = f2;
			 h_formula_star_pos = pos}) ->
		let l1 = alias_helper f1 in
		let res1 = (compute_heap_rest l1 f2 pos) in
		let l2 = alias_helper f2 in
		let res2 = (compute_heap_rest l2 f1 pos) in
		  res1 @ res2
  in
	alias_helper f0

and compute_heap_rest (l : (h_formula * match_type * (h_formula list) * h_formula) list) (h3 : h_formula) pos : (h_formula * match_type * (h_formula list) * h_formula) list  = 
	match l with 
	| (h1, m1, h2, r1) :: rest -> (h1, m1, h2, mkStarH r1 h3 pos) :: (compute_heap_rest rest h3 pos) 
	| [] -> []
	
	
(* computes must-alias sets from equalities, maintains the invariant *)
(* that these sets form a partition. *)
and alias (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = match ptr_eqs with
  | (v1, v2) :: rest -> begin
	  let rest_sets = alias rest in
	  let search (v : CP.spec_var) (asets : CP.spec_var list list) =
		List.partition (fun aset -> CP.mem v aset) asets in
	  let av1, rest1 = search v1 rest_sets in
	  let av2, rest2 = search v2 rest1 in
	  let v1v2_set = U.remove_dups (List.concat ([v1; v2] :: (av1 @ av2))) in
		v1v2_set :: rest2
	end
  | [] -> []

and get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list =
  let tmp = List.filter (fun a -> CP.mem v a) aset in
	match tmp with
	  | [] -> []
	  | [s] -> s
	  | _ -> failwith ((Cprinter.string_of_spec_var v) ^ " appears in more than one alias sets")