
open Cformula
open Cast

type context = (h_formula * h_formula * int * h_formula * match_type * h_formula * (int * h_formula) list)

(*
  1. the context itself (w/o the extracted formula)
  2. the formula extracted from the hole minus the consumed node (where the match occurred); it can be the case that nothing is consumed for imm nodes on the RHS. 
   - this is the formula to be used as LHS heap in the next step of the entailment
  3. the hole identifier
  4. the node where the match occurred
  5. a flag telling if a match happened at the root pointer or at a materialized argument, such as the tail pointer of a list with tail pointer
  6. --- the same context w/o the reading phases preceding the hole
  7. a list with all the immutability markings given as tuples (hole_id, node_to_b_input)
*)

and phase_type = 
  | Spatial
  | Classic

and match_type =
  | Root
  | MaterializedArg
  | Arg

and ctx_type = 
  | SpatialImm
  | SpatialMutable
  | ConjImm
  | ConjMutable

(* 
   returns a list of tuples: (rest, matching node, flag, phase, ctx)
   The flag associated with each node lets us know if the match is at the root pointer, materialized arg, arg.
*)

(*  (resth1, anode, r_flag, phase, ctx) *)   
let rec choose_context prog lhs_h lhs_p (p : CP.spec_var) (imm : bool) (phase : phase_type option) pos : (h_formula * h_formula * match_type * phase_type option * h_formula * int) list =
  let lhs_fv = (h_fv lhs_h) @ (CP.fv lhs_p) in
  let eqns' = ptr_equations lhs_p in
  let eqns = (p, p) :: eqns' in
  let asets = alias eqns in
    (* find the alias set paset containing p *)
  let paset = get_aset asets p in 
    if U.empty paset then 
      begin 
	(* no alias *)
	failwith ("choose_context: Error in getting aliases for " ^ (Cprinter.string_of_spec_var p))
      end 
    else
      begin
	if not(CP.mem p lhs_fv) || (!Globals.enable_syn_base_case && (CP.mem CP.null_var paset))
	then begin
	  Debug.devel_pprint ("choose_context: " ^ (Cprinter.string_of_spec_var p) ^ " is not mentioned in lhs\n\n") pos;
	  []
	end
	else 
	  (* before: let anodes = context_get_aliased_node prog lhs_h paset in *)
	  (* choose the type of context *)
	  let anodes = 
	    match phase with
	      | Some Spatial -> (* let _ = print_string("[choose_cxt]: Spatial ctx:\n") in *) (spatial_ctx_extract prog lhs_h paset imm) 
              | Some Classic -> (* let _ = print_string("[choose_ctx]: Conj ctx\n") in *) (conj_ctx_extract prog lhs_h paset imm)
	      | None -> (* let _ = print_string("[choose_ctx]: No ctx -> apply the conj one\n") in *) (conj_ctx_extract prog lhs_h paset imm) 	  
          in		  
	    List.map (fun (new_ctx, hole, hole_id, anode, flag, _, _) -> (hole, anode, flag, phase, new_ctx, hole_id)) anodes
      end	

(*
spatial context
*)
    
and spatial_ctx_extract_debug p f a i = Util.ho_debug_4 "spatial_context_extract " (fun _ -> "?") 
(Cprinter.string_of_h_formula) 
(fun _ -> "?") 
(string_of_bool)
(fun _ -> "?")
(fun _ -> true) 
spatial_ctx_extract p f a i

and spatial_ctx_extract prog (f0 : h_formula) (aset : CP.spec_var list) (imm : bool) : context list  =
  (* let _ = print_string("spatial_ctx_extract with f0 = " ^ (Cprinter.string_of_h_formula f0) ^ "\n") in *)
  let rec helper f = match f with
    | HTrue 
    | HFalse -> []
    | Hole _ -> []
    | DataNode ({h_formula_data_node = p1; 
		 h_formula_data_imm = imm1}) ->
	if ((CP.mem p1 aset) && (subtype imm1 imm)) then 
	  let matched_node = 
	    (* if the node is immutable -> do not consume it *)
	    if imm then f
	    (* otherwise consume it *)
	    else HTrue
	  in    
	  let hole_no = Globals.fresh_int() in 
	  [((Hole hole_no), matched_node, hole_no, f, Root, HTrue, [])]
	else 
	  []
    | ViewNode ({h_formula_view_node = p1;
		 h_formula_view_imm = imm1;
		 h_formula_view_arguments = vs1;
		 h_formula_view_name = c}) ->
	let matched_node = 
	    (* if the node is immutable -> do not consume it *)
	    if imm then f
	    (* otherwise consume it *)
	    else HTrue
	in      
	if (CP.mem p1 aset)  && (subtype imm imm1) then
	  let hole_no = Globals.fresh_int() in
	    [(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]
	else
	  let vdef = look_up_view_def_raw prog.prog_view_decls c in
	  let mvs = CP.subst_var_list_avoid_capture vdef.view_vars vs1
	    vdef.view_materialized_vars
	  in
	    if List.exists (fun v -> ((CP.mem v aset) && (subtype imm1 imm))) mvs then
	      let hole_no = Globals.fresh_int() in
		[(Hole hole_no, matched_node, hole_no, f, MaterializedArg, HTrue, [])]
	    else if List.exists (fun v -> ((CP.mem v aset) && (subtype imm imm1))) vs1 then
	      let hole_no = Globals.fresh_int() in 
		[(Hole hole_no, matched_node, hole_no, f, Arg, HTrue, [])]
	    else
	      []
    | Star ({h_formula_star_h1 = f1;
	     h_formula_star_h2 = f2;
	     h_formula_star_pos = pos}) ->
	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (ctx1, mkStarH hole1 f2 pos, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

	let l2 = helper f2 in
	let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, mkStarH f1 hole2 pos, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
	  res1 @ res2
    | Conj ({h_formula_conj_h1 = f1;
	     h_formula_conj_h2 = f2;
	     h_formula_conj_pos = pos}) -> (* [] *)
	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkConjH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

	let l2 = helper f2 in
	let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkConjH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
	  res1 @ res2

    | Phase ({h_formula_phase_rd = f1;
	     h_formula_phase_rw = f2;
	     h_formula_phase_pos = pos}) ->
	(* let _ = print_string("in phase with f1 = " ^ (Cprinter.string_of_h_formula f1) ^ "\n") in *)
	(* let _ = print_string("and f2 = " ^ (Cprinter.string_of_h_formula f2) ^ "\n") in *)
	let l1 = helper f1 in		
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkPhaseH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

	let l2 = helper f2 in
	let res2 = 
	  if not(imm) && (List.length l2) > 0 then
	    (* drop read phase *)
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
	  else
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
	in
	  res1 @ res2
(*	  
	let l2 = helper f2 in
	  (*List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> ((*mkPhaseH f1 ctx2 pos*)ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2*)
	List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2  
*)
  in
    (helper f0)


(*
conjunctive context
*)

and conj_ctx_extract_debug p f a i = Util.ho_debug_4 "conj_context_extract " (fun _ -> "?") 
(Cprinter.string_of_h_formula) 
(fun _ -> "?") 
(string_of_bool)
(fun _ -> "?")
(fun _ -> true) 
conj_ctx_extract p f a i

and conj_ctx_extract prog (f0 : h_formula) (aset : CP.spec_var list) (imm : bool) : context list  =
  (* let _ = print_string("conj_ctx_extract: input formula = " ^ (Cprinter.string_of_h_formula f0) ^ "\n") in *)
  let rec helper f = match f with
    | HTrue 
    | HFalse -> []
    | Hole _ -> []
    | DataNode ({h_formula_data_node = p1;
		 h_formula_data_imm = imm1}) ->
	if (CP.mem p1 aset) && (subtype imm1 imm) then
	  let matched_node =
	    if imm then f
	    else HTrue 
	   in   
	  let hole_no = Globals.fresh_int() in 
	  [((Hole hole_no), matched_node, hole_no, f, Root, HTrue, [])]  (* the node is imm, hence it is not consumed *)
	else 
	  []
    | ViewNode ({h_formula_view_node = p1;
		 h_formula_view_imm = imm1;
		 h_formula_view_arguments = vs1;
		 h_formula_view_name = c}) ->
	let matched_node =
	    if imm then f
	    else HTrue 
	   in   
	if (CP.mem p1 aset) && (subtype imm imm1) then
	  (*let _ = print_string("f = " ^ (Cprinter.string_of_h_formula f) ^ "\n") in
	  let _ = print_string("imm = " ^ (string_of_bool imm) ^ "\n") in
	  let _ = print_string("imm1 = " ^ (string_of_bool imm1) ^ "\n") in*)
	  let hole_no = Globals.fresh_int() in 
	    [(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]
	else
	  let vdef = look_up_view_def_raw prog.prog_view_decls c in
	  let mvs = CP.subst_var_list_avoid_capture vdef.view_vars vs1
	    vdef.view_materialized_vars
	  in
	    if List.exists (fun v -> ((CP.mem v aset) && (subtype imm imm1))) mvs then
	      let hole_no = Globals.fresh_int() in 
		[(Hole hole_no, matched_node, hole_no, f, MaterializedArg, HTrue, [])]
	    else if List.exists (fun v -> ((CP.mem v aset) && (subtype imm imm1))) vs1 then
	      let hole_no = Globals.fresh_int() in 
		[(Hole hole_no, matched_node, hole_no, f, Arg, HTrue, [])]
	    else []
    | Star ({h_formula_star_h1 = f1;
	     h_formula_star_h2 = f2;
	     h_formula_star_pos = pos}) ->

	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (ctx1, mkStarH hole1 f2 pos, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in
	
	let l2 = helper f2 in
	let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, mkStarH f1 hole2 pos, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
	  res1 @ res2
    | Conj ({h_formula_conj_h1 = f1;
	     h_formula_conj_h2 = f2;
	     h_formula_conj_pos = pos}) -> 
	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (ctx1, mkConjH hole1 f2 pos, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in
	
	let l2 = helper f2 in
	let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, mkConjH f1 hole2 pos, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
	  res1 @ res2

    | Phase ({h_formula_phase_rd = f1;
	     h_formula_phase_rw = f2;
	     h_formula_phase_pos = pos}) ->

	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (ctx1, mkPhaseH hole1 f2 pos, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in
	
	let l2 = helper f2 in
	let res2 = 
	  if not(imm) && (List.length l2) > 0 then
	    (* drop the read phase *)
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 
	  else    
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, mkPhaseH f1 hole2 pos, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 
	in
	  res1 @ res2
  in
    (helper f0)

(*
(* input to_input into the context ctx, into the hole id_hole *) 
and ctx_input (ctx : formula) (id_hole : int) (to_input : h_formula) : formula = 
  match ctx with
    | Base fb -> 
	let new_fb_heap = ctx_heap_input fb.formula_base_heap id_hole to_input in Base({fb with formula_base_heap = new_fb_heap;})  
    | Or fo ->
	let fo1 = ctx_input fo.formula_or_f1 id_hole to_input in
	let fo2 = ctx_input fo.formula_or_f2 id_hole to_input in  
	  Or({ fo with  formula_or_f1 = fo1; formula_or_f2 = fo2;})
    | Exists fe ->
	let new_fe_heap = ctx_heap_input fe.formula_exists_heap id_hole to_input in Exists({fe with formula_exists_heap = new_fe_heap;})
*)

and ctx_heap_input (ctx : h_formula) (id_hole : int) (to_input : h_formula) : h_formula =
  match ctx with
    | Hole id ->
	if id = id_hole then to_input
	else ctx
    | Star ({h_formula_star_h1 = f1;
	     h_formula_star_h2 = f2;
	     h_formula_star_pos = pos}) -> 
	let new_f1 = ctx_heap_input f1 id_hole to_input in 
	let new_f2 = ctx_heap_input f2 id_hole to_input in
	  Star ({h_formula_star_h1 = new_f1;
		 h_formula_star_h2 = new_f2;
		 h_formula_star_pos = pos})  
    | Conj ({h_formula_conj_h1 = f1;
	     h_formula_conj_h2 = f2;
	     h_formula_conj_pos = pos}) -> 
	let new_f1 = ctx_heap_input f1 id_hole to_input in 
	let new_f2 = ctx_heap_input f2 id_hole to_input in
	  Conj ({h_formula_conj_h1 = new_f1;
		 h_formula_conj_h2 = new_f2;
		 h_formula_conj_pos = pos})  
    | Phase ({h_formula_phase_rd = f1;
	     h_formula_phase_rw = f2;
	     h_formula_phase_pos = pos}) -> 
	let new_f1 = ctx_heap_input f1 id_hole to_input in 
	let new_f2 = ctx_heap_input f2 id_hole to_input in
	  Phase ({h_formula_phase_rd = new_f1;
		 h_formula_phase_rw = new_f2;
		 h_formula_phase_pos = pos})  
    | DataNode _ 
    | ViewNode _
    | HTrue | HFalse -> ctx

(* create an empty context *)
and mk_empty_ctx (id_hole : int) (*pos*) : h_formula = Hole(id_hole)
(*    Base({
	   formula_base_heap = Hole(id_hole);
	   formula_base_pure = Cpure.mkTrue pos;
	   formula_base_type = TypeTrue; 
	   formula_base_flow = (mkTrueFlow ());
           formula_base_branches = [];
	   formula_base_pos = pos;
	 })*)

(* check whether a context is empty *)
and is_empty_ctx (ctx : formula) : bool = match ctx with 
  | Base ({formula_base_heap = fb_h;}) -> is_hole_heap_ctx fb_h
  | _  -> failwith "context.ml, is_empty_ctx: check this\n" (* todo: check this *)

and is_hole_heap_ctx (ctx_h : h_formula) : bool = match ctx_h with
  | Hole _ -> true
  | _ -> false
	
(* assume that f is a satisfiable conjunct *)
and ptr_equations (f : CP.formula) : (CP.spec_var * CP.spec_var) list = match f with
  | CP.And (f1, f2, pos) -> (ptr_equations f1) @ (ptr_equations f2)
  | CP.BForm (bf,_) -> begin
	  match bf with
		| CP.Eq (e1, e2, _) ->
			if CP.can_be_aliased e1 && CP.can_be_aliased e2 then
			  let sv1 = CP.get_alias e1 in
			  let sv2 = CP.get_alias e2 in
				[(sv1, sv2)]
			else []
		| _ -> []
	end
  | _ -> []
	
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

(* M <: I *)
(* return true if imm1 <: imm2 *)	
and subtype (imm1 : bool) (imm2 : bool) : bool = not(imm1) or imm2

  
