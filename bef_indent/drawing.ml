#include "xdebug.cppo"
open VarGen
(*
  Turn formulas to graph drawings.
*)

open Globals
open Cpure
open Cformula

(*
  Each disjunct will be generated as a separate graph.
  Parameter n is used to attach a different number to
  variables appearing in each disjunct to distinguish
  different occurrences of the same variable in different
  disjuncts.
*)

(* TO BE IMPLEMENTED *)
let dot_of_partial_context_file prog ctx visib_names file0 = ()

let rec dot_of_context_file prog ctx visib_names file0 =
  let file = 
	if Filename.check_suffix file0 "_ps" then Filename.chop_suffix file0 "_ps"
	else file0 
  in
	if Sys.file_exists file then
	  ignore (print_string ("\ndprint: File " ^ file ^ " exists.\n"))
	else
	  let tmp2 = dot_of_context prog ctx visib_names in
	  (*let tmp2 = String.concat "\n\n" tmp1 in*)
	  let ochn = open_out file in
		output_string ochn tmp2;
		close_out ochn;
		if Filename.check_suffix file0  "_ps" then begin
		  ignore (Sys.command ("dot -Tps " ^ file ^ " -o " ^ file ^ ".ps"));
		  ignore (Sys.command ("gv " ^ file ^ ".ps"))
		end else begin
		  ignore (Sys.command ("dotty " ^ file))
		end;
		if not (Filename.check_suffix file0 "_keep") then
		  Sys.remove file
 

and dot_of_context prog ctx visib_names = dot_of_formula prog (formula_of_list_context ctx) visib_names

and dot_of_formula prog f visib_names =
  let buffer = Buffer.create 1024 in
	Buffer.add_string buffer "digraph prog_state {\n";
	dot_of_form prog 1 f visib_names buffer;
	Buffer.add_string buffer "\n}";
	Buffer.contents buffer

and dot_of_form prog (n : int) (f0 : formula) visib_names buffer = match f0 with
  | Or ({formula_or_f1 = f1;
		 formula_or_f2 = f2}) ->
	  dot_of_form prog n f1 visib_names buffer;
	  dot_of_form prog (n + 1) f2 visib_names buffer
  | Base ({formula_base_heap = h;
		   formula_base_pure = p})
  | Exists ({formula_exists_heap = h;
			 formula_exists_pure = p}) ->
	  dot_of_conjunct prog n h p visib_names buffer

(*
  Each conjunct is a subgraph
*)
and dot_of_conjunct prog n h p visib_names buffer = 
  let sgraph = fresh_name () in
  let () = Buffer.add_string buffer ("\nsubgraph " ^ sgraph ^ " {\n") in
  let nodes = gen_nodes prog n h buffer in
	gen_edges prog n h p nodes buffer;
	gen_edges_visib_names n visib_names p nodes buffer;
	Buffer.add_string buffer ("}\n");
	()

(*
  Generate nodes. Object as solid-line rectangles, predicates dashed.
  It also returns a list of names of nodes. Each element of the list
  is a pair. The first element of the pair is the key for looking up
  the node denoted by the second element of the pair. The first element
  is a variable name, whereas the second (node name) is the variable
  name augmented with a counter to distinguish the same variable in
  different disjuncts of a disjunctive formula.
*)
and gen_nodes prog n h0 buffer = match h0 with
  | Star ({h_formula_star_h1 = h1;
	   h_formula_star_h2 = h2}) 
  | StarMinus ({h_formula_starminus_h1 = h1;
	       h_formula_starminus_h2 = h2}) 	   
  | Phase ({h_formula_phase_rd = h1;
	    h_formula_phase_rw = h2}) 
  | Conj ({h_formula_conj_h1 = h1;
	   h_formula_conj_h2 = h2})
  | ConjStar ({h_formula_conjstar_h1 = h1;
	   h_formula_conjstar_h2 = h2})	   	    
  | ConjConj ({h_formula_conjconj_h1 = h1;
	   h_formula_conjconj_h2 = h2}) ->
      let nodes1 = gen_nodes prog n h1 buffer in
      let nodes2 = gen_nodes prog n h2 buffer in
	nodes1 @ nodes2
  | ThreadNode ({h_formula_thread_node = p;
	       h_formula_thread_name = c}) ->
      let pname = (dot_of_spec_var p) ^ "__" ^ (string_of_int n) in
	Buffer.add_string buffer (pname ^ " [shape=box,label=\"" ^ c ^ "\"];\n");
	[(dot_of_spec_var p, pname)]
  | DataNode ({h_formula_data_node = p;
	       h_formula_data_name = c}) ->
      let pname = (dot_of_spec_var p) ^ "__" ^ (string_of_int n) in
	Buffer.add_string buffer (pname ^ " [shape=box,label=\"" ^ c ^ "\"];\n");
	[(dot_of_spec_var p, pname)]
  | ViewNode ({h_formula_view_node = p;
	       h_formula_view_arguments = args;
	       h_formula_view_name = c}) ->
      let vdef = x_add Cast.look_up_view_def no_pos prog.Cast.prog_view_decls c in
      let mvars = subst_var_list_avoid_capture vdef.Cast.view_vars args 
        (Cast.mater_props_to_sv_list vdef.Cast.view_materialized_vars) in
      let pname = (dot_of_spec_var p) ^ "__" ^ (string_of_int n) in
	(*
	  materialized parameters are input paramters. External pointers will
	  be pointing to them. So associate them with the current predicate
	  node so that we can draw edges from external pointers to the current
	  predicate instance.
	*)
      let tmp = List.map (fun v -> (dot_of_spec_var v, pname)) mvars in
	Buffer.add_string buffer (pname ^ " [shape=box,style=dashed,label=\"" ^ c ^ "\"];\n");
	(dot_of_spec_var p, pname) :: tmp
  | HTrue | HFalse | HEmp | HVar _ |HRel _ |  Hole _ |  FrmHole _ -> []


and gen_edges prog n h0 p nodes buffer = 
  let hvars = h_fv h0 in
  let heqs = List.map (fun hv -> (hv, hv)) hvars in
  let asets = Csvutil.alias_nth 4 ((MCP.ptr_equations_with_null p) @ heqs) in
	(* see if an edge from start to finish can be added *)
  let make_edge start finish lbl =
    let aset' = Csvutil.get_aset asets finish in
    let aset = List.map dot_of_spec_var aset' in
      (* find out nodes that are aliased with finish *)
    let dest = List.filter (fun (a, b) -> List.mem a aset) nodes in
    let edges = List.map (fun (_, b) -> 
			    ((dot_of_spec_var start) ^ "__" ^ (string_of_int n))
			    ^ " -> " ^ b ^ " [label=" ^ lbl ^ "];\n") dest in
      List.map (fun e -> Buffer.add_string buffer e) edges
  in
    match h0 with
      | Star ({h_formula_star_h1 = h1;
	       h_formula_star_h2 = h2})
      | StarMinus ({h_formula_starminus_h1 = h1;
	       h_formula_starminus_h2 = h2}) 
      | Conj ({h_formula_conj_h1 = h1;
	       h_formula_conj_h2 = h2}) 
      | ConjStar ({h_formula_conjstar_h1 = h1;
	       h_formula_conjstar_h2 = h2}) 
      | ConjConj ({h_formula_conjconj_h1 = h1;
	       h_formula_conjconj_h2 = h2}) 	       	       
      | Phase ({h_formula_phase_rd = h1;
	       h_formula_phase_rw = h2}) ->
	  gen_edges prog n h1 p nodes buffer;
	  gen_edges prog n h2 p nodes buffer
      | ThreadNode _ -> failwith "make_edge: not support ThreadNode yet"
      | DataNode ({h_formula_data_node = p;
		   h_formula_data_name = c;
		   h_formula_data_arguments = args}) -> begin
	  let tmp = List.tl (List.tl args) in
	  let ddef = Cast.look_up_data_def no_pos prog.Cast.prog_data_decls c in
	  let field_names = List.map Cast.get_field_name ddef.Cast.data_fields in
	    ignore (List.map2 (fun a -> fun lbl -> make_edge p a lbl) tmp field_names)
	end
      | ViewNode ({h_formula_view_node = p;
		   h_formula_view_name = c;
		   h_formula_view_arguments = args}) -> begin
	  let vdef = x_add Cast.look_up_view_def no_pos prog.Cast.prog_view_decls c in
	  let param_names = List.map dot_of_spec_var vdef.Cast.view_vars in
	    ignore (List.map2 (fun a -> fun lbl -> make_edge p a lbl) args param_names)
	end
      | HTrue | HFalse | HEmp | HVar _ | HRel _ | Hole _ |  FrmHole _  -> ()

and gen_edges_visib_names n visib_names p nodes buffer =
  let visib_names = List.map (fun v -> SpecVar (Globals.null_type, v, Primed)) visib_names in
  let veqs = List.map (fun v -> (v, v)) visib_names in
  let asets = Csvutil.alias_nth 5 ((MCP.ptr_equations_with_null p) @ veqs) in
  let make_edge var =
    let aset' = Csvutil.get_aset asets var in
    let aset = List.map dot_of_spec_var aset' in
    let dest = List.filter (fun (a, b) -> List.mem a aset) nodes in
    let edges = List.map (fun (_, b) ->
			    ((dot_of_spec_var var) ^ "__" ^ (string_of_int n) ^ "__VAR"
			     ^ " -> " ^ b ^ ";\n")) dest in
      List.map (fun e -> Buffer.add_string buffer e) edges
  in
    ignore (List.map make_edge visib_names)

and dot_of_spec_var (sv : spec_var) : ident = match sv with
  | SpecVar (_, v, p) -> v ^ (if p = Unprimed then "" else "_PRM")
