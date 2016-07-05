#include "xdebug.cppo"
open VarGen
(*
   Created 26 - 08 - 2006
   View Generator
*)

open Globals
module C = Cast
module CF = Cformula
module CP = Cpure
module P = Cprinter


(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(* 
   receives a class c and generates its extended view 
*)
let rec gen_ext_view (prog : C.prog_decl) (c : C.data_decl) : C.proc_decl = 
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    (* constructing the extended view as a new procedure *)
    if (String.compare c.C.data_parent_name "Object") != 0 then
      begin
      (* the closest parent is where we extend from *)
      let parent = (C.look_up_data_def no_pos prog.C.prog_data_decls c.C.data_parent_name) in 
      let fn1 = fresh_var_name parent.C.data_name 0 in
      let fn2 = fresh_var_name c.C.data_name 0 in
      let actual_type_var = fresh_var_name c.C.data_name 0 in

(* prelucrating the lhs *)
(* this is considered as the precondition *)
      let lhs_base_heap = CF.ViewNode({ CF.h_formula_view_node = CP.SpecVar(Named(c.C.data_name), 
																			fn2, 
																			Unprimed);
										CF.h_formula_view_name = c.C.data_name;
										CF.h_formula_view_arguments = List.map(fun field -> CP.SpecVar((fst field), 
																									   (snd field), 
																									   Unprimed)) 
										  (* we take all the fields for that class 
											 - the ones inherited from the parent class 
											 - the auxiliary ones 
										  *)   
										  (look_up_all_fields prog c);
										CF.h_formula_view_pseudo_data = false;
										CF.h_formula_view_pos = no_pos}) in
      let lhs_base_pure = CP.BForm(CP.BConst(true, no_pos)) in
      let lhs_base_type = CF.TypeSub({
	  CF.t_formula_sub_type_var = CP.SpecVar(Named(c.C.data_name), 
						 actual_type_var, 
						 Unprimed);
	  CF.t_formula_sub_type_type = c.C.data_name}) in
      let pre = CF.Base ({
	  CF.formula_base_heap = lhs_base_heap;
	  CF.formula_base_pure = lhs_base_pure;
	  CF.formula_base_type = lhs_base_type;
          CF.formula_base_pos = no_pos}) in

(* prelucrating the rhs *)
(* this is considered as the postcondition *)
      let extension_var = fresh_var_name ("Ext" ^parent.C.data_name) 0 in  
      let extension_arg = CP.SpecVar(Named("Ext" ^ c.C.data_name), 
				     extension_var, 
				     Unprimed) in 
      let h_formula_star_h1 = CF.ViewNode({
	    CF.h_formula_view_node = CP.SpecVar(Named(parent.C.data_name), 
						fn1, 
						Unprimed);
	    CF.h_formula_view_name = parent.C.data_name;
	    CF.h_formula_view_arguments = (List.map
		(fun field -> CP.SpecVar((fst field), (snd field), Unprimed)) 
		 (look_up_all_fields prog parent) @ [extension_arg]);
		CF.h_formula_view_pseudo_data = false;
	    CF.h_formula_view_pos = no_pos}) in
      
      let h_formula_star_h2 = CF.ViewNode({
	    CF.h_formula_view_node = extension_arg;
	    CF.h_formula_view_name = "Ext" ^ c.C.data_name;
	    CF.h_formula_view_arguments = List.map(fun field -> CP.SpecVar((fst field), 
									 (snd field), 
									 Unprimed))  
					  c.C.data_fields;
		CF.h_formula_view_pseudo_data = false;
	    CF.h_formula_view_pos = no_pos}) in
      let rhs_base_heap = CF.Star({
	    CF.h_formula_star_h1 = h_formula_star_h1;
	    CF.h_formula_star_h2 = h_formula_star_h2;
	    CF.h_formula_star_pos = no_pos}) in
      let rhs_base_pure = CP.BForm(CP.BConst(true, no_pos)) in
      let rhs_base_type = CF.TypeSub({
	    CF.t_formula_sub_type_var = CP.SpecVar(Named(c.C.data_name),
						   actual_type_var, 
						   Unprimed);
	    CF.t_formula_sub_type_type = c.C.data_name}) in
      let post = CF.Base({
	    CF.formula_base_heap = rhs_base_heap;
	    CF.formula_base_pure = rhs_base_pure;
	    CF.formula_base_type = rhs_base_type;
            CF.formula_base_pos = no_pos}) in
      let new_proc = {
	    C.proc_name = fn1;
	    C.proc_coercion = true;
		C.proc_coercion_type = C.Equiv;
(*	    C.proc_equiv = true; *)
(*	    C.proc_source_target_list = [((fn1, fn2), (pre, post))]; *)
	    C.proc_coercion_list = [(fn1, (pre, post))];
	    C.proc_args = [(Named(c.C.data_name), fn2)];
	    C.proc_return = (CP.Prim Void);
	    C.proc_static_specs = [(pre, post)];
	    C.proc_dynamic_specs = [];
	    C.proc_by_name_params = [];
	    C.proc_body = None;
	    C.proc_loc = no_pos} in
            new_proc 
     end		    
     else raise Not_found (* we can't generate an upcast view because this is the superclass - its superclass is Object *)

(* 
   verifies if two typed identifiers are equal
*)
and equal_typed_ident (t_id1 : C.typed_ident) (t_id2 : C.typed_ident) : bool = 
  (snd t_id1 = snd t_id2)                (* same identifiers *)
    && 
  (equal_types (fst t_id1) (fst t_id2))  (* same types *)

(* 
   verifies if two types are equal 
*)
and equal_types (t1 : CP.typ) (t2 : CP.typ) : bool = 
  match t1 with
  | CP.Prim (p1) -> 
      begin 
	match t2 with
	| CP.Prim (p2) -> (p1 = p2)
	| _ -> false
      end	      
  | Named (i1) -> 
      begin 
	match t2 with
	| CP.OType (i2) -> (i1 = i2)
	| _ -> false
      end	      	


(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(* 
   receives a class c and constructs the total view - with all the extensions - for that class
*)
and gen_ext_all_view (prog : C.prog_decl) ( c : C.data_decl) : C.view_decl =
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
  let fn1 = fresh_var_name "ExtAll" 0 in
  let t2 = fresh_var_name "" 0 in
  let t1 = fresh_var_name c.C.data_name 0 in
(*******************************)
(* prelucrating the lhs *)
      let view_name = "ExtAll" in
      let view_vars = [CP.SpecVar(CP.OType(c.C.data_name), 
				  t1, 
				  Unprimed)] @
		      [CP.SpecVar(CP.OType(""), 
			          t2, 
				  Unprimed)] in
(*******************************)
(* prelucrating the rhs *)
      let formula= (gen_formula prog c t1 t2 fn1) in
      let new_view = {
	    C.view_name = view_name;
	    C.view_vars = view_vars;
	    C.view_data_name = "";
	    C.view_formula = formula;
	    C.view_user_inv = (CP.BForm(CP.BConst(true, no_pos)), []);
        C.view_complex_inv = None;
	    C.view_x_formula = (CP.BForm(CP.BConst(true, no_pos)), []);
	    C.view_addr_vars = []} in
            new_view 


and gen_formula (prog : C.prog_decl) (c : C.data_decl) (t1 : ident) (t2 : ident) (fn1 : ident) : CF.formula = 
  let subclasses = (look_up_subclasses prog.C.prog_data_decls c) in
  (* the base case *)
  let base_heap = CF.HEmp in
  let base_pure = 
  CP.BForm(
	     CP.Eq(
	        CP.Var(CP.SpecVar(CP.OType("ExtAll"), 
				  fn1, 
				  Unprimed), 
		      no_pos),
	        CP.Null(no_pos),
	        no_pos
	     )  
  ) in
  let base_type = CF.TypeExact({
	       CF.t_formula_sub_type_var = CP.SpecVar(CP.OType(c.C.data_name), 
						      t2, 
						      Unprimed);
	       CF.t_formula_sub_type_type = c.C.data_name}) in
  let base_case = CF.Base({
	       CF.formula_base_heap = base_heap;
	       CF.formula_base_pure = base_pure;
	       CF.formula_base_type = base_type;
               CF.formula_base_pos = no_pos}) in
  if (List.length subclasses) > 0 then
    CF.Or ({CF.formula_or_f1 = base_case;
	    CF.formula_or_f2 = (local_gen_formula prog c subclasses t1 t2 fn1 (*fn2*));
	    CF.formula_or_pos = no_pos})
  else    
    base_case

and local_gen_formula (prog : C.prog_decl) (c : C.data_decl) (subclasses : C.data_decl list) (t1 : ident) (t2 : ident) (fn1 : ident) : CF.formula = 
      match subclasses with
      | [] -> (* shouldn't get here *)
	  Error.report_error {Error.error_loc = no_pos;
				  Error.error_text = "error when computing ExtAll"}
      | subc :: rest -> 
	  let extension_var = fresh_var_name "ExtAll" 0 in  
	  let extension_arg = CP.SpecVar(CP.OType("ExtAll"), 
					 extension_var, 
					 Unprimed) in 
	  let h_formula_star_h1 = CF.ViewNode({
	    CF.h_formula_view_node = CP.SpecVar(CP.OType("Ext" ^ subc.C.data_name), 
						fn1, 
						Unprimed);
	    CF.h_formula_view_name = "Ext" ^ subc.C.data_name;
	    CF.h_formula_view_arguments = (List.map
		(fun field -> CP.SpecVar((fst field), (snd field), Unprimed)) 
		 (subc.C.data_fields) @ [extension_arg]);
		CF.h_formula_view_pseudo_data = false;
	    CF.h_formula_view_pos = no_pos}) in
      let h_formula_star_h2 = CF.ViewNode({
	    CF.h_formula_view_node = extension_arg;
	    CF.h_formula_view_name = "ExtAll";
	    CF.h_formula_view_arguments = [CP.SpecVar(CP.OType(subc.C.data_name), 
						      subc.C.data_name, 
						      Unprimed)] @
					  [CP.SpecVar(CP.OType(""), 
						      t2, 
						      Unprimed)];
		CF.h_formula_view_pseudo_data = false;
	    CF.h_formula_view_pos = no_pos}) in
	  let base_heap = CF.Star({
	    CF.h_formula_star_h1 = h_formula_star_h1;
	    CF.h_formula_star_h2 = h_formula_star_h2;
	    CF.h_formula_star_pos = no_pos}) in
	  let base_pure = CP.BForm(CP.BConst(true, no_pos)) in
	  let base_type = 
	    CF.TypeAnd({
		       CF.t_formula_and_f1 = CF.TypeSuper({
					   CF.t_formula_sub_type_var = CP.SpecVar(CP.OType(c.C.data_name), 
										  t1, 
										  Unprimed);
					   CF.t_formula_sub_type_type = subc.C.data_name}); 
		       CF.t_formula_and_f2 = CF.TypeSub({
					   CF.t_formula_sub_type_var = CP.SpecVar(CP.OType(""), 
										  t2, 
										  Unprimed);					   
					   CF.t_formula_sub_type_type = subc.C.data_name})}) in		     
	  let formula_or_f1 = CF.Base({
	    CF.formula_base_heap = base_heap;
	    CF.formula_base_pure = base_pure;
	    CF.formula_base_type = base_type;
            CF.formula_base_pos = no_pos}) in
	  let subsubclasses = (look_up_subclasses prog.C.prog_data_decls subc) in
	  if (List.length subsubclasses) > 0 && (List.length rest) > 0 then 
	    CF.Or ({CF.formula_or_f1 = formula_or_f1;
		    CF.formula_or_f2 = 
		       CF.Or ({CF.formula_or_f1 = (local_gen_formula prog c subsubclasses t1 t2 fn1);
			       CF.formula_or_f2 = (local_gen_formula prog c rest t1 t2 fn1 );
			       CF.formula_or_pos = no_pos});
		    CF.formula_or_pos = no_pos})
	  else
          if (List.length subsubclasses) > 0 then 
	    CF.Or ({CF.formula_or_f1 = formula_or_f1;
		    CF.formula_or_f2 = (local_gen_formula prog c subsubclasses t1 t2 fn1);
		    CF.formula_or_pos = no_pos})
          else
	  if (List.length rest) > 0 then 
	    CF.Or ({CF.formula_or_f1 = formula_or_f1;
		    CF.formula_or_f2 = (local_gen_formula prog c rest t1 t2 fn1 );
		    CF.formula_or_pos = no_pos})
          else  
	    formula_or_f1

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(* 
   look-up methods 
*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(* 
   returns the extension fields added by a class compared to its direct parent 
   - as the data is stored right now I don't need it, but I'll keep it in case the system changes
*)
and look_up_ext_fields (parent: C.data_decl) (fields : C.typed_ident list) : C.typed_ident list = 
  match fields with
  | [] -> []  
  | f :: rest -> 
      if not(List.exists 
	       (fun f1 -> (equal_typed_ident f f1))
		parent.C.data_fields)
      then f :: (look_up_ext_fields parent rest)	      
      else (look_up_ext_fields parent rest)	      	    

(* 
   takes a class and returns all the fields from that class:
     - the ones inherited from the parent class
     - the auxiliary ones 
*)
and look_up_all_fields (prog : C.prog_decl) (c : C.data_decl) : C.typed_ident list = 
  if (String.compare c.C.data_parent_name "Object") != 0 then
    let parent = (C.look_up_data_def no_pos prog.C.prog_data_decls c.C.data_parent_name) in 
       c.C.data_fields @ (look_up_all_fields prog parent)
  else			   
    c.C.data_fields

(*
   receives a class and returns all the direct subclasses of that class 
*)

and look_up_subclasses (data_decls : C.data_decl list) (c1 : C.data_decl) : C.data_decl list = 
  match data_decls with
  | [] -> []
  | c2 :: rest ->
      if (String.compare c1.C.data_name c2.C.data_parent_name) = 0 then
	c2 :: (look_up_subclasses rest c1)
      else 
	look_up_subclasses rest c1

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(* 
   some test printing 
*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

let string_of_t_formula_sub_type (tfst : CF.t_formula_sub_type) =
  ("type_var: " ^ (P.string_of_spec_var tfst.CF.t_formula_sub_type_var) ^ " and type: " ^ tfst.CF.t_formula_sub_type_type ^ "\n")

let rec string_of_t_formula (tf : CF.t_formula) = 
  match tf with
  | CF.TypeExact (subtype) -> ("Type exact - " ^ (string_of_t_formula_sub_type subtype) ^ "\n") 
  | CF.TypeSub (subtype) -> ("Subtype - " ^ (string_of_t_formula_sub_type subtype) ^ "\n")    
  | CF.TypeSuper (subtype) -> ("Supertype - " ^ (string_of_t_formula_sub_type subtype) ^ "\n")    	
  | CF.TypeAnd (andf) -> (string_of_t_formula andf.CF.t_formula_and_f1) ^ (string_of_t_formula andf.CF.t_formula_and_f2) 
  | CF.TypeTrue -> "TypeTrue \n"
  | CF.TypeFalse -> "TypeFalse \n"

let rec string_of_formula (f : CF.formula) = 
  match f with
  | CF.Base (fb) -> string_of_t_formula fb.CF.formula_base_type
  | CF.Or (fo) -> (string_of_formula fo.CF.formula_or_f1) ^ (string_of_formula fo.CF.formula_or_f2)
  | _ -> ""

let print_proc_decls (p : C.proc_decl) = 
  print_string "\nTesting the view generator...\n";   
	  print_string ((P.string_of_proc_decl p) ^ 
                       "type from lhs: " ^ (string_of_formula (fst (List.hd p.C.proc_static_specs))) ^
		       "type from rhs: " ^ (string_of_formula (snd (List.hd p.C.proc_static_specs)))
		       );
	  print_string "**********************************************\n"
	
     
let print_view_decls (p : C.view_decl) = 
  print_string "\nTesting the view generator...\n";   
	  print_string (p.C.view_name ^ "<" ^
			(String.concat ", " (List.map P.string_of_spec_var p.C.view_vars)) ^ "> = " ^
			P.string_of_formula p.C.view_formula ^ 
                        "type from rhs: " ^ (string_of_formula p.C.view_formula) ^ "\n");
	  print_string "**********************************************\n"
      


(*
	and add_inv_proc proc inv =
	let add_inv_pre_post (pre, post) =
	let new_pre = IF.mkAnd pre inv (IF.pos_of_formula pre) in
	let new_post = IF.mkAnd post inv (IF.pos_of_formula post) in
	(new_pre, new_post) in
	let new_static_sp = List.map add_inv_pre_post proc.I.proc_static_specs in
	let new_dynamic_sp = List.map add_inv_pre_post proc.I.proc_dynamic_specs in
	{proc with I.proc_static_specs = new_static_sp;
	I.proc_dynamic_specs = new_dynamic_sp}
*)

(*
and add_inv_formula prog f0 inv = match f0 with
  | CF.Or ({CF.formula_or_f1 = f1;
			CF.formula_or_f2 = f2;
			CF.formula_or_pos = pos}) -> begin
	  let if1 = add_inv_formula prog f1 inv in
	  let if2 = add_inv_formula prog f2 inv in
		CF.Or ({CF.formula_or_f1 = if1;
				CF.formula_or_f2 = if2;
				CF.formula_or_pos = pos})
	end
  | CF.Base ({CF.formula_base_heap = h;
			  CF.formula_base_pure = p;
			  CF.formula_base_pos = pos}) -> begin
	  let new_heap = add_inv_heap prog h inv in
	  let new_base = CF.Base ({CF.formula_base_heap = new_heap;
							   CF.formula_base_pure = p;
							   CF.formula_base_pos = pos})
		new_base
	end

and add_inv_heap prog h0 inv = match h0 with
  | CF.Star ({CF.h_formula_star_h1 = h1;
			  CF.h_formula_star_h2 = h2;
			  CF.h_formula_star_pos = pos}) -> begin
	  let ih1 = add_inv_heap prog h1 inv in
	  let ih2 = add_inv_heap prog h2 inv in
		CF.Star ({CF.h_formula_star_h1 = ih1;
				  CF.h_formula_star_h2 = ih2;
				  CF.h_formula_star_pos = pos})
	end
  | HeapNode ({h_formula_heap_name = cname;
			   h_formula_heap_with_inv = with_inv;
			   h_formula_heap_arguments = args;
			   h_formula_heap_pos = pos}) -> begin
	  if with_inv then
		try
		  let cdef = I.look_up_data_def pos prog.I.prog_data_decls cname in
		  let 
		with
		  | Not_found -> 
			  Err.report_error { Err.error_loc = pos;
								 Err.error_text = "invariant-enhanced view is only allowed for node" }
	  else
		h0 (* nothing to be done *)
	end
*)
