(*
  Created 19-Feb-2006

  Input AST
*)

open Globals

module F = Iformula
module P = Ipure
module Err = Error
module CP = Cpure

type typ =
  | Prim of prim_type
  | Named of ident (* named type, could be enumerated or object *)
  | Array of (typ * int option) (* base type and optional dimension *)
	  
and typed_ident = (typ * ident)

type prog_decl = { mutable prog_data_decls : data_decl list;
				   prog_enum_decls : enum_decl list;
				   mutable prog_view_decls : view_decl list;
				   prog_proc_decls : proc_decl list;
				   mutable prog_coercion_decls : coercion_decl list }

and data_decl = { data_name : ident;
				  data_fields : (typed_ident * loc) list;
				  data_parent_name : ident;
				  data_invs : F.formula list;
				  data_methods : proc_decl list }

and view_decl = { view_name : ident; 
				  mutable view_data_name : ident;
				  view_vars : ident list;
				  view_labels : branch_label list;
				  view_modes : mode list;
				  mutable view_typed_vars : (CP.typ * ident) list;
				  view_invariant : (P.formula * (branch_label * P.formula) list);
				  view_formula : Iformula.struc_formula }

and enum_decl = { enum_name : ident;
				  enum_fields : (ident * int option) list } 
	(* a field of an enum may optionally be initialized by an integer *)

and param_modifier =
  | NoMod
  | RefMod

and param = { param_type : typ;
			  param_name : ident;
			  param_mod : param_modifier;
			  param_loc : loc }

(*
and multi_spec = spec list

and spec = 
	| SCase of scase_spec
	| SRequires of srequires_spec
	| SEnsure of sensures_spec
	
and scase_spec = 
	{
			scase_branches : (Ipure.formula * multi_spec ) list ;
			scase_pos : loc 
		}
	
and srequires_spec = 
	{		
		srequires_explicit_inst : (ident * primed) list;
		srequires_implicit_inst : (ident * primed) list;
		srequires_base : Iformula.formula;
		srequires_continuation : multi_spec;
		srequires_pos : loc
		}	
	
and sensures_spec = 
	{
		sensures_base : Iformula.formula;
		sensures_pos : loc
	}
*)
and proc_decl = { proc_name : ident;
				  mutable proc_mingled_name : ident;
				  mutable proc_data_decl : data_decl option; (* the class containing the method *)
				  proc_constructor : bool;
				  proc_args : param list;
				  proc_return : typ;
				  proc_static_specs : Iformula.struc_formula;
				  proc_dynamic_specs : Iformula.struc_formula;
				  proc_body : exp option;
				  proc_loc : loc }

and coercion_decl = { coercion_type : coercion_type;
					  coercion_name : ident;
					  coercion_head : F.formula;
					  coercion_body : F.formula;
					  coercion_proof : exp }
and coercion_type = 
  | Left
  | Equiv
  | Right

and uni_op = 
  | OpUMinus
  | OpPreInc
  | OpPreDec
  | OpPostInc
  | OpPostDec
  | OpNot

and bin_op = 
  | OpPlus
  | OpMinus
  | OpMult
  | OpDiv
  | OpMod
  | OpEq
  | OpNeq
  | OpLt
  | OpLte
  | OpGt
  | OpGte
  | OpLogicalAnd
  | OpLogicalOr
  | OpIsNull
  | OpIsNotNull

and assign_op =
  | OpAssign
  | OpPlusAssign
  | OpMinusAssign
  | OpMultAssign
  | OpDivAssign
  | OpModAssign

and exp_assert = { exp_assert_asserted_formula : F.struc_formula option;
				   exp_assert_assumed_formula : F.formula option;
				   exp_assert_pos : loc }

and exp_assign = { exp_assign_op : assign_op;
				   exp_assign_lhs : exp;
				   exp_assign_rhs : exp;
				   exp_assign_pos : loc }

and exp_binary = { exp_binary_op : bin_op;
				   exp_binary_oper1 : exp;
				   exp_binary_oper2 : exp;
				   exp_binary_pos : loc }

and exp_bind = { exp_bind_bound_var : ident;
				 exp_bind_fields : ident list;
				 exp_bind_body : exp;
				 exp_bind_pos : loc }

and exp_block = { exp_block_body : exp;
				  exp_block_pos : loc }

and exp_bool_lit = { exp_bool_lit_val : bool;
					 exp_bool_lit_pos : loc }

and exp_call_nrecv = { exp_call_nrecv_method : ident;
					   exp_call_nrecv_arguments : exp list;
					   exp_call_nrecv_pos : loc }

and exp_call_recv = { exp_call_recv_receiver : exp;
					  exp_call_recv_method : ident;
					  exp_call_recv_arguments : exp list;
					  exp_call_recv_pos : loc }

and exp_cast = { exp_cast_target_type : typ;
				 exp_cast_body : exp;
				 exp_cast_pos : loc }

and exp_cond = { exp_cond_condition : exp;
				 exp_cond_then_arm : exp;
				 exp_cond_else_arm : exp;
				 exp_cond_pos : loc }

and exp_const_decl = { exp_const_decl_type : typ;
					   exp_const_decl_decls : (ident * exp * loc) list;
					   exp_const_decl_pos : loc }

and exp_debug = { exp_debug_flag : bool;
				  exp_debug_pos : loc }

and exp_float_lit = { exp_float_lit_val : float;
					  exp_float_lit_pos : loc }

and exp_int_lit = { exp_int_lit_val : int;
					exp_int_lit_pos : loc }

and exp_java = { exp_java_code : string;
				 exp_java_pos : loc }

and exp_member = { exp_member_base : exp;
				   exp_member_fields : ident list;
				   exp_member_pos : loc }

and exp_new = { exp_new_class_name : ident;
				exp_new_arguments : exp list;
				exp_new_pos : loc }

and exp_return = { exp_return_val : exp option;
				   exp_return_pos : loc }

and exp_seq = { exp_seq_exp1 : exp;
				exp_seq_exp2 : exp;
				exp_seq_pos : loc }

and exp_this = { exp_this_pos : loc }

and exp_throw = { exp_throw_type : ident;
				  exp_throw_pos : loc }

and exp_unary = { exp_unary_op : uni_op;
				  exp_unary_exp : exp;
				  exp_unary_pos : loc }

and exp_var = { exp_var_name : ident;
				exp_var_pos : loc }

and exp_var_decl = { exp_var_decl_type : typ;
					 exp_var_decl_decls : (ident * exp option * loc) list;
					 exp_var_decl_pos : loc }

and exp_while = { exp_while_condition : exp;
				  exp_while_body : exp;
				  exp_while_specs : Iformula.struc_formula (*multi_spec*);
				  exp_while_pos : loc }

and exp_dprint = { exp_dprint_string : string;
				   exp_dprint_pos : loc }

and exp_unfold = { exp_unfold_var : (string * primed);
				   exp_unfold_pos : loc } 

and exp =
  | Assert of exp_assert
  | Assign of exp_assign
  | Binary of exp_binary
  | Bind of exp_bind
  | Block of exp_block
  | BoolLit of exp_bool_lit
  | Break of loc
  | CallRecv of exp_call_recv
  | CallNRecv of exp_call_nrecv
  | Cast of exp_cast
  | Cond of exp_cond
  | ConstDecl of exp_const_decl
  | Continue of loc
  | Debug of exp_debug
  | Dprint of exp_dprint
  | Empty of loc
  | FloatLit of exp_float_lit
  | IntLit of exp_int_lit
  | Java of exp_java
  | Member of exp_member
  | New of exp_new
  | Null of loc
  | Return of exp_return
  | Seq of exp_seq
  | This of exp_this
(*  | Throw of exp_throw *)
  | Unary of exp_unary
  | Unfold of exp_unfold
  | Var of exp_var
  | VarDecl of exp_var_decl
  | While of exp_while

(* type constants *)

let void_type = Prim Void

let int_type = Prim Int

let float_type = Prim Float

let bool_type = Prim Bool

(* utility functions *)

let set_proc_data_decl (p : proc_decl) (d : data_decl) = p.proc_data_decl <- Some d

let name_of_type (t : typ) = match t with
  | Prim Int -> "int"
  | Prim Bool -> "bool"
  | Prim Void -> "void"
  | Prim Float -> "float"
  | Prim Bag -> "bag"
  | Named c -> c
  | Array _ -> "Array"

let are_same_type (t1 : typ) (t2 : typ) = t1 = t2 (*TODO: this function should be removed, use the one in Cast instead *)

let is_named_type (t : typ) = match t with
  | Named _ -> true
  | _ -> false

let is_null (e : exp) : bool = match e with
  | Null _ -> true
  | _ -> false

let is_var (e : exp) : bool = match e with
  | Var _ -> true
  | _ ->false

let get_exp_pos (e0 : exp) : loc = match e0 with
  | Assert e -> e.exp_assert_pos
  | Assign e -> e.exp_assign_pos
  | Binary e -> e.exp_binary_pos
  | Bind e -> e.exp_bind_pos
  | Block e -> e.exp_block_pos
  | BoolLit e -> e.exp_bool_lit_pos
  | Break p -> p
  | CallRecv e -> e.exp_call_recv_pos
  | CallNRecv e -> e.exp_call_nrecv_pos
  | Cast e -> e.exp_cast_pos
  | Cond e -> e.exp_cond_pos
  | ConstDecl e -> e.exp_const_decl_pos
  | Continue p -> p
  | Debug e -> e.exp_debug_pos
  | Dprint e -> e.exp_dprint_pos
  | Empty p -> p
  | FloatLit e -> e.exp_float_lit_pos
  | IntLit e -> e.exp_int_lit_pos
  | Java e -> e.exp_java_pos
  | Member e -> e.exp_member_pos
  | New e -> e.exp_new_pos
  | Null p -> p
  | Return e -> e.exp_return_pos
  | Seq e -> e.exp_seq_pos
  | This e -> e.exp_this_pos
  | Unary e -> e.exp_unary_pos
  | Var e -> e.exp_var_pos
  | VarDecl e -> e.exp_var_decl_pos
  | While e -> e.exp_while_pos
  | Unfold e -> e.exp_unfold_pos
	  
		

and mkSpecTrue pos = Iformula.mkETrue pos
	(*[SRequires {
		srequires_explicit_inst = [];
		srequires_implicit_inst = [];
		srequires_base  = Iformula.mkTrue pos;
		srequires_continuation =  [SEnsure{
			sensures_base =  Iformula.mkTrue pos;
			sensures_pos = pos
			}];
		srequires_pos = pos
		}]	*)
		
		
(* look up functions *)

let rec look_up_data_def pos (defs : data_decl list) (name : ident) = match defs with
  | d :: rest -> if d.data_name = name then d else look_up_data_def pos rest name
  | [] -> Err.report_error {Err.error_loc = pos; Err.error_text = "no type declaration named " ^ name ^ " is found"}

and look_up_parent_name pos ddefs name =
  let ddef = look_up_data_def pos ddefs name in
	ddef.data_parent_name

and look_up_data_def_raw (defs : data_decl list) (name : ident) = match defs with
  | d :: rest -> if d.data_name = name then d else look_up_data_def_raw rest name
  | [] -> raise Not_found

and look_up_view_def_raw (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> if d.view_name = name then d else look_up_view_def_raw rest name
  | [] -> raise Not_found

and look_up_enum_def pos (defs : enum_decl list) (name : ident) = match defs with
  | d :: rest -> if d.enum_name = name then d else look_up_enum_def pos rest name
  | [] -> Err.report_error {Err.error_loc = pos; Err.error_text = "no enum declaration named " ^ name ^ " is found"}

and look_up_enum_def_raw (defs : enum_decl list) (name : ident) = match defs with
  | d :: rest -> if d.enum_name = name then d else look_up_enum_def_raw rest name
  | [] -> raise Not_found

and look_up_proc_def_raw (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def_raw rest name
  | [] -> raise Not_found
	  
and look_up_proc_def_mingled_name (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_mingled_name = name then
		p
      else
		look_up_proc_def_mingled_name rest name
  | [] -> raise Not_found

(*
(* takes a proc and returns the class where it is declared *)
  and look_up_proc_class_mingled_name (classes : class_decl list) (name : string) = match classes with
  | c :: rest ->
  if (List.exists (fun t -> t.proc_mingled_name =  name) c.class_methods) then c
  else (look_up_proc_class_mingled_name rest name)
  | []	-> raise Not_found    
*)

(* takes a class and returns the list of all the methods from that class or from any of the parent classes *)
and look_up_all_methods (prog : prog_decl) (c : data_decl) : proc_decl list = match c.data_parent_name with 
  | "Object" -> c.data_methods (* it does not have a superclass *)
  | _ ->  
      let cparent_decl = List.find (fun t -> (String.compare t.data_name c.data_parent_name) = 0) prog.prog_data_decls in
        c.data_methods @ (look_up_all_methods prog cparent_decl)  

and look_up_all_fields (prog : prog_decl) (c : data_decl) : (typed_ident * loc) list = 
  let current_fields = c.data_fields in
	if (String.compare c.data_name "Object") = 0 then
	  []
	else
      let parent = (look_up_data_def no_pos prog.prog_data_decls c.data_parent_name) in 
		current_fields @ (look_up_all_fields prog parent)

(*
  Find view_data_name. Look at each branch, find the data self points to.
  If there are conflicts, report as errors.
*)

and data_name_of_view (view_decls : view_decl list) (f0 : Iformula.struc_formula) : ident = 

		let handle_list_res  (e:string list): string = 
					let r = List.filter (fun c-> (String.length c)>0) e in
						if (List.length r == 0 ) then ""
							else
								let h = List.hd r in
								let tl = List.tl r in
								if (List.for_all (fun c-> (String.compare c h)==0 ) tl) then (List.hd r)
													else "" in
		
		let rec data_name_in_ext (f:Iformula.ext_formula):ident = match f with
			| Iformula.EAssume b -> data_name_of_view1 view_decls b
			| Iformula.ECase b-> handle_list_res (List.map (fun (c1,c2) -> data_name_of_view  view_decls c2) b.Iformula.formula_case_branches)
			| Iformula.EBase b-> handle_list_res ([(data_name_of_view1 view_decls b.Iformula.formula_ext_base)]@
												  [(data_name_of_view view_decls b.Iformula.formula_ext_continuation)])
			in
			handle_list_res (List.map data_name_in_ext f0) 

and data_name_of_view1 (view_decls : view_decl list) (f0 : F.formula) : ident = 
  let rec get_name_from_heap (h0 : F.h_formula) : ident option = match h0 with
	| F.HeapNode h ->
		let (v, p), c = h.F.h_formula_heap_node, h.F.h_formula_heap_name in
		  if v = self then
			(* if c is a view, use the view's data name recursively.
			   Otherwise (c is data) use c *)
			try
			  let vdef = look_up_view_def_raw view_decls c in
				if String.length (vdef.view_data_name) > 0 then
				  Some vdef.view_data_name
				else
				  Some (data_name_of_view view_decls vdef.view_formula)
			with
			  | Not_found -> Some c
		  else
			None
	| F.Star h ->
		let h1, h2, pos = h.F.h_formula_star_h1, h.F.h_formula_star_h2, h.F.h_formula_star_pos in
		let n1 = get_name_from_heap h1 in
		let n2 = get_name_from_heap h2 in
		  if Util.is_some n1 && Util.is_some n2 then
			report_error pos ("multiple occurrences of self as heap nodes in one branch are not allowed")
		  else if Util.is_some n1 then
			n1
		  else
			n2
	| _ -> None 
  and get_name (f0 : F.formula) = match f0 with
	| F.Or f ->
		let f1, f2, pos = f.F.formula_or_f1, f.F.formula_or_f2, f.F.formula_or_pos in
		let n1 = get_name f1 in
		let n2 = get_name f2 in
		  if Util.is_some n1 && Util.is_some n2 then
			let nn1 = Util.unsome n1 in
			let nn2 = Util.unsome n2 in
			  if nn1 = nn2 then
				Some nn1
			  else
				report_error pos ("two branches define self with different node types")
		  else if Util.is_some n1 then
			n1
		  else
			n2
	| F.Base f ->
		let h, p, pos = f.F.formula_base_heap, f.F.formula_base_pure, f.F.formula_base_pos in
		  get_name_from_heap h
	| F.Exists f ->
		let h, p, pos = f.F.formula_exists_heap, f.F.formula_exists_pure, f.F.formula_exists_pos in
		  get_name_from_heap h
  in
  let data_name = match get_name f0 with
	| Some nn -> nn
	| None -> ""
  in
	data_name

and contains_field (e0 : exp) : bool = match e0 with
  | Assert _ -> false
  | Assign _ -> false
  | Binary e -> (contains_field e.exp_binary_oper1) || (contains_field e.exp_binary_oper2)
  | Bind e -> contains_field e.exp_bind_body
  | Block e -> contains_field e.exp_block_body
  | BoolLit _ -> false
  | Break _ -> false
  | CallRecv e -> 
	  contains_field e.exp_call_recv_receiver 
	  || (List.exists contains_field e.exp_call_recv_arguments)
  | CallNRecv e -> List.exists contains_field e.exp_call_nrecv_arguments
  | Cast e -> contains_field e.exp_cast_body
  | Cond e ->
	  let e1 = e.exp_cond_condition in
	  let e2 = e.exp_cond_then_arm in
	  let e3 = e.exp_cond_else_arm in
		(contains_field e1) || (contains_field e2) || (contains_field e3)
  | ConstDecl _ -> false
  | Continue _ -> false
  | Debug _ -> false
  | Dprint _ -> false
  | Empty _ -> false
  | FloatLit _ -> false
  | IntLit _ -> false
  | Java _ -> false
  | Member _ -> true
  | New e -> List.exists contains_field e.exp_new_arguments
  | Null _ -> false
  | Return e -> 
	  let ret_val = e.exp_return_val in
		if Util.is_some ret_val then contains_field (Util.unsome ret_val) else false
  | Seq e -> (contains_field e.exp_seq_exp1) || (contains_field e.exp_seq_exp2)
  | This e -> false
  | Unary e -> contains_field e.exp_unary_exp
  | Var _ -> false
  | VarDecl _ -> false (* this can't happen on RHS anyway *)
  | While e -> (contains_field e.exp_while_condition) || (contains_field e.exp_while_body)
  | Unfold _ -> false


(* smart constructors *)

let mkConstDecl t d p = ConstDecl { exp_const_decl_type = t;
									exp_const_decl_decls = d;
									exp_const_decl_pos = p }

and mkVarDecl t d p = VarDecl { exp_var_decl_type = t;
								exp_var_decl_decls = d;
								exp_var_decl_pos = p }

and mkSeq e1 e2 l = match e1 with
  | Empty _ -> e2
  | _ -> match e2 with
	  | Empty _ -> e1
	  | _ -> Seq { exp_seq_exp1 = e1;
				   exp_seq_exp2 = e2;
				   exp_seq_pos = l }

and mkAssign op lhs rhs pos = 	Assign { exp_assign_op = op;
										 exp_assign_lhs = lhs;
										 exp_assign_rhs = rhs;
										 exp_assign_pos = pos }

and mkBinary op oper1 oper2 pos = Binary { exp_binary_op = op;
										   exp_binary_oper1 = oper1;
										   exp_binary_oper2 = oper2;
										   exp_binary_pos = pos }

and mkUnary op oper pos = Unary { exp_unary_op = op;
								  exp_unary_exp = oper;
								  exp_unary_pos = pos }

(*************************************************************)
(* Building the graph representing the class hierarchy       *)
(*************************************************************)

type ch_node = { ch_node_name : ident
				   (* mutable ch_node_class : data_decl option *) }
	
module CD = struct
  type t = ch_node
  let compare c1 c2 = compare c1.ch_node_name c2.ch_node_name
  let hash c = Hashtbl.hash c.ch_node_name
  let equal c1 c2 = (c1.ch_node_name = c2.ch_node_name)
end

module CH = Graph.Imperative.Digraph.Concrete(CD)
module TraverseCH = Graph.Traverse.Dfs(CH)

module W = struct
  type label = CH.E.label
  type t = int
  let weight x = 1
  let zero = 0
  let add = (+)
  let compare = compare
end

module PathCH = Graph.Path.Dijkstra(CH)(W)

let class_hierarchy = CH.create ()

let build_hierarchy (prog : prog_decl) =
  (* build the class hierarchy *)
  let add_edge (cdef : data_decl) = 
	CH.add_edge class_hierarchy (CH.V.create {ch_node_name = cdef.data_name})
	  (CH.V.create {ch_node_name = cdef.data_parent_name}) in
  let _ = List.map add_edge prog.prog_data_decls in
	if TraverseCH.has_cycle class_hierarchy then begin
	  print_string ("Error: Class hierarchy has cycles\n");
	  failwith ("Class hierarchy has cycles\n");
	end (* else begin
	  (* now add class definitions in *)
		   let update_node node = 
		   let cdef = look_up_data_def no_pos prog.prog_data_decls node.ch_node_name in
		   node.ch_node_class <- Some cdef
		   in
		   CH.iter_vertex update_node class_hierarchy
		   end
		*)

(*
  see if c1 is sub class of c2 and what are the classes in between.
*)
let find_classes (c1 : ident) (c2 : ident) : ident list = 
  let v1 = CH.V.create {ch_node_name = c1} in
  let v2 = CH.V.create {ch_node_name = c2} in
  let path, _ = PathCH.shortest_path class_hierarchy v1 v2 in
	List.map (fun e -> (CH.E.dst e).ch_node_name) path

let sub_type (t1 : typ) (t2 : typ) = 
  let c1 = name_of_type t1 in
  let c2 = name_of_type t2 in
	if c1 = c2 || (is_named_type t2 && c1 = "") then true
	else false
	  (*
		try
		let _ = find_classes c1 c2 in
		true
		with
		| Not_found -> false
	  *)

let compatible_types (t1 : typ) (t2 : typ) = sub_type t1 t2 || sub_type t2 t1
