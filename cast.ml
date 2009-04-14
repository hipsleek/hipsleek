(*
  Created 21-Feb-2006

  AST for the core language
*)

open Globals

module F = Cformula
module P = Cpure
module Err = Error
module U = Util

type typed_ident = (P.typ * ident)

and prog_decl = { mutable prog_data_decls : data_decl list;
				  mutable prog_view_decls : view_decl list;
				  prog_proc_decls : proc_decl list;
				  mutable prog_left_coercions : coercion_decl list;
				  mutable prog_right_coercions : coercion_decl list }
	
and prog_or_branches = 
		| Prog of prog_decl
		| Branches of (Cpure.formula * ((string*Cpure.formula)list)*(Cpure.spec_var list))
	
and data_decl = { data_name : ident;
				  data_fields : typed_ident list;
				  data_parent_name : ident;
				  data_invs : F.formula list;
				  data_methods : proc_decl list }
	
and view_decl = { view_name : ident; 
				  view_vars : P.spec_var list;
				  view_case_vars : P.spec_var list; (* predicate parameters that are bound to guard of case, but excluding self; subset of view_vars*)
				  view_labels : branch_label list;
				  view_modes : mode list;
				  mutable view_partially_bound_vars : bool list;
				  mutable view_materialized_vars : P.spec_var list; (* view vars that can point to objects *)
				  view_data_name : ident;
				  view_formula : F.struc_formula;
				  view_user_inv : (P.formula * (branch_label * P.formula) list);
				  mutable view_x_formula : (P.formula * (branch_label * P.formula) list);
				  mutable view_addr_vars : P.spec_var list;
				  view_un_struc_formula : Cformula.formula; (*used by the unfold, pre transformed in order to avoid multiple transformations*)
				  view_base_case : (Cpure.formula *(Cpure.formula*((branch_label*Cpure.formula)list))) option;}
	
and proc_decl = { proc_name : ident;
				  proc_args : typed_ident list;
				  proc_return : P.typ;
				  proc_static_specs : Cformula.struc_formula;
				  proc_static_specs_with_pre : Cformula.struc_formula;
				  proc_dynamic_specs : Cformula.struc_formula;
				  proc_dynamic_specs_with_pre : Cformula.struc_formula;
				  proc_by_name_params : P.spec_var list;
				  proc_body : exp option;
				  proc_loc : loc }

and coercion_decl = { coercion_name : ident;
					  coercion_head : F.formula;
					  coercion_body : F.formula;
					  coercion_univ_vars : P.spec_var list; (* list of universally quantified variables. *)
					  (* coercion_proof : exp; *)
					  coercion_head_exist : F.formula;
					  coercion_head_view : ident; 
					  (* the name of the predicate where this coercion can be applied *)
					  coercion_body_view : ident  (* used for cycles checking *) }

and coercion_type = 
  | Left
  | Equiv
  | Right

and exp_assert = { exp_assert_asserted_formula : F.struc_formula option;
				   exp_assert_assumed_formula : F.formula option;
				   exp_assert_pos : loc }

and exp_assign = { exp_assign_lhs : ident;
				   exp_assign_rhs : exp;
				   exp_assign_pos : loc }

and exp_bconst = { exp_bconst_val : bool;
				   exp_bconst_pos : loc }

and exp_bind = { exp_bind_type : P.typ; (* the type of the entire bind construct, i.e. the type of the body *)
				 exp_bind_bound_var : typed_ident;
				 exp_bind_fields : typed_ident list;
				 exp_bind_body : exp;
				 exp_bind_pos : loc }

and exp_block = { exp_block_type : P.typ;
				  exp_block_body : exp;
				  exp_block_local_vars : typed_ident list;
				  exp_block_pos : loc }

and exp_cast = { exp_cast_target_type : P.typ;
				 exp_cast_body : exp;
				 exp_cast_pos : loc }

and exp_cond = { exp_cond_type : P.typ;
				 exp_cond_condition : ident;
				 exp_cond_then_arm : exp;
				 exp_cond_else_arm : exp;
				 exp_cond_pos : loc }

and exp_debug = { exp_debug_flag : bool;
				  exp_debug_pos : loc }

and exp_fconst = { exp_fconst_val : float;
				   exp_fconst_pos : loc }

(* instance call *)
and exp_icall = { exp_icall_type : P.typ;
				  exp_icall_receiver : ident;
				  exp_icall_receiver_type : P.typ;
				  exp_icall_method_name : ident;
				  exp_icall_arguments : ident list;
				  exp_icall_visible_names : P.spec_var list; (* list of visible names at location the call is made *)
				  exp_icall_pos : loc }

and exp_iconst = { exp_iconst_val : int;
				   exp_iconst_pos : loc }

and exp_new = { exp_new_class_name : ident;
				exp_new_parent_name : ident;
				exp_new_arguments : typed_ident list;
				exp_new_pos : loc }

and exp_return = { exp_return_type : P.typ;
				   exp_return_val : exp option;
				   exp_return_pos : loc }

(* static call *)
and exp_scall = { exp_scall_type : P.typ;
				  exp_scall_method_name : ident;
				  exp_scall_arguments : ident list;
				  exp_scall_visible_names : P.spec_var list; (* list of visible names at location the call is made *)
				  exp_scall_pos : loc }

and exp_seq = { exp_seq_type : P.typ;
				exp_seq_exp1 : exp;
				exp_seq_exp2 : exp;
				exp_seq_pos : loc }

and exp_this = { exp_this_type : P.typ;
				 exp_this_pos : loc }

and exp_var = { exp_var_type : P.typ;
				exp_var_name : ident;
				exp_var_pos : loc }

and exp_var_decl = { exp_var_decl_type : P.typ;
					 exp_var_decl_name : ident;
					 exp_var_decl_pos : loc }

and exp_while = { exp_while_condition : ident;
				  exp_while_body : exp;
				  exp_while_spec : Cformula.struc_formula (*multi_spec*);
				  exp_while_pos : loc }

and exp_dprint = { exp_dprint_string : ident;
				   exp_dprint_visible_names : ident list;
				   exp_dprint_pos : loc }

and exp_unfold = { exp_unfold_var : P.spec_var;
				   exp_unfold_pos : loc }

and exp_check_ref = { exp_check_ref_var : ident;
					  exp_check_ref_pos : loc }

and exp_java = { exp_java_code : string;
				 exp_java_pos : loc}

and exp = (* expressions keep their types *)
	(* for runtime checking *)
  | CheckRef of exp_check_ref
  | Java of exp_java
	  (* standard expressions *)
  | Assert of exp_assert
  | Assign of exp_assign
  | BConst of exp_bconst
  | Bind of exp_bind
  | Block of exp_block
  | Cond of exp_cond
  | Cast of exp_cast
  | Debug of exp_debug
  | Dprint of exp_dprint
  | FConst of exp_fconst
	  (*
		| FieldRead of (P.typ * (ident * P.typ) * (ident * int) * loc) 
	  (* v.f --> (type of f, v, (f, position of f in field list), pos *)
		| FieldWrite of ((ident * P.typ) * (ident * int) * ident * loc) 
	  (* field assignment is flattened to form x.f = y only *)
	  *)
  | ICall of exp_icall
  | IConst of exp_iconst
  | New of exp_new
  | Null of loc
  | Print of (int * loc)
  | Return of exp_return
  | SCall of exp_scall
  | Seq of exp_seq
  | This of exp_this
  | Var of exp_var
  | VarDecl of exp_var_decl
  | Unfold of exp_unfold
  | Unit of loc
  | While of exp_while

let distributive_views : string list ref = ref ([])

let distributive c = List.mem c !distributive_views

let add_distributive c = distributive_views := c :: !distributive_views

(* type constants *)

let void_type = P.Prim Void

let int_type = P.Prim Int

let float_type = P.Prim Float

let bool_type = P.Prim Bool

let bag_type = P.Prim Bag

let place_holder = P.SpecVar (int_type, "pholder___", Unprimed)

(* smart constructors *)
(*let mkMultiSpec pos = [ SEnsure {
		sensures_base = Cformula.mkTrue pos;
		sensures_pos = pos;
	}]*)
	
let mkEAssume pos = [Cformula.EAssume  ([],(Cformula.mkTrue pos))]
	
let mkSeq t e1 e2 pos = match e1 with
  | Unit _ -> e2
  | _ -> match e2 with
	  | Unit _ -> e1
	  | _ -> Seq ({exp_seq_type = t; exp_seq_exp1= e1; exp_seq_exp2 = e2; exp_seq_pos = pos})

(* utility functions *)

let is_var (e : exp) = match e with Var _ -> true | _ -> false

let get_var (e : exp) = match e with Var ({exp_var_type = _; exp_var_name = v; exp_var_pos = _}) -> 
  v | _ -> failwith ("get_var: can't get identifier")

let is_block (e : exp) : bool = match e with Block _ -> true | _ -> false

let is_call (e : exp) : bool = match e with SCall _ -> true | _ -> false

let is_new (e : exp) : bool = match e with New _ -> true | _ -> false

let is_unit (e : exp) : bool = match e with Unit _ -> true | _ -> false

let is_cond (e : exp) : bool = match e with Cond _ -> true | _ -> false

let rec type_of_exp (e : exp) = match e with
  | CheckRef _ -> None
  | Java _ -> None
  | Assert _ -> None
  | Assign _ -> Some void_type
  | BConst _ -> Some bool_type
  | Bind ({exp_bind_type = t; 
		   exp_bind_bound_var = _; 
		   exp_bind_fields = _;
		   exp_bind_body = _;
		   exp_bind_pos = _}) -> Some t
  | Block ({exp_block_type = t;
			exp_block_body = _;
			exp_block_local_vars = _;
			exp_block_pos = _}) -> Some t
  | ICall ({exp_icall_type = t;
			exp_icall_receiver = _;
			exp_icall_method_name = _;
			exp_icall_arguments = _;
			exp_icall_visible_names = _;
			exp_icall_pos = _}) -> Some t
  | Cast ({exp_cast_target_type = t}) -> Some t
  | Cond ({exp_cond_type = t;
		   exp_cond_condition = _;
		   exp_cond_then_arm = _;
		   exp_cond_else_arm = _;
		   exp_cond_pos = _}) -> Some t
  | Debug _ -> None
  | Dprint _ -> None
  | FConst _ -> Some float_type
	  (*| FieldRead (t, _, _, _) -> Some t*)
	  (*| FieldWrite _ -> Some void_type*)
  | IConst _ -> Some int_type
  | New ({exp_new_class_name = c; 
		  exp_new_arguments = _; 
		  exp_new_pos = _}) -> Some (P.OType c) (*---- ok? *)
  | Null _ -> Some (P.OType "")
  | Print _ -> None
  | Return ({exp_return_type = t; 
			 exp_return_val = _; 
			 exp_return_pos = _}) -> Some t
  | SCall ({exp_scall_type = t;
			exp_scall_method_name = _;
			exp_scall_arguments = _;
			exp_scall_visible_names = _;
			exp_scall_pos = _}) -> Some t
  | Seq ({exp_seq_type = t; exp_seq_exp1 = _; exp_seq_exp2 = _; exp_seq_pos = _}) -> Some t
  | This ({exp_this_type = t}) -> Some t
  | Var ({exp_var_type = t; exp_var_name = _; exp_var_pos = _}) -> Some t
  | VarDecl _ -> Some void_type
  | Unit _ -> Some void_type
  | While _ -> Some void_type
  | Unfold _ -> Some void_type

and is_transparent e = match e with
  | Assert _ | Assign _ | Debug _ | Print _ -> true
  | _ -> false

let name_of_type (t : P.typ) = match t with
  | P.Prim Int -> "int"
  | P.Prim Bool -> "bool"
  | P.Prim Void -> "void"
  | P.Prim Float -> "float"
  | P.Prim Bag -> "bag"
  | P.OType c -> c

let mingle_name (m : ident) (targs : P.typ list) = 
  let param_tnames = String.concat "~" (List.map name_of_type targs) in
	m ^ "$" ^ param_tnames

let unmingle_name (m : ident) = 
  try
	let i = String.index m '$' in
	  String.sub m 0 i
  with
	| Not_found -> m

let rec look_up_view_def_raw (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> if d.view_name = name then d else look_up_view_def_raw rest name
  | [] -> raise Not_found

let rec look_up_view_def (pos : loc) (defs : view_decl list) (name : ident) = match defs with
  | d :: rest -> 
	  if d.view_name = name then d 
	  else look_up_view_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = name ^ " is not a view definition"}

let rec look_up_data_def pos (ddefs : data_decl list) (name : string) = match ddefs with
  | d :: rest -> 
	  if d.data_name = name then d 
	  else look_up_data_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = name ^ " is not a data/class declaration"}

let rec look_up_parent_name pos ddefs name =
  let ddef = look_up_data_def pos ddefs name in
	ddef.data_parent_name

let rec look_up_proc_def_raw (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def_raw rest name
  | [] -> raise Not_found
	  
let rec look_up_proc_def pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
      if p.proc_name = name then
		p
      else
		look_up_proc_def pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}

let rec look_up_proc_def_no_mingling pos (procs : proc_decl list) (name : string) = match procs with
  | p :: rest ->
	  if unmingle_name p.proc_name = name then p
	  else look_up_proc_def_no_mingling pos rest name
  | [] -> Error.report_error {Error.error_loc = pos;
							  Error.error_text = "procedure " ^ name ^ " is not found"}

(* takes a class and returns the list of all the methods from that class or from any of the parent classes *)
and look_up_all_methods (prog : prog_decl) (c : data_decl) : proc_decl list = match c.data_name with 
  | "Object" -> [] (* it does not have a superclass *)
  | _ ->  
      let cparent_decl = List.find (fun t -> (String.compare t.data_name c.data_parent_name) = 0) prog.prog_data_decls in
        c.data_methods @ (look_up_all_methods prog cparent_decl)  

(*
  coers: a list of coercion rules (proc_coercion must be true)
*)
(*
let rec look_up_distributive_def_raw coers (c : ident) : (F.formula * F.formula) list = match coers with
  | p :: rest -> begin
	  let rec find_formula coercion_list = match coercion_list with
		| (pc, (pre, post)) :: rest ->
			if pc = c then
			  Some (pre, post)
			else
			  find_formula rest
		| [] -> None 
	  in
	  let rest_coers = look_up_distributive_def_raw rest c in
		match find_formula p.proc_coercion_list with
		  | Some (pre, post) -> (pre, post) :: rest_coers
		  | None -> rest_coers
	end
  | [] -> []
*)

let rec look_up_coercion_def_raw coers (c : ident) : coercion_decl list = match coers with
  | p :: rest -> begin
	  let tmp = look_up_coercion_def_raw rest c in
		if p.coercion_head_view = c then p :: tmp
		else tmp
	end
  | [] -> []

let rec callees_of_proc (prog : prog_decl) (name : ident) : ident list =
  let pdef = look_up_proc_def_no_mingling no_pos prog.prog_proc_decls name in
  let callees = 
	match pdef.proc_body with
	  | Some e -> callees_of_exp e
	  | None -> [] 
  in
	callees

and callees_of_exp (e0 : exp) : ident list = match e0 with
  | CheckRef _ -> []
  | Java _ -> []
  | Assert _ -> []
  | Assign ({exp_assign_lhs = _;
			 exp_assign_rhs = e;
			 exp_assign_pos = _}) -> callees_of_exp e
  | BConst _ -> []
  | Bind ({exp_bind_type = _;
		   exp_bind_bound_var = _;
		   exp_bind_fields = _;
		   exp_bind_body = e;
		   exp_bind_pos = _}) -> callees_of_exp e
  | Block ({exp_block_type = _;
			exp_block_body = e;
			exp_block_local_vars = _;
			exp_block_pos = _}) -> callees_of_exp e
  | Cast ({exp_cast_body = e}) -> callees_of_exp e
  | Cond ({exp_cond_type = _;
		   exp_cond_condition = _;
		   exp_cond_then_arm = e1;
		   exp_cond_else_arm = e2;
		   exp_cond_pos = _}) -> U.remove_dups (callees_of_exp e1 @ callees_of_exp e2)
  | Debug _ -> []
  | Dprint _ -> []
  | FConst _ -> []
	  (*| FieldRead _ -> []*)
	  (*| FieldWrite _ -> []*)
  | ICall ({exp_icall_type = _;
			exp_icall_receiver = _;
			exp_icall_method_name = n;
			exp_icall_arguments = _;
			exp_icall_visible_names = _; 
			exp_icall_pos = _}) -> [unmingle_name n] (* to be fixed: look up n, go down recursively *)
  | IConst _ -> []
  | New _ -> []
  | Null _ -> []
  | Print _ -> []
  | Return ({exp_return_type = _;
			 exp_return_val = oe;
			 exp_return_pos = _}) -> 
	  begin
		match oe with
		  | Some e -> callees_of_exp e
		  | None -> []
	  end
  | SCall ({exp_scall_type = _;
			exp_scall_method_name = n;
			exp_scall_arguments = _;
			exp_scall_visible_names = _; 
			exp_scall_pos = _}) -> [unmingle_name n]
  | Seq ({exp_seq_type = _;
		  exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2;
		  exp_seq_pos = _}) -> U.remove_dups (callees_of_exp e1 @ callees_of_exp e2)
  | This _ -> []
  | Var _ -> []
  | VarDecl _ -> []
  | Unit _ -> []
  | While ({exp_while_condition = _;
			exp_while_body = e;
			exp_while_spec = _;
			exp_while_pos = _ }) -> callees_of_exp e (*-----???*)
  | Unfold _ -> []

let procs_to_verify (prog : prog_decl) (names : ident list) : ident list =
  let tmp1 = List.map (callees_of_proc prog) names in
  let tmp2 = names @ (List.concat tmp1) in
  let tmp3 = U.remove_dups tmp2 in
	tmp3


(*************************************************************)
(* Building the graph representing the class hierarchy       *)
(*************************************************************)

type ch_node = { ch_node_name : ident;
				 mutable ch_node_class : data_decl option;
				 mutable ch_node_coercion : proc_decl option (* coercion rule to the parent class *) }

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
	CH.add_edge class_hierarchy (CH.V.create {ch_node_name = cdef.data_name; 
											  ch_node_class = None; 
											  ch_node_coercion = None})
	  (CH.V.create {ch_node_name = cdef.data_parent_name; 
					ch_node_class = None; 
					ch_node_coercion = None}) in
  let _ = List.map add_edge prog.prog_data_decls in
	if TraverseCH.has_cycle class_hierarchy then begin
		print_string ("Class hierarchy has cycles");
		failwith ("Class hierarchy has cycles");
	  end 
	else begin
		(* now add class definitions in *)
		let update_node node = 
		  if not (node.ch_node_name = "") then
			let cdef = look_up_data_def no_pos prog.prog_data_decls node.ch_node_name in
			  node.ch_node_class <- Some cdef
		in
		  CH.iter_vertex update_node class_hierarchy
	  end

(*
  subnode: the sub class object to be converted to super class object plus
           extesions
  cdefs: list of class definition, going from super class to sub class
*)
let rec generate_extensions (subnode : F.h_formula_data) cdefs0 pos : F.h_formula = match cdefs0 with
  | cdef1 :: _ -> begin
	  (* generate the first node *)
	  let sub_tvar = List.hd subnode.F.h_formula_data_arguments in
	  let sub_ext_var = List.hd (List.tl subnode.F.h_formula_data_arguments) in
		(* call gen_exts with sup_ext_var to link the 
		   head node with extensions *)
	  let heap_args = List.tl (List.tl subnode.F.h_formula_data_arguments) in
	  let n = List.length cdef1.data_fields in
	  let to_sup, rest_fields = U.split_at heap_args n in
	  let ext_name = gen_ext_name subnode.F.h_formula_data_name cdef1.data_name in
	  (*--- 09.05.2000 *)
	  let fn1 = fresh_var_name ext_name pos.Lexing.pos_lnum in
		(*let _ = (print_string ("\n[cast.ml, line 556]: fresh name = " ^ fn1 ^ "!!!!!!!!!!!\n\n")) in*)
		(*09.05.2000 ---*)
	  let sup_ext_var = P.SpecVar (P.OType ext_name, fn1, Unprimed) in
	  let sup_h = F.DataNode ({F.h_formula_data_node = subnode.F.h_formula_data_node;
							   F.h_formula_data_name = cdef1.data_name;
							   F.h_formula_data_arguments = sub_tvar :: sup_ext_var :: to_sup;
							   F.h_formula_data_pos = pos}) in
		(* generate extensions for the rest of the fields *)
	  let rec gen_exts top_p link_p args cdefs : F.h_formula = match cdefs with
		| cdef1 :: cdef2 :: rest -> begin
			let i = List.length cdef2.data_fields in
			let to_ext, rest_fields = U.split_at args i in
			let ext_name = gen_ext_name cdef1.data_name cdef2.data_name in
			  if U.empty rest then
				let ext_h = F.DataNode ({F.h_formula_data_node = top_p;
										 F.h_formula_data_name = ext_name;
										 F.h_formula_data_arguments = link_p :: to_ext;
										 F.h_formula_data_pos = pos}) in
				  ext_h
			  else
				let ext_link_name = gen_ext_name cdef2.data_name ((List.hd rest).data_name) in
				(*--- 09.05.2000 *)
	  		let fn2 = fresh_var_name ext_name pos.Lexing.pos_lnum in
				(*let _ = (print_string ("\n[cast.ml, line 579]: fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n\n")) in*)
				(*09.05.2000 ---*)
				let ext_link_p = P.SpecVar (P.OType ext_link_name, fn2, Unprimed) in
				let ext_h = F.DataNode ({F.h_formula_data_node = top_p;
										 F.h_formula_data_name = ext_name;
										 F.h_formula_data_arguments = ext_link_p :: to_ext;
										 F.h_formula_data_pos = pos}) in
				let rest_exts = gen_exts ext_link_p link_p rest_fields (cdef2 :: rest) in
				let ext = F.mkStarH ext_h rest_exts pos in
				  ext
		  end
		| _ -> F.HTrue in
	  let exts = gen_exts sup_ext_var sub_ext_var rest_fields cdefs0 in
	  let res = F.mkStarH sup_h exts pos in
		res
	end
  | _ -> F.HTrue


(*
  Checks if c1 is subtype of c2 or the other way and returns the 
  list of classes going from c1 to c2 (or c2 to c1), including c2.

  If the first component of the result is true, c1 is subtype of c2.
  If it is false, c2 is subtype of c1
*)

let find_classes (c1 : ident) (c2 : ident) : (bool * data_decl list) = 
  let v1 = CH.V.create {ch_node_name = c1; ch_node_class = None; ch_node_coercion = None} in
  let v2 = CH.V.create {ch_node_name = c2; ch_node_class = None; ch_node_coercion = None} in
	try
	  let path, _ = PathCH.shortest_path class_hierarchy v1 v2 in
		(true, List.rev (List.map (fun e -> U.unsome ((CH.E.dst e).ch_node_class)) path))
	with
	  | Not_found -> 
		  try
			let path, _ = PathCH.shortest_path class_hierarchy v2 v1 in
			  (false, List.rev (List.map (fun e -> U.unsome ((CH.E.dst e).ch_node_class)) path))
		  with
			| Not_found -> failwith ("find_classes: " ^ c1 ^ " and " ^ c2 ^ " are not related!")


and sub_type (t1 : P.typ) (t2 : P.typ) = match t1 with
  | P.Prim _ -> t1 = t2
  | P.OType c1 -> match t2 with
	  | P.Prim _ -> false
	  | P.OType c2 ->
		  if c1 = c2 then true
		  else if c1 = "" then true (* t1 is null in this case *)
		  else 
			let v1 = CH.V.create {ch_node_name = c1; 
								  ch_node_class = None; 
								  ch_node_coercion = None} in
			let v2 = CH.V.create {ch_node_name = c2; 
								  ch_node_class = None; 
								  ch_node_coercion = None} in
			  try
				let _ = PathCH.shortest_path class_hierarchy v1 v2 in
				  true
			  with
				| Not_found -> false

				
				
and exp_to_check (e:exp) :bool = match e with
  | CheckRef _
  | Debug _
  | Dprint _
  | Bind _
  | Seq _
  | Unfold _
  | Unit _
  | Print _
  | VarDecl _
  | Cast _
  | Block _
  | FConst _
  | Assert _ 
  | Cond _
  | Java _ -> false
  
  | BConst _
  | Assign _
  | ICall _
  | IConst _
  | While _ 
  | This _
  | Var _
  | Null _
  | New _
  | Return _
  | SCall _ -> true
  
  
and pos_of_exp (e:exp) :Lexing.position = match e with
  | CheckRef b -> b.exp_check_ref_pos
  | BConst b -> b.exp_bconst_pos
  | Bind b -> b.exp_bind_pos
  | Cast b -> b.exp_cast_pos
  | Debug b -> b.exp_debug_pos
  | Dprint b -> b.exp_dprint_pos
  | Assign b -> b.exp_assign_pos
  | FConst b -> b.exp_fconst_pos
  | ICall b -> b.exp_icall_pos
  | IConst b -> b.exp_iconst_pos
  | Print (_,b) -> b
  | Seq b -> b.exp_seq_pos
  | VarDecl b -> b.exp_var_decl_pos
  | Unfold b -> b.exp_unfold_pos
  | Unit b -> b
  | This b -> b.exp_this_pos
  | Var b -> b.exp_var_pos
  | Null b -> b
  | Cond b -> b.exp_cond_pos
  | Block b -> b.exp_block_pos
  | Java b  -> b.exp_java_pos
  | Assert b -> b.exp_assert_pos
  | New b -> b.exp_new_pos
  | Return b -> b.exp_return_pos
  | SCall b -> b.exp_scall_pos
  | While b -> b.exp_while_pos