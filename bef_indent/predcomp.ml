#include "xdebug.cppo"
open VarGen
(*
  Predicate compiler: compiles predicates to executable code.

  Each predicate c is associated with a class c_checker that
  has a "traverse" method that traverses the heap covered by
  c. c_checker has fields for all input parameters of c. 
  
  "traverse" returns set of pairs, where each pair consists
  of a set of references (a footprint) and an output parameter
  assignment of type c_output. c_output has fields for all
  output parameters of c.

  For now, "traverse" returns only (at most) one pair.

  TODO:
  - how to handle existential variables: ex v. H & v = f(...) & F(t)

  - insert check for accessibility when traversing p::c<> where c is
  object type: 
    + add field named "accessor", add asignment 
    + <new_checker>.accessor = accessor when setting up new checker
*)

open Globals
open Cformula
open Iast

module CP = Cpure
module C = Cast
module Err = Error
module H = Hashtbl

type pred_output = ident (* name of the variable containing the result *)

and heap_output = (ident * (ident * ident)) list
(* 
   and entry [v -> (e, f)] in heap_output means
   variable v should be replaced by field access e.f 
   where e is the output of a predicate that has been
   evaluated and f is an output parameter thereof.
*)

(* used for unbound var *)
exception Unbound_var of string

type var_map_entry =
	(* 
	   bindings from pure part. It can contain unbound subexpressions.
	*)
  | PExp of CP.exp 
	  (*
		bindings from heap part, basically field accesses, either from
		objects, or from recursive checker.

		Third component: whether this field is partially bound.
	  *)
  | HExp of (ident * ident * bool)

and var_map = (ident, var_map_entry) H.t

(* 
   if there is a constraint, for example, x::node<next = r> * r::node<val = v>, then
   output [(x, r), (r, v)]. The idea is to perform a topological sort, and assign
   variables in the sequence x (not assigned), r, v.
*)
and var_order = (ident * ident) list

(*
  Convert a DNF formula to a list of disjuncts
*)
let rec formula_to_disjuncts (f0 : formula) : formula list = match f0 with
  | Or ({formula_or_f1 = f1;
		 formula_or_f2 = f2}) -> begin
	  let l1 = formula_to_disjuncts f1 in
	  let l2 = formula_to_disjuncts f2 in
	  l1 @ l2
  end
  | _ -> [f0]

(*
  Convert a *-joined heap formula to a list of heap nodes
*)
and heap_to_nodes (h0 : h_formula) : h_formula list = match h0 with
  | Star ({h_formula_star_h1 = h1;
		   h_formula_star_h2 = h2}) -> begin
	  let l1 = heap_to_nodes h1 in
	  let l2 = heap_to_nodes h2 in
	  l1 @ l2
  end
  | _ -> [h0]

and class_name_of_view (c : ident) : ident = c ^ "_Checker"

and is_in_vars (e : CP.exp) (vars : ident list) : bool =
  if CP.is_var e then
	let tmp = CP.to_var e in
	let sv = CP.name_of_spec_var tmp in
	List.mem sv vars
  else false

and is_in_svars (e : CP.exp) (svars : CP.spec_var list) : bool = 
  if CP.is_var e then
	let tmp = CP.to_var e in
	CP.mem tmp svars
  else
	false

and aug_class_name (t : typ) = match t with
  | UNK  -> 	
        Error.report_error {Error.error_loc = no_pos; 
        Error.error_text = "unexpected UNKNOWN type"}
  | Pointer _ -> "Pointer"
  | Named c -> c ^ "Aug"
  | Int -> "IntAug"
  | INFInt -> "INFIntAug"
  | AnnT -> "AnnAug"
  | RelT _ -> "RelAug"
  | FuncT _ -> "FuncAug"
  | UtT -> "UtTAug"
  | Bool -> "BoolAug"
  | Float -> "FloatAug"
  | NUM -> "NUMAug"
  | FORM -> "FORMAug"
  | Void -> "void"
  | Tree_sh -> "tree_share"
  | Tup2 _ -> "Tup2"
  | Bptyp -> "Bperm"
  | HpT -> "HeapP"
  (* | SLTyp -> "SLAug" *)
  | (BagT t) -> "Set("^(aug_class_name t)^")"
  | (TVar i) -> "TVar["^(string_of_int i)^"]"
  | List t -> "List("^(aug_class_name t)^")"
  | Array (et, _) -> aug_class_name et ^ "[]" (* An Hoa *)

(*
  split view parameters according to their modes:
  the first returned list has mode ModeIn, the second ModeOut
*)
and split_params_mode (view_vars : CP.spec_var list) (modes : mode list) : (CP.spec_var list * CP.spec_var list) = match view_vars, modes with
  | (var :: rest1, m :: rest2) -> begin
	  let tmp1, tmp2 = split_params_mode rest1 rest2 in
	  if m = ModeIn then (var :: tmp1, tmp2)
	  else (tmp1, var :: tmp2)
  end
  | ([], []) -> ([], [])
  | _ -> failwith ("split_params_mode: two input lists must be of the same length.")

(* 
   generate fields from a set of spec_vars

   field_vars : spec vars to be converted to fields
   pbvars : partially bound output parameters
*)
and gen_fields (field_vars : CP.spec_var list) (pbvars : CP.spec_var list) pos =
  (* generator for in and fully bound out parameters *)
  let rec helper vvars = match vvars with
	| var :: rest1 -> begin
		let rest_result = helper rest1 in
		(* An Hoa MARKED *)
		let rec ityp_of_ctyp ct = match ct with
		  | Named c -> Named c
		  | Array (et, _) -> ityp_of_ctyp et 
		  | p -> p in
		let t = ityp_of_ctyp (CP.type_of_spec_var var) in
		(* An Hoa END *)
		let fld = ((t, CP.name_of_spec_var var), pos, false, [gen_field_ann t](* F_NO_ANN *)) in (* An Hoa : Add [false] for inline record. TODO revise *)
		fld :: rest_result
	end
	| [] -> [] in
  (* generator for partially bound out parameters *)
  let rec helper2 (CP.SpecVar (t, v, p)) =
	let cls_name = aug_class_name t in
	let atype = Named cls_name in
	((atype, v), pos, false,[gen_field_ann atype] (* F_NO_ANN *))  (* An Hoa : Add [false] for inline record. TODO revise *) in 
  let pb_fields = List.map helper2 pbvars in
  let normal_vvars = Gen.BList.difference_eq CP.eq_spec_var field_vars pbvars in
  let normal_fields = helper normal_vvars in
  pb_fields @ normal_fields

(*
  Compilation of a formula will generate a class/data declaration
  and a traverse function. Make it a program
*)

let main_result = Var ({exp_var_name = "main_result";
						exp_var_pos = no_pos})

(**********************************************************************************)
(* First attempt.

(*
  Each formula is compiled into a class. Predicate definitions
  are put to class with name c_checker where c is the name of
  the predicate.
*)
let rec compile_view (prog : C.prog_decl) (vdef : C.view_decl) : data_decl =
  let pos = pos_of_formula vdef.C.view_formula in
  let fields = ((Named vdef.C.view_data_name, self), pos) :: (gen_fields vdef pos) intype filter text
  let in_params, out_params = split_params_mode vdef.C.view_vars vdef.C.view_modes in
  let in_names = List.map CP.name_of_spec_var in_params in
  let out_names = List.map CP.name_of_spec_var out_params in
  let combined_exp = compile_formula prog vdef.C.view_formula (self :: in_names) out_names in
  let check_proc = { proc_name = "traverse";
					 proc_mingled_name = "traverse";
					 proc_data_decl = None;
					 proc_constructor = false;
					 proc_args = [];
					 proc_return = Named "Set";
					 proc_static_specs = [];
					 proc_dynamic_specs = [];
					 proc_body = Some combined_exp;
					 proc_loc = no_pos } in
  let ddef = { data_name = class_name_of_view vdef.C.view_name;
			   data_fields = fields;
			   data_parent_name = "Object";
			   data_invs = [];
			   data_methods = [check_proc] } 
  in
	check_proc.proc_data_decl <- Some ddef;
	ddef

and compile_formula (prog : C.prog_decl) (f0 : formula) (input_vars : ident list) (output_vars : ident list) : exp =
  let disjs = formula_to_disjuncts f0 in
  let pos = pos_of_formula f0 in
  let disj_results = List.map (fun disj -> compile_disjunct prog disj input_vars output_vars) disjs in
  let combined_exp = combine_disjuncts disj_results pos in
  let ret_null = Return ({exp_return_val = Some (Null pos);
						  exp_return_pos = pos}) in
  let seq = Seq ({exp_seq_exp1 = combined_exp;
				  exp_seq_exp2 = ret_null;
				  exp_seq_pos = pos}) in
	seq

(*
  If a disjunct returns a non-null result set, add it to the
  main result.

  Deterministic case (disjunctions return only one address set):
  In case more than one disjunct succeeds, choose the first one.
  
  result_i = <compile_disjunct i>;
  if (result_i != null) return result_i;
*)
and combine_disjuncts disj_results pos : exp = match disj_results with
  | (e, output) :: rest -> begin
	  let outputexp = Var ({exp_var_name = output;
							exp_var_pos = pos}) in
	  let test = Binary ({exp_binary_op = OpIsNotNull;
						  exp_binary_oper1 = outputexp;
						  exp_binary_oper2 = Null pos;
						  exp_binary_pos = pos}) in
	  let ret = Return ({exp_return_val = Some outputexp;
						 exp_return_pos = pos}) in
	  let cond = Cond ({exp_cond_condition = test;
						exp_cond_then_arm = ret;
						exp_cond_else_arm = Empty pos;
						exp_cond_pos = pos}) in
	  let seq1 = Seq ({exp_seq_exp1 = e;
					   exp_seq_exp2 = cond;
					   exp_seq_pos = pos}) in
	  let rest_e = combine_disjuncts rest pos in
	  let seq2 = Seq ({exp_seq_exp1 = seq1;
					   exp_seq_exp2 = rest_e;
					   exp_seq_pos = pos}) in
		seq2
	end
  | [] -> Empty pos

and compile_disjunct (prog : C.prog_decl) (f0 : formula) (input_vars : ident list) (output_vars : ident list) : (exp * pred_output) = match f0 with
  | Base ({formula_base_heap = h;
		   formula_base_pure = pure;
		   formula_base_pos = pos})
  | Exists ({formula_exists_heap = h;
			 formula_exists_pure = pure;
			 formula_exists_pos = pos}) -> begin
	  let () = print_string ("\n\tCompiling disjunct: " ^ (Cprinter.string_of_formula f0) ^ "\n") in
		(* Compile heap for now *)
	  let h_exp, h_out, h_map = compile_heap prog f0 input_vars h in
	  let evars_sv, _ = split_quantifiers f0 in
	  let evars = List.map CP.name_of_spec_var evars_sv in
	  let gvars = (List.map fst h_map) @ input_vars in
	  let hvars = List.map CP.name_of_spec_var (h_fv h) in
	  let pure', pmap = gen_exists_subst pure evars gvars hvars in
	  let o_assignments, o_tests = 
		compile_pure prog f0 input_vars output_vars h_map pmap pure' in
	  let assign = match o_assignments with
		| Some e -> e
		| None -> Empty pos in
	  let test = match o_tests with
		| Some e -> e
		| None -> BoolLit ({exp_bool_lit_val = true;
							exp_bool_lit_pos = pos}) in
	  let reset = Assign ({exp_assign_op = OpAssign;
						   exp_assign_lhs = Var ({exp_var_name = h_out;
												  exp_var_pos = pos});
						   exp_assign_rhs = Null pos;
						   exp_assign_pos = pos}) in
	  let cond = Cond ({exp_cond_condition = test;
						exp_cond_then_arm = assign;
						exp_cond_else_arm = reset;
						exp_cond_pos = pos}) in
	  let seq = Seq ({exp_seq_exp1 = h_exp;
					  exp_seq_exp2 = cond;
					  exp_seq_pos = pos}) in
		(seq, h_out)
	end
  | _ -> failwith ("compile_disjunct: disjunctive formula")

(*
  compile_heap generates code that traverses the heap and computes
  output parameter values.

  Consider the following example:

  root::node<l, r> * l::tree<n1> * r::tree<n2> & 0 <= n1 - n2 <= 1

  What should output be like?
  Output should be a map from variables to (object name, field name)

  So checking the heap part of the above formula will generate the 
  following map:
  [n1 -> (lout, n), n2 -> (rout, n)]
  where lout and rout are outputs of checking l::tree<n1> and r::tree<n2>,
  respectively.

  Note that the "exp" component of the returned result is actually
  a set of pairs, each pair consists of a set of references, and a
  mapping of type heap_output. The compilation of * needs to generate
  Java code to traverse the set and combine the results.

  For now: exp only return (at most) one pair
*)
and compile_heap (prog : C.prog_decl) disj (input_vars : ident list) (h0 : h_formula) : (exp * ident * heap_output) = match h0 with
  | Star ({h_formula_star_h1 = h1;
		   h_formula_star_h2 = h2;
		   h_formula_star_pos = pos}) -> begin
	  (*
		id1 == <output of h1>
		id2 == <output of h2>
		Set output;
		if (id1 == null) output = null;
		else if (id2 == null) output = null;
		else if (rtc.Slrc.intersect(id1, id2)) output = null;
		else {
		output = id1; any problem with this aliasing? x::node<> * x::node<> shouldn't be a problem
		output.addAll(id2);
		}
	  *)
	  let e1, id1, o1 = compile_heap prog disj input_vars h1 in
	  let e2, id2, o2 = compile_heap prog disj input_vars h2 in
	  let id1_var = Var ({exp_var_name = id1;
						  exp_var_pos = pos}) in
	  let id2_var = Var ({exp_var_name = id2;
						  exp_var_pos = pos}) in
	  let id1_is_null = Binary ({exp_binary_op = OpIsNull;
								 exp_binary_oper1 = id1_var;
								 exp_binary_oper2 = Null pos;
								 exp_binary_pos = pos}) in
	  let id2_is_null = Binary ({exp_binary_op = OpIsNull;
								 exp_binary_oper1 = id2_var;
								 exp_binary_oper2 = Null pos;
								 exp_binary_pos = pos}) in
	  let out_name = fresh_name () in
	  let out_var = Var ({exp_var_name = out_name;
						  exp_var_pos = pos}) in
	  let var_decl = VarDecl ({ exp_var_decl_type = Named "Set";
								exp_var_decl_decls = [(out_name, None, pos)];
								exp_var_decl_pos = pos}) in
	  let output_null = Assign ({exp_assign_op = OpAssign;
								 exp_assign_lhs = out_var;
								 exp_assign_rhs = Null pos;
								 exp_assign_pos = pos}) in
		(* both results are nonnull, and disjoint *)
	  let tmp1 = Assign ({exp_assign_op = OpAssign;
						  exp_assign_lhs = out_var;
						  exp_assign_rhs = id1_var;
						  exp_assign_pos = pos}) in
	  let tmp2 = CallRecv ({exp_call_recv_receiver = out_var;
							exp_call_recv_method = "add";
							exp_call_recv_arguments = [id2_var];
							exp_call_recv_pos = pos}) in
	  let seq1 = Seq ({exp_seq_exp1 = tmp1;
					   exp_seq_exp2 = tmp2;
					   exp_seq_pos = pos}) in
		(* null tests *)
	  let intersect_test = CallNRecv ({exp_call_nrecv_method = "intersect";
									   exp_call_nrecv_arguments = [id1_var; id2_var];
									   exp_call_nrecv_pos = pos}) in
	  let cond1 = Cond ({exp_cond_condition = intersect_test;
						 exp_cond_then_arm = output_null;
						 exp_cond_else_arm = seq1;
						 exp_cond_pos = pos}) in
	  let cond2 = Cond ({exp_cond_condition = id2_is_null;
						 exp_cond_then_arm = output_null;
						 exp_cond_else_arm = cond1;
						 exp_cond_pos = pos}) in
	  let cond3 = Cond ({exp_cond_condition = id1_is_null;
						exp_cond_then_arm = output_null;
						exp_cond_else_arm = cond2;
						exp_cond_pos = pos}) in
		(* Combine all results *)
	  let seq2 = Seq ({exp_seq_exp1 = var_decl;
					   exp_seq_exp2 = cond3;
					   exp_seq_pos = pos}) in
	  let seq3 = Seq ({exp_seq_exp1 = e2;
					   exp_seq_exp2 = seq2;
					   exp_seq_pos = pos}) in
	  let seq4 = Seq ({exp_seq_exp1 = e1;
					   exp_seq_exp2 = seq3;
					   exp_seq_pos = pos}) in
		(seq4, out_name, o1 @ o2)
	end
  | DataNode ({h_formula_data_node = p;
			   h_formula_data_name = c;
			   h_formula_data_arguments = vs;
			   h_formula_data_pos = pos}) -> begin
	  (*
		p::c<vs>

		Set output = new HashSet();
		output.add(p);
	  *)
	  let new_exp = New ({exp_new_class_name = "HashSet";
						  exp_new_arguments = [];
						  exp_new_pos = pos}) in
	  let out_ident = fresh_name () in
	  let out_var = Var ({exp_var_name = out_ident;
						  exp_var_pos = pos}) in
	  let res_var = VarDecl ({exp_var_decl_type = Named "Set";
							  exp_var_decl_decls = 
								 [(out_ident, Some new_exp, pos)];
							  exp_var_decl_pos = pos }) in
	  let add_exp = CallRecv ({exp_call_recv_receiver = out_var;
							   exp_call_recv_method = "add";
							   exp_call_recv_arguments = 
								  [Var ({exp_var_name = CP.name_of_spec_var p;
										 exp_var_pos = pos})];
							   exp_call_recv_pos = pos}) in
	  let seq = Seq ({exp_seq_exp1 = res_var;
					  exp_seq_exp2 = add_exp;
					  exp_seq_pos = pos}) in
		(seq, out_ident, [])
	end
  | ViewNode ({h_formula_view_node = p;
			   h_formula_view_name = c;
			   h_formula_view_arguments = vs;
			   h_formula_view_modes = modes;
			   h_formula_view_pos = pos}) -> begin
	  (*
		Make a call. Set up inputs and all that.
		Now how to do that?

		c_checker ckr = new c_checker();
		ckr.root = p;
		Set< Pair<Set<Object>, c_output> > poutput = ckr.traverse();
		return <poutput, map>;

		What's the problem here? 
		poutput is a set of pairs, but it is in a Java's Set.
		How can we break it up here?
	  *)
	  let vdef = x_add C.look_up_view_def_raw prog.C.prog_view_decls c in
	  let cls = class_name_of_view c in
	  let new_checker = New ({exp_new_class_name = cls;
							  exp_new_arguments = [];
							  exp_new_pos = pos}) in
	  let new_checker_name = fresh_name () in
	  let new_checker_var = Var ({exp_var_name = new_checker_name;
								  exp_var_pos = pos}) in
	  let new_checker_decl = VarDecl ({exp_var_decl_type = Named cls;
									   exp_var_decl_decls = 
										  [(new_checker_name, Some new_checker, pos)];
									   exp_var_decl_pos = no_pos}) in		
		(* Call checker *)
	  let call_checker = CallRecv ({exp_call_recv_receiver = new_checker_var;
									exp_call_recv_method = "traverse";
									exp_call_recv_arguments = [];
									exp_call_recv_pos = pos}) in
	  let out_name = fresh_name () in
	  let out_decl = VarDecl ({exp_var_decl_type = Named "Set";
							   exp_var_decl_decls = [(out_name, Some call_checker, pos)];
							   exp_var_decl_pos = no_pos}) in
		(* Set up inputs *)
		(* helper: Constructs a list of assignments to set up inputs *)
	  let rec helper params modes : exp list = match params, modes with
		| (param :: rest1, m :: rest2) -> begin
			let rest = helper rest1 rest2 in
			  if m = ModeIn then
				let e = gen_input_exp prog disj input_vars [] (CP.name_of_spec_var p) pos in
				let lhs = Member ({exp_member_base = new_checker_var;
								   exp_member_fields = [CP.name_of_spec_var param];
								   exp_member_pos = pos}) in
				let assignment = Assign ({exp_assign_op = OpAssign;
										  exp_assign_lhs = lhs;
										  exp_assign_rhs = e;
										  exp_assign_pos = pos}) in
				  assignment :: rest
			  else rest
		  end
		| [], [] -> [] 
		| _ -> failwith ("compile_heap: params and modes are supposed to be lists with the same length.") in
	  let self_var = CP.SpecVar (CP.OType vdef.C.view_data_name, self, Unprimed) in
	  let tmp1 = helper (self_var :: vdef.C.view_vars) (ModeIn :: vdef.C.view_modes) in
	  let helper2 e1 e2 = mkSeq e2 e1 pos in
	  let init_inputs = List.fold_left helper2 out_decl tmp1 in
		(* compute the heap_output map *)
	  let args = List.map CP.name_of_spec_var vs in
	  let out_map = gen_output_map vdef.C.view_vars vdef.C.view_modes new_checker_name args in
	  let seq1 = Seq ({exp_seq_exp1 = new_checker_decl;
					   exp_seq_exp2 = init_inputs;
					   exp_seq_pos = pos}) in
		(seq1, out_name, out_map)
	end
  | HTrue ->
	  let fname = fresh_name () in
	  let new_exp = New ({exp_new_class_name = "HashSet";
						  exp_new_arguments = [];
						  exp_new_pos = no_pos}) in
	  let var = VarDecl ({exp_var_decl_type = Named "Set";
						  exp_var_decl_decls = [(fname, Some new_exp, no_pos)];
						  exp_var_decl_pos = no_pos}) 
	  in
		(var, fname, [])
  | HFalse -> 
	  let fname = fresh_name () in
	  let var = VarDecl ({exp_var_decl_type = Named "Set";
						  exp_var_decl_decls = [(fname, Some (Null no_pos), no_pos)];
						  exp_var_decl_pos = no_pos}) 
	  in
		(var, fname, [])

and gen_output_map (fargs : CP.spec_var list) (modes : mode list) pout (args : ident list) : heap_output = 
  match (fargs, modes, args) with
	| ((f :: rest1), (m :: rest2), (a :: rest3)) -> begin
		let tmp1 = 
		  if m = ModeIn then []
		  else [(a, (pout, CP.name_of_spec_var f))] in
		let tmp2 = gen_output_map rest1 rest2 pout rest3 in
		  tmp1 @ tmp2
	  end
	| ([], [], []) -> []
	| _ -> failwith ("gen_output_map: the three input lists are supposed to be of the same length")

(*
  For formula F = root::node<l, r> * l::tree<n1> * r::tree<n2>

  gen_input_exp F "l" = "root.left"
  gen_input_exp F "r" = "root.right"

  How to do that?

  See if below works well enough

  Just one level for now.
*)

(*
  input_vars0 : set of program-visible variables
  var0 : the (existentially quantified) variable that
         we are searching for
*)
and gen_input_exp (prog : C.prog_decl) (disj : formula) (input_vars0 : ident list) (hmap : heap_output) (var0 : ident) pos : exp =
  if List.mem var0 input_vars0 then 
	(*
	  A more complete version should consider equalities in disj.
	*)
	Var ({exp_var_name = var0;
		  exp_var_pos = pos})
  else
	match disj with
	  | Base ({formula_base_heap = h;
			   formula_base_pure = pure})
	  | Exists ({formula_exists_heap = h;
				 formula_exists_pure = pure}) ->
			(* find the alias set containing var0 *)
		  let eqns = Solver.ptr_equations pure in
		  let asets = Solver.alias eqns in
		  let aset = Solver.get_aset asets (CP.SpecVar (CP.OType "", var0, Unprimed)) in 
		  let var0_alias = var0 :: (List.map CP.name_of_spec_var aset) in
		  let rec helper1 input_vars : exp option = match input_vars with
			| (input_var :: rest) -> begin
				let s = gen_input_object prog h input_var var0_alias in
				  match s with
					| Some e -> s
					| None -> helper1 rest
			  end
			| [] -> None
		  in
		  let oe = helper1 input_vars0 in
			begin
			  match oe with 
				| Some e -> e
				| None ->
					let oe2 = gen_input_view hmap var0 pos in
					  match oe2 with
						| Some e2 -> e2
						| None -> (* Out of luck *)
							let msg = "\nFile \"" ^ pos.Lexing.pos_fname 
							  ^ "\", line " ^ (string_of_int pos.Lexing.pos_lnum) ^ ": "
							  ^ "gen_input_exp: cannot generate input expression for variable " 
							  ^ var0 
							in
							  failwith msg
			end
	  | _ -> failwith ("gen_input_exp: disjunctive formula is not expected here.")

and gen_input_view (hmap : heap_output) (var : ident) pos : exp option =
  try
	let b, f = List.assoc var hmap in
	let e = Member ({exp_member_base = Var ({exp_var_name = b;
											 exp_var_pos = pos});
					 exp_member_fields = [f];
					 exp_member_pos = pos}) in
	  Some e
  with
	| Not_found -> None

and gen_input_object (prog : C.prog_decl) (h0 : h_formula) (ivar : ident) (var_alias : ident list) : exp option = match h0 with
  | Star ({h_formula_star_h1 = h1;
		   h_formula_star_h2 = h2;
		   h_formula_star_pos = pos}) ->
	  let s1 = gen_input_object prog h1 ivar var_alias in
		if Gen.is_some s1 then s1
		else gen_input_object prog h2 ivar var_alias
  | DataNode ({h_formula_data_node = p;
			   h_formula_data_name = c;
			   h_formula_data_arguments = vs;
			   h_formula_data_pos = pos}) -> begin
	  if CP.name_of_spec_var p = ivar then
		try
		  let i = Gen.BList.find_index (fun v -> List.mem (CP.name_of_spec_var v) var_alias) vs in
		  let ddef = C.look_up_data_def pos prog.C.prog_data_decls c in
		  let fname = snd (List.nth ddef.C.data_fields ((fst i) - 2)) in (* minus the first two parameters *)
		  let base = Var ({exp_var_name = ivar;
						   exp_var_pos = pos}) in
		  let e = Member ({exp_member_base = base;
						   exp_member_fields = [fname];
						   exp_member_pos = pos}) in
			Some e
		with
		  | Not_found -> None
	  else None
	end
  | ViewNode _ -> None
  | HTrue | HFalse -> None

(*
  pure : input pure formula
  evars : existentially quantified variables
  gvars : groundable variables
  hvars : variables appearing in the heap part. 
  Formulas mentioninng hvars can't be considered for substitution
  
  return value:
  - substitution of existential variables of form v = f(...)
  - the remaining part of pure after removing all formulas making substitutions
*)
and gen_exists_subst (pure : CP.formula) (evars : ident list) (gvars : ident list) (hvars : ident list) : (CP.formula * (ident * CP.exp) list) = match pure with
  | CP.And (p1, p2, pos) ->
	  let tmp1, subst1 = gen_exists_subst p1 evars gvars hvars in
	  let tmp2, subst2 = gen_exists_subst p2 evars gvars hvars in
	  let tmp3 = CP.mkAnd tmp1 tmp2 pos in
	  let subst = subst1 @ subst2 in
		(tmp3, subst)
  | CP.BForm bf -> 
	  let bf1, subst = gen_exists_subst_bform bf evars gvars hvars in
		(CP.BForm bf1, subst)
  | _ -> (pure, [])

and gen_exists_subst_bform (bf : CP.b_formula) (evars : ident list) (gvars : ident list) (hvars : ident list) : (CP.b_formula * (ident * CP.exp) list) = match bf with
  | CP.EqMax (em, e1, e2, pos) -> begin
	  if CP.is_var em then
		let sv = CP.to_var em in
		let tmp = CP.name_of_spec_var sv in
		  if List.mem tmp evars then
			let fvars = List.map CP.name_of_spec_var ((CP.afv e1) @ (CP.afv e2)) in
			  if List.for_all (fun v -> List.mem v gvars) fvars 
				&& (not (List.exists (fun v -> List.mem v hvars) (tmp :: fvars)))
			  then
				(CP.BConst (true, pos), [(tmp, CP.Max (e1, e2, pos))])
			  else
				(bf, [])
		  else
			(bf, [])
	  else
		(bf, [])
	end
  | CP.EqMin (em, e1, e2, pos) -> begin
	  if CP.is_var em then
		let sv = CP.to_var em in
		let tmp = CP.name_of_spec_var sv in
		  if List.mem tmp evars then
			let fvars = List.map CP.name_of_spec_var ((CP.afv e1) @ (CP.afv e2)) in
			  if List.for_all (fun v -> List.mem v gvars) fvars 
				&& (not (List.exists (fun v -> List.mem v hvars) (tmp :: fvars)))
			  then
				(CP.BConst (true, pos), [(tmp, CP.Min (e1, e2, pos))])
			  else
				(bf, [])
		  else
			(bf, [])
	  else
		(bf, [])
	end
  | CP.Eq (e1, e2, pos) -> begin
	  if is_in_vars e1 evars then
		let tmp = CP.name_of_spec_var (CP.to_var e1) in
		let fvars = List.map CP.name_of_spec_var (CP.afv e2) in
		  if List.for_all (fun v -> List.mem v gvars) fvars 
			&& (not (List.exists (fun v -> List.mem v hvars) (tmp :: fvars)))
		  then
			(CP.BConst (true, pos), [(tmp, e2)])
		  else
			(bf, [])
	  else if is_in_vars e2 evars then
		gen_exists_subst_bform (CP.Eq (e2, e1, pos)) evars gvars hvars
	  else (bf, [])
	end
  | _ -> (bf, [])

(*
  Pure formula compilation.
*)
and compile_pure (prog : C.prog_decl) (disj : formula) (input_vars : ident list) (output_vars : ident list) (hmap : heap_output) (pmap : (ident * CP.exp) list) (p0 : CP.formula) : (exp option * exp option) = match p0 with
  | CP.And (p1, p2, pos) ->  begin
	  let oa1, ot1 = compile_pure prog disj input_vars output_vars hmap pmap p1 in
	  let oa2, ot2 = compile_pure prog disj input_vars output_vars hmap pmap p2 in
	  let oa = match oa1, oa2 with
		| None, None -> None
		| None, Some a 
		| Some a, None -> Some a
		| Some a1, Some a2 ->
			let a = mkSeq a1 a2 pos in
			  Some a in
	  let ot = match ot1, ot2 with
		| None, None -> None
		| None, Some t
		| Some t, None -> Some t
		| Some t1, Some t2 -> 
			let t = Binary ({exp_binary_op = OpLogicalAnd;
							 exp_binary_oper1 = t1;
							 exp_binary_oper2 = t2;
							 exp_binary_pos = pos}) in
			  Some t
	  in
		(oa, ot)
	end
  | CP.BForm bf -> begin
	  compile_bform prog disj hmap pmap input_vars output_vars bf
	end
  | _ -> failwith ((Cprinter.string_of_pure_formula p0) ^ " is not supported")

(*
  The first component consists of assignments to output parameters.
  The second component consists of tests of input parameters.
*)
and compile_bform prog disj hmap pmap input_vars output_vars bf0 : (exp option * exp option) = match bf0 with
  | CP.Eq (e1, e2, pos) -> begin
	  if is_in_vars e1 output_vars then
		(* sv is an output parameters, generate assignments *)
		let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
		let lhs = Var ({exp_var_name = (CP.name_of_spec_var (CP.to_var e1));
						exp_var_pos = pos}) in
		let ce = Assign ({exp_assign_op = OpAssign;
						  exp_assign_lhs = lhs;
						  exp_assign_rhs = ce2;
						  exp_assign_pos = pos}) in
		  (Some ce, None)
	  else if is_in_vars e2 output_vars then
		compile_bform prog disj hmap pmap input_vars output_vars (CP.Eq (e2, e1, pos))
	  else
		(None, Some (gen_pure_test prog disj hmap pmap input_vars bf0))
	end
  | CP.EqMin (em, e1, e2, pos) when is_in_vars em output_vars -> begin
	  let tmp1 = CP.Min (e1, e2, pos) in
	  let tmp2 = CP.Eq (em, tmp1, pos) in
		compile_bform prog disj hmap pmap input_vars output_vars tmp2
	end
  | CP.EqMax (em, e1, e2, pos) when is_in_vars em output_vars -> begin
	  let tmp1 = CP.Max (e1, e2, pos) in
	  let tmp2 = CP.Eq (em, tmp1, pos) in
		compile_bform prog disj hmap pmap input_vars output_vars tmp2
	end
  | _ -> (None, Some (gen_pure_test prog disj hmap pmap input_vars bf0))

and gen_pure_test prog disj hmap pmap input_vars (bf0 : CP.b_formula) : exp = match bf0 with
  | CP.Eq (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpEq;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce
	end
  | CP.Lte (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpLte;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce	  
	end
  | CP.Lt (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpLt;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce	  
	end
  | CP.Gte (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpGte;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce	  
	end
  | CP.Gt (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpGt;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce	  
	end
  | CP.EqMax (emax, e1, e2, pos) -> begin
	  let cem = compile_pure_exp prog disj hmap pmap input_vars emax in
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let maxe = CallNRecv ({exp_call_nrecv_method = "Math.max";
							 exp_call_nrecv_arguments = [ce1; ce2];
							 exp_call_nrecv_pos = pos}) in
	  let ce = Binary ({exp_binary_op = OpEq;
						exp_binary_oper1 = cem;
						exp_binary_oper2 = maxe;
						exp_binary_pos = pos}) in
		ce
	end
  | CP.EqMin (emax, e1, e2, pos) -> begin
	  let cem = compile_pure_exp prog disj hmap pmap input_vars emax in
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let maxe = CallNRecv ({exp_call_nrecv_method = "Math.min";
							 exp_call_nrecv_arguments = [ce1; ce2];
							 exp_call_nrecv_pos = pos}) in
	  let ce = Binary ({exp_binary_op = OpEq;
						exp_binary_oper1 = cem;
						exp_binary_oper2 = maxe;
						exp_binary_pos = pos}) in
		ce
	end
  | _ -> failwith ("gen_pure_test: " ^ (Cprinter.string_of_b_formula bf0) ^ " is not supported")

and compile_pure_exp prog disj hmap pmap input_vars e0 : exp = match e0 with
  | CP.Add (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpPlus;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce
	end
  | CP.Subtract (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = Binary ({exp_binary_op = OpMinus;
						exp_binary_oper1 = ce1;
						exp_binary_oper2 = ce2;
						exp_binary_pos = pos}) in
		ce
	end
  | CP.Max (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = CallNRecv ({exp_call_nrecv_method = "Math.max";
						   exp_call_nrecv_arguments = [ce1; ce2];
						   exp_call_nrecv_pos = pos}) in
		ce
	end
  | CP.Min (e1, e2, pos) -> begin
	  let ce1 = compile_pure_exp prog disj hmap pmap input_vars e1 in
	  let ce2 = compile_pure_exp prog disj hmap pmap input_vars e2 in
	  let ce = CallNRecv ({exp_call_nrecv_method = "Math.min";
						   exp_call_nrecv_arguments = [ce1; ce2];
						   exp_call_nrecv_pos = pos}) in
		ce
	end
  | CP.Var (sv, pos) -> begin
	  let var = CP.name_of_spec_var sv in
		try
		  let e = gen_input_exp prog disj input_vars hmap var pos in
			e
		with
		  | _ -> 
			  try
				let subst_e = List.assoc var pmap in
				  compile_pure_exp prog disj hmap pmap input_vars subst_e
			  with
				| _ -> 
					Err.report_error {Err.error_loc = pos;
									  Err.error_text = "compile_pure_exp: cannot compile " 
						^ (Cprinter.string_of_formula_exp e0)}
	end
  | CP.IConst (i, pos) ->
	  IntLit ({exp_int_lit_val = i;
			   exp_int_lit_pos = pos})
  | CP.Null pos ->
	  Null pos
  | _ -> failwith ((Cprinter.string_of_formula_exp e0) ^ " is not supported")

End of first attempt *)

(**********************************************************************************)


(*
  Generate bindings for existential variables 
  based on the pure part.
  
  ex v, v1 . H[v] & v = v1 & v = a & v = p

  Result:
  vmap is modified to include new bindings
  the result is pure, less the bindings that have been
  added to vmap. (Other bindings will be turned to tests.)

  Variables are either i) existentially quantified, ii)
  input, iii) output.

  var_map maps existentially quantified and output variables
  to groudable terms, maps input vars to themselves. After 
  building the map, if there is a variable not present in 
  the map, the formula is rejected.

  v1 = v2
  v1 = term

  v1 = v2:
  - If both are not bound, create two map entries for v1 and v2,
    both points to the same var_map_entry.
  - If one is bound, make the other points to the same entry.
  - If both are bound, need a test. (e.g. v1 = t1 & v2 = t2 & v1 = v2)

  Make things simple now:
  For v = t, where v is a variable that needs to be instantiated, then
  t is a groundable term. There's no transitive equation.
*)

let disj_count = ref 1
let stub_branch_point_id s = Some (-1,s) 

let return_true pos = Return ({exp_return_val = Some
							  (BoolLit ({exp_bool_lit_val = true;
										 exp_bool_lit_pos = pos}));
								exp_return_path_id = stub_branch_point_id "pred_comp_generated";
						   exp_return_pos = pos})

let return_false pos = Return ({exp_return_val = Some
							   (BoolLit ({exp_bool_lit_val = false;
										  exp_bool_lit_pos = pos}));
								exp_return_path_id = stub_branch_point_id "pred_comp_generated";
							exp_return_pos = pos})

let cur_color pos = { param_type = Named "long";
					  param_name = "curColor";
					  param_mod = NoMod;
					  param_loc = pos }
  
let new_color pos = {(cur_color pos) with param_name = "newColor"}

let cur_color_exp pos = Var ({exp_var_name = "curColor";
							  exp_var_pos = pos})

let new_color_exp pos = Var ({exp_var_name = "newColor";
							  exp_var_pos = pos})
  
let next_disj_count () =
  let t = !disj_count in
	disj_count := !disj_count + 1;
	t

(* for compilation of precondition *)
let precond_output = ref ([] : CP.spec_var list)

(*
  Split a pure formula into two parts: assignments to unbound vars
  to go to vmap, and test (return value).
*)
let rec gen_bindings_pure (pure : CP.formula) (unbound_vars : CP.spec_var list) (vmap : var_map) : CP.formula = match pure with
  | CP.And (p1, p2, pos) -> 
	let p1' = gen_bindings_pure p1 unbound_vars vmap in
	let p2' = gen_bindings_pure p2 unbound_vars vmap in
	let p = CP.mkAnd p1' p2' pos in
	p
  | CP.BForm ((CP.Eq (e1, e2, pos), il), _) -> begin
      if is_in_svars e1 unbound_vars then
	let tmp = CP.name_of_spec_var (CP.to_var e1) in
	(* if tmp is already bound, this formula will be turned into a test. *)
	try
	  let be1 = H.find vmap tmp in
	  if is_in_svars e2 unbound_vars then
	    (* 
	       to handle cases like ex v. x::node<val = v> & v = s,
	       where s is output parameters. 
	    *)
	    (*
	      gen_bindings_pure (CP.BForm (CP.Eq (e2, e1, pos))) unbound_vars vmap
	    *)
	    let tmp2 = CP.name_of_spec_var (CP.to_var e2) in
	    H.add vmap tmp2 be1;
	    CP.mkTrue pos
	  else
	    pure
	with
	  | Not_found -> begin
	      H.add vmap tmp (PExp e2);
	      CP.mkTrue pos
	    end
      else if is_in_svars e2 unbound_vars then
	gen_bindings_pure (CP.BForm ((CP.Eq (e2, e1, pos), il), None)) unbound_vars vmap
      else
	pure
    end
  | CP.BForm ((CP.EqMax (e1, e2,e3, pos), il), _) -> begin
      if is_in_svars e1 unbound_vars then
	let emax = CP.Max (e2, e3, pos) in
	let tmp = CP.Eq (e1, emax, pos) in
	gen_bindings_pure (CP.BForm ((tmp, il), None)) unbound_vars vmap
      else
	pure
    end
  | CP.BForm ((CP.EqMin (e1, e2,e3, pos), il), _) -> begin
      if is_in_svars e1 unbound_vars then
	let emin = CP.Min (e2, e3, pos) in
	let tmp = CP.Eq (e1, emin, pos) in
	gen_bindings_pure (CP.BForm ((tmp, il), None)) unbound_vars vmap
      else
	pure
    end
  | _ -> pure

and gen_bindings_heap prog (h0 : h_formula) (unbound_vars : CP.spec_var list) (vmap : var_map) : var_order = match h0 with
  | Star ({h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos})
  | StarMinus ({h_formula_starminus_h1 = h1;
	   h_formula_starminus_h2 = h2;
	   h_formula_starminus_pos = pos})	   
  | Conj ({h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = h1;
	   h_formula_conjstar_h2 = h2;
	   h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = h1;
	   h_formula_conjconj_h2 = h2;
	   h_formula_conjconj_pos = pos})
  | Phase ({h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos}) -> begin
      let o1 = gen_bindings_heap prog h1 unbound_vars vmap in
      let o2 = gen_bindings_heap prog h2 unbound_vars vmap in
      o1 @ o2
  end
  | ThreadNode _ -> failwith "gen_bindings_heap: not support ThreadNode yet"
  | DataNode ({h_formula_data_node = p;
    h_formula_data_name = c;
    h_formula_data_arguments = vs;
    h_formula_data_pos = pos}) -> begin
      let ddef = C.look_up_data_def pos prog.C.prog_data_decls c in
      let pname = CP.name_of_spec_var p in
      let vnames = List.map CP.name_of_spec_var (List.tl (List.tl vs)) in
      let field_names = List.map C.get_field_name ddef.C.data_fields in
      let helper v f = 
	(* 
	   v : exists. var, f: corresponding field, 
	   object fields can never be partially bound
	*)
	H.add vmap v (HExp (pname, f, false))
      in
      ignore (List.map2 helper vnames field_names);
      List.map (fun v -> (pname, v)) vnames (* all variables in vs are dependent on p *)
    end
  | ViewNode ({h_formula_view_node = p;
    h_formula_view_name = c;
    h_formula_view_arguments = vs;
    h_formula_view_modes = modes;
    h_formula_view_pos = pos}) -> begin
      (* 
	 map each variable v in vs to p.f where f is the view parameter
	 corresponding positionally to v.
      *)
      let pname = CP.name_of_spec_var p in
      let vdef = x_add C.look_up_view_def_raw 30 prog.C.prog_view_decls c in
      let helper v vp m pb =
	if m = ModeOut then
	  let vname = CP.name_of_spec_var v in
	  let vpname = CP.name_of_spec_var vp in
	  H.add vmap vname (HExp (pname, vpname, pb));
	  [(pname, vname)]
	else 
	  [] in
      let tmp1 = Gen.map4 helper vs vdef.C.view_vars modes vdef.C.view_partially_bound_vars in
      let tmp2 = List.concat tmp1 in
      tmp2
    end
  | HRel _ -> []
  | Hole _ | FrmHole _  -> []
  | HTrue -> []
  | HEmp | HVar _-> []
  | HFalse -> [] (* what to do here? *)

(* 
   compiling logical constructs to executable code based on the generated bindings.

   All variables take their values form vmap. An input var x is mapped to this.x.
   Mappings for input vars are provided from outside. This faciliate the linking
   of precondition and postcondition.

   If a lookup using vmap returns an unbound var, continue the look-up.
*)
and gen_pure_exp (pe : CP.exp) (vmap : var_map) (unbound_vars : CP.spec_var list) : (exp * bool) = match pe with
  | CP.Add (e1, e2, pos) -> begin
      let ce1, p1 = gen_pure_exp e1 vmap unbound_vars in
      let ce2, p2 = gen_pure_exp e2 vmap unbound_vars in
      let ce = Binary ({exp_binary_op = OpPlus;
      exp_binary_oper1 = ce1;
      exp_binary_oper2 = ce2;
      exp_binary_path_id = None;
      exp_binary_pos = pos}) in
      (ce, p1 || p2)
    end
  | CP.Subtract (e1, e2, pos) -> begin
      let ce1, p1 = gen_pure_exp e1 vmap unbound_vars in
      let ce2, p2 = gen_pure_exp e2 vmap unbound_vars in
      let ce = Binary ({exp_binary_op = OpMinus;
      exp_binary_oper1 = ce1;
      exp_binary_oper2 = ce2;
      exp_binary_path_id = None;
      exp_binary_pos = pos}) in
      (ce, p1 || p2)
    end
  | CP.Max (e1, e2, pos) -> begin
      let ce1, p1 = gen_pure_exp e1 vmap unbound_vars in
      let ce2, p2 = gen_pure_exp e2 vmap unbound_vars in
      let ce = CallNRecv ({
        exp_call_nrecv_method = "IntAug.max";
        exp_call_nrecv_arguments = [ce1; ce2];
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
        exp_call_nrecv_pos = pos}) in
      (ce, p1 || p2)
    end
  | CP.Min (e1, e2, pos) -> begin
      let ce1, p1 = gen_pure_exp e1 vmap unbound_vars in
      let ce2, p2 = gen_pure_exp e2 vmap unbound_vars in
      let ce = CallNRecv ({exp_call_nrecv_method = "IntAug.min";
        exp_call_nrecv_lock = None;
        exp_call_nrecv_arguments = [ce1; ce2];
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
        exp_call_nrecv_pos = pos}) in
      (ce, p1 || p2)
    end
  | CP.Var (sv, pos) -> begin
      let var = CP.name_of_spec_var sv in
      try
	let tmp = H.find vmap var in
	match tmp with
	  | HExp (v, f, p) -> 
		(*
		  For simplicity, suppose v is a bound variable.
		  If v is not, perform a recursive look-up.
		*)
		let v_e = Var ({exp_var_name = v;
		exp_var_pos = pos}) in
		let ce = Member ({exp_member_base = v_e;
		exp_member_fields = [f];
		exp_member_path_id = (fresh_branch_point_id "");
		exp_member_pos = pos}) in
		(ce, p)
	  | PExp me -> 
		if CP.is_var me then
		  let lsvar = CP.to_var me in
		  if not (CP.mem lsvar unbound_vars) then
		    let ce = Var ({exp_var_name = CP.name_of_spec_var lsvar;
		    exp_var_pos = pos}) in
		    (ce, false)
		  else
		    gen_pure_exp me vmap unbound_vars
		else
		  gen_pure_exp me vmap unbound_vars
		      (* if me is still unbound, this recursive invocation
			 will chase it up *)
      with
	| Not_found -> 
	      raise (Unbound_var ((Debug.string_of_pos pos) ^ var ^ " is unbound"))
		  (*
		    Debug.print_info "gen_pure_exp" (var ^ " is unbound") pos;
		    Empty pos
		  *)
    end
  | CP.IConst (i, pos) ->
	(IntLit ({exp_int_lit_val = i;
	exp_int_lit_pos = pos}), false)
  | CP.Null pos ->
	(Null pos, false)
  | _ -> failwith ("gen_pure_exp: " ^ (Cprinter.string_of_formula_exp pe) ^ " is not supported")

(*
  Note that this is compilation of tests only. All assignments have been put in vmap.

  pbound_vars : partially bound output variables.
*)
and gen_pure_formula (pure : CP.formula) (vmap : var_map) (unbound_vars : CP.spec_var list) (pbound_vars : CP.spec_var list) : exp = match pure with
  | CP.And (p1, p2, pos) ->  begin
      let pe1 = gen_pure_formula p1 vmap unbound_vars pbound_vars in
      let pe2 = gen_pure_formula p2 vmap unbound_vars pbound_vars in
      let pe = Binary ({exp_binary_op = OpLogicalAnd;
      exp_binary_oper1 = pe1;
      exp_binary_oper2 = pe2;
      exp_binary_path_id = None;
      exp_binary_pos = pos}) 
      in
      pe
    end
  | CP.BForm (bf,_) -> begin
      gen_pure_bform bf vmap unbound_vars
    end
  | _ -> failwith ((Cprinter.string_of_pure_formula pure) ^ " is not supported")

and has_partially_bound_field (e0 : exp) (pbound_vars : CP.spec_var list) = match e0 with
  | Member ({exp_member_base = base;
    exp_member_fields = fs}) ->
	let flag = List.exists (fun pv -> (CP.name_of_spec_var pv) = (List.hd fs)) pbound_vars in
	flag
            (*
	      let tbase = type_of_exp base in
	      let name = CP.name_of_type tbase in
	      let len = Str.length name in
	      let len2 = Str.length "_Checker" in
	      if len < len2 then false
	      else
	      let tail = String.sub name (len - len2) len2 in
	      if tail = "_Checker" then flag
	      else false
            *)
  | _ -> false

and gen_pure_bform (bf0 : CP.b_formula) (vmap : var_map) (unbound_vars : CP.spec_var list) : exp =
  let (pf,il) = bf0 in
  match pf with
    | CP.Eq (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "EQ";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "EQ";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "EQ";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else 
	  let ce = Binary ({exp_binary_op = OpEq;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.Neq (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "NEQ";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "NEQ";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "NEQ";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else 
	  let ce = Binary ({exp_binary_op = OpNeq;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.Lte (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "LTE";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "LTE";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "GTE";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else
	  let ce = Binary ({exp_binary_op = OpLte;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.Lt (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  failwith ("gen_pure_bform: both sides of <= is partially bound: " 
	  ^ (Cprinter.string_of_b_formula bf0))
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "LT";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "GT";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else
	  let ce = Binary ({exp_binary_op = OpLt;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.Gte (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  failwith ("gen_pure_bform: both sides of >= is partially bound: " 
	  ^ (Cprinter.string_of_b_formula bf0))
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "GTE";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "LTE";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else
	  let ce = Binary ({exp_binary_op = OpGte;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.Gt (e1, e2, pos) -> begin
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	if pb1 && pb2 then
	  failwith ("gen_pure_bform: both sides of > is partially bound: " 
	  ^ (Cprinter.string_of_b_formula bf0))
	else if pb1 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce1;
	  exp_call_recv_method = "GT";
	  exp_call_recv_arguments = [ce2];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else if pb2 then
	  let ce = CallRecv ({exp_call_recv_receiver = ce2;
	  exp_call_recv_method = "LT";
	  exp_call_recv_arguments = [ce1];
	  exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
	  exp_call_recv_pos = pos}) in
	  ce
	else
	  let ce = Binary ({exp_binary_op = OpGt;
	  exp_binary_oper1 = ce1;
	  exp_binary_oper2 = ce2;
	  exp_binary_path_id = None;
	  exp_binary_pos = pos}) in
	  ce
      end
    | CP.EqMax (emax, e1, e2, pos) -> begin
	let cem, pbcem = gen_pure_exp emax vmap unbound_vars in
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	let maxe = CallNRecv ({
    exp_call_nrecv_method = "Math.max";
    exp_call_nrecv_lock = None;
    exp_call_nrecv_arguments = [ce1; ce2];
    exp_call_nrecv_ho_arg = None;
    exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
    exp_call_nrecv_pos = pos}) in
	let ce = Binary ({exp_binary_op = OpEq;
	exp_binary_oper1 = cem;
	exp_binary_oper2 = maxe;
	exp_binary_path_id = None;
	exp_binary_pos = pos}) in
	ce
      end
    | CP.EqMin (emin, e1, e2, pos) -> begin
	let cem, pbcem = gen_pure_exp emin vmap unbound_vars in
	let ce1, pb1 = gen_pure_exp e1 vmap unbound_vars in
	let ce2, pb2 = gen_pure_exp e2 vmap unbound_vars in
	let mine = CallNRecv ({
    exp_call_nrecv_method = "Math.min";
    exp_call_nrecv_lock = None;
    exp_call_nrecv_arguments = [ce1; ce2];
    exp_call_nrecv_ho_arg = None;
    exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
    exp_call_nrecv_pos = pos}) in
	let ce = Binary ({exp_binary_op = OpEq;
	exp_binary_oper1 = cem;
	exp_binary_oper2 = mine;
	exp_binary_path_id = None;
	exp_binary_pos = pos}) in
	ce
      end
    | CP.BConst (b, pos) ->
	  BoolLit ({exp_bool_lit_val = b;
	  exp_bool_lit_pos = pos})
    | _ -> failwith ("gen_pure_bform: " ^ (Cprinter.string_of_b_formula bf0) 
      ^ " is not supported")

(*
  Return value: executable code
*)
and gen_heap prog (h0 : h_formula) (vmap : var_map) (unbound_vars : CP.spec_var list) : exp = match h0 with
  | Star ({h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos})
  | StarMinus ({h_formula_starminus_h1 = h1;
	   h_formula_starminus_h2 = h2;
	   h_formula_starminus_pos = pos})	   
  | Conj ({h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = h1;
	   h_formula_conjstar_h2 = h2;
	   h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = h1;
	   h_formula_conjconj_h2 = h2;
	   h_formula_conjconj_pos = pos})	   	   
  | Phase ({h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos}) -> begin
      (*
	<code for h1>
	<code for h2>
      *)
      let e1 = gen_heap prog h1 vmap unbound_vars in
      let e2 = gen_heap prog h2 vmap unbound_vars in
      let seq = mkSeq e1 e2 pos in
      seq
  end
  | ThreadNode _ -> failwith "gen_heaps: not support ThreadNode yet"
  | DataNode ({h_formula_data_node = p;
    h_formula_data_name = c;
    h_formula_data_arguments = vs;
    h_formula_data_pos = pos}) -> begin
      (*
	p::c<vs>

	if (p.color == curColor) p.color = newColor;
	else return false;
      *)
      let pvar = Var ({exp_var_name = CP.name_of_spec_var p;
      exp_var_pos = pos}) in
      let pcolor = Member ({exp_member_base = pvar;
      exp_member_fields = ["color"];
      exp_member_path_id = (fresh_branch_point_id "");
      exp_member_pos = pos}) in
      let pnewcolor = Assign ({exp_assign_op = OpAssign;
      exp_assign_lhs = pcolor;
      exp_assign_rhs = new_color_exp pos;
      exp_assign_path_id = None;
      exp_assign_pos = pos}) in
      (* now for the test *)
      let test = Binary ({exp_binary_op = OpEq;
      exp_binary_oper1 = pcolor;
      exp_binary_oper2 = cur_color_exp pos;
      exp_binary_path_id = None;
      exp_binary_pos = pos}) in
      let cond = Cond ({exp_cond_condition = test;
      exp_cond_then_arm = pnewcolor;
      exp_cond_else_arm = return_false pos;
      exp_cond_path_id = stub_branch_point_id "pred_comp_generated";
      exp_cond_pos = pos}) 
      in
      cond
    end
  | ViewNode ({h_formula_view_node = p;
    h_formula_view_name = c;
    h_formula_view_arguments = vs;
    h_formula_view_modes = modes;
    h_formula_view_pos = pos}) -> begin
      (*
	Make a call. Set up inputs and all that.
	Now how to do that?

	c_checker ckr = new c_checker();
	ckr.root = p;
	if (!ckr.traverse(curColor, newColor)) return false;
      *)
      let vdef = x_add C.look_up_view_def_raw 31 prog.C.prog_view_decls c in
      let cls = class_name_of_view c in
      let new_checker = New ({exp_new_class_name = cls;
      exp_new_arguments = [];
      exp_new_pos = pos}) in
      let new_checker_name = CP.name_of_spec_var p in
      let new_checker_var = Var ({exp_var_name = new_checker_name;
      exp_var_pos = pos}) in
      let new_checker_decl = VarDecl ({exp_var_decl_type = Named cls;
      exp_var_decl_decls = 
	      [(new_checker_name, Some new_checker, pos)];
      exp_var_decl_pos = no_pos}) in		
      (* Call checker and test for result *)
      let call_checker = CallRecv ({exp_call_recv_receiver = new_checker_var;
      exp_call_recv_method = "traverse";
      exp_call_recv_arguments = 
	      [cur_color_exp pos; new_color_exp pos];
      exp_call_recv_path_id = stub_branch_point_id "pred_comp_generated";
      exp_call_recv_pos = pos}) in
      let neg_call = Unary ({exp_unary_op = OpNot;
      exp_unary_exp = call_checker;
      exp_unary_path_id = None;
      exp_unary_pos = pos}) in
      let call_cond = Cond ({exp_cond_condition = neg_call;
      exp_cond_then_arm = return_false pos;
      exp_cond_else_arm = Empty pos;
      exp_cond_path_id = stub_branch_point_id "pred_comp_generated";
      exp_cond_pos = pos}) in
      (* Set up inputs *)
      (* helper: Constructs a list of assignments to set up inputs *)
      let rec helper fargs params modes : exp list = match fargs, params, modes with
	| (farg :: rest1, param :: rest2, m :: rest3) -> begin
	    let rest = helper rest1 rest2 rest3 in
	    if m = ModeIn then
	      let param_e = CP.Var (param, pos) in
	      let e, _ = gen_pure_exp param_e vmap unbound_vars in
	      let lhs = Member ({exp_member_base = new_checker_var;
	      exp_member_fields = [CP.name_of_spec_var farg];
	      exp_member_path_id = (fresh_branch_point_id "");
	      exp_member_pos = pos}) in
	      let assignment = Assign ({exp_assign_op = OpAssign;
	      exp_assign_lhs = lhs;
	      exp_assign_rhs = e;
	      exp_assign_path_id = None;
	      exp_assign_pos = pos}) in
	      assignment :: rest
	    else rest
	  end
	| [], [], [] -> [] 
	| _ -> failwith ("gen_heap: params and modes are supposed to be lists with the same length.") in
      (* gen inputs *)
      let self_var = CP.SpecVar (Named vdef.C.view_data_name, self, Unprimed) in
      let tmp1 = helper (self_var :: vdef.C.view_vars) (p :: vs) (ModeIn :: vdef.C.view_modes) in
      let helper2 e1 e2 = mkSeq e2 e1 pos in
      let init_inputs = List.fold_left helper2 call_cond tmp1 in
      (* *)
      let seq1 = Seq ({exp_seq_exp1 = new_checker_decl;
      exp_seq_exp2 = init_inputs;
      exp_seq_pos = pos}) in
      seq1
    end
  | Hole _ | FrmHole _ | HTrue | HEmp | HVar _ | HRel _ ->
        Empty no_pos
  | HFalse -> 
        return_false no_pos

(*
  Compiling disjunct:
  - rename bound variables
  - generate unbound variables: 
  they include output parameters and existential variables. Note that inputs
  for recursive predicate invocations are included in existentially quantified
  variables.
  - generate var_map

  return value:
  - disjunct procedure
*)
and gen_disjunct prog (disj0 : formula) (vmap0 : var_map) (output_vars : CP.spec_var list) (pbound_vars : CP.spec_var list) : proc_decl =
  (* 
     rename bound vars to avoid name clashes between disjuncts, since
     checkers for predicate invocations will use the same name as the
     root pointer for the predicate instance.
  *)
  (*  let () = print_string ("\n\tCompiling: " ^ (Cprinter.string_of_formula disj0) ^ "\n") in *)
  let disj = disj0 (* x_add_1 rename_bound_vars disj0 *) in
  let qvars, base = split_quantifiers disj in
  let h, pure0,_,_, _,_ = split_components base in
  let pos = pos_of_formula disj in
  (* unbound vars include existential vars and output vars *)
  let unbound_vars = output_vars @ qvars in
  (* generate bindings *)
  (*
    let vmap = H.create 103 in
  *)
  let vmap = H.copy vmap0 in
  let _(*v_order*) = gen_bindings_heap prog h unbound_vars vmap in
  let pure0 = MCP.fold_mem_lst (CP.mkTrue no_pos) true true pure0  in
  let pure = gen_bindings_pure pure0 unbound_vars vmap in
  (*  let () = print_vmap vmap in *)
  (* compile *)
  (* tests *)
  let h_exp = gen_heap prog h vmap unbound_vars in
  let pure_exp = gen_pure_formula pure vmap unbound_vars pbound_vars in
  (* assignments to output *)
  (*
    generate assignments to output parameters.
    
    out_vars: output variables
    
    For now, ignore var order v_order.
  *)
  let rec gen_assignment_output (out_vars : CP.spec_var list) : exp = match out_vars with
    | (((CP.SpecVar (ovar_t, ovar, _)) as sovar) :: rest) -> begin
	let rest_e = gen_assignment_output rest in
	let v = Var ({exp_var_name = ovar;
	exp_var_pos = pos}) in
	let rhs = 
	  try
	    fst (gen_pure_exp (CP.Var (sovar, pos)) vmap unbound_vars)
	  with
	    | Unbound_var msg -> 
		  (* bind to a "unbound" boxed object *)
		  New ({exp_new_class_name = aug_class_name ovar_t;
		  exp_new_arguments = [];
		  exp_new_pos = pos})
	in
	let tmp = List.filter (fun pv -> CP.name_of_spec_var pv = ovar) pbound_vars in
	let assign = 
	  match tmp with
	    | (CP.SpecVar (t, _, _)) :: _ ->
		  let new_e = New ({exp_new_class_name = aug_class_name t;
		  exp_new_arguments = [rhs];
		  exp_new_pos = pos}) in
		  Assign ({exp_assign_op = OpAssign;
		  exp_assign_lhs = v;
		  exp_assign_rhs = new_e;
		  exp_assign_path_id = None;
		  exp_assign_pos = pos})
	    | [] -> Assign ({exp_assign_op = OpAssign;
	      exp_assign_lhs = v;
	      exp_assign_rhs = rhs;
	      exp_assign_path_id = None;
	      exp_assign_pos = pos})
	in
	let seq = mkSeq assign rest_e pos in
	seq
      end
    | [] -> Empty pos in
  (* code for successful check *)
  let output_vars = !precond_output @ output_vars in
  let assignments = gen_assignment_output output_vars in
  let seq1 = mkSeq assignments (return_true pos) pos in
  (* code for failure *)
  (* now make the pure test *)
  let cond = Cond ({exp_cond_condition = pure_exp;
  exp_cond_then_arm = seq1;
  exp_cond_else_arm = return_false pos;
  exp_cond_path_id = stub_branch_point_id "pred_comp_generated";
  exp_cond_pos = pos}) in
  (* code for the entire disjunct procedure body *)
  let seq2 = Seq ({exp_seq_exp1 = h_exp;
  exp_seq_exp2 = cond;
  exp_seq_pos = pos}) in
  (* now make the disjunct procedure *)
  let dproc_name = "disj_" ^ (string_of_int (next_disj_count())) in
  let disj_proc = 
    { proc_name = dproc_name;
    proc_source = "source_file";
    proc_flags = [];
    proc_hp_decls = [];
    proc_mingled_name = dproc_name;
    proc_data_decl = None; (* the class containing the method *)
    proc_constructor = false;
    proc_args = [cur_color pos; new_color pos];
    proc_args_wi =  List.map (fun p -> (p.param_name,Globals.I)) [cur_color pos; new_color pos];
    proc_ho_arg = None;
    proc_return = Bool;
    (* proc_static_specs = Iformula.mkEFalseF (); *)
    proc_static_specs = Iformula.mkETrueF ();
    proc_dynamic_specs = Iformula.mkEFalseF ();
    proc_exceptions = [];
    proc_body = Some seq2;
    proc_is_main = false;
    proc_is_while = false;
    proc_has_while_return = false;
    proc_is_invoked = false;
    proc_verified_domains = [];
    proc_file = "";
    proc_loc = pos ;
    proc_test_comps = None} 
  in
  disj_proc


and combine_disj_results disj_results pos : exp = match disj_results with
  | disj_proc :: rest -> begin
      (* 
	 call the disjunct procedure, assign the returned 
	 value to bvar_name 
      *)
      let bvar_name = fresh_var_name "xxx" pos.start_pos.Lexing.pos_lnum in
      let disj_res = Var ({exp_var_name = bvar_name;
      exp_var_pos = pos}) in
      let call = CallNRecv ({
        exp_call_nrecv_method = disj_proc.proc_name;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_arguments = [cur_color_exp pos; new_color_exp pos];
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
        exp_call_nrecv_pos = pos}) in
      let undo_call' = CallNRecv ({
        exp_call_nrecv_method = disj_proc.proc_name;
        exp_call_nrecv_lock = None;
        exp_call_nrecv_arguments = [new_color_exp pos; cur_color_exp pos];
        exp_call_nrecv_ho_arg = None;
        exp_call_nrecv_path_id = stub_branch_point_id "pred_comp_generated";
        exp_call_nrecv_pos = pos}) in
      let undo_call = VarDecl {exp_var_decl_type = Bool;
      exp_var_decl_decls = [(fresh_var_name "bool" pos.start_pos.Lexing.pos_lnum, Some undo_call', pos)];
      exp_var_decl_pos = pos } in
      let call_disj = VarDecl {exp_var_decl_type = Bool;
      exp_var_decl_decls = [(bvar_name, Some call, pos)];
      exp_var_decl_pos = pos } in
      (*
	now make the test
      *)
      let cond = Cond ({exp_cond_condition = disj_res;
      exp_cond_then_arm = return_true pos;
      exp_cond_else_arm = undo_call;
      exp_cond_path_id = stub_branch_point_id "pred_comp_generated";
      exp_cond_pos = pos}) in
      let seq1 = Seq ({exp_seq_exp1 = call_disj;
      exp_seq_exp2 = cond;
      exp_seq_pos = pos}) in
      let rest_e = combine_disj_results rest pos in
      let seq2 = Seq ({exp_seq_exp1 = seq1;
      exp_seq_exp2 = rest_e;
      exp_seq_pos = pos}) in
      seq2
    end
  | [] -> Empty pos

(* 
   Generate checking function for a DNF formula.

   A DNF formula is compiled to a set of procedures, one for each
   disjunct, and a driver procedure that orchestrates the disjunct
   procedures. If multiple disjuncts can potentialy return true,
   then the first such one is selected.

   gen_formula does not need to know what the input parameters are;
   they are set by the caller. On the other hand, it has to know
   output parameters, so that it can set up their values upon successful
   completion of checking.

   Return value:
   exp: driver procedure
   proc_decl list: list of disjunct procedures
   CP.spec_var list: partially bound output parameters
*)
and gen_formula (prog : C.prog_decl) (f0 : formula) (vmap : var_map) (output_vars : CP.spec_var list) : (exp * proc_decl list * CP.spec_var list) =
  let pbvars = gen_partially_bound_params output_vars f0 in
  let disjs = formula_to_disjuncts f0 in
  let pos = pos_of_formula f0 in
  let disj_results = List.map (fun disj -> gen_disjunct prog disj vmap output_vars pbvars) disjs in
  let combined_exp = combine_disj_results disj_results pos in
  let ret_false = Return ({exp_return_val = Some 
	  (BoolLit ({exp_bool_lit_val = false;
	  exp_bool_lit_pos = pos}));
  exp_return_path_id = stub_branch_point_id "pred_comp_generated";
  exp_return_pos = pos}) in
  let seq = Seq ({exp_seq_exp1 = combined_exp;
  exp_seq_exp2 = ret_false;
  exp_seq_pos = pos}) in
  (seq, disj_results, pbvars)

and gen_view (prog : C.prog_decl) (vdef : C.view_decl) : (data_decl * CP.spec_var list)  =
  let pos = pos_of_struc_formula vdef.C.view_formula in
  let in_params, out_params = 
    split_params_mode vdef.C.view_vars vdef.C.view_modes in
  (* 
     build mapping for input parameters.
     Input param v is mapped to this.v
  *)
  let in_names = List.map CP.name_of_spec_var in_params in
  let vmap = H.create 103 in
  let () = List.iter 
    (fun iv -> H.add vmap iv (HExp ("this", iv, false))) (self :: in_names) in
  let pbvars0 = gen_partially_bound_params out_params (C.formula_of_unstruc_view_f vdef) in
  (* update partially bound vars for vdef *)
  let () = update_partially_bound vdef pbvars0 in
  let combined_exp, disj_procs, pbvars = 
    gen_formula prog (C.formula_of_unstruc_view_f vdef) vmap out_params in
  (* generate fields *)
  let fields = ((Named vdef.C.view_data_name, self), pos, false, [gen_field_ann (Named vdef.C.view_data_name)](* F_NO_ANN *)) (* An Hoa : add [false] for inline record. TODO revise *) 
    :: (gen_fields vdef.C.view_vars pbvars pos) in
  (* parameters for traverse *)
  let check_proc = 
    { proc_name = "traverse";
    proc_source = "source_file";
    proc_flags = [];
    proc_hp_decls = [];
    proc_mingled_name = "traverse";
    proc_data_decl = None;
    proc_constructor = false;
    proc_args = [cur_color pos; new_color pos];
    proc_args_wi = List.map (fun p -> (p.param_name,Globals.I)) [cur_color pos; new_color pos];
    proc_ho_arg = None;
    proc_return = Bool;
    proc_static_specs = Iformula.mkETrueF ();
    proc_dynamic_specs = Iformula.mkEFalseF ();
    proc_body = Some combined_exp;
    proc_exceptions = [];
    proc_is_main = false;
    proc_is_while = false;
    proc_has_while_return = false;
    proc_is_invoked = false;
    proc_verified_domains = [];
    proc_file = "";
    proc_loc = no_pos;
    proc_test_comps = None} in
  let ddef = { data_name = class_name_of_view vdef.C.view_name;
  data_fields = fields;
  data_pos = vdef.C.view_pos;
  data_parent_name = "Object";
  data_invs = [];
  data_is_template = false;
  data_methods = check_proc :: disj_procs } in
  check_proc.proc_data_decl <- Some ddef;
  ddef, pbvars

and update_partially_bound (vdef : C.view_decl) (pbvars : CP.spec_var list) : unit = 
  let rec helper vvars : bool list = match vvars with
    | v :: rest -> 
	  let tmp = helper rest in
	  if CP.mem v pbvars then
	    true :: tmp
	  else
	    false :: tmp
    | [] -> []
  in
  let tmp = helper vdef.C.view_vars in
  vdef.C.view_partially_bound_vars <- tmp

and get_partially_bound_vars_heap prog (h0 : h_formula) : CP.spec_var list = match h0 with
  | Star ({h_formula_star_h1 = h1;
    h_formula_star_h2 = h2}) ->
	let vars1 = get_partially_bound_vars_heap prog h1 in
	let vars2 = get_partially_bound_vars_heap prog h2 in
	vars1 @ vars2
  | ViewNode ({h_formula_view_arguments = args0;
    h_formula_view_name = c}) ->
	let vdef = x_add C.look_up_view_def_raw 32 prog.C.prog_view_decls c in
	let rec helper flags args = match flags, args with
	  | (flag :: rest1, arg :: rest2) ->
		let tmp = helper rest1 rest2 in
		if flag then arg :: tmp
		else tmp
	  | ([], []) -> []
	  | _ -> failwith ("get_partially_bound_heap: " ^ c ^ " different lengths.")
	in
	helper vdef.C.view_partially_bound_vars args0
  | _ -> []

and get_partially_bound_vars prog (f0 : formula) : CP.spec_var list = match f0 with
  | Or ({formula_or_f1 = f1;
    formula_or_f2 = f2}) ->
	let vars1 = get_partially_bound_vars prog f1 in
	let vars2 = get_partially_bound_vars prog f2 in
	vars1 @ vars2
  | Exists ({formula_exists_heap = h})
  | Base ({formula_base_heap = h}) ->
	get_partially_bound_vars_heap prog h

(*
  Generate names of out parameters that are bound
  by a pure formula.
*)
and gen_bound_params (output_vars : CP.spec_var list) (p0 : CP.formula) : CP.spec_var list = match p0 with
  | CP.And (p1, p2, pos) -> 
	let b1 = gen_bound_params output_vars p1 in
	let b2 = gen_bound_params output_vars p2 in
	b1 @ b2
  | CP.BForm ((CP.Eq (e1, e2, pos), _), _) -> 
	if is_in_svars e1 output_vars && (not (is_in_svars e2 output_vars)) then
	  [CP.to_var e1]
	else if is_in_svars e2 output_vars && (not (is_in_svars e1 output_vars))  then
	  [CP.to_var e2]
	else
	  []
  | CP.BForm ((CP.EqMax (e1, _, _, _), _), _)
  | CP.BForm ((CP.EqMin (e1, _, _, _), _), _) ->
	if is_in_svars e1 output_vars then
	  [CP.to_var e1]
	else
	  []
  | _ -> []

(*
  Generate partially bound out parameters.

  CP.spec_var is used so that we know the type of the variable.
*)
and gen_partially_bound_params (output_vars : CP.spec_var list) (f0 : formula) : CP.spec_var list = match f0 with
  | Or ({formula_or_f1 = f1;
    formula_or_f2 = f2}) ->
	let p1 = gen_partially_bound_params output_vars f1 in
	let p2 = gen_partially_bound_params output_vars f2 in
	p1 @ p2
  | Base ({formula_base_pure = p})
  | Exists ({formula_exists_pure = p}) ->
	let bound_vars = gen_bound_params output_vars (MCP.fold_mem_lst (CP.mkTrue no_pos) true true p) in
	let partially_bounds = Gen.BList.difference_eq CP.eq_spec_var output_vars bound_vars in
	partially_bounds

(*
  Generate classes for partially bound output parameters.
  A partially bound parameter p of type T will be converted
  to a one of type T_Aug { boolean bound; T val }
*)
and gen_partially_bound_types (pbvars : CP.spec_var list) pos : data_decl list =
  let tmp1 = List.map (fun t -> gen_partially_bound_type t pos) pbvars in
  let tmp2 = List.concat tmp1 in
  tmp2
      
and gen_partially_bound_type ((CP.SpecVar (t, v, p)) : CP.spec_var) pos : data_decl list = match t with
  | Named c ->
	let cls_aug = c ^ "Aug" in
	(* An Hoa : Add [false] for inline record. TODO revise *)
	let fields = [((Bool, "bound"), pos, false, [gen_field_ann Bool] (*F_NO_ANN*)); ((Named (string_of_typ t), "val"), pos, false,[] (* F_NO_ANN *))] in
	let ddef = { data_name = cls_aug;
	data_fields = fields;
	data_pos = no_pos;
	data_parent_name = "Object";
	data_invs = [];
        data_is_template = false;
	data_methods = [] }
	in
	[ddef]
  | _ -> []

and print_vmap (vmap : var_map) : unit =
  let print_entry v e =
    print_string (v ^ " -> ");
    match e with
      | HExp (v1, f, p) -> print_string (v1 ^ "." ^ f ^ ":" ^ (string_of_bool p) ^ "\n")
      | PExp pe -> print_string ((Cprinter.string_of_formula_exp pe) ^ "\n")
  in
  print_string ("\nvmap:\n");
  H.iter print_entry vmap;
  print_string ("\n")
