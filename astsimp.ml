
(*  Created 21 Feb 2006

	Simplify Iast to Cast
*)

open Globals

module C = Cast
module E = Env
module Err = Error
module I = Iast
module U = Util
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module H = Hashtbl
module TP = Tpdispatcher
module Chk = Checks
  (* module VG = View_generator *)

type trans_exp_type = (C.exp * CP.typ)

and spec_var_info = { mutable sv_info_kind : spec_var_kind }

and spec_var_table = (ident, spec_var_info) H.t
	
and spec_var_kind = 
  | Known of CP.typ
  | Unknown


(************************************************************
															 Primitives handling stuff
************************************************************)

let prim_str = 
  "int add___(int a, int b) requires true ensures res=a+b;
int minus___(int a, int b) requires true ensures res=a-b;
int mult___(int a, int b) requires true ensures true;
int div___(int a, int b) requires true ensures true;
int mod___(int a, int b) requires true ensures -b<res<b;
bool eq___(int a, int b) requires true ensures res & a=b or !res & a!=b;
bool eq___(bool a, bool b) requires true ensures res & a=b or !res & a!=b;
bool neq___(int a, int b) requires true ensures !res & a=b or res & a!=b;
bool neq___(bool a, bool b) requires true ensures !res & a=b or res & a!=b;
bool lt___(int a, int b) requires true ensures res & a<b or a>=b & !res;
bool lte___(int a, int b) requires true ensures res & a<=b or a>b & !res;
bool gt___(int a, int b) requires true ensures a>b & res or a<=b & !res;
bool gte___(int a, int b) requires true ensures a>=b & res or  a<b & !res;
bool land___(bool a, bool b) requires true ensures a & b & res or !a & !res or !b & !res;
bool lor___(bool a, bool b) requires true ensures a & res or b & res or !a & !b & !res;
bool not___(bool a) requires true ensures a & !res or !a & res;
"

let prim_buffer = Buffer.create 1024

(* search prog and generate all eq, neq for all the  *)
(* data declaration, along with the ones in prim_str *)
let gen_primitives (prog : I.prog_decl) : I.proc_decl list = 
  let rec helper (ddecls : I.data_decl list) = match ddecls with
	| ddef :: rest -> 
		let eq_str = "bool eq___(" ^ ddef.I.data_name ^ " a, " 
		  ^ ddef.I.data_name ^ " b) requires true ensures res & a=b or a!=b & !res;\n" in
		let neq_str = "bool neq___(" ^ ddef.I.data_name ^ " a, " 
		  ^ ddef.I.data_name ^ " b) requires true ensures a=b & !res or a!=b & res;\n" in
		let is_null_str = "bool is_null___(" ^ ddef.I.data_name ^ " a"
		  ^ ") requires true ensures res & a=null or !res & a!=null;\n" in
		let is_not_null_str = "bool is_not_null___(" ^ ddef.I.data_name ^ " a"
		  ^ ") requires true ensures !res & a=null or res & a!=null;\n" in
		  Buffer.add_string prim_buffer eq_str;
		  Buffer.add_string prim_buffer neq_str;
		  Buffer.add_string prim_buffer is_null_str;
		  Buffer.add_string prim_buffer is_not_null_str;
		  helper rest
	| [] -> ()
  in
	Buffer.add_string prim_buffer prim_str;
	helper prog.I.prog_data_decls;
	let all_prims = Buffer.contents prim_buffer in
	let input = Lexing.from_string all_prims in
	let prog = Iparser.program (Ilexer.tokenizer "primitives") input in
	  prog.I.prog_proc_decls

let op_map = Hashtbl.create 19
let _ = List.map (fun (op, func) -> Hashtbl.add op_map op func)
  [(I.OpPlus, "add___");
   (I.OpMinus, "minus___");
   (I.OpMult, "mult___");
   (I.OpDiv, "div___");
   (I.OpMod, "mod___");
   (I.OpEq, "eq___");
   (I.OpNeq, "neq___");
   (I.OpLt, "lt___");
   (I.OpLte, "lte___");
   (I.OpGt, "gt___");
   (I.OpGte, "gte___");
   (I.OpLogicalAnd, "land___");
   (I.OpLogicalOr, "lor___");
   (I.OpIsNull, "is_null___");
   (I.OpIsNotNull, "is_not_null___")]

let get_binop_call (bop : I.bin_op) : ident =
  try
	Hashtbl.find op_map bop
  with
	| Not_found -> failwith ("binary operator " ^ (Iprinter.string_of_binary_op bop) ^ " is not supported")

let assign_op_to_bin_op_map = [(I.OpPlusAssign, I.OpPlus); 
							   (I.OpMinusAssign, I.OpMinus);
							   (I.OpMultAssign, I.OpMult);
							   (I.OpDivAssign, I.OpDiv);
							   (I.OpModAssign, I.OpMod)]

let bin_op_of_assign_op (aop : I.assign_op) = List.assoc aop assign_op_to_bin_op_map

(************************************************************
															 AST translation
************************************************************)

module Name = struct
  type t = ident
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module NG = Graph.Imperative.Digraph.Concrete(Name)
module TopoNG = Graph.Topological.Make(NG)
module DfsNG = Graph.Traverse.Dfs(NG)

let node2_to_node prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap = 
  (* 
	 match named arguments with formal parameters to generate a list
	 of position-based arguments. If a parameter does not appear in
	 args, then it is instantiated to a fresh name.
  *)
  let rec match_args (params : ident list) args : IP.exp list = match params with
	| (p :: rest) -> begin
		let tmp1 = match_args rest args in
		let tmp2 = List.filter (fun a -> fst a = p) args in
		let tmp3 = match tmp2 with
		  | [(_, e)] -> e
		  | _ -> 
		  IP.Var ((fresh_name(), Unprimed), h0.IF.h_formula_heap2_pos) in
		let tmp4 = tmp3 :: tmp1 in
		  tmp4
	  end
	| [] -> []
  in
	try
	  let vdef = I.look_up_view_def_raw prog.I.prog_view_decls h0.IF.h_formula_heap2_name in
	  let hargs = match_args vdef.I.view_vars h0.IF.h_formula_heap2_arguments in
	  let h = { IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
				IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
				IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
				IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
				IF.h_formula_heap_arguments = hargs;
				IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
				IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos }
	  in
		h
	with
	  | Not_found ->
		  let ddef = I.look_up_data_def h0.IF.h_formula_heap2_pos 
			prog.I.prog_data_decls h0.IF.h_formula_heap2_name in
		  let params = List.map (fun ((t, v), p) -> v) ddef.I.data_fields in
		  let hargs = match_args params h0.IF.h_formula_heap2_arguments in
		  let h = { IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
					IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
					IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
					IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
					IF.h_formula_heap_arguments = hargs;
					IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
					IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos }
		  in
			h

(* 
   convert HeapNode2 to HeapNode 
*)
let rec convert_heap2_heap prog (h0 : IF.h_formula) : IF.h_formula = match h0 with
  | IF.Star (({IF.h_formula_star_h1 = h1;
			   IF.h_formula_star_h2 = h2}) as h)->
	  let tmp1 = convert_heap2_heap prog h1 in
	  let tmp2 = convert_heap2_heap prog h2 in
		IF.Star {h with IF.h_formula_star_h1 = tmp1;
				   IF.h_formula_star_h2 = tmp2}
  | IF.HeapNode2 h2 -> IF.HeapNode (node2_to_node prog h2)
  | _ -> h0

and convert_heap2 prog (f0 : IF.formula) : IF.formula = match f0 with
  | IF.Or (({IF.formula_or_f1 = f1;
			 IF.formula_or_f2 = f2}) as f) ->
	  let tmp1 = convert_heap2 prog f1 in
	  let tmp2 = convert_heap2 prog f2 in
		IF.Or {f with IF.formula_or_f1 = tmp1;
				 IF.formula_or_f2 = tmp2}
  | IF.Base (({IF.formula_base_heap = h0}) as f) ->
	  let h = convert_heap2_heap prog h0 in
		IF.Base {f with IF.formula_base_heap = h}
  | IF.Exists (({IF.formula_exists_heap = h0}) as f) ->
	  let h = convert_heap2_heap prog h0 in
		IF.Exists {f with IF.formula_exists_heap = h}

let order_views (view_decls0 : I.view_decl list) : I.view_decl list =
  (* generate pairs (vdef.view_name, v) where v is a view appearing in vdef *)
  let rec gen_name_pairs_heap vname h = match h with
	| IF.Star ({IF.h_formula_star_h1 = h1;
				IF.h_formula_star_h2 = h2}) -> (gen_name_pairs_heap vname h1) @ (gen_name_pairs_heap vname h2)
	| IF.HeapNode ({IF.h_formula_heap_name = c}) -> 
		if c = vname then [] 
		else begin
		  try
			let _ = I.look_up_view_def_raw view_decls0 c in
			  [(vname, c)]
		  with
			| Not_found -> []
		end
	| _ -> [] in
  let rec gen_name_pairs vname (f : IF.formula) : (ident * ident) list = match f with
	| IF.Or ({IF.formula_or_f1 = f1;
			  IF.formula_or_f2 = f2}) -> (gen_name_pairs vname f1) @ (gen_name_pairs vname f2)
	| IF.Base ({IF.formula_base_heap = h;
				IF.formula_base_pure = p})  -> gen_name_pairs_heap vname h 
	| IF.Exists ({IF.formula_exists_heap = h;
				  IF.formula_exists_pure = p}) -> gen_name_pairs_heap vname h
  in
  let tmp = List.map (fun vdef -> gen_name_pairs vdef.I.view_name vdef.I.view_formula) view_decls0 in
  let edges = List.concat tmp in
  let g = NG.create () in
    ignore (List.map (fun (v1, v2) -> NG.add_edge g (NG.V.create v1) (NG.V.create v2)) edges);
	if DfsNG.has_cycle g then
	  failwith ("View definitions are mutually recursive");
	(* take out the view names in reverse order *)
	let view_names = ref ([] : ident list) in
	let store_name n = view_names := n :: !view_names in
	  TopoNG.iter store_name g;
	  (* now reorder the views *)
	  let rec reorder_views (view_decls : I.view_decl list) (ordered_names : ident list) = match ordered_names with
		| n :: rest ->
			let n_view, rest_decls = List.partition (fun v -> v.I.view_name = n) view_decls in
			let rest_views, new_rest_decls = reorder_views rest_decls rest in
			  (* n_view should contain only one views *)
			  (n_view @ rest_views, new_rest_decls)
		| [] -> ([], view_decls) in
	  let (r1, r2) = reorder_views view_decls0 !view_names in
		r1 @ r2

let loop_procs : C.proc_decl list ref = ref []

(*
  let rec pick_coercions (procs : C.proc_decl list) : (C.proc_decl list * C.proc_decl list) = match procs with
  | proc :: rest -> begin
  let rest_l2r, rest_r2l = pick_coercions rest in
  match proc.C.proc_coercion_type with
  | C.Coercion -> (proc :: rest_l2r, rest_r2l)
  | C.Equiv -> (proc :: rest_l2r, proc :: rest_r2l)
  | C.Reverse -> (rest_l2r, proc :: rest_r2l)
  | C.NotACoercion -> (rest_l2r, rest_r2l)
  end
  | [] -> ([], [])
*)

let rec trans_prog (prog0 : I.prog_decl) : C.prog_decl =
  let _ = I.build_hierarchy prog0 in
  let check_overridding = (Chk.overridding_correct prog0) in         (* overriding test *)
  let check_field_dup = (Chk.no_field_duplication prog0) in          (* field duplication test *) 
  let check_method_dup = (Chk.no_method_duplication prog0) in        (* method duplication test *) 
  let check_field_hiding = (Chk.no_field_hiding prog0) in            (* field hiding test *) 
	if check_field_dup && check_method_dup && check_overridding && check_field_hiding then  
      let prims = gen_primitives prog0 in
      let prog = {prog0 with I.prog_proc_decls = prims @ prog0.I.prog_proc_decls} in
		set_mingled_name prog;
		let all_names = (List.map (fun p -> p.I.proc_mingled_name) prog0.I.prog_proc_decls) 
		  @ (List.map (fun ddef -> ddef.I.data_name) prog0.I.prog_data_decls)
		  @ (List.map (fun vdef -> vdef.I.view_name) prog0.I.prog_view_decls) in
		let dups = U.find_dups all_names in
		  if not (U.empty dups) then begin
			print_string ("duplicated top-level name(s): " ^ (String.concat ", " dups) ^ "\n");
			failwith ("Error detected")
		  end else
			let tmp_views = order_views prog.I.prog_view_decls in
			let cviews = List.map (trans_view prog) tmp_views in
			let cdata = List.map (trans_data prog) prog.I.prog_data_decls in
			let cprocs1 = List.map (trans_proc prog) prog.I.prog_proc_decls in
			let cprocs = !loop_procs @ cprocs1 in
			let l2r_coers, r2l_coers = trans_coercions prog0 in
			let cprog = { C.prog_data_decls = cdata;
						  C.prog_view_decls = cviews;
						  C.prog_proc_decls = cprocs;
						  C.prog_left_coercions = l2r_coers;
						  C.prog_right_coercions = r2l_coers }
			in
			  ignore (List.map (fun vdef -> compute_view_x_formula 
								  cprog vdef !Globals.n_xpure) cviews);
			  ignore (List.map (fun vdef -> set_materialized_vars cprog vdef) cviews);
			  ignore (C.build_hierarchy cprog);
			  cprog
	else 
      failwith ("Error detected")

and trans_data (prog : I.prog_decl) (ddef : I.data_decl) : C.data_decl = 
  let trans_field ((t, c), pos) : C.typed_ident = (trans_type prog t pos, c) in
	{ C.data_name = ddef.I.data_name;
	  C.data_fields = List.map trans_field ddef.I.data_fields;
	  C.data_parent_name = ddef.I.data_parent_name;
	  C.data_methods = List.map (trans_proc prog) ddef.I.data_methods;
	  C.data_invs = [] } (*TODO: fix this *)	  

and compute_view_x_formula (prog : C.prog_decl) (vdef : C.view_decl) (n : int) =
  if n > 0 then begin
	let pos = CF.pos_of_formula vdef.C.view_formula in
	  (* keep the quantifiers generated by xpure *)
	let xform', addr_vars' = Solver.xpure_symbolic_no_exists prog vdef.C.view_formula in 
	let addr_vars = U.remove_dups addr_vars' in
	let new_xform' = (*Omega.pairwisecheck*) (*Isabelle.pairwisecheck*) TP.simplify xform' in
	let xform = new_xform' in
	  (* let xform = CP.mkExists addr_vars new_xform' 
		 (CF.pos_of_formula vdef.C.view_formula) in *)
	  (* let xform = Omega.pairwisecheck xform' in *)
	let ctx = CF.build_context (CF.true_ctx pos) (CF.formula_of_pure xform pos) pos in
	let rs, _ = Solver.heap_entail prog false [ctx] 
	  (CF.formula_of_pure vdef.C.view_user_inv pos) pos in
	  if not (U.empty rs) then begin
		(*TODO: check entailment in the other way *)
		(*
		  print_string ("\nxform' for view: " ^ vdef.C.view_name ^ "\n"
		  ^ (Cprinter.string_of_pure_formula xform') ^ "\n");
		*)
		(*
		  print_string ("\noriginal formula:\n" ^ 
		  (Cprinter.string_of_formula vdef.C.view_formula));
		*)
		vdef.C.view_x_formula <- xform;
		vdef.C.view_addr_vars <- addr_vars;
		compute_view_x_formula prog vdef (n-1)
	  end else
		Err.report_error { Err.error_loc = pos;
						   Err.error_text = "view formula does not entail supplied invariant" }
  end;
  if !Globals.print_x_inv && n=0 then begin
	print_string ("\ncomputed invariant for view: " ^ vdef.C.view_name ^ "\n"
				  ^ (Cprinter.string_of_pure_formula vdef.C.view_x_formula) ^ "\n");
	(* print_string ("\nxform':\n" ^ 
	   (Cprinter.string_of_pure_formula vdef.C.view_x_formula) ^ "\n"); *)
	print_string ("addr_vars: " 
				  ^ (String.concat ", " (List.map CP.name_of_spec_var vdef.C.view_addr_vars)) 
				  ^ "\n\n");
  end;

and trans_view (prog : I.prog_decl) (vdef : I.view_decl) : C.view_decl =
  let stab = H.create 103 in
  let view_formula = convert_heap2 prog vdef.I.view_formula in
  let data_name = I.data_name_of_view prog.I.prog_view_decls view_formula in
	vdef.I.view_data_name <- data_name;
	H.add stab self {sv_info_kind = Known (CP.OType data_name)};
	(*	H.add stab self {sv_info_kind = Unknown}; *)
	let cf = trans_formula prog true (self :: res :: vdef.I.view_vars) view_formula stab in
	let pf = trans_pure_formula vdef.I.view_invariant stab in
	let cf_fv = List.map CP.name_of_spec_var (CF.fv cf) in
	let pf_fv = List.map CP.name_of_spec_var (CP.fv pf) in
	  if List.mem res cf_fv || List.mem res pf_fv then
		Err.report_error {Err.error_loc = IF.pos_of_formula view_formula;
						  Err.error_text = "res is not allowed in view definition or invariant"}
	  else
		let name_to_sv (v : ident) : CP.spec_var = 
		  try
			let vinfo = H.find stab v in
			  match vinfo.sv_info_kind with
				| Known t -> CP.SpecVar (t, v, Unprimed)
				| Unknown -> Err.report_error {Err.error_loc = (IF.pos_of_formula view_formula);
											   Err.error_text = "couldn't infer type for " ^ v}
		  with
			| Not_found -> Err.report_error {Err.error_loc = (IF.pos_of_formula view_formula);
											 Err.error_text = v ^ " is undefined"} in
		let view_sv_vars = List.map name_to_sv vdef.I.view_vars in
		let get_vvar_type vvar =
		  try
			let vinfo = H.find stab vvar in
			  match vinfo.sv_info_kind with
				| Known t -> (t, vvar)
				| Unknown -> Err.report_error {Err.error_loc = (IF.pos_of_formula view_formula);
											   Err.error_text = "couldn't infer type for " ^ vvar}
		  with
			| Not_found -> failwith ("trans_view: serious error: " ^ vvar ^ " is not found in stab") in
		let typed_vars = List.map get_vvar_type vdef.I.view_vars in
		  (* setting view_typed_vars *)
		let _ = vdef.I.view_typed_vars <- typed_vars in
		let mvars = [] (* find_materialized_vars prog view_sv_vars cf *) in
		  (*
			let _ = print_string ("mvars for " ^ vdef.I.view_name ^ ": " 
			^ (String.concat ", " (List.map CP.name_of_spec_var mvars)) ^ "\n") in
		  *)
		let cvdef = { C.view_name = vdef.I.view_name;
					  C.view_vars = view_sv_vars;
					  C.view_modes = vdef.I.view_modes;
					  C.view_partially_bound_vars = []; (* set by Predcomp.gen_view *)
					  C.view_materialized_vars = mvars;
					  C.view_data_name = data_name;
					  C.view_formula = cf;
					  C.view_x_formula = pf;
					  C.view_addr_vars = [];
					  C.view_user_inv = pf } in
		  Debug.devel_pprint ("\n"^ Cprinter.string_of_view_decl cvdef) (CF.pos_of_formula cf);
		  (*
			print_string ("\n\nView " ^ cvdef.C.view_name ^ ":\n");
			print_stab stab;
		  *)
		  cvdef

and set_materialized_vars prog cdef = 
  let mvars = find_materialized_vars prog cdef.C.view_vars cdef.C.view_formula in
	if !Globals.print_mvars then begin
	  print_string ("\nInput parameters of predicate " ^ cdef.C.view_name ^ ": ");
	  print_string ((String.concat ", " (List.map CP.name_of_spec_var mvars)) ^ "\n")
	end;
	cdef.C.view_materialized_vars <- mvars;
	cdef

(*
  This function can repeatedly unfold all predicates
  used in the definition until no more parameter is
  materialized or all parameters are materialized.
  Since there is a finite number of parameters, the
  process terminates.
*)
and find_materialized_vars prog params (f0 : CF.formula) : CP.spec_var list =
  let tmp0 = find_mvars prog params f0 in
  let all_mvars = ref tmp0 in
  let ef = ref f0 in
  let quit_loop = ref false in
	while not !quit_loop do
	  ef := Solver.expand_all_preds prog !ef;
	  let tmp1 = find_mvars prog params !ef in
	  let tmp2 = CP.remove_dups (tmp1 @ !all_mvars) in
	  let tmp3 = CP.difference tmp2 !all_mvars in
		if U.empty tmp3 then begin
		  quit_loop := true
		end else begin
		  all_mvars := tmp3
		end
	done;
	!all_mvars

and find_mvars prog (params : CP.spec_var list) (f0 : CF.formula) : CP.spec_var list = match f0 with
  | CF.Or ({CF.formula_or_f1 = f1;
			CF.formula_or_f2 = f2}) ->
	  let mvars1 = find_mvars prog params f1 in
	  let mvars2 = find_mvars prog params f2 in
	  let mvars = CP.remove_dups (mvars1 @ mvars2) in
	  let tmp = CP.intersect mvars params in
		tmp
  | CF.Base ({CF.formula_base_heap = hf;
			  CF.formula_base_pure = pf}) ->
	  let mvars = find_mvars_heap prog params hf pf in
	  let tmp = CP.intersect mvars params in
		tmp
  | CF.Exists ({CF.formula_exists_qvars = qvars;
				CF.formula_exists_heap = hf;
				CF.formula_exists_pure = pf}) ->
	  let mvars1 = find_mvars_heap prog params hf pf  in
	  let mvars = CP.difference mvars1 qvars in
	  let tmp = CP.intersect mvars params in
		tmp

and find_mvars_heap prog params hf pf = match hf with
  | CF.HTrue | CF.HFalse -> []
  | _ -> begin 
	  (* 
		 if the heap part if non-empty, by well-founded condition, 
		 self must be pointing to a node 
	  *)
	  let eqns = Solver.ptr_equations pf in
	  let asets = Solver.alias eqns in
		(* find the alias set containing p *)
	  let self_aset = Solver.get_aset asets (CP.SpecVar (CP.OType "", self, Unprimed)) in 
		self_aset
	end
	  
and all_paths_return (e0 : I.exp) : bool = match e0 with
  | I.Assert _ -> false
  | I.Assign _ -> false
  | I.Binary _ -> false
  | I.Bind e -> all_paths_return e.I.exp_bind_body
  | I.Block e -> all_paths_return e.I.exp_block_body
  | I.BoolLit _ -> false
  | I.Break _ -> false
  | I.CallNRecv _ -> false
  | I.CallRecv _ -> false
  | I.Cast _ -> false
  | I.Cond e -> all_paths_return e.I.exp_cond_then_arm && all_paths_return e.I.exp_cond_else_arm
  | I.ConstDecl _ -> false
  | I.Continue _ -> false
  | I.Debug _ -> false
  | I.Dprint _ -> false
  | I.Empty _ -> false
  | I.FloatLit _ -> false
  | I.IntLit _ -> false
  | I.Java _ -> false
  | I.Member _ -> false
  | I.New _ -> false
  | I.Null _ -> false
  | I.Return _ -> true
  | I.Seq e -> all_paths_return e.I.exp_seq_exp1 || all_paths_return e.I.exp_seq_exp2
  | I.This _ -> false
  | I.Unary _ -> false
  | I.Var _ -> false
  | I.VarDecl _ -> false
  | I.While _ -> false (* the body of while may be skipped, so may the returns in there *)
  | I.Unfold _ -> false

and check_return (proc : I.proc_decl) : bool = match proc.I.proc_body with
  | None -> true
  | Some e -> 
	  if (not (I.are_same_type I.void_type proc.I.proc_return)) && (not (all_paths_return e)) then
		false
	  else 
		true

and trans_proc (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  let dup_names = U.find_one_dup (fun a1 -> fun a2 -> 
									a1.I.param_name = a2.I.param_name) proc.I.proc_args in
	if not (U.empty dup_names) then
	  let p = List.hd dup_names in
		Err.report_error { Err.error_loc = p.I.param_loc; 
						   Err.error_text = "parameter " 
			^ p.I.param_name ^ " is duplicated" }
	else if not (check_return proc) then
	  Err.report_error { Err.error_loc = proc.I.proc_loc; 
						 Err.error_text = "not all paths of " 
		  ^ proc.I.proc_name ^ " contain a return"}
	else begin
	  E.push_scope ();
	  (* add parameter to the new scope *)
	  let all_args = 
		if U.is_some proc.I.proc_data_decl then
		  let cdef = U.unsome proc.I.proc_data_decl in
		  let this_arg = { I.param_type = I.Named cdef.I.data_name;
						   I.param_name = this;
						   I.param_mod = I.NoMod;
						   I.param_loc = proc.I.proc_loc } in
			this_arg :: proc.I.proc_args
		else
		  proc.I.proc_args in
	  let p2v (p : I.param) = { E.var_name = p.I.param_name;
								E.var_alpha = p.I.param_name;
								E.var_type = p.I.param_type } in
	  let vinfos = List.map p2v all_args in
	  let _ = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
		(* check pre/post list: build list of free vars and initial stab *)
	  let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
	  let free_vars = List.map (fun p -> p.I.param_name) all_args in
	  let stab = H.create 103 in
	  let add_param p = H.add stab p.I.param_name 
		{sv_info_kind = Known (trans_type prog p.I.param_type p.I.param_loc)}
	  in
		ignore (List.map add_param all_args);
		let trans_pre_post (pre, post) = 
		  let cpre = trans_formula prog false free_vars pre stab in
		  let tmp_vars = List.map CP.name_of_spec_var (CF.fv cpre) in
		  let post_free_vars = self :: res :: (U.remove_dups (free_vars @ tmp_vars)) in
		  let _ = H.add stab res {sv_info_kind = (Known cret_type)} in
		  let cpost = trans_formula prog true post_free_vars post stab in
		  let pre_fv = List.map CP.name_of_spec_var (CF.fv cpre) in
		  let post_fv = List.map CP.name_of_spec_var (CF.fv cpost) in
			if (List.mem self pre_fv || List.mem self post_fv) then
			  Err.report_error {Err.error_loc = (IF.pos_of_formula pre);
								Err.error_text = "self is not allowed in pre/postcondition"}
			else if List.mem res pre_fv then
			  Err.report_error {Err.error_loc = (IF.pos_of_formula pre);
								Err.error_text = "res is not allowed in precondition"}
			else
			  (* check if res has the correct type, pre/post don't contain self *)
			  try 
				let resinfo = H.find stab res in
				  match resinfo.sv_info_kind with
					| Known t -> 
						if sub_type t cret_type then (cpre, cpost)
						else Err.report_error {Err.error_loc = (IF.pos_of_formula post);
											   Err.error_text = "res is used inconsistently"}
					| Unknown ->
						Err.report_error {Err.error_loc = (IF.pos_of_formula post);
										  Err.error_text = "can't infer type for res"}
						  
			  with
				| Not_found -> (cpre, cpost) in
		let static_specs_list = List.map trans_pre_post proc.I.proc_static_specs in
		let dynamic_specs_list = List.map trans_pre_post proc.I.proc_dynamic_specs in
		  (* check method body *)
		let body = match proc.I.proc_body with
		  | None -> None
		  | Some e -> begin
			  let b, tb = trans_exp prog proc e in
				Some b
			end in
		let args = List.map (fun p -> (trans_type prog p.I.param_type p.I.param_loc, p.I.param_name)) 
		  proc.I.proc_args in
		let by_names_tmp = List.filter (fun p -> (p.I.param_mod = I.RefMod)) proc.I.proc_args in
		let new_pt p = trans_type prog p.I.param_type p.I.param_loc in
		let by_names = List.map (fun p -> CP.SpecVar 
								   (new_pt p, p.I.param_name, Unprimed)) by_names_tmp in
		let final_static_specs_list = 
		  if U.empty static_specs_list then [(CF.mkTrue proc.I.proc_loc, CF.mkTrue proc.I.proc_loc)] 
		  else static_specs_list in
        let final_dynamic_specs_list = 
		  (* if U.empty dynamic_specs_list then [(CF.mkTrue proc.I.proc_loc, CF.mkTrue proc.I.proc_loc)] 
			 else *) dynamic_specs_list in   
		let cproc = { C.proc_name = proc.I.proc_mingled_name;
					  C.proc_args = args;
					  C.proc_return = trans_type prog proc.I.proc_return proc.I.proc_loc;
					  C.proc_static_specs = final_static_specs_list;
			          C.proc_dynamic_specs = final_dynamic_specs_list;
					  C.proc_by_name_params = by_names;
					  C.proc_body = body;
					  C.proc_loc = proc.I.proc_loc } in
		  E.pop_scope ();
		  cproc
	end

(*
  translating coercions, split them to left to right and right to left coercions
*)
and trans_coercions (prog : I.prog_decl) : (C.coercion_decl list * C.coercion_decl list) =
  let tmp = List.map (fun coer -> trans_one_coercion prog coer) prog.I.prog_coercion_decls in
  let tmp1, tmp2 = List.split tmp in
  let tmp3 = List.concat tmp1 in
  let tmp4 = List.concat tmp2 in
	(tmp3, tmp4)

(*
  translation of pre/post condition: different translations for 2 directions.
  left-to-right direction: LHS: precond, RHS: postcond
  right-to-left direction: RHS: precond, LHS: postcond
  ???
*)
and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl) : (C.coercion_decl list * C.coercion_decl list) =
  let stab = H.create 103 in
	(* translate the formulae *)
  let c_lhs = trans_formula prog false [self] coer.I.coercion_head stab in
  let lhs_fnames = List.map CP.name_of_spec_var (CF.fv c_lhs) in
	(* compute universally quantified variables *)
  let compute_univ () =
	let h, p, _ = CF.split_components c_lhs in
	let pvars = CP.fv p in
	let hvars = CF.h_fv h in
	let univ_vars = CP.difference pvars hvars in
	  CP.remove_dups univ_vars 
  in
  let univ_vars = compute_univ () in
	(* 
	   we only existentially quantify variables that are not
	   already universally quantified in the antecedent.
	*)
  let lhs_fnames = Util.difference lhs_fnames (List.map CP.name_of_spec_var univ_vars) in
  let c_rhs = trans_formula prog (U.empty univ_vars) (self :: lhs_fnames) coer.I.coercion_body stab in
  let rhs_fnames = List.map CP.name_of_spec_var (CF.fv c_rhs) in
  let c_lhs_exist = trans_formula prog true (self :: rhs_fnames) coer.I.coercion_head stab in
	(* find the names of the predicates from the LHS and RHS of the coercion *)
  let lhs_name = find_view_name c_lhs self (IF.pos_of_formula coer.I.coercion_head) in
  let rhs_name = 
	try find_view_name c_rhs self (IF.pos_of_formula coer.I.coercion_body) 
	with
	  | _ -> ""
  in
	if lhs_name = "" then
	  Error.report_error { Err.error_loc = IF.pos_of_formula coer.I.coercion_head;
						   Err.error_text = "root pointer of node on LHS must be self" }
		(* TODO: FIX IT
		   else if rhs_name = "" then
		   Error.report_error { Err.error_loc = IF.pos_of_formula coer.I.coercion_body;
		   Err.error_text = "self must point to a node in RHS" }
		*)
	else
	  let c_coer = { C.coercion_name = coer.I.coercion_name;
					 C.coercion_head = c_lhs;
					 C.coercion_body = c_rhs;
					 C.coercion_univ_vars = univ_vars;
					 C.coercion_head_exist = c_lhs_exist;
					 C.coercion_head_view = lhs_name;
					 C.coercion_body_view = rhs_name } in
		(*		print_string ("\ncoercion_head: " ^ (Cprinter.string_of_formula c_lhs) ^ "\n");
				print_string ("\ncoercion_body: " ^ (Cprinter.string_of_formula c_rhs) ^ "\n"); *)
		match coer.I.coercion_type with
		  | I.Left -> ([c_coer], [])
		  | I.Equiv -> ([c_coer], [c_coer])
		  | I.Right -> ([], [c_coer])

(*
  and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl) : (C.coercion_decl list * C.coercion_decl list) =
  let stab1 = H.create 103 in
(* for left-to-right direction *)
  let l2r_pre = trans_formula prog false [self] coer.I.coercion_head stab1 in
  let l2r_fnames = List.map CP.name_of_spec_var (CF.fv l2r_pre) in
  let l2r_post = trans_formula prog true (self :: l2r_fnames) coer.I.coercion_body stab1 in
(* for right-to-left direction *)
  let stab2 = H.create 103 in
  let r2l_pre = trans_formula prog false [self] coer.I.coercion_body stab2 in
  let r2l_fnames = List.map CP.name_of_spec_var (CF.fv r2l_pre) in
  let r2l_post = trans_formula prog true (self :: r2l_fnames) coer.I.coercion_head stab2 in
(* find the names of the predicates from the LHS and RHS of the coercion *)
  let lhs_name = find_view_name l2r_pre self (IF.pos_of_formula coer.I.coercion_head) in
  let rhs_name = find_view_name l2r_post self (IF.pos_of_formula coer.I.coercion_body) in
  if lhs_name = "" then
  Error.report_error { Err.error_loc = IF.pos_of_formula coer.I.coercion_head;
  Err.error_text = "root pointer of node on LHS must be self" }
  else if rhs_name = "" then
  Error.report_error { Err.error_loc = IF.pos_of_formula coer.I.coercion_body;
  Err.error_text = "self must point to a node in RHS" }
  else
  let l2r = { C.coercion_head = l2r_pre;
  C.coercion_body = l2r_post;
  C.coercion_head_view = lhs_name;
  C.coercion_body_view = rhs_name } in
  let r2l = { C.coercion_head = r2l_pre;
  C.coercion_body = r2l_post;
  C.coercion_head_view = rhs_name;
  C.coercion_body_view = lhs_name } in
(*		print_string ("\ncoercion_head: " ^ (Cprinter.string_of_formula c_lhs) ^ "\n");
  print_string ("\ncoercion_body: " ^ (Cprinter.string_of_formula c_rhs) ^ "\n"); *)
  match coer.I.coercion_type with
  | I.Left -> ([l2r], [])
  | I.Equiv -> ([l2r], [r2l])
  | I.Right -> ([], [r2l])
*)

(* find the name of the view pointed by v in f0  *)
and find_view_name (f0 : CF.formula) (v : ident) pos = match f0 with
  | CF.Base ({CF.formula_base_heap = h;
			  CF.formula_base_pure = _;
			  CF.formula_base_pos = _}) 
  | CF.Exists ({CF.formula_exists_qvars = _;
				CF.formula_exists_heap = h;
				CF.formula_exists_pure = _;
				CF.formula_exists_pos = _}) -> 
	  begin
		let rec find_view_heap h0 = match h0 with
		  | CF.Star ({CF.h_formula_star_h1 = h1;
					  CF.h_formula_star_h2 = h2;
					  CF.h_formula_star_pos = _}) ->
			  let name1 = find_view_heap h1 in
			  let name2 = find_view_heap h2 in
				if name1 = "" then name2
				else if name2 = "" then name1
				else
				  Err.report_error { Err.error_loc = pos;
									 Err.error_text = v ^ " must point to only one view" }
		  | CF.DataNode ({CF.h_formula_data_node = p;
						  CF.h_formula_data_name = c;
						  CF.h_formula_data_arguments = _;
						  CF.h_formula_data_pos = _}) ->
			  if CP.name_of_spec_var p = v then
				Err.report_error { Err.error_loc = pos;
								   Err.error_text = v ^ " must point to a view" }
			  else ""
		  | CF.ViewNode ({CF.h_formula_view_node = p;
						  CF.h_formula_view_name = c;
						  CF.h_formula_view_arguments = _;
						  CF.h_formula_view_pos = _}) ->
			  if CP.name_of_spec_var p = v then
				c
			  else ""
		  | CF.HTrue | CF.HFalse -> ""
		in
		  find_view_heap h
	  end
  | CF.Or _ -> Err.report_error { Err.error_loc = pos;
								  Err.error_text = "Pre- and post-conditions of coercion rules must not be disjunctive" }

(*
  What are done by this function:
  - standard type checking
  - flattening AST
  - alpha-renaming
  - substitute constant in

  -- too much stuff inside one function

  What does it need to do its job:
  - environment

  return value:
  - translated expression (having type C.exp (in second component))
  - type of expression 
  - whether this can be assignment target, and if so, 
  what is the target. used with translating e1 = e2
*)
and trans_exp (prog : I.prog_decl) (proc : I.proc_decl) (ie : I.exp) : trans_exp_type = match ie with
  | I.Unfold ({I.exp_unfold_var = (v, p);
			   I.exp_unfold_pos = pos}) -> begin
	  (C.Unfold ({C.exp_unfold_var = CP.SpecVar (CP.OType "", v, p);
				  C.exp_unfold_pos = pos}), C.void_type)
	end
  | I.Assert ({I.exp_assert_asserted_formula = assert_f_o;
			   I.exp_assert_assumed_formula = assume_f_o;
			   I.exp_assert_pos = pos}) -> 
	  begin
		(* translate two formulae using all visible names *)
		let tmp_names = E.visible_names () in
		  (* build initial stab *)
		let all_names = List.map (fun (t, n) -> (trans_type prog t pos, n)) tmp_names in
		let free_vars = List.map snd all_names in
		let stab = H.create 19 in
		  ignore (List.map (fun (t, n) -> H.add stab n {sv_info_kind = Known t}) all_names);
		  let assert_cf_o = 
			match assert_f_o with
			  | Some f -> Some (trans_formula prog false free_vars f stab)
			  | None -> None in
		  let assume_cf_o = 
			match assume_f_o with
			  | None -> None
			  | Some f -> Some (trans_formula prog false free_vars f stab) in
		  let assert_e = C.Assert ({C.exp_assert_asserted_formula = assert_cf_o;
									C.exp_assert_assumed_formula = assume_cf_o;
									C.exp_assert_pos = pos}) in
			(assert_e, C.void_type)
	  end
  | I.Assign ({I.exp_assign_op = aop;
			   I.exp_assign_lhs = lhs;
			   I.exp_assign_rhs = rhs;
			   I.exp_assign_pos = pos_a}) -> 
	  begin
		match aop with
		  | I.OpAssign -> begin
			  match lhs with
				| I.Var ({I.exp_var_name = v0; I.exp_var_pos = pos}) ->
					let ce1, te1 = trans_exp prog proc lhs in
					let ce2, te2 = trans_exp prog proc rhs in
					  if not (sub_type te2 te1) then
						Err.report_error {Err.error_loc = pos; 
										  Err.error_text = "lhs and rhs do not match"}
					  else
						let v = C.get_var ce1 in (* v0 could be alpha-converted *)
						let assign_e = C.Assign ({C.exp_assign_lhs = v; 
												  C.exp_assign_rhs = ce2; 
												  C.exp_assign_pos = pos}) in
						  if C.is_var ce1 then
							(assign_e, C.void_type)
						  else
							let seq_e = C.Seq ({C.exp_seq_type = C.void_type;
												C.exp_seq_exp1 = ce1;
												C.exp_seq_exp2 = assign_e;
												C.exp_seq_pos = pos}) in
							  (seq_e, C.void_type)
				| I.Member ({I.exp_member_base = base_e;
							 I.exp_member_fields = fs;
							 I.exp_member_pos = pos}) -> 
					begin
					  let rhs_c, rhs_t = trans_exp prog proc rhs in
					  let fn, new_var =
						match rhs_c with
						  | C.Var ({C.exp_var_name = v}) -> (v, false)
						  | _ -> (fresh_name (), true) in
					  let fn_var = C.Var ({C.exp_var_type = rhs_t;
										   C.exp_var_name = fn;
										   C.exp_var_pos = pos}) in
					  let tmp_e, tmp_t = flatten_to_bind prog proc base_e 
						(List.rev fs) (Some fn_var) pos in
					  let fn_decl = 
						if new_var then 
						  C.VarDecl ({C.exp_var_decl_type = rhs_t;
									  C.exp_var_decl_name = fn;
									  C.exp_var_decl_pos = pos}) 
						else C.Unit pos in
					  let init_fn = 
						if new_var then
						  C.Assign ({C.exp_assign_lhs = fn;
									 C.exp_assign_rhs = rhs_c;
									 C.exp_assign_pos = pos}) 
						else C.Unit pos in
					  let seq1 = C.mkSeq tmp_t init_fn tmp_e pos in
					  let seq2 = C.mkSeq tmp_t fn_decl seq1 pos in
						if new_var then
						  (C.Block ({C.exp_block_type = tmp_t;
									 C.exp_block_body = seq2;
									 C.exp_block_local_vars = [(rhs_t, fn)];
									 C.exp_block_pos = pos}), tmp_t)
						else 
						  (seq2, tmp_t)

					(*					  
					(* if not (I.contains_field rhs) then begin *)
										  if I.is_var rhs then begin
										  match base_e with
										  | I.Member ({I.exp_member_base = e1;
										  I.exp_member_fields = fs1;
										  I.exp_member_pos = pos1}) -> 
										  let new_ie = I.Assign ({I.exp_assign_op = aop;
										  I.exp_assign_lhs = I.Member ({I.exp_member_base = e1;
										  I.exp_member_fields = fs1 @ fs;
										  I.exp_member_pos = pos});
										  I.exp_assign_rhs = rhs;
										  I.exp_assign_pos = pos_a}) in
										  trans_exp prog proc new_ie
										  | _ -> begin
										  let ce, te = trans_exp prog proc base_e in
										  let ce2, te2 = trans_exp prog proc rhs in
										  let dname = C.name_of_type te in
										  if C.is_var ce then
										  let res_e,_ = convert_to_bind prog (C.get_var ce) dname fs (Some ce2) pos in
										  (res_e, C.void_type)
										  else
										  let fn = fresh_name () in
										  let fn_decl = C.VarDecl ({C.exp_var_decl_type = te;
										  C.exp_var_decl_name = fn;
										  C.exp_var_decl_pos = pos}) in
										  let init_fn = C.Assign ({C.exp_assign_lhs = fn;
										  C.exp_assign_rhs = ce;
										  C.exp_assign_pos = pos}) in
										  let fn_e, fn_t = convert_to_bind prog fn dname fs (Some ce2) pos in
										  let seq1 = C.Seq ({C.exp_seq_type = fn_t;
										  C.exp_seq_exp1 = init_fn;
										  C.exp_seq_exp2 = fn_e;
										  C.exp_seq_pos = pos}) in
										  let local_vars = [(te, fn)] in (* this is the newly introduced variable in this block *)
										  let seq2 = C.Block ({C.exp_block_type = fn_t;
										  C.exp_block_body = C.Seq ({C.exp_seq_type = fn_t; C.exp_seq_exp1 = fn_decl; C.exp_seq_exp2 = seq1; C.exp_seq_pos = pos}); 
										  C.exp_block_local_vars = local_vars;
										  C.exp_block_pos = pos}) in
										  (seq2, fn_t)
										  end
										  end else begin
					(* in case RHS is a complex expression, like x.f = y.g, 
										  introduce a local variable: tmp = y.g; x.f = tmp *)
										  let _, lhs_t = trans_exp prog proc lhs in 
					(* I know this causes lhs to be re-translated, 
										  but hopefully not too much work *)
										  let lhs_it = trans_type_back lhs_t in
										  let fn = fresh_name () in
										  let fn_decl = I.VarDecl ({I.exp_var_decl_type = lhs_it;
										  I.exp_var_decl_decls = [(fn, Some rhs, pos)];
										  I.exp_var_decl_pos = pos}) in
										  let lhs_a = I.Assign ({I.exp_assign_op = aop;
										  I.exp_assign_lhs = lhs;
										  I.exp_assign_rhs = (I.Var ({I.exp_var_name = fn;
										  I.exp_var_pos = pos}));
										  I.exp_assign_pos = pos}) in
										  let seq = I.Seq ({I.exp_seq_exp1 = fn_decl;
										  I.exp_seq_exp2 = lhs_a;
										  I.exp_seq_pos = pos}) in
										  trans_exp prog proc seq
										  end
					*)
					end
				| _ -> Err.report_error {Err.error_loc = pos_a; Err.error_text = "lhs is not an lvalue"}
			end
		  | _ -> begin
			  let bop = bin_op_of_assign_op aop in
			  let new_rhs = I.Binary ({I.exp_binary_op = bop;
									   I.exp_binary_oper1 = lhs;
									   I.exp_binary_oper2 = rhs;
									   I.exp_binary_pos = pos_a}) in
			  let new_assign = I.Assign ({I.exp_assign_op = I.OpAssign;
										  I.exp_assign_lhs = lhs;
										  I.exp_assign_rhs = new_rhs;
										  I.exp_assign_pos = pos_a}) in
				trans_exp prog proc new_assign
			end
	  end
  | I.Binary ({I.exp_binary_op = b_op;
			   I.exp_binary_oper1 = e1;
			   I.exp_binary_oper2 = e2;
			   I.exp_binary_pos = pos}) -> begin
	  if I.is_null e1 || I.is_null e2 then
		let e1', e2' = if I.is_null e2 then (e1, e2) else (e2, e1) in
		let new_op = (match b_op with
						| I.OpEq -> I.OpIsNull
						| I.OpNeq -> I.OpIsNotNull
						| _ -> Err.report_error {Err.error_loc = pos; 
												 Err.error_text = "null can only be used with == or !="}) in
		let b_call = get_binop_call new_op in
		let new_e = I.CallNRecv ({I.exp_call_nrecv_method = b_call;
								  I.exp_call_nrecv_arguments = [e1'];
								  I.exp_call_nrecv_pos = pos}) in
		  trans_exp prog proc new_e
	  else
		let b_call = get_binop_call b_op in
		let new_e = I.CallNRecv ({I.exp_call_nrecv_method = b_call;
								  I.exp_call_nrecv_arguments = [e1; e2];
								  I.exp_call_nrecv_pos = pos}) in
		  trans_exp prog proc new_e
	end
  | I.Bind ({I.exp_bind_bound_var = v;
			 I.exp_bind_fields = vs;
			 I.exp_bind_body = e;
			 I.exp_bind_pos = pos}) -> 
	  begin
		try
		  let vinfo_tmp = E.look_up v in
			match vinfo_tmp with
			  | E.VarInfo vi -> begin
				  match vi.E.var_type with
					| I.Named c ->
						let ddef = I.look_up_data_def pos prog.I.prog_data_decls c in
						  if List.length vs != List.length ddef.I.data_fields then
							Err.report_error {Err.error_loc = pos; 
											  Err.error_text = "bind " ^ v 
								^ ": different number of variables"}
						  else begin
							E.push_scope ();
							let _ = List.map2 (fun vi -> fun ti ->
												 let alpha = E.alpha_name vi in
												   E.add vi (E.VarInfo {E.var_name = vi; 
																		E.var_alpha = alpha; 
																		E.var_type = ti}))
							  vs (List.map fst (List.map fst ddef.I.data_fields)) in
							let vs_types = List.map (fun fld -> 
													   trans_type prog (fst (fst fld)) (snd fld)) 
							  ddef.I.data_fields in
							let vt = trans_type prog vi.E.var_type pos in
							let ce, te = trans_exp prog proc e in
							let _ = E.pop_scope () in
							  (C.Bind ({C.exp_bind_type = te;
										C.exp_bind_bound_var = (vt, v);
										C.exp_bind_fields = (List.combine vs_types vs);
										C.exp_bind_body = ce;
										C.exp_bind_pos = pos}), te)
						  end
					| I.Prim _ -> Err.report_error {Err.error_loc = pos; 
													Err.error_text = v ^ " is not a data type"}
					| I.Array _ -> Err.report_error {Err.error_loc = pos; 
													 Err.error_text = v ^ " is not a data type"}
				end
			  | _ -> Err.report_error {Err.error_loc = pos; Err.error_text = v ^ " is not a data type"}
		with
		  | Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = v ^ " is not defined"}
	  end
  | I.Block ({I.exp_block_body = e;
			  I.exp_block_pos = pos}) -> 
	  begin
		E.push_scope();
		let ce, te = trans_exp prog proc e in
		let tmp_local_vars = E.names_on_top () in
		let local_vars = List.map (fun (t, n) -> (trans_type prog t pos, n)) tmp_local_vars in
		  E.pop_scope();
		  (C.Block ({C.exp_block_type = te;
					 C.exp_block_body = ce;
					 C.exp_block_local_vars = local_vars;
					 C.exp_block_pos = pos}), te)
	  end
  | I.BoolLit ({I.exp_bool_lit_val = b;
				I.exp_bool_lit_pos = pos}) -> 
	  (C.BConst ({C.exp_bconst_val = b; C.exp_bconst_pos = pos}), C.bool_type)
  | I.CallRecv ({I.exp_call_recv_receiver = recv; 
				 I.exp_call_recv_method = mn;
				 I.exp_call_recv_arguments = args;
				 I.exp_call_recv_pos = pos}) -> 
	  begin
		let crecv, crecv_t = trans_exp prog proc recv in
		let recv_ident, recv_init, new_recv_ident = (* receiver identifier and how to initialize it *)
		  match crecv with
			| C.Var ({C.exp_var_name = v}) -> (v, C.Unit pos, false)
			| _ -> 
				let fname = fresh_name () in
				let fdecl = C.VarDecl ({C.exp_var_decl_type = crecv_t;
										C.exp_var_decl_name = fname;
										C.exp_var_decl_pos = pos}) in
				let finit = C.Assign ({C.exp_assign_lhs = fname;
									   C.exp_assign_rhs = crecv;
									   C.exp_assign_pos = pos}) in
				let seq = C.mkSeq C.void_type fdecl finit pos in
				  (fname, seq, true) in
		let tmp = List.map (trans_exp prog proc) args in
		let cargs, cts = List.split tmp in
		let mingled_mn = C.mingle_name mn cts in
		let class_name = C.name_of_type crecv_t in
		  try
			let cdef = I.look_up_data_def pos prog.I.prog_data_decls class_name in
			let all_methods = I.look_up_all_methods prog cdef in
			let pdef = I.look_up_proc_def_mingled_name all_methods mingled_mn in
			  if List.length args != List.length pdef.I.proc_args then
				Err.report_error {Err.error_loc = pos; 
								  Err.error_text = "number of arguments does not match"}
			  else
				let parg_types = List.map 
				  (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
				  if List.exists2 (fun t1 -> fun t2 -> not (sub_type t1 t2)) cts parg_types then
					Err.report_error {Err.error_loc = pos; 
									  Err.error_text = "argument types do not match"}
				  else
					let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
					let positions = List.map I.get_exp_pos args in
					let local_vars, init_seq, arg_vars = trans_args (U.combine3 cargs cts positions) in
					let visi_names = E.visible_names () in
					let visi_svars = List.map 
					  (fun (t, n) -> CP.SpecVar (trans_type prog t pos, n, Primed)) visi_names in
					let call_e = C.ICall ({C.exp_icall_type = ret_ct;
										   C.exp_icall_receiver = recv_ident;
										   C.exp_icall_receiver_type = crecv_t;
										   C.exp_icall_method_name = mingled_mn;
										   C.exp_icall_arguments = arg_vars;
										   C.exp_icall_visible_names = visi_svars;
										   C.exp_icall_pos = pos}) in
					let seq1 = C.mkSeq ret_ct init_seq call_e pos in
					let seq2 = C.mkSeq ret_ct recv_init seq1 pos in
					let blk = C.Block ({C.exp_block_type = ret_ct;
										C.exp_block_body = seq2;
										C.exp_block_local_vars = 
										   (if new_recv_ident then [(crecv_t, recv_ident)] else [])
										   @ local_vars;
										C.exp_block_pos = pos}) in
					  (blk, ret_ct)
		  with
		    | Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = "procedure " ^ mingled_mn ^ " is not found"};
      end
  | I.CallNRecv ({I.exp_call_nrecv_method = mn;
				  I.exp_call_nrecv_arguments = args;
				  I.exp_call_nrecv_pos = pos}) ->
      begin
		let tmp = List.map (trans_exp prog proc) args in
		let cargs, cts = List.split tmp in
		let mingled_mn = C.mingle_name mn cts in
		let this_recv = (* finding if "this" is the potential receiver *)
		  if U.is_some proc.I.proc_data_decl then 
			let cdef = U.unsome proc.I.proc_data_decl in
			let tmp1 = I.look_up_all_methods prog cdef in
			let tmp2 = List.exists (fun p -> p.I.proc_mingled_name = mingled_mn) tmp1 in
			  tmp2
		  else false 
		in
		  if this_recv then
			let call_recv = I.CallRecv ({I.exp_call_recv_receiver = I.This ({I.exp_this_pos = pos});
										 I.exp_call_recv_method = mingled_mn;
										 I.exp_call_recv_arguments = args;
										 I.exp_call_recv_pos = pos}) in
			  trans_exp prog proc call_recv
		  else 
			try (* only static methods need to be considered *)
			  let pdef = I.look_up_proc_def_mingled_name prog.I.prog_proc_decls mingled_mn in
				if List.length args != List.length pdef.I.proc_args then
				  Err.report_error {Err.error_loc = pos; Err.error_text = "number of arguments does not match"}
				else
				  let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
					if List.exists2 (fun t1 -> fun t2 -> not (sub_type t1 t2)) cts parg_types then
					  Err.report_error {Err.error_loc = pos; 
										Err.error_text = "argument types do not match"}
					else if Inliner.is_inlined mn then
					  let inlined_exp = Inliner.inline prog pdef ie in
						trans_exp prog proc inlined_exp
					else
					  let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
					  let positions = List.map I.get_exp_pos args in
					  let local_vars, init_seq, arg_vars = trans_args (U.combine3 cargs cts positions) in
					  let visi_names = E.visible_names () in
					  let visi_svars = List.map (fun (t, n) -> CP.SpecVar (trans_type prog t pos, n, Primed)) visi_names in
					  let call_e = C.SCall ({C.exp_scall_type = ret_ct;
											 C.exp_scall_method_name = mingled_mn;
											 C.exp_scall_arguments = arg_vars;
											 C.exp_scall_visible_names = visi_svars;
											 C.exp_scall_pos = pos}) in
					  let seq_1 = C.mkSeq ret_ct init_seq call_e pos in
						(C.Block ({C.exp_block_type = ret_ct;
								   C.exp_block_body = seq_1;
								   C.exp_block_local_vars = local_vars;
								   C.exp_block_pos = pos}), ret_ct)
			with
			  | Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = "procedure " ^ mingled_mn ^ " is not found"};
      end
  | I.Cond ({I.exp_cond_condition = e1;
			 I.exp_cond_then_arm = e2;
			 I.exp_cond_else_arm = e3;
			 I.exp_cond_pos = pos}) -> begin
	  let ce1, te1 = trans_exp prog proc e1 in
		if not (CP.are_same_types te1 C.bool_type) then
		  Err.report_error {Error.error_loc = pos; Error.error_text = "conditional expression is not bool"}
		else
		  let ce2', te2 = trans_exp prog proc e2 in
		  let ce3', te3 = trans_exp prog proc e3 in
		  let ce2 = insert_dummy_vars ce2' pos in
		  let ce3 = insert_dummy_vars ce3' pos in
			(* if not (CP.are_same_types te2 te3) then
			   Err.report_error {Error.error_loc = pos; Error.error_text = "two branches of if do not match"}
			   else *)
			match ce1 with
			  | C.Var ({C.exp_var_type = _;
						C.exp_var_name = v;
						C.exp_var_pos = _}) -> (C.Cond ({C.exp_cond_type = te2;
														 C.exp_cond_condition = v;
														 C.exp_cond_then_arm = ce2;
														 C.exp_cond_else_arm = ce3;
														 C.exp_cond_pos = pos}), te2)
			  | _ -> begin
				  let fn = fresh_name () in
				  let vd = C.VarDecl ({C.exp_var_decl_type = C.bool_type;
									   C.exp_var_decl_name = fn;
									   C.exp_var_decl_pos = pos}) in
				  let init_e = C.Assign ({C.exp_assign_lhs = fn;
										  C.exp_assign_rhs = ce1;
										  C.exp_assign_pos = pos}) in
				  let cond_e = C.Cond ({C.exp_cond_type = te2;
										C.exp_cond_condition = fn;
										C.exp_cond_then_arm = ce2;
										C.exp_cond_else_arm = ce3;
										C.exp_cond_pos = pos}) in
				  let tmp_e1 = C.Seq ({C.exp_seq_type = te2;
									   C.exp_seq_exp1 = init_e;
									   C.exp_seq_exp2 = cond_e;
									   C.exp_seq_pos = pos}) in
				  let tmp_e2 = C.Seq ({C.exp_seq_type = te2;
									   C.exp_seq_exp1 = vd;
									   C.exp_seq_exp2 = tmp_e1;
									   C.exp_seq_pos = pos}) in
					(tmp_e2, te2)
				end
	end
  | I.Debug ({I.exp_debug_flag = flag;
			  I.exp_debug_pos = pos}) -> begin
	  (C.Debug ({C.exp_debug_flag = flag; 
				 C.exp_debug_pos = pos}), C.void_type)
	end
  | I.Dprint ({I.exp_dprint_string = str;
			   I.exp_dprint_pos = pos}) -> begin
	  let tmp_visib_names = E.visible_names () in
	  let tmp_visib_names = List.filter (fun v -> I.is_named_type (fst v)) tmp_visib_names in
	  let visib_names = List.map snd tmp_visib_names in
	  let ce = C.Dprint ({C.exp_dprint_string = str;
						  C.exp_dprint_visible_names = visib_names;
						  C.exp_dprint_pos = pos}) in
		(ce, C.void_type)
	end
  | I.Empty pos -> (C.Unit pos, C.void_type)
  | I.IntLit ({I.exp_int_lit_val = i;
			   I.exp_int_lit_pos = pos}) -> (C.IConst ({C.exp_iconst_val = i;
														C.exp_iconst_pos = pos}), C.int_type)
  | I.Java ({I.exp_java_code = jcode;
			 I.exp_java_pos = pos }) -> begin
	  (C.Java ({C.exp_java_code = jcode;
				C.exp_java_pos = pos}), C.void_type)
	end
  | I.Member ({I.exp_member_base = e;
			   I.exp_member_fields = fs;
			   I.exp_member_pos = pos}) -> 
	  begin
		flatten_to_bind prog proc e (List.rev fs) None pos
	  end
  | I.New ({I.exp_new_class_name = c;
			I.exp_new_arguments = args;
			I.exp_new_pos = pos}) -> 
      begin
		let data_def = I.look_up_data_def pos prog.I.prog_data_decls c in
		let all_fields = I.look_up_all_fields prog data_def in
		let field_types = List.map (fun f -> fst (fst f)) all_fields in
		let nargs = List.length args in
		  if nargs != List.length field_types then
			Err.report_error {Err.error_loc = pos; 
							  Err.error_text = "number of arguments does not match"}
		  else		  
			let tmp = List.map (trans_exp prog proc) args in
			let cargs, cts = List.split tmp in
			let parg_types = List.map (fun ft -> trans_type prog ft pos) field_types in
			  if List.exists2 (fun t1 -> fun t2 -> not (sub_type t1 t2)) cts parg_types then
				Err.report_error {Err.error_loc = pos; 
								  Err.error_text = "argument types do not match"}
			  else
				let positions = U.repeat pos nargs in
				let local_vars, init_seq, arg_vars = trans_args (U.combine3 cargs cts positions) in
				let new_e = C.New ({C.exp_new_class_name = c;
									C.exp_new_parent_name = data_def.I.data_parent_name;
									C.exp_new_arguments = (List.combine parg_types arg_vars);
									C.exp_new_pos = pos}) in
				let new_t = CP.OType c in
				let seq_e = C.mkSeq new_t init_seq new_e pos in
				  (C.Block ({C.exp_block_type = new_t;
							 C.exp_block_body = seq_e;
							 C.exp_block_local_vars = local_vars;
							 C.exp_block_pos = pos}), new_t)
      end
  | I.Null pos -> (C.Null pos, CP.OType "")
  | I.Return ({I.exp_return_val = oe;
			   I.exp_return_pos = pos}) -> 
	  begin
		let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
		  match oe with
			| None -> 
				if CP.are_same_types cret_type C.void_type then
				  (C.Return ({C.exp_return_type = C.void_type;
							  C.exp_return_val = None;
							  C.exp_return_pos = pos}), C.void_type)
				else
				  Err.report_error { Err.error_loc = proc.I.proc_loc; 
									 Err.error_text = "return statement for procedures with non-void return type need a value" }
			| Some e -> 
				let ce, ct = trans_exp prog proc e in
				  if sub_type ct cret_type then
					(C.Return ({C.exp_return_type = C.void_type;
								C.exp_return_val = Some ce;
								C.exp_return_pos = pos}), C.void_type)
				  else
					Err.report_error { Err.error_loc = proc.I.proc_loc; 
									   Err.error_text = "return type doesn't match" }

	  end
  | I.Seq ({I.exp_seq_exp1 = e1;
			I.exp_seq_exp2 = e2;
			I.exp_seq_pos = pos}) -> begin
	  let ce1', te1 = trans_exp prog proc e1 in
	  let ce2, te2 = trans_exp prog proc e2 in
	  let ce1 = insert_dummy_vars ce1' pos in
		(C.Seq ({C.exp_seq_type = te2;
				 C.exp_seq_exp1 = ce1;
				 C.exp_seq_exp2 = ce2;
				 C.exp_seq_pos = pos}), te2)
	end
  | I.This ({I.exp_this_pos = pos}) -> begin
	  if U.is_some proc.I.proc_data_decl then
		let cdef = U.unsome proc.I.proc_data_decl in
		let ct = CP.OType cdef.I.data_name in
		  (C.This ({C.exp_this_type = ct;
					C.exp_this_pos = pos}), ct)
	  else
		Err.report_error { Err.error_loc = pos;
						   Err.error_text = "\"this\" can only be used in members of a class" }
	end
  | I.Unary ({I.exp_unary_op = u_op;
			  I.exp_unary_exp = e;
			  I.exp_unary_pos = pos}) -> 
	  begin
		match u_op with
		  | I.OpNot -> begin
			  let u_call = "not___" in
			  let call_e = I.CallNRecv ({I.exp_call_nrecv_method = u_call;
										 I.exp_call_nrecv_arguments = [e];
										 I.exp_call_nrecv_pos = pos}) in
				trans_exp prog proc call_e
			end
		  | I.OpPostInc -> begin (* only integers *)
			  let fn = fresh_name () in
			  let fn_decl = I.VarDecl ({I.exp_var_decl_type = I.int_type;
										I.exp_var_decl_decls = [(fn, Some e, pos)];
										I.exp_var_decl_pos = pos}) in
			  let add1_e = I.Binary ({I.exp_binary_op = I.OpPlus;
									  I.exp_binary_oper1 = e;
									  I.exp_binary_oper2 = I.IntLit ({I.exp_int_lit_val = 1;
																	  I.exp_int_lit_pos = pos});
									  I.exp_binary_pos = pos}) in
			  let assign_e = I.Assign ({I.exp_assign_op = I.OpAssign;
										I.exp_assign_lhs = e;
										I.exp_assign_rhs = add1_e;
										I.exp_assign_pos = pos}) in
			  let seq1 = I.Seq ({I.exp_seq_exp1 = assign_e;
								 I.exp_seq_exp2 = I.Var ({I.exp_var_name = fn; I.exp_var_pos = pos});
								 I.exp_seq_pos = pos}) in
			  let seq2 = I.Seq ({I.exp_seq_exp1 = fn_decl;
								 I.exp_seq_exp2 = seq1;
								 I.exp_seq_pos = pos}) in
				trans_exp prog proc (I.Block ({I.exp_block_body = seq2;
											   I.exp_block_pos = pos}))
			end
		  | I.OpPostDec -> begin
			  let fn = fresh_name () in
			  let fn_decl = I.VarDecl ({I.exp_var_decl_type = I.int_type;
										I.exp_var_decl_decls = [(fn, Some e, pos)];
										I.exp_var_decl_pos = pos}) in
			  let sub1_e = I.Binary ({I.exp_binary_op = I.OpMinus;
									  I.exp_binary_oper1 = e;
									  I.exp_binary_oper2 = I.IntLit ({I.exp_int_lit_val = 1;
																	  I.exp_int_lit_pos = pos});
									  I.exp_binary_pos = pos}) in
			  let assign_e = I.Assign ({I.exp_assign_op = I.OpAssign;
										I.exp_assign_lhs = e;
										I.exp_assign_rhs = sub1_e;
										I.exp_assign_pos = pos}) in
			  let seq1 = I.Seq ({I.exp_seq_exp1 = assign_e;
								 I.exp_seq_exp2 = I.Var ({I.exp_var_name = fn;
														  I.exp_var_pos = pos});
								 I.exp_seq_pos = pos}) in
			  let seq2 = I.Seq ({I.exp_seq_exp1 = fn_decl;
								 I.exp_seq_exp2 = seq1;
								 I.exp_seq_pos = pos}) in
				trans_exp prog proc (I.Block ({I.exp_block_body = seq2;
											   I.exp_block_pos = pos}))
			end
		  | I.OpPreInc -> begin (* only integers *)
			  let add1_e = I.Binary ({I.exp_binary_op = I.OpPlus;
									  I.exp_binary_oper1 = e;
									  I.exp_binary_oper2 = I.IntLit ({I.exp_int_lit_val = 1;
																	  I.exp_int_lit_pos = pos});
									  I.exp_binary_pos = pos}) in
			  let assign_e = I.Assign ({I.exp_assign_op = I.OpAssign;
										I.exp_assign_lhs = e;
										I.exp_assign_rhs = add1_e;
										I.exp_assign_pos = pos}) in
			  let seq = I.Seq ({I.exp_seq_exp1 = assign_e;
								I.exp_seq_exp2 = e;
								I.exp_seq_pos = pos}) in
				trans_exp prog proc (I.Block ({I.exp_block_body = seq;
											   I.exp_block_pos = pos}))
			end
		  | I.OpPreDec -> begin (* only integers *)
			  let sub1_e = I.Binary ({I.exp_binary_op = I.OpMinus;
									  I.exp_binary_oper1 = e;
									  I.exp_binary_oper2 = I.IntLit ({I.exp_int_lit_val = 1;
																	  I.exp_int_lit_pos = pos});
									  I.exp_binary_pos = pos}) in
			  let assign_e = I.Assign ({I.exp_assign_op = I.OpAssign;
										I.exp_assign_lhs = e;
										I.exp_assign_rhs = sub1_e;
										I.exp_assign_pos = pos}) in
			  let seq = I.Seq ({I.exp_seq_exp1 = assign_e;
								I.exp_seq_exp2 = e;
								I.exp_seq_pos = pos}) in
				trans_exp prog proc (I.Block ({I.exp_block_body = seq;
											   I.exp_block_pos = pos}))
			end
		  | _ -> failwith ("u_op not supported yet")
	  end
  | I.Var ({I.exp_var_name = v;
			I.exp_var_pos = pos}) -> 
	  begin
		try
		  let vinfo_tmp = E.look_up v in
			match vinfo_tmp with
			  | E.VarInfo vi -> let ct = trans_type prog vi.E.var_type pos in
				  (C.Var ({C.exp_var_type = ct;
						   C.exp_var_name = vi.E.var_alpha;
						   C.exp_var_pos = pos}), ct)
			  | E.ConstInfo ci -> let ct = trans_type prog ci.E.const_type pos in
				  (ci.E.const_value, ct)
			  | E.EnumInfo ei -> let ct = trans_type prog ei.E.enum_type pos in
				  (C.IConst ({C.exp_iconst_val = ei.E.enum_value;
							  C.exp_iconst_pos = pos}), ct)
		with
		  | Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = v ^ " is not defined"}
	  end
  | I.VarDecl ({I.exp_var_decl_type = t;
				I.exp_var_decl_decls = decls;
				exp_var_decl_pos = tpos}) -> 
	  begin (* decls can't be empty *)
		let ct = trans_type prog t tpos in
		let rec helper ds = match ds with
		  | [(v, oe, pos)] -> begin
			  if E.name_clash v then
				Err.report_error {Err.error_loc = pos; Err.error_text = v ^ " is already declared"}
			  else begin
				let alpha = E.alpha_name v in
				  E.add v (E.VarInfo {E.var_name = v; E.var_alpha = alpha; E.var_type = t});
				  let init_val = match oe with
					| Some e -> begin
						let tmp_e, tmp_t = trans_exp prog proc e in
						  if sub_type tmp_t ct then
							tmp_e
						  else
							Err.report_error {Err.error_loc = pos; 
											  Err.error_text = "initializer doesn't match variable type"}
					  end
					| None -> default_value ct pos in
				  let init_e = C.Assign ({C.exp_assign_lhs = alpha;
										  C.exp_assign_rhs = init_val;
										  C.exp_assign_pos = pos}) in
				  let var_decl = C.VarDecl ({C.exp_var_decl_type = ct;
											 C.exp_var_decl_name = alpha;
											 C.exp_var_decl_pos = pos}) in
					C.Seq ({C.exp_seq_type = C.void_type;
							C.exp_seq_exp1 = var_decl;
							C.exp_seq_exp2 = init_e;
							C.exp_seq_pos = pos})
			  end
			end
		  | (v, oe, pos) :: rest -> begin
			  let crest = helper rest in
			  let ce = helper [(v, oe, pos)] in
				C.Seq ({C.exp_seq_type = C.void_type;
						C.exp_seq_exp1 = ce;
						C.exp_seq_exp2 = crest;
						C.exp_seq_pos = pos})
			end
		  | [] -> failwith ("trans_exp: VarDecl has an empty declaration list")
		in
		  (helper decls, C.void_type)
	  end
  | I.While ({I.exp_while_condition = cond;
			  I.exp_while_body = body;
			  I.exp_while_specs = prepost;
			  I.exp_while_pos = pos}) -> 
	  begin
		let tvars = E.visible_names () in
		let w_args = List.map (fun tv -> I.Var ({I.exp_var_name = snd tv;
												 I.exp_var_pos = pos})) tvars in
		let w_name = fresh_name () ^ "_" ^ (U.replace_path_sep_with_uscore 
											  (U.replace_dot_with_uscore (string_of_loc pos))) in
		let w_body_1 = convert_while_body body w_name w_args in
		let w_body_2 = I.Block ({I.exp_block_body = I.Seq ({I.exp_seq_exp1 = w_body_1;
															I.exp_seq_exp2 = I.CallNRecv ({I.exp_call_nrecv_method = w_name;
																						   I.exp_call_nrecv_arguments = w_args;                                                                                           I.exp_call_nrecv_pos = pos});
															I.exp_seq_pos = pos});
								 I.exp_block_pos = pos}) in
		let w_body = I.Block ({I.exp_block_body = I.Cond ({I.exp_cond_condition = cond;
														   I.exp_cond_then_arm = w_body_2;
														   I.exp_cond_else_arm = I.Empty pos;
														   I.exp_cond_pos = pos});
							   I.exp_block_pos = pos}) in
		let w_formal_args = List.map (fun tv -> { I.param_type = fst tv; 
												  I.param_name = snd tv;
												  I.param_mod = I.RefMod;
												  I.param_loc = pos }) tvars in
		let w_proc = { I.proc_name = w_name;
					   I.proc_mingled_name = mingle_name_enum prog w_name (List.map fst tvars);
					   I.proc_data_decl = proc.I.proc_data_decl;
					   I.proc_constructor = false;
					   I.proc_args = w_formal_args;
					   I.proc_return = I.void_type;
                       I.proc_static_specs = prepost;			 
			           I.proc_dynamic_specs = []; 		  
					   I.proc_body = Some w_body;
					   I.proc_loc = pos } in
		let w_call = I.CallNRecv ({I.exp_call_nrecv_method = w_name;
								   I.exp_call_nrecv_arguments = w_args;
								   I.exp_call_nrecv_pos = pos}) in
		let new_prog = {prog with I.prog_proc_decls = w_proc :: prog.I.prog_proc_decls} in
		let iw_call, _ = trans_exp new_prog w_proc w_call in
		let cw_proc = trans_proc new_prog w_proc in
		  loop_procs := cw_proc :: !loop_procs;
		  (iw_call, C.void_type)
	  end
  | _ -> failwith ((Iprinter.string_of_exp ie))

and default_value (t : CP.typ) pos : C.exp = match t with
  | CP.Prim Int -> C.IConst ({C.exp_iconst_val = 0; C.exp_iconst_pos = pos})
  | CP.Prim Bool -> C.BConst ({C.exp_bconst_val = false; C.exp_bconst_pos = pos})
  | CP.Prim Float -> C.FConst ({C.exp_fconst_val = 0.0; C.exp_fconst_pos = pos})
  | CP.Prim Void -> failwith ("default_value: void in variable declaration should have been rejected by parser")
  | CP.Prim Bag -> failwith ("default_value: bag can only be used for constraints")
  | CP.OType c -> C.Null pos

and sub_type (t1 : CP.typ) (t2 : CP.typ) =
  let it1 = trans_type_back t1 in
  let it2 = trans_type_back t2 in
	I.sub_type it1 it2

and trans_type (prog : I.prog_decl) (t : I.typ) (pos : loc) : CP.typ = match t with
  | I.Prim p -> CP.Prim p
  | I.Named c -> begin
	  try
		let _ = I.look_up_data_def_raw prog.I.prog_data_decls c in
		  CP.OType c
	  with
		| Not_found -> begin
			try 
			  let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c in
				CP.Prim Int
			with
			  | Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = c ^ " is neither data nor enum type"}
		  end
	end
  | I.Array _ -> Err.report_error {Err.error_loc = pos; 
								   Err.error_text = "trans_type: array is not supported yet"}

(*
  rev_fs: the reversed of the list of field names.
  rhs_o: the optional rhs if the member access in on the lhs of an assignment.
  This parameter is only significant for the last field access, i.e. the first
  in rev_fs. Any recursive call will have a None for rhs_o.
*)
and flatten_to_bind prog proc (base : I.exp) (rev_fs : ident list) (rhs_o : C.exp option) pos = match rev_fs with
  | f :: rest -> begin
	  let cbase, base_t = flatten_to_bind prog proc base rest None pos in
	  let fn, new_var =
		match cbase with
		  | C.Var ({C.exp_var_name = v}) -> (v, false)
		  | _ -> (fresh_name (), true) in
	  let fn_decl = 
		if new_var then 
		  C.VarDecl ({C.exp_var_decl_type = base_t;
					  C.exp_var_decl_name = fn;
					  C.exp_var_decl_pos = pos}) 
		else C.Unit pos in
	  let init_fn = 
		if new_var then
		  C.Assign ({C.exp_assign_lhs = fn;
					 C.exp_assign_rhs = cbase;
					 C.exp_assign_pos = pos}) 
		else C.Unit pos in
		(* now we have fn.f as the field access *)
	  let dname = CP.name_of_type base_t in
	  let ddef = I.look_up_data_def pos prog.I.prog_data_decls dname in
		(* gen_names: generates fresh names for fields. 
		   It also returns the name generated for the field being accessed (fn) 
		   as the first component of the returned value *)
	  let rec gen_names (fn : ident) (flist : I.typed_ident list) : (I.typed_ident option * ident list) = match flist with
		| [] -> (None, [])
		| f::rest -> 
			let fresh_fn = (snd f) ^ "_" ^ (fresh_name ()) in
			let tmp, new_rest = gen_names fn rest in
			  if snd f = fn then
				(Some (fst f, fresh_fn), fresh_fn :: new_rest)
			  else
				(tmp, fresh_fn :: new_rest) in
	  let all_fields = I.look_up_all_fields prog ddef in
	  let field_types = List.map (fun f -> trans_type prog (fst (fst f)) pos) all_fields in
	  let tmp1, fresh_names = gen_names f (List.map fst all_fields) in
		if not (U.is_some tmp1) then
		  Err.report_error {Err.error_loc = pos; 
							Err.error_text = "field " ^ f ^ " is not accessible"}
		else
		  let vt, fresh_v = U.unsome tmp1 in
		  let ct = trans_type prog vt pos in
		  let bind_body, bind_type = 
			match rhs_o with
			  | None -> (C.Var ({C.exp_var_type = ct;
								 C.exp_var_name = fresh_v;
								 C.exp_var_pos = pos}), ct)
			  | Some rhs_e -> 
				  let rhs_t = C.type_of_exp rhs_e in
					if U.is_some rhs_t && sub_type (U.unsome rhs_t) ct then
					  (C.Assign ({C.exp_assign_lhs = fresh_v;
								  C.exp_assign_rhs = rhs_e;
								  C.exp_assign_pos = pos}), C.void_type)
					else
					  Err.report_error {Err.error_loc = pos; 
										Err.error_text = "lhs and rhs do not match"} in
		  let bind_e = C.Bind ({C.exp_bind_type = bind_type;
								C.exp_bind_bound_var = (CP.OType dname, fn);
								C.exp_bind_fields = (List.combine field_types fresh_names);
								C.exp_bind_body = bind_body;
								C.exp_bind_pos = pos}) in
		  let seq1 = C.mkSeq bind_type init_fn bind_e pos in
		  let seq2 = C.mkSeq bind_type fn_decl seq1 pos in
			if new_var then
			  (C.Block ({C.exp_block_type = bind_type;
						 C.exp_block_body = seq2;
						 C.exp_block_local_vars = [(base_t, fn)];
						 C.exp_block_pos = pos}), bind_type)
			else 
			  (seq2, bind_type)
	end
  | [] -> trans_exp prog proc base

and convert_to_bind prog (v : ident) (dname : ident) (fs : ident list) (rhs : C.exp option) pos : trans_exp_type = match fs with
  | f :: rest -> begin
	  try
		let ddef = I.look_up_data_def_raw prog.I.prog_data_decls dname in
		  (* gen_names: generates fresh names for fields. It also returns the name
			 generated for the field being accessed (fn) as the first component of the returned value *)
		let rec gen_names (fn : ident) (flist : I.typed_ident list) : (I.typed_ident option * ident list) = match flist with
		  | [] -> (None, [])
		  | f::rest -> 
			  let fresh_fn = (snd f) ^ "_" ^ (fresh_name ()) in
			  let tmp, new_rest = gen_names fn rest in
				if snd f = fn then
				  (Some (fst f, fresh_fn), fresh_fn :: new_rest)
				else
				  (tmp, fresh_fn :: new_rest) in
		let field_types = List.map (fun f -> trans_type prog (fst (fst f)) pos) ddef.I.data_fields in
		let tmp1, fresh_names = gen_names f (List.map fst ddef.I.data_fields) in
		  if not (U.is_some tmp1) then
			Err.report_error {Err.error_loc = pos; Err.error_text = "can't follow field " ^ f}
		  else
			let vt, fresh_v = U.unsome tmp1 in
			let ct = trans_type prog vt pos in
			let bind_body, bind_type = 
			  if U.empty rest then
			    match rhs with
				  | None -> (C.Var ({C.exp_var_type = ct;
									 C.exp_var_name = fresh_v;
									 C.exp_var_pos = pos}), ct)
				  | Some rhs_e -> 
					  let rhs_t = C.type_of_exp rhs_e in
						if U.is_some rhs_t && sub_type (U.unsome rhs_t) ct then
						  (C.Assign ({C.exp_assign_lhs = fresh_v;
									  C.exp_assign_rhs = rhs_e;
									  C.exp_assign_pos = pos}), C.void_type)
						else
						  Err.report_error {Err.error_loc = pos; Err.error_text = "lhs and rhs do not match"}
			  else
				convert_to_bind prog fresh_v (I.name_of_type vt) rest rhs pos
			in
			  (C.Bind ({C.exp_bind_type = bind_type;
						C.exp_bind_bound_var = (CP.OType dname, v);
						C.exp_bind_fields = (List.combine field_types fresh_names);
						C.exp_bind_body = bind_body;
						C.exp_bind_pos = pos}), bind_type)
	  with
		| Not_found -> Err.report_error {Err.error_loc = pos; Err.error_text = "can't follow field " ^ f}
	end
  | [] -> failwith ("convert_to_bind: empty field list")

and trans_type_back (te : CP.typ) : I.typ = match te with
  | CP.Prim p -> I.Prim p
  | CP.OType n -> I.Named n

(*
  flattening call arguments: 
  - assuming args and typs have the same length
  - introduce variables for arguments that are complex expressions (not variables)
  - initialize the variables to expression that the variable substitutes
  - return the newly introduced variable as a local variable (can be quantified after the call)
*)
and trans_args (args : (C.exp * CP.typ * loc) list) : (C.typed_ident list * C.exp * ident list) = match args with
  | arg :: rest -> begin
	  let rest_local_vars, rest_e, rest_names = trans_args rest in
		match arg with
		  | (C.Var ({C.exp_var_type = _;
					 C.exp_var_name = v;
					 C.exp_var_pos = _}), _, _) -> (rest_local_vars, rest_e, v::rest_names)
		  | (arg_e, at, pos) -> 
			  let fn = fresh_name () in
			  let fn_decl = C.VarDecl ({C.exp_var_decl_type = at;
										C.exp_var_decl_name = fn;
										C.exp_var_decl_pos = pos}) in
			  let fn_init = C.Assign ({C.exp_assign_lhs = fn;
									   C.exp_assign_rhs = arg_e;
									   C.exp_assign_pos = pos}) in
			  let seq1 = C.mkSeq C.void_type fn_init rest_e pos in (* rest_e, init_e are assignments, so they have type void *)
			  let seq2 = C.mkSeq C.void_type fn_decl seq1 pos in
			  let local_var = (at, fn) in
				(local_var :: rest_local_vars, seq2, fn::rest_names)
	end
  | [] -> ([], C.Unit no_pos, [])

and get_type_name_for_mingling (prog : I.prog_decl) (t : I.typ) : ident = match t with
  | I.Prim _ -> I.name_of_type t
  | I.Named c -> begin
	  try
		let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c in
		  "int" (* found an enum with type c, treat it as int *)
	  with
		| Not_found -> c (* assuming data otherwise *)
	end
  | I.Array _ -> failwith ("get_type_name_for_mingling: array is not supported yet")

and mingle_name_enum prog (m : ident) (targs : I.typ list) = 
  let param_tnames = String.concat "~" (List.map (get_type_name_for_mingling prog) targs) in
	m ^ "$" ^ param_tnames

and set_mingled_name (prog : I.prog_decl) =
  let rec helper1 (pdecls : I.proc_decl list) = match pdecls with
	| pdef :: rest ->
		let ptypes = List.map (fun p -> p.I.param_type) pdef.I.proc_args in
		  pdef.I.proc_mingled_name <- mingle_name_enum prog pdef.I.proc_name ptypes;
		  helper1 rest
	| [] -> ()
  in
  let rec helper2 (cdecls : I.data_decl list) = match cdecls with
	| cdef :: rest ->
		helper1 cdef.I.data_methods;
		helper2 rest
	| [] -> ()
  in
	helper1 prog.I.prog_proc_decls;
	helper2 prog.I.prog_data_decls

and convert_while_body (body0 : I.exp) (w_call : ident) (w_args : I.exp list) : I.exp = match body0 with
  | I.Break pos -> I.Return ({I.exp_return_val = None; I.exp_return_pos =  pos})
  | I.Continue pos -> I.CallNRecv ({I.exp_call_nrecv_method = w_call; 
									I.exp_call_nrecv_arguments = w_args;
									I.exp_call_nrecv_pos = pos})
  | I.Block ({I.exp_block_body = e;
			  I.exp_block_pos = pos}) -> 
	  let ce = convert_while_body e w_call w_args in
		I.Block ({I.exp_block_body = ce;
				  I.exp_block_pos = pos})
  | I.Cond ({I.exp_cond_condition = e1;
			 I.exp_cond_then_arm = e2;
			 I.exp_cond_else_arm = e3;
			 I.exp_cond_pos = pos}) -> 
	  let ce2 = convert_while_body e2 w_call w_args in
	  let ce3 = convert_while_body e3 w_call w_args in
		I.Cond ({I.exp_cond_condition = e1;
				 I.exp_cond_then_arm = ce2;
				 I.exp_cond_else_arm = ce3;
				 I.exp_cond_pos = pos})
  | I.Seq ({I.exp_seq_exp1 = e1;
			I.exp_seq_exp2 = e2;
			I.exp_seq_pos = pos}) ->
	  let ce1 = convert_while_body e1 w_call w_args in
	  let ce2 = convert_while_body e2 w_call w_args in
		I.Seq ({I.exp_seq_exp1 = ce1;
				I.exp_seq_exp2 = ce2;
				I.exp_seq_pos = pos})
  | I.While ({I.exp_while_condition = e1;
			  I.exp_while_body = e2;
			  I.exp_while_specs = prepost;
			  I.exp_while_pos = pos}) ->
	  let ce2 = convert_while_body e2 w_call w_args in
		I.While ({I.exp_while_condition = e1;
				  I.exp_while_body = ce2;
				  I.exp_while_specs = prepost;
				  I.exp_while_pos = pos})
  | _ -> body0

(* convert subexpression e of ce to v=e if e is non-void *)
and insert_dummy_vars (ce : C.exp) (pos : loc) : C.exp = match ce with
  | C.Seq ({C.exp_seq_type = t;
			C.exp_seq_exp1 = ce1;
			C.exp_seq_exp2 = ce2;
			C.exp_seq_pos = pos}) -> begin
	  (* we don't need to go down ce1 here, as trans_exp already does that *)
	  let new_ce2 = insert_dummy_vars ce2 pos in
		C.Seq ({C.exp_seq_type = t;
				C.exp_seq_exp1 = ce1;
				C.exp_seq_exp2 = new_ce2;
				C.exp_seq_pos = pos})
	end
  | _ -> begin
	  match C.type_of_exp ce with
		| None -> ce
		| Some t ->
			if CP.are_same_types t C.void_type then
			  ce
			else (* non-void e1, store the value to a dummy variable *)
			  let fn = fresh_name () in
			  let fn_decl = C.VarDecl ({C.exp_var_decl_type = t;
										C.exp_var_decl_name = fn;
										C.exp_var_decl_pos = pos}) in
			  let assign_e = C.Assign ({C.exp_assign_lhs = fn;
										C.exp_assign_rhs = ce;
										C.exp_assign_pos = pos}) in
			  let local_vars = [(t, fn)] in
			  let seq = C.Seq ({C.exp_seq_type = C.void_type;
								C.exp_seq_exp1 = fn_decl;
								C.exp_seq_exp2 = assign_e;
								C.exp_seq_pos = pos}) in
			  let block_e = C.Block ({C.exp_block_type = C.void_type;
									  C.exp_block_body = seq;
									  C.exp_block_local_vars = local_vars;
									  C.exp_block_pos = pos}) in
				block_e
	end


(* 
   translating formula
   - constraint type inference
   - convert complex heap arguments to variables and equalities
   - 

   quantify: true for post/view/assert/assume: some variables will be exist. quant.
   false for view: no variables in precondition will be exist. quant.

   fvars: when quantify is true, variables appearing in fvars are not quantified.

   f0: input formula
   
*)

and trans_formula (prog : I.prog_decl) (quantify : bool) (fvars: ident list) (f0 : IF.formula) stab : CF.formula =
  let f1 = convert_heap2 prog f0 in
	trans_formula1 prog quantify fvars f1 stab

and trans_formula1 prog quantify fvars f0 stab : CF.formula = match f0 with
  | IF.Or ({IF.formula_or_f1 = f1;
			IF.formula_or_f2 = f2;
			IF.formula_or_pos = pos}) ->
	  let tf1 = trans_formula1 prog quantify fvars f1 stab in
	  let tf2 = trans_formula1 prog quantify fvars f2 stab in
		CF.mkOr tf1 tf2 pos
  | IF.Base ({IF.formula_base_heap = h;
			  IF.formula_base_pure = p;
			  IF.formula_base_pos = pos}) -> begin
	  collect_type_info_pure p stab;
	  collect_type_info_heap prog h stab;
	  let ch = linearize_formula prog quantify fvars f0 stab in		
		(* remove all keys but keys in fvars if quantify is true *)
		if quantify then begin
		  let tmp_stab = H.create 103 in
			U.copy_keys fvars stab tmp_stab;	  
			H.clear stab;
			U.copy_keys fvars tmp_stab stab;
		end;
		ch
	end
  | IF.Exists ({IF.formula_exists_qvars = qvars;
				IF.formula_exists_heap = h;
				IF.formula_exists_pure = p;
				IF.formula_exists_pos = pos}) -> begin
	  collect_type_info_pure p stab;
	  collect_type_info_heap prog h stab;
	  let helper1 (ve, pe) stab =
		let ve_info = H.find stab ve in
		  match ve_info.sv_info_kind with
			| Known t -> CP.SpecVar (t, ve, pe)
			| Unknown -> Err.report_error 
				{Err.error_loc = pos;
				 Err.error_text = "couldn't infer type for " ^ ve}
	  in
	  let f1 = IF.Base ({IF.formula_base_heap = h;
						 IF.formula_base_pure = p;
						 IF.formula_base_pos = pos}) in
	  let ch = linearize_formula prog quantify fvars f1 stab in
	  let qsvars = List.map (fun qv -> helper1 qv stab) qvars in
	  let ch = CF.push_exists qsvars ch in
		(* remove all keys but keys in fvars if quantify is true *)
		if quantify then begin
		  let tmp_stab = H.create 103 in
		  let fvars = (List.map fst qvars) @ fvars in
			U.copy_keys fvars stab tmp_stab;	  
			H.clear stab;
			U.copy_keys fvars tmp_stab stab;
		end;
		ch
	end

(* linearize heap/view variables                            *)
(* quantify is true for view definition and postcondition   *)
(* and false for precondition. fvars are free variables,    *)
(* any occurrences of fvars inside formula need linearized  *)
(* The function returns a linearized formula with additional*)
(* constraints for the newly-introduced variables. It also  *)
(* returns a list of variables to be quantified.            *)
and linearize_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list) (f0 : IF.formula) (stab : spec_var_table) =
  (* this function process the list of arguments of a heap node and determine which  *)
  (* one should be linearized.                                                       *)
  (* idents in used_names include parameters/view vars and heap args and must be     *)
  (* quantified *)
  let rec match_exp (used_names : ident list) (hargs : IP.exp list) pos : 
	  (ident list * CP.spec_var list * CP.spec_var list * CP.formula) = match hargs with
		  (* return value: new_used_names, vars to be heap args, vars to be quantified, linking formula *)
		| e :: rest -> begin
			let new_used_names, e_hvars, e_evars, e_link = 
			  match e with
				| IP.Var ((ve, pe), pos_e) -> begin
					try
					  let ve_info = H.find stab ve in
					  let ve_sv = (match ve_info.sv_info_kind with
									 | Known t -> CP.SpecVar (t, ve, pe)
									 | Unknown -> Err.report_error 
										 {Err.error_loc = pos_e;
										  Err.error_text = "couldn't infer type for " ^ ve}) in
						if List.mem ve fvars || List.mem ve used_names then
						  (* if ve is a free var or ve already occurs, replace it by a fresh name *)
						  let fresh_v = CP.fresh_spec_var ve_sv in
						  (*--
						  print_string ("[astsimp.ml]: Fresh var " ^ (Cprinter.string_of_spec_var fresh_v) ^ "\n");
						  --*)
						  let link_f = CP.mkEqExp (CP.mkVar fresh_v pos_e) (CP.mkVar ve_sv pos_e) pos_e in
						  let quantified_var = if quantify then [fresh_v] else [] in
							(* no need to add fresh_v to used_names since it is a fresh variable, 
							   there's no other occurences of fresh_v *)
							(used_names, [fresh_v], quantified_var, link_f)
						else (* ve occurs for the first time *)
						  let quantified_var = if quantify then [ve_sv] else [] in
							(ve :: used_names, [ve_sv], quantified_var, CP.mkTrue pos_e)
					with
					  | Not_found -> 
						  Err.report_error {Err.error_loc = pos_e;
											Err.error_text = ve ^ " is undefined"}
				  end
				| _ -> begin (* if e is not a Var, it must be either null or arithmetic term (int_type) *)
					let pos_e = IP.pos_of_exp e in
					let fresh_n = (fresh_name ()) in
					let fresh_type =
					  if IP.is_null e then CP.OType "" 
					  else if IP.is_bag e then C.bag_type
					  else C.int_type
					in
					let fresh_v = CP.SpecVar (fresh_type, fresh_n, Unprimed) in
					  (* let fresh_v = CP.SpecVar (IP.get_exp_type e, fresh_n, Unprimed) in *)
					let link_f = CP.mkEqExp (CP.mkVar fresh_v pos_e) (trans_pure_exp e stab) pos_e in
					  (* let quantified_var = if quantify then [fresh_v] else [] in *)
					let quantified_var = [fresh_v] in
					  (used_names, [fresh_v], quantified_var, link_f)
				  end in
			let rest_used_names, rest_hvars, rest_evars, rest_link = match_exp new_used_names rest pos in
			let hvars = e_hvars @ rest_hvars in
			let evars = e_evars @ rest_evars in
			let link_f = CP.mkAnd e_link rest_link pos in
			  (rest_used_names, hvars, evars, link_f)
		  end
		| [] -> (used_names, [], [], CP.mkTrue pos) in
	(*
	  linearize_heap:
	  - used_names: names already used, so any new occurences in heap constraints
	  must be quantified
	  - f: input formula
	  return values:
	  - #1: more used names
	  - #2: variables to be quantified
	  - #3: output formula
	  - #4: formula to link newly introduced variables
	  - #5: constraint over type variables
	*)
  let rec linearize_heap used_names (f : IF.h_formula) pos : 
	  (ident list * CP.spec_var list * CF.h_formula * CP.formula * CF.t_formula) = match f with
		| IF.HeapNode2 h2 -> 
			let h = node2_to_node prog h2 in
			let fh = IF.HeapNode h in
			  linearize_heap used_names fh pos
		| IF.HeapNode ({IF.h_formula_heap_node = (v, p);
						IF.h_formula_heap_name = c;
						IF.h_formula_heap_arguments = exps;
						IF.h_formula_heap_full = full;
						IF.h_formula_heap_pos = pos}) -> begin
			try
			  let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
			  let new_used_names, hvars, evars, link_f = match_exp used_names exps pos in
			  let c0 =
				if vdef.I.view_data_name = "" then
				  let _ = trans_view prog vdef in
					(* print_string ("linearize_heap: trans_view invoked."); *)
					vdef.I.view_data_name
				else
				  vdef.I.view_data_name
			  in
			  let new_v = CP.SpecVar (CP.OType c0, v, p) in (*TODO: find the data name of vdef *)
			  let new_h = CF.ViewNode ({CF.h_formula_view_node = new_v;
										CF.h_formula_view_name = c;
										CF.h_formula_view_arguments = hvars;
										CF.h_formula_view_modes = vdef.I.view_modes;
										CF.h_formula_view_coercible = true;
										CF.h_formula_view_origins = [];
										CF.h_formula_view_pos = pos}) in
				(new_used_names, evars, new_h, link_f, CF.TypeTrue)
			with
			  | Not_found ->
			  	(*--
			  		for data node
			  	--*)
				  let ddef = I.look_up_data_def pos prog.I.prog_data_decls c in
				  let new_used_names, hvars, evars, link_f' = match_exp used_names exps pos in
				  let new_v = CP.SpecVar (CP.OType c, v, p) in
					(* we can use c for tvar. The actual type can be determined later on,
					   during entailment *)
				  let t_var = CP.SpecVar (CP.OType c, c(* --change made on 16.04.2008-- fresh_name ()*), Unprimed) in
				  (*--16.04.2008   *)
				  (*print_string ("[astsimp.ml]: type var " ^ (Cprinter.string_of_spec_var t_var) ^ "\n");*)
				  (*   16.04.2008--*)
				  let type_constr = CF.TypeSub ({CF.t_formula_sub_type_var = t_var;
												 CF.t_formula_sub_type_type = c}) in
					(*--16.04.2008   *)							 
					(*print_string ("[astsimp.ml]: Type " ^ c ^ "\n");	*)											 
					(*   16.04.2008--*)
					(* extension pointer *)
				  let pname = I.look_up_parent_name pos prog.I.prog_data_decls c in
				  let ext_name = gen_ext_name c pname in
				  let ext_var = CP.SpecVar (CP.OType ext_name, c (* --change made on 16.04.2008-- fresh_name ()*), Unprimed) in
				  (*--16.04.2008   *)
				  (*print_string ("[astsimp.ml]: extension var " ^ (Cprinter.string_of_spec_var ext_var) ^ "\n");*)
				  (*   16.04.2008--*)
				  let link_f =
					if full then
					  let ext_constr = CP.mkNull ext_var pos in
						CP.mkAnd link_f' ext_constr pos
					else
					  link_f' in
				  let new_h = CF.DataNode ({CF.h_formula_data_node = new_v;
											CF.h_formula_data_name = c;
											CF.h_formula_data_arguments = t_var :: ext_var :: hvars;
											CF.h_formula_data_pos = pos}) in
					(new_used_names, evars, new_h, link_f, type_constr)
		  end
		| IF.Star ({IF.h_formula_star_h1 = f1;
					IF.h_formula_star_h2 = f2;
					IF.h_formula_star_pos = pos}) ->
			let new_used_names1, qv1, lf1, link1, type1 = linearize_heap used_names f1 pos in
			let new_used_names2, qv2, lf2, link2, type2 = linearize_heap new_used_names1 f2 pos in
			let tmp_h = CF.mkStarH lf1 lf2 pos in
			let tmp_link = CP.mkAnd link1 link2 pos in
			let tmp_type = CF.mkAndType type1 type2 in
			  (new_used_names2, qv1 @ qv2, tmp_h, tmp_link, tmp_type)
		| IF.HTrue -> (used_names, [], CF.HTrue, CP.mkTrue pos, CF.TypeTrue)
		| IF.HFalse -> (used_names, [], CF.HFalse, CP.mkTrue pos, CF.TypeFalse) in
  let linearize_base used_names base = 
	let h = base.IF.formula_base_heap in
	let p = base.IF.formula_base_pure in
	let pos = base.IF.formula_base_pos in
	let _, h_evars, new_h, link_f, type_f = linearize_heap used_names h pos in
	let cp = trans_pure_formula p stab in
	let new_p = CP.mkAnd cp link_f pos in
	let tmp_evars4 =
	  if quantify then
		let tmp_evars1 = CP.fv cp in
		let excluded_evars = fvars in
		let tmp_evars2 = List.filter 
		  (fun (CP.SpecVar (_, v, _)) -> not (List.mem v excluded_evars)) tmp_evars1  in
		let tmp_evars3 = U.remove_dups (h_evars @ tmp_evars2) in
		  tmp_evars3
	  else
		h_evars in
	let tmp_evars = List.filter (fun (CP.SpecVar (_, v, _)) -> v != self) tmp_evars4 in 
	  (* remove self from quantified variables *)
	let result = CF.mkExists tmp_evars new_h new_p type_f pos in
	  (* at this point of time, no information about type is available,
		 hence the TypeTrue *)
	  if not (Util.empty tmp_evars) then begin
		Debug.pprint ("linearize_constraint: "
					  ^ (String.concat ", " (List.map Cprinter.string_of_spec_var tmp_evars))
					  ^ " are quantified\n") pos
	  end;
	  result
  in
	match f0 with
	  | IF.Or ({IF.formula_or_f1 = f1;
				IF.formula_or_f2 = f2;
				IF.formula_or_pos = pos}) ->
		  let lf1 = linearize_formula prog quantify fvars f1 stab in
		  let lf2 = linearize_formula prog quantify fvars f2 stab in
		  let result = CF.mkOr lf1 lf2 pos in
			result
	  | IF.Base base -> linearize_base [] base
	  | IF.Exists ({IF.formula_exists_heap = h;
					IF.formula_exists_pure = p;
					IF.formula_exists_pos = pos}) ->
		  let base = ({IF.formula_base_heap = h;
					   IF.formula_base_pure = p;
					   IF.formula_base_pos = pos}) in
			linearize_base [] base


and trans_pure_formula (f0 : IP.formula) stab : CP.formula = match f0 with
  | IP.BForm bf -> CP.BForm (trans_pure_b_formula bf stab)
  | IP.And (f1, f2, pos) -> 
	  let pf1 = trans_pure_formula f1 stab in
	  let pf2 = trans_pure_formula f2 stab in
		CP.mkAnd pf1 pf2 pos
  | IP.Or (f1, f2, pos) ->
	  let pf1 = trans_pure_formula f1 stab in
	  let pf2 = trans_pure_formula f2 stab in
		CP.mkOr pf1 pf2 pos
  | IP.Not (f, pos) ->
	  let pf = trans_pure_formula f stab in
		CP.mkNot pf pos
  | IP.Forall ((v, p), f, pos) ->
	  let pf = trans_pure_formula f stab in
	  let v_type = 
		let v_info = H.find stab v in
		  match v_info.sv_info_kind with
			| Known t -> t
			| Unknown -> Err.report_error {Err.error_loc = pos;
										   Err.error_text = "couldn't infer type for " ^ v} in
	  let sv = CP.SpecVar (v_type, v, p) in
		CP.mkForall [sv] pf pos
  | IP.Exists ((v, p), f, pos) ->
	  let pf = trans_pure_formula f stab in
	  let v_type = 
		let v_info = H.find stab v in
		  match v_info.sv_info_kind with
			| Known t -> t
			| Unknown -> Err.report_error {Err.error_loc = pos;
										   Err.error_text = "couldn't infer type for " ^ v} in
	  let sv = CP.SpecVar (v_type, v, p) in
		CP.mkExists [sv] pf pos

and trans_pure_b_formula (b0 : IP.b_formula) stab : CP.b_formula = match b0 with
  | IP.BConst (b, pos) -> CP.BConst (b, pos)
  | IP.BVar ((v, p), pos) -> CP.BVar (CP.SpecVar (C.bool_type, v, p), pos)
  | IP.Lt (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkLt pe1 pe2 pos
  | IP.Lte (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkLte pe1 pe2 pos
  | IP.Gt (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkGt pe1 pe2 pos
  | IP.Gte (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkGte pe1 pe2 pos
  | IP.Eq (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkEq pe1 pe2 pos
  | IP.Neq (e1, e2, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.mkNeq pe1 pe2 pos
  | IP.EqMax (e1, e2, e3, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
	  let pe3 = trans_pure_exp e3 stab in
		CP.EqMax (pe1, pe2, pe3, pos)
  | IP.EqMin (e1, e2, e3, pos) ->
	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
	  let pe3 = trans_pure_exp e3 stab in
		CP.EqMin (pe1, pe2, pe3, pos)
  | IP.BagIn ((v, p), e, pos) ->
      let pe = trans_pure_exp e stab in
		begin
		  try
			let v_info = H.find stab v in
			  match v_info.sv_info_kind with
				| Known t -> 
					let sv = CP.SpecVar (t, v, p) in
					  CP.BagIn (sv, pe, pos)
				| Unknown -> Err.report_error {Err.error_loc = pos;
											   Err.error_text = "couldn't infer type for " ^ v}
		  with
			| Not_found -> Err.report_error {Err.error_loc = pos;
											 Err.error_text = v ^ " is undefined"}
		end
		  (*let pe = trans_pure_exp e stab in
			CP.BagIn (CP.SpecVar (C.int_type, v, p), pe, pos) -- not OK because we might have other things besides primitive int inside the bag *)
  | IP.BagNotIn ((v, p), e, pos) ->
	  let pe = trans_pure_exp e stab in
		begin
		  try
			let v_info = H.find stab v in
			  match v_info.sv_info_kind with
				| Known t -> 
					let sv = CP.SpecVar (t, v, p) in
					  CP.BagNotIn (sv, pe, pos)
				| Unknown -> Err.report_error {Err.error_loc = pos;
											   Err.error_text = "couldn't infer type for " ^ v}
		  with
			| Not_found -> Err.report_error {Err.error_loc = pos;
											 Err.error_text = v ^ " is undefined"}
		end
		  (*CP.BagNotIn (CP.SpecVar (C.int_type, v, p), pe, pos)*)
  | IP.BagSub (e1, e2, pos) ->
  	  let pe1 = trans_pure_exp e1 stab in
	  let pe2 = trans_pure_exp e2 stab in
		CP.BagSub (pe1, pe2, pos)
  | IP.BagMax ((v1, p1), (v2, p2), pos) ->
	  CP.BagMax (CP.SpecVar (C.int_type, v1, p1), CP.SpecVar (C.bag_type, v2, p2), pos) (* for max and min I think is ok to consider int_type for now *)	
  | IP.BagMin ((v1, p1), (v2, p2), pos) ->
	  CP.BagMin (CP.SpecVar (C.int_type, v1, p1), CP.SpecVar (C.bag_type, v2, p2), pos)	

and trans_pure_exp (e0 : IP.exp) stab : CP.exp = match e0 with
  | IP.Null pos -> CP.Null pos
  | IP.Var ((v, p), pos) -> begin
	  try
		let v_info = H.find stab v in
		  match v_info.sv_info_kind with
			| Known t -> 
				let sv = CP.SpecVar (t, v, p) in
				  CP.Var (sv, pos)
			| Unknown ->
				let sv = CP.SpecVar (CP.OType "", v, p) in
				  CP.Var (sv, pos)
					(*TODO: fix this dirty hack
					  | Unknown -> Err.report_error {Err.error_loc = pos;
					  Err.error_text = "couldn't infer type for " ^ v}
					*)
	  with
		| Not_found -> Err.report_error {Err.error_loc = pos;
										 Err.error_text = v ^ " is undefined"}
	end
  | IP.IConst (c, pos) -> CP.IConst (c, pos)
  | IP.Add (e1, e2, pos) -> CP.Add (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Subtract (e1, e2, pos) -> CP.Subtract (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Mult (c, e, pos) -> CP.Mult (c, trans_pure_exp e stab, pos)
  | IP.Max (e1, e2, pos) -> CP.Max (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Min (e1, e2, pos) -> CP.Min (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Bag (elist, pos) -> begin 
	  CP.Bag (trans_pure_exp_list elist stab, pos) 
	end
  | IP.BagUnion (elist, pos) -> begin 
	  CP.BagUnion (trans_pure_exp_list elist stab, pos); 
	end
  | IP.BagIntersect (elist, pos) -> begin 
  	  CP.BagIntersect (trans_pure_exp_list elist stab, pos); 
	end
  | IP.BagDiff (e1, e2, pos) -> CP.BagDiff (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
	  
and trans_pure_exp_list (elist : IP.exp list) stab : CP.exp list = match elist with
  | [] -> begin []; end
  | e::rest -> trans_pure_exp e stab :: trans_pure_exp_list rest stab
	  
(******************************************************************)
(* Type reconstruction ********************************************)
(* First collect type for all variables appearing in constraints, *)
(* then use the info to transform constraints to correct forms    *)
(* Collecting type information order: heap, then arithmetic, then *)
(* pure pointer constraints. **************************************)
(******************************************************************)

and unify_var_kind (k1 : spec_var_kind) (k2 : spec_var_kind) : spec_var_kind option = match k1 with
  | Unknown -> Some k2
  | Known t1 ->
	  match k2 with
		| Unknown -> Some k1
		| Known t2 ->
			match t1 with
			  | CP.Prim _ -> if t1 = t2 then Some k1 else None
			  | CP.OType c1 ->
				  match t2 with
					| CP.Prim _ -> None
					| CP.OType c2 ->
						if c1 = "" then Some k2
						else if c2 = "" then Some k1
						else if c1 = c2 then Some k1
						else if sub_type t1 t2 then Some k1 (* the real type is t1 *)
						else if sub_type t2 t1 then Some k2 (* the real type is t2 *)
						else None
						  
(* returns var's binding if it is in stab. Otherwise returns Undetermined *)
and get_var_kind (var : ident) (stab : spec_var_table) = 
  try
	let r = H.find stab var in
	  r.sv_info_kind
  with
	| Not_found -> Unknown

and set_var_kind (var : ident) (k : spec_var_kind) (stab : spec_var_table) = 
  try 
	let r = H.find stab var in
	  r.sv_info_kind <- k;
	  r
  with
	| Not_found -> H.add stab var {sv_info_kind = k};
		H.find stab var

and collect_type_info_var (var : ident) stab (var_kind : spec_var_kind) pos =
  try
	let k = H.find stab var in
	let tmp = unify_var_kind k.sv_info_kind var_kind in
	  match tmp with
		| Some tmp_k -> k.sv_info_kind <- tmp_k
		| None -> report_error pos (var ^ " is used inconsistently")
  with
	| Not_found ->
		H.add stab var {sv_info_kind = var_kind}

and collect_type_info_pure (p0 : IP.formula) (stab : spec_var_table) : unit = match p0 with
  | IP.BForm b -> 
	  collect_type_info_b_formula b stab
  | IP.And (p1, p2, pos) | IP.Or (p1, p2, pos) ->
	  collect_type_info_pure p1 stab;
	  collect_type_info_pure p2 stab
  | IP.Not (p1, pos) -> 
	  collect_type_info_pure p1 stab
  | IP.Forall ((qv, qp), qf, pos) | IP.Exists ((qv, qp), qf, pos) ->
	  (* check to see if any uses of variables if qf conflicts with info stab *)
	  if H.mem stab qv then
		Err.report_error {Err.error_loc = pos;
						  Err.error_text = qv ^ " shallows outer name"}
	  else begin
		(* H.add stab qv {sv_info_kind = Known C.int_type}; *) (* only allow integer variable to be quantified *)
		collect_type_info_pure qf stab 
		  (* H.remove stab qv *) (* name shadowing is not allowed, hence this is not needed *)
	  end
		
and collect_type_info_b_formula b0 stab = match b0 with
  | IP.BConst _ -> ()
  | IP.BVar ((bv, bp), pos) ->
	  collect_type_info_var bv stab (Known C.bool_type) pos
  | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) 
  | IP.Gt (a1, a2, pos) | IP.Gte (a1, a2, pos) ->
	  collect_type_info_arith a1 stab;
	  collect_type_info_arith a2 stab
  | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) ->
	  collect_type_info_arith a1 stab;
	  collect_type_info_arith a2 stab;
	  collect_type_info_arith a2 stab
  | IP.BagIn ((v, p), e, pos) ->
	  (*collect_type_info_var v stab (Known C.int_type) pos;*)
	  collect_type_info_var v stab Unknown pos;
	  collect_type_info_bag e stab
  | IP.BagNotIn ((v, p), e, pos) ->
      collect_type_info_var v stab Unknown pos;
	  (*collect_type_info_var v stab (Known C.int_type) pos;*)
	  collect_type_info_bag e stab
  | IP.BagSub (e1, e2, pos) ->
  	  collect_type_info_bag e1 stab;
	  collect_type_info_bag e2 stab
  | IP.BagMax ((v1, p1), (v2, p2), pos) ->
	  collect_type_info_var v1 stab (Known C.int_type) pos;
	  collect_type_info_var v2 stab (Known C.bag_type) pos
  | IP.BagMin ((v1, p1), (v2, p2), pos) ->
	  collect_type_info_var v1 stab (Known C.int_type) pos;
	  collect_type_info_var v2 stab (Known C.bag_type) pos
  | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) -> 
	  (* can only say a1, a2 have to have the same type *)
	  if IP.is_var a1 && IP.is_var a2 then
		let va1 = IP.name_of_var a1 in
		let va2 = IP.name_of_var a2 in
		let k1 = get_var_kind va1 stab in
		let k2 = get_var_kind va2 stab in
		let r = unify_var_kind k1 k2 in
		  match r with
			| Some k -> (* make a1 and a2 point to the same entry *)
				let r = set_var_kind va1 k stab in
				  H.replace stab va2 r
			| None -> 
				print_stab stab;
				Err.report_error {
				  Err.error_loc = pos;
				  Err.error_text = "type-mismatch in equation (1): " 
					^ (Iprinter.string_of_b_formula b0)}
	  else if IP.is_var a1 || IP.is_var a2 then
		let a1', a2' = if IP.is_var a1 then a1, a2 else a2, a1 in
		let va1' = IP.name_of_var a1' in
		let k1 = get_var_kind va1' stab in
		let k2, _ = 
		  if IP.is_null a2' then 
			(Known (CP.OType "")), collect_type_info_pointer a2' (Known (CP.OType "")) stab
		  else 
			if IP.is_bag a2' then 
			  (Known C.bag_type), collect_type_info_bag a2' stab
			else (* since a2 is not a variable, if it's not null, it must be arithmetic term *)
			  (Known C.int_type), collect_type_info_arith a2' stab in
		let r = unify_var_kind k1 k2 in
		  match r with
			| Some k ->
				ignore (set_var_kind va1' k stab)
			| None -> Err.report_error {
				Err.error_loc = pos;
				Err.error_text = "type-mismatch in equation (2): "
				  ^ (Iprinter.string_of_b_formula b0)}
	  else (* both are expressions *)
		if IP.is_null a1 && IP.is_null a2 then
		  () (* null=null or null!=null --> nothing to do *)
		else if (not (IP.is_null a1)) && (not (IP.is_null a2)) then begin
		  if IP.is_bag a1 && IP.is_bag a2 then begin
			collect_type_info_bag a1 stab; 
		  	collect_type_info_bag a2 stab
		  end	
		  else begin
		  	collect_type_info_arith a1 stab; (* can only be arithmetic expression *)
		  	collect_type_info_arith a2 stab
		  end	
		end else
		  Err.report_error {
			Err.error_loc = pos;
			Err.error_text = "type-mismatch in equation (3): "
			  ^ (Iprinter.string_of_b_formula b0)}

and collect_type_info_arith a0 stab = match a0 with
  | IP.Null pos -> Err.report_error {Err.error_loc = pos;
									 Err.error_text = "null is not allowed in arithmetic term"}
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab (Known C.int_type) pos
  | IP.IConst _ -> ()
  | IP.Add (a1, a2, pos) 
  | IP.Subtract (a1, a2, pos) 
  | IP.Max (a1, a2, pos) 
  | IP.Min (a1, a2, pos) ->
	  collect_type_info_arith a1 stab;
	  collect_type_info_arith a2 stab
  | IP.Mult (c, a1, pos) ->
	  collect_type_info_arith a1 stab
  | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> 
	  failwith ("collect_type_info_arith: encountered bag constraint")

and collect_type_info_bag_content a0 stab = match a0 with
  | IP.Null pos -> Err.report_error {Err.error_loc = pos;
									 Err.error_text = "null is not allowed in arithmetic term"}
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab (Unknown) pos
  | IP.IConst _ -> ()
  | IP.Add (a1, a2, pos) 
  | IP.Subtract (a1, a2, pos) 
  | IP.Max (a1, a2, pos) 
  | IP.Min (a1, a2, pos) ->
	  collect_type_info_arith a1 stab;
	  collect_type_info_arith a2 stab
  | IP.Mult (c, a1, pos) ->
	  collect_type_info_arith a1 stab
  | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> 
	  failwith ("collect_type_info_arith: encountered bag constraint")

and collect_type_info_bag (e0 : IP.exp) stab = match e0 with	  
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab (Known C.bag_type) pos
  | IP.Bag(a::rest, pos) -> 
  	  collect_type_info_bag_content a stab;
  	  collect_type_info_bag (IP.Bag(rest, pos)) stab
  | IP.Bag([], pos) -> ()
  | IP.BagUnion (a::rest, pos) -> 
  	  collect_type_info_bag a stab;
  	  collect_type_info_bag (IP.BagUnion(rest, pos)) stab
  | IP.BagUnion ([], pos) -> ()
  | IP.BagIntersect (a::rest, pos) -> 
  	  collect_type_info_bag a stab;
  	  collect_type_info_bag (IP.BagIntersect(rest, pos)) stab
  | IP.BagIntersect ([], pos) -> ()	
  | IP.BagDiff (a1, a2, pos) ->
  	  collect_type_info_bag a1 stab;
  	  collect_type_info_bag a2 stab
  | IP.Min _ | IP.Max _ | IP.Mult _ | IP.Subtract _ | IP.Add _ | IP.IConst _ | IP.Null _ ->
	  failwith ("collect_type_info_bag: encountered arithmetic constraint")

and collect_type_info_pointer (e0 : IP.exp) (k : spec_var_kind) stab = match e0 with
  | IP.Null _ -> ()
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab k pos
  | _ -> Err.report_error {Err.error_loc = IP.pos_of_exp e0;
						   Err.error_text = "arithmetic is not allowed in pointer term"}

and collect_type_info_heap prog (h0 : IF.h_formula) stab = match h0 with
  | IF.Star ({IF.h_formula_star_h1 = h1;
			  IF.h_formula_star_h2 = h2;
			  IF.h_formula_star_pos = pos}) ->
	  collect_type_info_heap prog h1 stab;
	  collect_type_info_heap prog h2 stab
  | IF.HeapNode2 h2 -> 
	  let h = node2_to_node prog h2 in
	  let fh = IF.HeapNode h in
		collect_type_info_heap prog fh stab
  | IF.HeapNode ({IF.h_formula_heap_node = (v, p);
				  IF.h_formula_heap_name = c;
				  IF.h_formula_heap_arguments = ies;
				  IF.h_formula_heap_pos = pos}) -> begin
	  (* if c is a view, use the underlying data name *)
	  let dname =
		try
		  let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
			(* 
			   if c is a view, then see if types of arguments of the view
			   has been determined 
			*)
			if not (U.empty vdef.I.view_typed_vars) then begin
			  let rec helper exps tvars = match exps, tvars with
				| [], [] -> []
				| e :: rest1, t :: rest2 -> begin
					let tmp = helper rest1 rest2 in
					  match e with
						| IP.Var ((v, p), pos) -> (fst t, v) :: tmp
						| _ -> tmp 
				  end 
				| _ -> 
					Err.report_error {
					  Err.error_loc = pos;
					  Err.error_text = "number of arguments for view " 
						^ c ^ " does not match"} in
			  let tmp = helper ies vdef.I.view_typed_vars in
				ignore (List.map 
						  (fun (t, n) -> collect_type_info_var n stab (Known t) pos) tmp)
			end;
			vdef.I.view_data_name
		with
		  | Not_found -> (* check if it is a data *)
			  try
				ignore (I.look_up_data_def_raw prog.I.prog_data_decls c); c 
			  with
				| Not_found -> Err.report_error {Err.error_loc = pos;
												 Err.error_text = c 
					  ^ " is neither a data nor view name"} in
	  let check_ie st ie t =  (match t with
								 | CP.Prim Bool -> 
									 if IP.is_var ie then
									   collect_type_info_var (IP.name_of_var ie) 
										 st (Known C.bool_type) (IP.pos_of_exp ie)
									 else
									   Err.report_error {Err.error_loc = IP.pos_of_exp ie;
														 Err.error_text = "expecting type bool"}
								 | CP.Prim Int -> collect_type_info_arith ie st
								 | CP.Prim _ -> ()
								 | CP.OType _ -> collect_type_info_pointer ie (Known t) st); st
	  in
		if not (dname = "") then
		  (* we know for sure that this view is based on a data node  *)
		  (* v must be a pointer of type dname *)
		  collect_type_info_var v stab (Known (CP.OType dname)) pos; 
		try
		  let ddef = I.look_up_data_def_raw prog.I.prog_data_decls c in
		  let fields = I.look_up_all_fields prog ddef in
			if List.length ies = List.length fields then
			  let typs = List.map (fun f -> trans_type prog (fst (fst f)) pos) fields in
			  let _ = List.fold_left2 check_ie stab ies typs in
				()
			else
			  Err.report_error {Err.error_loc = pos;
								Err.error_text = "number of arguments for data " 
				  ^ c ^ " does not match"}
		with (* c is a view, get the types of the variables of c *)
		  | Not_found -> begin
			  try (* View vars and arguments must have same type.
					 This is done by making equations between view vars
					 and corresponding arguments and do type inference over them *)
				let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
				  if List.length ies = List.length vdef.I.view_vars then
					let mk_eq v ie = 
					  let pos = IP.pos_of_exp ie in
						IP.mkEqExp (IP.Var ((v, Unprimed), pos)) ie pos in
					let all_eqns = List.map2 mk_eq vdef.I.view_vars ies in
					let tmp_form = List.fold_left (fun f1 -> fun f2 -> IP.mkAnd f1 f2 pos) 
					  (IP.mkTrue pos) all_eqns 
					in
					  collect_type_info_pure tmp_form stab
				  else
					Err.report_error {Err.error_loc = pos;
									  Err.error_text = "number of arguments for view " ^ c ^ " does not match"}
			  with
				| Not_found -> report_error pos (c ^ " is neither a view nor data declaration")
			end
	end
  | IF.HTrue | IF.HFalse -> ()

and get_spec_var_stab (v : ident) stab pos =
  try
	let v_info = H.find stab v in
	  match v_info.sv_info_kind with
		| Known t -> 
			let sv = CP.SpecVar (t, v, Unprimed) in
			  sv
		| Unknown ->
			Err.report_error {Err.error_loc = pos;
							  Err.error_text = v ^ " is undefined"}
  with
	| Not_found -> Err.report_error {Err.error_loc = pos;
									 Err.error_text = v ^ " is undefined"}
		

(* some debugging utilities *)

and print_spec_var_kind (k : spec_var_kind) = match k with
  | Unknown -> "Unk"
  | Known t -> Cprinter.string_of_typ t

and print_stab (stab : spec_var_table) =
  let p k i = print_string (k ^ " --> " ^ (print_spec_var_kind i.sv_info_kind) ^ "\n") in
	print_string "\n";
	H.iter p stab;
	print_string "\n"
