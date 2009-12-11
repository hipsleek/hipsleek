(** New xpure, normalization, predicate soundness checking 
	Created December 2009 *)

(*

===========
   Notes
===========

- To see the xpure results, use:
   sleek filename.slk
- The results are of type memo (see below)
- Some examples in: examples/cuong_sleek

*)
	
open Globals
open Sleekcommons

module I = Iast
module IF = Iformula
module P = Ipure
module CP = Cpure
module IP = Iprinter
module O = Omega

type triple = (P.exp * P.exp * P.formula)

type memo = (triple list * P.formula)

(********** Utility functions **********)

let add_prime (p : primed) (id : ident)  = 
	(id,p) 
;;

let get_var_exp (e : IF.ext_exp) : (ident * primed) =
	match e with
	| IF.Pure pure_exp ->
		begin
			match pure_exp with
			| P.Var (id_p,l) -> id_p
			| _ -> failwith ("Heap arguments not variable")
		end
	| _ -> failwith ("Heap arguments not variable")
;;

let rec e_subst sst (e : P.exp) =
	match sst with
	| s::rest -> e_subst rest (P.e_apply_one s e)
	| [] -> e
;;

let print_triple (t : P.exp * P.exp * P.formula) =
	print_string (" (" ^ (IP.string_of_formula_exp (fst3 t)) ^ "," ^
		(IP.string_of_formula_exp (snd3 t)) ^ "," ^ (IP.string_of_pure_formula (thrd3 t)) ^ ") ")
;;

let print_memo (m : memo) =
	let triples_list = fst m in
	let inv = snd m in
	let _ = print_string "[" in
	let _ = List.iter print_triple triples_list in
	print_string ("]," ^ (IP.string_of_pure_formula inv) ^ "\n")
;;

(********** Conver formulas to cpure formulas **********)

let cpure_of_spec_var ((v,p) : (ident * primed)) : CP.spec_var =
	CP.SpecVar (CP.Prim Int, v, p)
;;

let rec cpure_of_exp e0 =
	match e0 with
	| P.Null l -> CP.Null l
	| P.Var (sv, l) -> CP.Var (cpure_of_spec_var sv, l)
	| P.IConst (i, l) -> CP.IConst (i, l)
	| P.Add (a1, a2, l) -> CP.Add (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Subtract (a1, a2, l) -> CP.Subtract (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Mult _ -> failwith ("Multiplication failed")
	| P.Max _
	| P.Min _ -> failwith ("Max/Min failed")
	| _ -> failwith ("Omega.omega_of_exp: bag constraint")

and cpure_of_b_formula b =
	match b with
	| P.BConst (c, l) -> CP.BConst (c, l)
	| P.BVar (bv, l) -> CP.BVar (cpure_of_spec_var bv, l)
	| P.Lt (a1, a2, l) -> CP.Lt (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Lte (a1, a2, l) -> CP.Lte (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Gt (a1, a2, l) -> CP.Gt (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Gte (a1, a2, l) -> CP.Gte (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Eq (a1, a2, l) -> CP.Eq (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.Neq (a1, a2, l) -> CP.Neq (cpure_of_exp a1, cpure_of_exp a2, l)
	| P.EqMax (a1, a2, a3, l) -> CP.EqMax (cpure_of_exp a1, cpure_of_exp a2, cpure_of_exp a3, l)
	| P.EqMin (a1, a2, a3, l) -> CP.EqMin (cpure_of_exp a1, cpure_of_exp a2, cpure_of_exp a3, l)
	| _ -> failwith ("Omega.omega_of_exp: bag constraint")

and cpure_of_formula f  =
	match f with
	| P.BForm b -> CP.BForm (cpure_of_b_formula b)
	| P.And (p1, p2, l) -> CP.And (cpure_of_formula p1, cpure_of_formula p2, l)
	| P.Or (p1, p2, l) -> CP.Or (cpure_of_formula p1, cpure_of_formula p2, l)
	| P.Not (p, l) -> CP.Not (cpure_of_formula p, l)
	| P.Forall (sv, p, l) -> CP.Forall (cpure_of_spec_var sv, cpure_of_formula p, l)
	| P.Exists (sv, p, l) -> CP.Exists (cpure_of_spec_var sv, cpure_of_formula p, l)
;;

(********** XPure **********)

(** Find the Xpure of a structural formula
	@param views view declaration list
	@param f_struc structural formula
	@return list of memory *)
let rec xpure_struc_formula (views : I.view_decl list) (f_struc : IF.struc_formula) : memo list =
	List.concat (List.map (xpure_ext_formula views) f_struc)

(** Find the Xpure of an extended formula
	@param views view declaration list
	@param f_ext extended formula
	@return list of memory *)
and xpure_ext_formula (views : I.view_decl list) (f_ext : IF.ext_formula) : memo list =
	match f_ext with
	| IF.ECase _ -> 
		[]
	| IF.EBase f_ext_base -> 
		xpure_formula views f_ext_base.IF.formula_ext_base
	| IF.EAssume f -> 
		xpure_formula views f

(** Find the Xpure of a formula
	@param views view declaration list
	@param f formula
	@return list of memory *)
and xpure_formula (views : I.view_decl list) (f : IF.formula) : memo list =
	match f with
	| IF.Base f_base -> [xpure_formula_base views f_base]
	| IF.Exists f_exists -> [xpure_formula_exists views f_exists]
	| IF.Or f_or -> xpure_formula_or views f_or

(** Find the Xpure of a formula base
	@param views view declaration list
	@param fb formula base
	@return memory *)
and xpure_formula_base (views : I.view_decl list) (fb : IF.formula_base) : memo =
	let (m,p) = xpure_h_formula views fb.IF.formula_base_heap in
	(m, P.mkAnd p fb.IF.formula_base_pure no_pos)

(** Find the Xpure of a formula exists
	@param views view declaration list
	@param fe formula exists
	@return memory *)
and xpure_formula_exists (views : I.view_decl list) (fe : IF.formula_exists) : memo =
	let (m,p) = xpure_h_formula views fe.IF.formula_exists_heap in
	(m, P.mkAnd p fe.IF.formula_exists_pure no_pos)

(** Find the Xpure of a heap formula
	@param views view declaration list
	@param fh heap formula
	@return memory *)
and xpure_h_formula (views : I.view_decl list) (fh : IF.h_formula) : memo =
	match fh with
	| IF.Star fhs -> xpure_h_formula_star views fhs
	| IF.HeapNode hfh -> xpure_h_formula_heap views hfh
	| _ -> ([], (P.mkTrue no_pos))

(** Find the Xpure of a formula or
	@param views view declaration list
	@param fo formula or
	@return list of memory *)
and xpure_formula_or (views : I.view_decl list) (fo : IF.formula_or) : memo list =
	let l1 = xpure_formula views fo.IF.formula_or_f1 in
	let l2 = xpure_formula views fo.IF.formula_or_f2 in
	l1@l2

(** Find the Xpure of a heap formula star
	@param views view declaration list
	@param fhs heap formula star
	@return memory *)
and xpure_h_formula_star (views : I.view_decl list) (fhs : IF.h_formula_star) : memo =
	let (m1,p1) = xpure_h_formula views fhs.IF.h_formula_star_h1 in
	let (m2,p2) = xpure_h_formula views fhs.IF.h_formula_star_h2 in
	(m1@m2, P.mkAnd p1 p2 no_pos)

(** Find the Xpure of a heap formula heap node
	@param views view declaration list
	@param hfh heap formula heap
	@return memory *)
and xpure_h_formula_heap (views : I.view_decl list) (hfh : IF.h_formula_heap) : memo =
	let curr_view = I.look_up_view_def_raw views hfh.IF.h_formula_heap_name in
	let (x,y,c) = curr_view.I.view_mem in
	let inv = fst curr_view.I.view_invariant in
	let args_list = hfh.IF.h_formula_heap_arguments.IF.apf_args_head in
	let param_list = curr_view.I.view_vars.I.apf_param_head in
	let param_primed_list = ("self",Unprimed)::(List.map (add_prime Unprimed) param_list) in
	let arg_primed_list = hfh.IF.h_formula_heap_node::(List.map get_var_exp args_list) in
	let sst = List.combine param_primed_list arg_primed_list in
	let new_x = e_subst sst x in
	let new_y = e_subst sst y in
	let new_c = P.subst sst c in
	let new_inv = P.subst sst inv in
	([(new_x,new_y,new_c)], new_inv)
;;

(********** Normalization **********)

(** Normalization
	@param xpure_mem memory before normalization
	@return memory after normalization *)
(* Incomplete *)
let normalize (xpure_mem : memo) : memo =
	let _ = print_memo xpure_mem in
	xpure_mem
;;

(***** Checking the soundness of a predicate *****)

(** Check if a disjuntion of memory is enough to cover the memory description of a predicate 
	@param mem_list a disjuntion of memory
	@param view_mem memory description of a predicate
	@param view_inv invariant of a predicate *)
(* Incomplete *)
let check_cover (mem_list : memo list) (view_mem : triple) (view_inv : P.formula) : bool =
	true
;;

(** Check the soundness of a predicate 
	@param views view declaration list
	@param pred the input predicate
	@return true/false *)
let soundness_check (views : I.view_decl list) (pred : I.view_decl) : bool =
	let xpure_mem = xpure_struc_formula views pred.I.view_formula in
	let xpure_mem_simplified = List.map normalize xpure_mem in
	check_cover xpure_mem_simplified pred.I.view_mem (fst pred.I.view_invariant)
;;

(** Check the soundness of predicates and print out the results 
	@param views view declaration list
	@param pred predicate to be checked 
	@return unit *)
let soundness_check_and_print (views : I.view_decl list) (pred : I.view_decl) =
	if (pred.I.view_name <> "Elem") then
	begin
		let _ = print_string (pred.I.view_name ^ ": ") in
		if ((soundness_check views pred) = true) then print_string "Sound\n"
		else print_string "Not sound\n"
	end
;;

(** Process the commands and check the soundness of predicates 
	@param cmd command list
	@return unit *)
let process_cmd_and_check (cmd : command list) =
	let views = 
		(List.fold_left 
			(fun l1 curr_cmd -> 
				match curr_cmd with
				| PredDef pdef -> l1@[pdef]
				| _ -> l1) 
			[] cmd) in 
	let _ = print_string ((IP.string_of_view_decl_list views) ^ "\n") in
	let _ = List.iter (soundness_check_and_print views) views in 
	(exit 0)

