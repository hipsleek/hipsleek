(** Type inference module 
	Created August 2009 *)
	
(*

===========
   Notes
===========

- To view the type information, use: 
   hip filename.ss
- Type information is stored in the type context, see function print_type_info to understand how to use them.
- Some examples in: examples/cuong_type

*)


open Globals

module I = Iast

module IF = Iformula

module P = Ipure

module IP = Iprinter

module H = Hashtbl

module CP = Cpure


(** Type constraint with equality relationship *)
type typ_constr = { 
	left_hand_side : I.typ;
	right_hand_side : I.typ; 
  }
	  
(** Type context - a hash table of identifiers and associated types *)
type typ_context = (ident, I.typ) H.t


(************* Utility functions ****************)

(** An extended version of split with list of triples
	@param l list of triples
	@return a triple of lists *)
let rec split3 l =
  match l with
  | [] -> [], [], []
  | (c1,c2,c3)::t -> 
	  let t1,t2,t3 = split3 t in
	  c1::t1,c2::t2,c3::t3
;;

(** Get the first and third elements of a triple 
	@param a1 first element
	@param a3 third element *)
let fst_thrd_3 (a1,_,a3) = (a1,a3)
;;

(** Merge two contexts, the result is stored in the destination context
	@param des destination context
	@param src source context
	@return unit *)
let merge_context (des : typ_context) (src : typ_context) : unit =
  H.iter (H.replace des) src
;;

(** Construct a type constrain from two types 
	@param t1 first type
	@param t2 second type
	@return type constraint *)
let make_constr (t1 : I.typ) (t2 : I.typ) : typ_constr =
  { left_hand_side = t1;
    right_hand_side = t2 }
;;

(** Construct a function type 
	@param contxt current type context
	@param params list of parameters of the function to look up types in contxt 
	@param ret return type of the function 
	@return the function type *)
let rec make_func_typ_1 (contxt : typ_context) (params : ident list) (ret : I.typ) : I.typ =
  match params with
  | [] -> ret
  | h::t -> I.FuncType ((H.find contxt h), (make_func_typ_1 contxt t ret))
;;

(** Construct a function type
	@param params_typ types for the parameters
	@ret return type of the function
	@return the function type *)
let rec make_func_typ_2 (params_typ : I.typ list) (ret : I.typ) : I.typ =
  match params_typ with
  | [] -> ret
  | h::t -> I.FuncType (h, (make_func_typ_2 t ret))
;;

(** Get the view name of a view declation 
	@param v view declaration
	@return view name *)
let get_view_id (v : I.view_decl) : ident =
  v.I.view_name
;;

(** Get the function name of a lambda function declaration
	@param f lambda function declaration
	@return function name *)
let get_func_id (f : I.func_decl) : ident =
  f.I.func_decl_name
;;

(** Add new type entry for an identifier into the context 
	@param contxt current type context
	@param id identifier to add into the context 
	@return unit *)
let add_new_typ_entry (contxt : typ_context) (id : ident) =
  let new_name = fresh_type_var_name () in
  H.replace contxt id (I.VarType new_name)
;;

(** Try to look for the type of an id in a context. 
	If there is one, return the context together with the type. 
	If not, create a new type for id, return the new contxt and new type. 
	@param contxt current type context
	@param id identifier to look for type 
	@return a pair of new context and type *)
let try_look_for_type (contxt : typ_context) (id : ident) : typ_context * I.typ =
  try
	let t = H.find contxt id in
	contxt, t
  with
	Not_found -> 
	  let contxt1 = H.copy contxt in
	  let _ = add_new_typ_entry contxt1 id in
	  let t = H.find contxt1 id in
	  contxt1, t
;;

(** Check if a type is a pointer type
	@param t the given type
	@return true if t is a pointer type, false otherwise *)
let isPointerType (t : I.typ) : bool =
  match t with
  | I.Prim _ -> false
  | I.Named _ -> true
  | I.Array _ -> false
  | I.FuncType _ -> false
  | I.Pointer -> true
  | I.TypPointer _ -> true
  | I.VarType _ -> false
  | I.PolyBag _ -> false
;;

(** Print one context entry in a type context 
	@param id identifier of the entry 
	@param typ type of id *)
let print_context_entry (id : ident) (typ : I.typ) =
  print_string (id ^ " : " ^ (IP.string_of_typ typ) ^ "\n")
;;

(** Print the type info of the input type context
	@param ti input type context *)
let print_type_info (ti : typ_context) =
  H.iter print_context_entry ti
;;

(** Print a type constraints 
	@param c the input type contraint*)
let print_constr (c : typ_constr) =
  print_string ((IP.string_of_typ c.left_hand_side) ^ " = " ^ (IP.string_of_typ c.right_hand_side) ^ "\n")
;;

(** Translate an I.typ to a CP.typ *)
let rec ityp_to_ctyp (ityp : I.typ) : CP.typ =
  match ityp with
  | I.Prim t -> CP.Prim t
  | I.Named id -> CP.OType id
  | I.Array (t,d) -> CP.Array (ityp_to_ctyp t,d)
  | I.FuncType (t1,t2) -> CP.FuncType (ityp_to_ctyp t1, ityp_to_ctyp t2)
  | I.Pointer -> CP.Pointer
  | I.TypPointer t -> CP.TypPointer (ityp_to_ctyp t)
  | I.VarType id -> CP.VarType id
  | I.PolyBag t -> CP.PolyBag (ityp_to_ctyp t)
;;

(****************** Get type constraints ********************)

(** Get the type info of a lambda extension formula
	@param contxt current type context
	@param lextf lambda extension formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
let rec get_l_ext_formula_info (contxt : typ_context) (lextf : IF.l_ext_formula) : typ_context * I.typ * (typ_constr list) =
  match lextf with
  | IF.HeapFormula sf -> get_struc_formula_info contxt sf
  | IF.LambdaFormula le -> get_lambda_exp_info contxt le

(** Get the type info of an extented case formula 
	@param contxt current type context
	@param ecf extended case formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_ext_case_formula_info (contxt : typ_context) (ecf : IF.ext_case_formula) : typ_context * I.typ * (typ_constr list) =
  let formula_list, struc_formula_list = List.split ecf.IF.formula_case_branches in
  let result_contxt = H.copy contxt in
  let info_list_1 = List.map (get_pure_formula_info contxt) formula_list in
  let contxt_list_1, typ_list_1, constr_list_list_1 = split3 info_list_1 in
  let _ = List.map (merge_context result_contxt) contxt_list_1 in
  let constr_list_1 = List.concat constr_list_list_1 in
  let info_list_2 = List.map (get_struc_formula_info contxt) struc_formula_list in
  let contxt_list_2, typ_list_2, constr_list_list_2 = split3 info_list_2 in
  let _ = List.map (merge_context result_contxt) contxt_list_2 in
  let constr_list_2 = List.concat constr_list_list_2 in
  result_contxt, I.Prim Bool, constr_list_1@constr_list_2

(** Get the type info of an extented base formula 
	@param contxt current type context
	@param ebf extended base formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_ext_base_formula_info (contxt : typ_context) (ebf : IF.ext_base_formula) : typ_context * I.typ * (typ_constr list) =
  let id_list_1, _ = List.split ebf.IF.formula_ext_explicit_inst in
  let id_list_2, _ = List.split ebf.IF.formula_ext_implicit_inst in
  let id_list_3, _ = List.split ebf.IF.formula_ext_exists in
  let id_list = id_list_1 @ id_list_2 @ id_list_3 in
  let new_contxt = H.copy contxt in
  let _ = List.map (add_new_typ_entry new_contxt) id_list in
  let contxt1, typ1, constr1 = get_formula_info new_contxt ebf.IF.formula_ext_base in
  let contxt2, typ2, constr2 = get_struc_formula_info new_contxt ebf.IF.formula_ext_continuation in
  let _ = merge_context contxt1 contxt2 in
  contxt1, I.Prim Bool, constr1@constr2
								   
(** Get the type info of a heap formula star
	@param contxt current type context
	@param fs heap formula star
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_heap_formula_star_info (contxt : typ_context) (fs : IF.h_formula_star) : typ_context * I.typ * (typ_constr list) =
  let contxt1, typ1, constr1 = get_heap_formula_info contxt fs.IF.h_formula_star_h1 in
  let contxt2, typ2, constr2 = get_heap_formula_info contxt fs.IF.h_formula_star_h2 in
  let _ = merge_context contxt1 contxt2 in
  contxt1, I.Prim Bool, constr1@constr2

(** Get the type info of a heap formula heap
	@param contxt current type context
	@param fh heap formula heap
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_heap_formula_heap_info (contxt : typ_context) (fh : IF.h_formula_heap) : typ_context * I.typ * (typ_constr list) =
  let typ_node = H.find contxt (fst fh.IF.h_formula_heap_node) in
  let typ_name = H.find contxt fh.IF.h_formula_heap_name in
  let info_list = List.map (get_ext_exp_info contxt) fh.IF.h_formula_heap_arguments.IF.apf_args_head in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let result_contxt = H.copy contxt in
  let _ = List.map (merge_context result_contxt) contxt_list in
  let new_constr = make_constr typ_name (make_func_typ_2 (typ_node::typ_list) (I.Prim Bool)) in
  let constr_list = List.concat constr_list_list in
  result_contxt, I.Prim Bool, new_constr::constr_list
											
(** Get the type info of a heap formula lambda function
	@param contxt current type context
	@param fh heap formula lambda function
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_heap_formula_func_info (contxt : typ_context) (ff : IF.h_formula_func) : typ_context * I.typ * (typ_constr list) =
  let typ_name = H.find contxt ff.IF.h_formula_func_name in
  let info_list = List.map (get_ext_exp_info contxt) ff.IF.h_formula_func_arguments in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let result_contxt = H.copy contxt in
  let _ = List.map (merge_context result_contxt) contxt_list in
  let new_constr = make_constr typ_name (make_func_typ_2 typ_list (I.Prim Bool)) in
  let constr_list = List.concat constr_list_list in
  result_contxt, I.Prim Bool, new_constr::constr_list
											
(** Get the type info of a heap formula 
	@param contxt current type context
	@param hf heap formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_heap_formula_info (contxt : typ_context) (hf : IF.h_formula) : typ_context * I.typ * (typ_constr list) =
  match hf with
  | IF.Star fs -> get_heap_formula_star_info contxt fs
  | IF.HeapNode fh -> get_heap_formula_heap_info contxt fh
  | IF.HeapNode2 fh2 ->
	  Error.report_error 
		{ 
		  Error.error_loc = fh2.IF.h_formula_heap2_pos;
		  Error.error_text = "Heap node 2 must be converted to normal heap node!" 
		}
  | IF.HTrue 
  | IF.HFalse -> contxt, I.Prim Bool, []
  | IF.LambdaFunc ff -> get_heap_formula_func_info contxt ff

(** Get the type info of a formula base 
	@param contxt current type context
	@param fb formula base
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_formula_base_info (contxt : typ_context) (fb : IF.formula_base) : typ_context * I.typ * (typ_constr list) =
  let contxt_heap, typ_heap, constr_heap = get_heap_formula_info contxt fb.IF.formula_base_heap in
  let contxt_pure, typ_pure, constr_pure = get_pure_formula_info contxt fb.IF.formula_base_pure in
  let _, formula_list = List.split fb.IF.formula_base_branches in
  let info_list = List.map (get_pure_formula_info contxt) formula_list in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let result_contxt = H.copy contxt in
  let _ = merge_context result_contxt contxt_heap in
  let _ = merge_context result_contxt contxt_pure in
  let _ = List.map (merge_context result_contxt) contxt_list in
  let constr_list = List.concat constr_list_list in
  let result_constr = constr_heap@constr_pure@constr_list in
  result_contxt, I.Prim Bool, result_constr

(** Get the type info of a formula exists
	@param contxt current type context
	@param fe formula exists
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_formula_exists_info (contxt : typ_context) (fe : IF.formula_exists) : typ_context * I.typ * (typ_constr list) =
  let id_list, _ = List.split fe.IF.formula_exists_qvars in
  let new_contxt = H.copy contxt in
  let _ = List.map (add_new_typ_entry new_contxt) id_list in
  let contxt1, typ1, constr1 = get_heap_formula_info new_contxt fe.IF.formula_exists_heap in
  let contxt2, typ2, constr2 = get_pure_formula_info new_contxt fe.IF.formula_exists_pure in
  let _ = merge_context contxt1 contxt2 in
  contxt1, I.Prim Bool, constr1@constr2

(** Get the type info of a formula or 
	@param contxt current type context
	@param fo formula or
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_formula_or_info (contxt : typ_context) (fo : IF.formula_or) : typ_context * I.typ * (typ_constr list) =
  let contxt1, typ1, constr1 = get_formula_info contxt fo.IF.formula_or_f1 in
  let contxt2, typ2, constr2 = get_formula_info contxt fo.IF.formula_or_f2 in
  let _ = merge_context contxt1 contxt2 in
  let constr = constr1@constr2 in
  contxt1, I.Prim Bool, constr

(** Get the type info of a formula 
	@param contxt current type context
	@param f formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_formula_info (contxt : typ_context) (f : IF.formula) : typ_context * I.typ * (typ_constr list) =
  match f with
  | IF.Base fb -> get_formula_base_info contxt fb
  | IF.Exists fe -> get_formula_exists_info contxt fe
  | IF.Or fo -> get_formula_or_info contxt fo

(** Get the type info of an extented formula 
	@param contxt current type context
	@param ef extended formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_ext_formula_info (contxt : typ_context) (ef : IF.ext_formula) : typ_context * I.typ * (typ_constr list) =
  match ef with
  | IF.ECase ecf -> get_ext_case_formula_info contxt ecf
  | IF.EBase ebf -> get_ext_base_formula_info contxt ebf
  | IF.EAssume f -> get_formula_info contxt f

(** Get the type info of a structured formula 
	@param contxt current type context
	@param sf structured formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_struc_formula_info (contxt : typ_context) (sf : IF.struc_formula) : typ_context * I.typ * (typ_constr list) =
  let info_list = List.map (get_ext_formula_info contxt) sf in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let result_contxt = H.copy contxt in
  let _ = List.map (merge_context result_contxt) contxt_list in
  let result_constr_list = List.concat constr_list_list in
  result_contxt, I.Prim Bool, result_constr_list

(** Get the type info of a pure boolean formula 
	@param contxt current type context
	@param bf pure boolean formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_pure_b_formula_info (contxt : typ_context) (bf : P.b_formula) : typ_context * I.typ * (typ_constr list) =
  match bf with
  | P.BConst _ -> contxt, I.Prim Bool, []
  | P.BVar ((id, _), _) -> contxt, (H.find contxt id), []
  | P.Lt (e1, e2, _)
  | P.Lte (e1, e2, _)
  | P.Gt (e1, e2, _)
  | P.Gte (e1, e2, _)
  | P.Eq (e1, e2, _)
  | P.Neq (e1, e2, _) ->
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, typ2, constr2 = get_pure_exp_info contxt e2 in
	  let _ = merge_context contxt1 contxt2 in
	  let new_constr1 = make_constr typ1 typ2 in
	  contxt1, I.Prim Bool, new_constr1::(constr1@constr2)
  | P.EqMax (e1, e2, e3, _)
  | P.EqMin (e1, e2, e3, _) ->
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, typ2, constr2 = get_pure_exp_info contxt e2 in
	  let contxt3, typ3, constr3 = get_pure_exp_info contxt e3 in
	  let _ = merge_context contxt1 contxt2 in
	  let _ = merge_context contxt1 contxt3 in
	  let new_constr1 = make_constr typ1 typ2 in
	  let new_constr2 = make_constr typ1 typ3 in
	  contxt1, I.Prim Bool, constr1@constr2@[new_constr1; new_constr2]
  | P.BagIn ((id, _), e1, _)
  | P.BagNotIn ((id, _), e1, _) ->
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let new_constr = make_constr typ1 (I.Prim Bag) in
	  contxt1, I.Prim Bool, new_constr::constr1
  | P.BagSub (e1, e2, _) -> 
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, typ2, constr2 = get_pure_exp_info contxt e2 in
	  let _ = merge_context contxt1 contxt2 in
	  let new_constr1 = make_constr typ1 typ2 in
	  contxt1, I.Prim Bool, new_constr1::(constr1@constr2)
  | P.BagMin ((id1, _), (id2, _), _) 
  | P.BagMax ((id1, _), (id2, _), _) ->
	  contxt, I.Prim Bool, []

(** Get the type info of a pure formula 
	@param contxt current type context
	@param pf pure formula
	@return a type context for all variables in the formula, type of the formula, and the list of type constraints *)
and get_pure_formula_info (contxt : typ_context) (pf : P.formula) : typ_context * I.typ * (typ_constr list) =
  match pf with
  | P.BForm bf -> get_pure_b_formula_info contxt bf
  | P.And (f1, f2, _)
  | P.Or (f1, f2, _) ->
	  let contxt1, typ1, constr1 = get_pure_formula_info contxt f1 in
	  let contxt2, typ2, constr2 = get_pure_formula_info contxt f2 in
	  let _ = merge_context contxt1 contxt2 in
	  let new_constr1 = make_constr typ1 typ2 in
	  let new_constr2 = make_constr typ1 (I.Prim Bool) in
	  let constr = constr1@constr2@[new_constr1; new_constr2] in
	  contxt1, I.Prim Bool, constr
  | P.Not (f1, _) ->
	  let contxt1, typ1, constr1 = get_pure_formula_info contxt f1 in
	  let new_constr1 = make_constr typ1 (I.Prim Bool) in
	  let constr = new_constr1::constr1 in
	  contxt1, I.Prim Bool, constr
  | P.Forall ((id, _), f1, _)
  | P.Exists ((id, _), f1, _) ->
	  let new_contxt = H.copy contxt in
	  let _ = add_new_typ_entry new_contxt id in
	  get_pure_formula_info new_contxt f1

(** Get the type info of a pure expression 
	@param contxt current type context
	@param pe pure expression
	@return a type context for all variables in the expression, type of the expression, and the list of type constraints *)
and get_pure_exp_info (contxt : typ_context) (pe : P.exp) : typ_context * I.typ * (typ_constr list) =
  match pe with
  | P.Null _ -> contxt, I.Pointer, []
  | P.Var ((id,_),_) -> 
		let contxt1, typ1 = try_look_for_type contxt id in
		contxt1, typ1, []
  | P.IConst _ -> contxt, I.Prim Int, []
  | P.Add (e1,e2,_) ->
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, typ2, constr2 = get_pure_exp_info contxt e2 in
	  let _ = merge_context contxt1 contxt2 in
	  let new_constr1 = make_constr typ2 (I.Prim Int) in
	  contxt1, typ1, new_constr1::(constr1@constr2)
  | P.Subtract (e1,e2,_)
  | P.Mult (e1,e2,_)
  | P.Max (e1,e2,_)
  | P.Min (e1,e2,_) ->
	  let contxt1, typ1, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, typ2, constr2 = get_pure_exp_info contxt e2 in
	  let _ = merge_context contxt1 contxt2 in
	  let new_constr1 = make_constr typ1 typ2 in
	  contxt1, typ1, new_constr1::(constr1@constr2)
  | P.Bag (el,_)
  | P.BagUnion (el,_)
  | P.BagIntersect (el,_) ->
	  let info_list = List.map (get_pure_exp_info contxt) el in
	  let contxt_list, _, constr_list_list = split3 info_list in
	  let result_contxt = H.copy contxt in
	  let _ = List.map (merge_context result_contxt) contxt_list in
	  let result_constr_list = List.concat constr_list_list in
	  result_contxt, I.Prim Bag, result_constr_list
  | P.BagDiff (e1,e2,_) ->
	  let contxt1, _, constr1 = get_pure_exp_info contxt e1 in
	  let contxt2, _, constr2 = get_pure_exp_info contxt e2 in
	  let _ = merge_context contxt1 contxt2 in
	  contxt1, I.Prim Bag, constr1@constr2
  | P.PrimFuncCall (_,_,l) ->
	  Error.report_error 
		{ 
		  Error.error_loc = l;
		  Error.error_text = "Primitive functions are not supported at this moment!" 
		}

(** Get the type info of an extension expression
	@param contxt current type context
	@param ee extension expression
	@return a type context for all variables in the expression, type of the expression, and the list of type constraints *)
and get_ext_exp_info (contxt : typ_context) (ee : IF.ext_exp) : typ_context * I.typ * (typ_constr list) =
  match ee with
  | IF.Pure pe -> get_pure_exp_info contxt pe
  | IF.LambdaExp le -> get_lambda_exp_info contxt le

(** Get the type info of a lambda application
	@param contxt current type context
	@param la lambda application expression
	@return a type context for all variables in the application, type of the application, and the list of type constraints *)
and get_lambda_apply_info (contxt : typ_context) (la : IF.lambda_apply) : typ_context * I.typ * (typ_constr list) =
  let contxt0, typ0, constr0 = get_lambda_exp_info contxt la.IF.lambda_apply_func in
  let info_list = List.map (get_ext_exp_info contxt) la.IF.lambda_apply_args in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let result_contxt = H.copy contxt0 in
  let _ = List.map (merge_context result_contxt) contxt_list in
  let new_typ = I.VarType (fresh_type_var_name ()) in
  let new_constr = make_constr typ0 (make_func_typ_2 typ_list new_typ) in
  let result_constr_list = new_constr::(List.concat constr_list_list) in
  result_contxt, new_typ, result_constr_list

(** Get the type info of a lambda expression
	@param contxt current type context
	@param le lambda expression
	@return a type context for all variables in the expression, type of the expression, and the list of type constraints *)
and get_lambda_exp_info (contxt : typ_context) (le : IF.lambda_exp) : typ_context * I.typ * (typ_constr list) =
  match le with
  | IF.LDef ld -> get_lambda_def_info contxt ld
  | IF.LApply la -> get_lambda_apply_info contxt la

(** Get the type info of a lambda function definition
	@param contxt current type context 
	@param ld lambda function definition
	@return a type context for all variables in the definition, type of the definition, and the list of type constraints *)
and get_lambda_def_info (contxt : typ_context) (ld : IF.lambda_def) : typ_context * I.typ * (typ_constr list) =
  let new_contxt = H.copy contxt in
  let _ = List.map (add_new_typ_entry new_contxt) ld.IF.lambda_def_params in
  let contxt1, typ1, constr1 = get_l_ext_formula_info new_contxt ld.IF.lambda_def_body in
  let new_typ = I.VarType (fresh_type_var_name ()) in
  let new_constr = make_constr new_typ (make_func_typ_1 new_contxt ld.IF.lambda_def_params typ1) in
  contxt1, new_typ, new_constr::constr1

(** Get the type info of a lambda function declaration 
	@param contxt current type context
	@param func lambda function declaration
	@return a type context for all variables in the declaration, type of the declaration, and the list of type constraints *)
and get_func_decl_info (contxt : typ_context) (func : I.func_decl) : typ_context * I.typ * (typ_constr list) =
  let t = H.find contxt func.I.func_decl_name in
  let contxt1, typ1, constr1 = get_lambda_def_info contxt func.I.func_decl_def in
  let new_constr = make_constr t typ1 in
  contxt1, t, new_constr::constr1

(** Get the type info of a view declaration
	@param contxt current type context
	@param view view declaration
	@return a type context for all variables in the declaration, type of the declaration, and the list of type constraints *)
and get_view_decl_info (contxt : typ_context) (view : I.view_decl) : typ_context * I.typ * (typ_constr list) =
  let view_typ = H.find contxt view.I.view_name in
  let new_contxt = H.copy contxt in
  let _ = add_new_typ_entry new_contxt "self" in
  let _ = add_new_typ_entry new_contxt "loc" in
  let _ = List.map (add_new_typ_entry new_contxt) view.I.view_vars.I.apf_param_head in
  let inv_formula_list = (fst view.I.view_invariant)::(List.map snd (snd view.I.view_invariant)) in
  let formula_list = inv_formula_list in
  let contxt0, typ0, constr0 = get_struc_formula_info new_contxt view.I.view_formula in
  let info_list = List.map (get_pure_formula_info new_contxt) formula_list in
  let new_constr1 = make_constr view_typ (make_func_typ_1 new_contxt ("self"::view.I.view_vars.I.apf_param_head) typ0) in
  let contxt_list, typ_list, constr_list_list = split3 info_list in
  let _ = List.map (merge_context contxt0) contxt_list in
  let new_constraints = new_constr1::(List.map (make_constr (I.Prim Bool)) typ_list) in
  let old_constraints = constr0@(List.concat constr_list_list) in
  let new_constr_list = new_constraints@old_constraints in
  contxt0, view_typ, new_constr_list
;;


(**********************************************)

(** Check whether a type variable is contained in a type expression 
	@param id identifier for the type variable 
	@param t the type expression
	@return true if id is contained in t, false otherwise *)
let rec contain (id : ident) (t : I.typ) : bool =
  match t with
  | I.Prim _ -> false
  | I.Named _ -> false
  | I.Array (t1,_) -> contain id t1
  | I.FuncType (t1,t2) -> (contain id t1) || (contain id t2)
  | I.Pointer -> false
  | I.TypPointer t1 -> contain id t1
  | I.VarType id1 -> id = id1
  | I.PolyBag t1 -> contain id t1
;;

(** Substitute a variable type with a type expression (in a type expression)
	@param id the id of the variable type
	@param sub_t the type expression that is substituted into id 
	@param t the type expression
	@return the new type expression with id substituted by sub_t *)
let rec substitute_vartype_typ (id : ident) (sub_t : I.typ) (t : I.typ) : I.typ =  match t with
  | I.Prim _ -> t
  | I.Named _ -> t
  | I.Array (t1,d) -> I.Array (substitute_vartype_typ id sub_t t1, d)
  | I.FuncType (t1,t2) -> I.FuncType (substitute_vartype_typ id sub_t t1, substitute_vartype_typ id sub_t t2)
  | I.Pointer -> t
  | I.TypPointer t1 -> I.TypPointer (substitute_vartype_typ id sub_t t1)
  | I.VarType id1 ->
	  if id1 = id then sub_t
	  else t
  | I.PolyBag t1 -> I.PolyBag (substitute_vartype_typ id sub_t t1)
;;

(** Substitute a variable type with a type expression (in a type constraint)
	@param id the id of the variable type
	@param sub_t the type expression that is substituted into id 
	@param t the type constraint
	@return the new constraint with id substituted by sub_t *)
let substitute_vartype_constr (id : ident) (sub_t : I.typ) (t : typ_constr) : typ_constr =
  let lhs = t.left_hand_side in
  let rhs = t.right_hand_side in
  let new_lhs = substitute_vartype_typ id sub_t lhs in
  let new_rhs = substitute_vartype_typ id sub_t rhs in
  make_constr new_lhs new_rhs
;;

(** Update the type of an input type expression using the information in a type context 
	@param contxt the current type context
	@param t the input type expression
	@return the new type expression *)
let rec update_typ (contxt : typ_context) (t : I.typ) : I.typ =
  match t with
  | I.Prim _ -> t
  | I.Named _ -> t
  | I.Array (t1,d) -> I.Array (update_typ contxt t1, d)
  | I.FuncType (t1,t2) -> I.FuncType (update_typ contxt t1, update_typ contxt t2)
  | I.Pointer -> t
  | I.TypPointer t1 -> I.TypPointer (update_typ contxt t1)
  | I.VarType id1 ->
	  begin
		try
		  H.find contxt id1
		with
		  Not_found -> t
	  end
  | I.PolyBag t1 -> I.PolyBag (update_typ contxt t1)
;;

(** Unify the list of constraints 
	@param contxt current type context
	@param constraints the current list of type constraints
	@return the new type context and the unified list of type constraints *)
let rec unify_constr_list (contxt : typ_context) (constraints : typ_constr list) : typ_context * typ_constr list =
  match constraints with
  | [] -> contxt, []
  | h::t ->
	  begin
		let lhs = h.left_hand_side in
		let rhs = h.right_hand_side in
		if lhs = rhs then
		  unify_constr_list contxt t
		else if (lhs = I.Pointer || lhs = (I.Prim Int)) && (isPointerType rhs) then
		  unify_constr_list contxt t
		else if (rhs = I.Pointer || rhs = (I.Prim Int)) && (isPointerType lhs) then
		  unify_constr_list contxt t
		else
		  begin
			match lhs with
			| I.VarType id_l ->
				if (contain id_l rhs) then
				  failwith ("Type error !")
				else
				  let new_t = List.map (substitute_vartype_constr id_l rhs) t in
				  let new_contxt, unified_t = unify_constr_list contxt new_t in
				  let new_rhs = update_typ new_contxt rhs in
				  let _ = H.replace new_contxt id_l new_rhs in
				  let new_constr = make_constr lhs new_rhs in
				  new_contxt, new_constr::unified_t
			| _ -> 
				begin
				  match rhs with 
				  | I.VarType id_r -> 
					  if (contain id_r lhs) then
						failwith ("Type error !")
					  else
						let new_t = List.map (substitute_vartype_constr id_r lhs) t in
						let new_contxt, unified_t = unify_constr_list contxt new_t in
						let new_lhs = update_typ new_contxt lhs in
						let _ = H.replace new_contxt id_r new_lhs in
						let new_constr = make_constr rhs new_lhs in
						new_contxt, new_constr::unified_t
				  | _ ->
					  begin
						match lhs with
						| I.FuncType (l1,l2) ->
							begin
							  match rhs with 
							  | I.FuncType (r1,r2) ->
								  let constr1 = make_constr l1 r1 in
								  let constr2 = make_constr l2 r2 in
								  unify_constr_list contxt (constr1::(constr2::t))
							  | _ -> failwith ("Type error !")
							end
						| _ -> failwith ("Type error!")
					  end
				end
		  end
	  end
;;

(** Find the type of id in the input list of constraints and update the context 
	@param constraints list of constraints
	@param contxt the current context
	@param id identifier
	@param t type of id *)
let rec find_and_replace (constraints : typ_constr list) (contxt : typ_context) (id : ident) (id_typ : I.typ) =
  match constraints with
  | [] -> ()
  | h::t -> 
	  let lhs = h.left_hand_side in
	  let rhs = h.right_hand_side in
	  if lhs = id_typ then
		H.replace contxt id rhs
	  else
		find_and_replace t contxt id id_typ
;;

(** Unify the type constraints and update the context 
	@param contxt the current context
	@param constraints the current list of type constraints 
	@return a pair of new context and simplified list of type constraints *)
let simplify_contxt_constr ((contxt,constraints) : typ_context * typ_constr list) : typ_context * typ_constr list =
  let _ = print_string "\nType information\n" in
  let _ = print_type_info contxt in
  let _ = print_string "\nConstraints list:\n" in
  let _ = List.map print_constr constraints in
  let new_contxt, new_constraints = unify_constr_list contxt constraints in
  let _ = print_string "\nNew constraints:\n" in
  let _ = List.map print_constr new_constraints in
  new_contxt, new_constraints
;;

(** Add the primitive data as a function type into a context table 
	@param contxt the context table *)
let add_primitive_data_typ_entry (contxt : typ_context) =
  let func_bool = make_func_typ_2 [I.TypPointer (I.Prim Bool); (I.Prim Bool)] (I.Prim Bool) in
  let func_float = make_func_typ_2 [I.TypPointer (I.Prim Float); (I.Prim Float)] (I.Prim Bool) in
  let func_int = make_func_typ_2 [I.TypPointer (I.Prim Int); (I.Prim Int)] (I.Prim Bool) in
  let _ = H.replace contxt "bool" func_bool in
  let _ = H.replace contxt "float" func_float in
  let _ = H.replace contxt "int" func_int in
  ()
;;

(** Add the data type as a function type into a context table 
	@param contxt the context table
	@param data the data declaration *)
let add_data_typ_entry (contxt : typ_context) (data : I.data_decl) =
  let name = data.I.data_name in
  let fields,_ = List.split data.I.data_fields in
  let type_list,_ = List.split fields in
  let func_data = make_func_typ_2 ((I.Named name)::type_list) (I.Prim Bool) in
  H.replace contxt name func_data
;;

(** Infer the types in a program 
	@param prog program declaration
	@return a type context for the types in the input program *)
let infer_type_prog (prog : I.prog_decl) : typ_context =
  let typ_table = H.create 103 in
  let _ = add_primitive_data_typ_entry typ_table in
  let datas = prog.I.prog_data_decls in
  let _ = List.map (add_data_typ_entry typ_table) datas in
  let funcs = prog.I.prog_func_decls in
  let views = prog.I.prog_view_decls in
  let func_ids = List.map get_func_id funcs in
  let view_ids = List.map get_view_id views in
  let _ = List.map (add_new_typ_entry typ_table) func_ids in
  let _ = List.map (add_new_typ_entry typ_table) view_ids in
  let func_type_info_list = List.map (get_func_decl_info typ_table) funcs in
  let view_type_info_list = List.map (get_view_decl_info typ_table) views in
  let func_contxt_constr_list = List.map fst_thrd_3 func_type_info_list in
  let view_contxt_constr_list = List.map fst_thrd_3 view_type_info_list in
  let _ = print_string "\n\nFunction constraint solving\n" in
  let simplified_func_contxt_constr_list = List.map simplify_contxt_constr func_contxt_constr_list in
  let _ = print_string "\n\nView constraint solving\n" in
  let simplified_view_contxt_constr_list = List.map simplify_contxt_constr view_contxt_constr_list in
  let func_constr_list_list = List.map snd simplified_func_contxt_constr_list in
  let view_constr_list_list = List.map snd simplified_view_contxt_constr_list in
  let new_constr_list = (List.concat func_constr_list_list) @ (List.concat view_constr_list_list) in
  let _ = print_string "\n\nCombined constraint solving\n" in
  let new_typ_contxt, final_constr_list = unify_constr_list typ_table new_constr_list in
  let _ = print_string "\nConstraint solved\n" in
  new_typ_contxt
;;
