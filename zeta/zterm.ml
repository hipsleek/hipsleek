(**
 * Data structure and algorithms to
 * manipulate terms in the language
 * for first order logic. Support  
 * a subset of SMTLIB 2.0 standard for 
 * theory of integers with 
 * uninterpreted functions for arrays 
 * reasoning.
 *
 * @author Vu An Hoa
 *)

open Zsort
open Zutils


(**
 * Data structure for LOGICAL TERM
 *
 * Note: For the case FunApp:
 * 
 * If func = GFunc then the first
 * argument must be a Var term whose
 * name is the function/array name.
 * 
 * If func = Exists or Forall then 
 * the first argument term is the
 * formula and the rest are variables
 * under the quantification.
 *
 * TODO consider removing sort from var
 * such information is deducible from
 * the context
 *)
type term =
	| Num of int (* Numeral constant *)
	| Var of sort * string (* Variables/Function symbols *)
	| FunApp of func * term list
	
and func =
	| Add | Sub | Mul | Div | Mod
	| Lt | Le | Gt | Ge | Eq | Ne
	| Top | Bot | And | Or | Neg
	| Implies | Iff | Exists | Forall
	| GFunc

(* TERM TREE POST-ORDER TRAVERSAL *)

(** child nodes are processed from left to right *)
let rec term_fold f_pre f_arg f_post a t =
	(* pre-process the root node *)
	let nr = f_pre a t in
	(* check if output can be decided without traversal *)
	match nr with
		| Some r -> r (* decided *)
		| None -> match t with (* traverse and accumulate *)
			| FunApp (f, x) -> (* process childs by left folding *)
				let na = f_arg f x a in (* prepare starting argument for the first child *)
				let a = List.fold_left (term_fold f_pre f_arg f_post) na x in
					f_post f x a (* cook up final result using f_post *)
			| _ -> failwith "[term_fold] : leaf nodes must be decided by f_pre!"

(** child nodes are processed independently *)
let rec term_trans f_pre f_arg f_post a t =
	let nr = f_pre a t in
	match nr with
		| Some r -> r
		| None -> match t with
			| FunApp (f, x) ->
				let na = f_arg f x a in
				let nx = List.map (term_trans f_pre f_arg f_post na) x in
					f_post f nx a
			| _ -> failwith "[term_trans] : leaf nodes must be decided by f_pre!"

(* TERM PRINTING *)

let precedence_of f = match f with
	| Add | Sub -> 8 | Mul | Div | Mod -> 9
	| Lt | Le | Gt | Ge | Eq | Ne -> 7
	| Top | Bot -> 10 | And -> 3 | Or -> 2 | Neg -> 5
	| Implies | Iff -> 1 | Exists | Forall -> 4
	| GFunc -> 10

let rec print_term_helper pr_var pr_func p t  = match t with
	| Num i -> string_of_int i
	| Var (s, v) -> pr_var s v
	| FunApp (f, x) ->
		let pf = precedence_of f in
		let xp = match f with | GFunc -> 0 | _ -> pf in
		let sx = List.map (print_term_helper pr_var pr_func xp) x in
		let sf = pr_func f in
		let e = match f with
			| Top | Bot -> sf
			| Exists | Forall -> sf ^ " " ^ (String.concat "," (List.tl sx)) ^ " : " ^ (List.hd sx)
			| GFunc -> (List.hd sx) ^ "[" ^ (String.concat "," (List.tl sx)) ^ "]"
			| Neg -> sf ^ " " ^ (List.hd sx)
			| _ -> String.concat (" " ^ sf ^ " ") sx in
		if (pf < p) then "(" ^ e ^ ")" else e

let print_term pr_var pr_func t = print_term_helper pr_var pr_func 0 t

let string_of_func f = match f with
	| Add -> "+" | Sub -> "-" | Mul -> "*" 
	| Div -> "/" | Mod -> "mod"
	| Lt -> "<" | Le -> "<=" | Gt -> ">"
	| Ge -> ">=" | Eq -> "=" | Ne -> "!="
	| Top -> "T" | Bot -> "F" | And -> " /\\ " 
	| Or -> " \\/ " | Neg -> "~" | Implies -> "->" 
	| Iff -> "<->" | Exists -> "E" | Forall -> "A"
	| GFunc -> ""

let latex_of_func f = match f with
	| Add -> "+" | Sub -> "-" | Mul -> "\\times"
	| Div -> "\\div" | Mod -> "\\bmod"
	| Lt -> "<" | Le -> "\\leq" | Gt -> ">"
	| Ge -> "\\geq" | Eq -> "=" | Ne -> "\\not="
	| Top -> "\\top" | Bot -> "\\bot" | And -> "\\land"
	| Or -> "\\lor" | Neg -> "\\neg"
	| Implies -> "\\rightarrow" | Iff -> "\\leftrightarrow"
	| Exists -> "\\exists" | Forall -> "\\forall"
	| GFunc -> ""

let string_of_var s v = v
	(*"(" ^ v ^ ":" ^ (string_of_sort s) ^ ")"*)
	(*"(" ^ v ^ " \\in " ^ (latex_of_sort s) ^ ")"*)
	
let string_of_term = print_term string_of_var string_of_func

let latex_of_term = print_term string_of_var latex_of_func

let string_of_term_list vl =
	String.concat "," (List.map string_of_term vl)
	
(* TERM UTILITIES *)

(**
 * Get the name of a variable term
 *)
let name_of_var t = match t with
	| Var (_, v) -> v
	| _ -> failwith ("[name_of_var] : input term " ^ (string_of_term t) ^ " is not a var!")

(**
 * Get the sort of the result of function
 * application from the functor
 *)
let sort_of_func f = match f with
	| Add | Sub | Mul | Div | Mod -> SInt
	| Lt | Le | Gt | Ge | Eq | Ne | Top | Bot | And | Or | Neg | Implies | Iff | Exists | Forall -> SBool
	| GFunc -> SWild 0

(**
 * Get the sort of each arguments from the functor
 *)
let argsort_of_func f = match f with
	| Add | Sub | Mul | Div | Mod | Lt | Le | Gt | Ge | Eq | Ne -> SInt
	| Top | Bot | And | Or | Neg | Implies | Iff -> SBool
	| Exists | Forall | GFunc -> SWild 0

(**
 * Get the sort of a term.
 *)
let rec sort_of_term t = match t with
	| Num i -> SInt
	| Var (s, v) -> s
	| FunApp (f, x) -> let sf = sort_of_func f in
		match sf with
			| SWild _ -> List.hd (signature_of_smap (sort_of_term (List.hd x)))
			| _ -> sf

(**
 * Compare two variables term
 *)
let eq_var v1 v2 = (name_of_var v1 = name_of_var v2)

let rec subst_sort_term ssl t = match t with
	| Num _ -> t
	| Var (s, v) -> Var (List.fold_right subst_sort ssl s, v)
	| FunApp (f, x) -> FunApp (f, List.map (subst_sort_term ssl) x)

let rec replace_vars (v, w) t = match t with
	| Num _ -> t
	| Var _ -> if eq_var t v then w else t
	| FunApp (f, x) ->
		let nx = List.map (replace_vars (v,w)) x in
			FunApp (f, nx)

(* TERM CONSTRUCTORS *)

let set_term_sort s t = match t with
	| Var (_,v) -> Var (s, v)
	| FunApp (GFunc, x) -> 
		let o, x = List.hd x, List.tl x in
		let d = signature_of_smap (sort_of_term o) in
		let o = Var (SMap (s :: List.tl d), name_of_var o) in
			FunApp (GFunc, o :: x)
	| _ -> t

(* current number of wild sorts *)
let var_count = ref 0

let inc v = v := !v + 1; !v

let mkListTerm f xs = match f with
	| GFunc -> (* replace the sort for operator so that any query sort_of_term is safe! *)
		let o, x = List.hd xs, List.tl xs in
		let sf = sort_of_term o in (* assume that o has unique sort identifier ==> can be reused *)
		let o = Var (SMap (sf :: (List.map sort_of_term x)), name_of_var o) in
			FunApp (GFunc, o :: x)
	| Exists | Forall -> FunApp (f, (set_term_sort SBool (List.hd xs)) :: (List.tl xs))
	| _ -> let xf = argsort_of_func f in FunApp (f, List.map (set_term_sort xf) xs)

let mkBinTerm f x1 x2 = mkListTerm f [x1; x2]

let mkUnaryTerm f x = mkListTerm f [x]

let mkFunApp f l = FunApp (f, l)

let mkTop () = FunApp (Top, [])

let mkBot () = FunApp (Bot, [])

let mkVar v = Var (SWild (inc var_count), v) (* add a wild sort for the IMAGE *)

(* TERM UTILITIES *)

let rec collect_vars t = match t with
	| Num _ -> []
	| Var _ -> [t]
	| FunApp (_, x) -> List.flatten (List.map collect_vars x)

let rec collect_fun_apps t = match t with
	| Num _ | Var _ -> []
	| FunApp (f, x) ->
		let fapps = List.flatten (List.map collect_fun_apps x) in
		match f with
			| GFunc -> t :: fapps
			| _ -> fapps

let is_fun_app t = match t with
	| FunApp (GFunc, _) -> true
	| _ -> false
	
let get_functor_name t = match t with
	| FunApp (GFunc, x) -> name_of_var (List.hd x)
	| _ -> failwith "[functor_name] : expect a function application"

let get_fun_app_arg t = match t with
	| FunApp (GFunc, x) -> List.tl x
	| _ -> failwith "[get_fun_app_arg] : expect a function application"

(**
 * Get all free variables in a term t (with duplicates)
 *)
let rec frv t = match t with
	| Num _ -> []
	| Var _ -> [t]
	| FunApp (f, x) ->
		let vx = List.map frv x in
		let vl = match f with
			| Exists | Forall ->
				let qvars = List.flatten (List.tl vx) in
					GList.remove_all_eq eq_var (List.hd vx) qvars
			| _ -> List.flatten vx in
		GList.remove_dups_eq eq_var vl

(**
 * Substitute simultaneously [v/vt]
 * for all pairs (v,vt) in stl where
 * v is the variable name to be 
 * substituted, vt is the term to
 * substitute it with.
 *)
let rec subst stl t = if stl = [] then t 
	else match t with
		| Num _ -> t
		| Var (_, v) -> begin
			try 
				List.assoc v stl
			with 
				| Not_found -> t end
		| FunApp (f, x) -> match f with
			| Exists | Forall ->
				let fml = List.hd x in
				let qvars = List.tl x in
				let qvarsnames = List.map name_of_var qvars in
				let stl = GList.remove_all_eq (fun (v,_) q -> v = q) stl qvarsnames in
					FunApp (f, (subst stl fml) :: qvars)
			| _ -> (* Warning : potential dangerous substitution of functors *)
				FunApp (f, List.map (subst stl) x)
				
let filter_defined_symbols st vl =
	List.filter (fun x -> not (Hashtbl.mem st (name_of_var x))) vl