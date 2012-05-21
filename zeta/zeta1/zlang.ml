(**
 * Logical language
 *
 * @author Vu An Hoa
 *)

open Zutils

(**
 * Data structure and utilities to
 * manipulate sorts (i.e. types) in 
 * the formal language.
 *)
module Sort =
	struct
		type sort =
			| SBool
			| SInt (* primitive sorts *)
			| SMap of sort list (* head is sort of image and tail is sort of arguments *)
			| SWild of int (* wildcard sort with ID *)
		
		(* SORT PRINTING *)
		
		let rec string_of_sort s = match s with
			| SWild i -> "X_{" ^ (string_of_int i) ^ "}"
			| SInt -> "Z"
			| SMap d -> (String.concat "x" (List.map string_of_sort (List.tl d))) ^ "->" ^ (string_of_sort (List.hd d))
			| SBool -> "2"
		
		let rec latex_of_sort s = match s with
			| SWild i -> "\\mathcal{X}_{" ^ (string_of_int i) ^ "}" 
			| SInt -> "\\mathbb{Z}"
			| SMap d -> (String.concat "\\times" (List.map latex_of_sort (List.tl d))) ^
					" \\mapsto " ^ (latex_of_sort (List.hd d))
			| SBool -> "\\mathbb{B}"
		
		(* SORT UTILITIES *)
		
		(**
		 * Get the signature of a SMap sort
		 *)
		let signature_of_smap s = match s with
			| SMap d -> d
			| _ -> failwith "[signature_of_smap] : input sort is not a SMap"
		
		let rec eq_sort s1 s2 = match (s1,s2) with
			| (SWild i, SWild j) -> i = j
			| (SInt, SInt)
			| (SBool, SBool) -> true
			| (SMap d1, SMap d2) -> List.for_all2 (fun x y -> eq_sort x y) d1 d2
			| _ -> false
		
		let rec unify_sort s1 s2 = match (s1, s2) with
			| (SWild i, SWild j) -> 
				if (j > i) then ([(s1, s2)], s2)
				else if (i > j) then ([(s2, s1)], s1)
				else ([], s1)
			| (SWild _, _) -> ([(s1, s2)], s2)
			| (_, SWild _) -> ([(s2, s1)], s1)
			| (SMap d1, SMap d2) ->
				let soln, rs = List.split (List.map2 unify_sort d1 d2) in
					(List.flatten soln, SMap rs)
			| (SInt, SInt)
			| (SBool, SBool) -> ([], s1)
			| _ -> failwith ("[unify_sort] : sorts " ^ (string_of_sort s1) ^
						" and " ^ (string_of_sort s2) ^ " are not unifiable")
		
		let rec unify_sort_list sl =
			let unf (ps, x) y =
				let ns, z = unify_sort x y in
					(List.append ps ns, z) in
			let soln, rs = List.fold_left unf ([], SWild 0) sl in
			let soln = List.filter (fun (x, y) -> match x with SWild 0 -> false | _ -> true) soln in
				(soln, rs)
		
		let rec subst_sort (s1,s2) s =
			let s1i = match s1 with
				| SWild i -> i
				| _ -> failwith "Unexpected sort" in   
			match s with
				| SWild i ->
					if (i = s1i) then s2 else s
				| SMap d ->
					SMap (List.map (subst_sort (s1,s2)) d)
				| _ -> s
		
		let rec is_ground_sort s = match s with
			| SWild _ -> false
			| SMap d ->
				List.for_all is_ground_sort d
			| _ -> true
		
		let eq_sort_pair (x,y) (z,t) =
			(eq_sort x z) && (eq_sort y t)
		
		let rec subst_ground_sorts a sl =
			let gr, rs = List.partition (fun (_, y) -> is_ground_sort y) sl in
			let gr = GList.remove_dups_eq eq_sort_pair gr in
			(*let _ = List.map (fun (x,y) -> print_endline ("Ground substitution found : " ^ (string_of_sort x) ^ " --> " ^ (string_of_sort y))) gr in*)
			if (gr = []) then (GList.remove_dups_eq eq_sort_pair a, sl)
			else
				let rs = List.map (fun (x,y) ->
					try let u,v = List.find (fun (z,t) -> eq_sort x z) gr in
						fst (unify_sort y v)
					with Not_found -> [(x,y)]) rs in
				let rs = List.flatten rs in 
				let rs = List.fold_right (fun (x,y) r -> List.map (fun (z,t) -> (z, subst_sort (x,y) t)) r) gr rs in
					subst_ground_sorts (List.append a gr) rs

end;;

module type NumeralType =
	sig
		type t
	end;;
	
module type SymbolType =
	sig
		type t
		val to_string : t -> string
		val equal : t -> t -> bool
		val compare : t -> t -> int
	end;;

(**
 * Modules for functions and logical
 * operators.
 *)
module Func =
	struct
		type func =
			| Add
			| Sub
			| Mul
			| Div
			| Mod
			| Lt
			| Le
			| Gt
			| Ge
			| Eq
			| Ne
			| Top
			| Bot
			| And
			| Or
			| Neg
			| Implies
			| Iff
			| Exists
			| Forall
			| GFunc
		
		let precedence_of f = match f with
			| Implies | Iff -> 1
			| Or -> 2
			| And -> 3
			| Exists | Forall -> 4
			| Neg -> 5
			| Lt | Le | Gt | Ge | Eq | Ne -> 7
			| Add | Sub -> 8
			| Mul | Div | Mod -> 9			
			| Top | Bot -> 10
			| GFunc -> 10

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
	
		(**
		 * Get the sort of the result of function application from the functor
		 *)
		let sort_of_func f = match f with
			| Add | Sub | Mul | Div | Mod -> SInt
			| Lt | Le | Gt | Ge | Eq | Ne | Top | Bot | And | Or | Neg | Implies | Iff | Exists | Forall -> SBool
			| GFunc -> SWild 0
		
		(**
		 * Get common sort of all arguments from the functor
		 *)
		let argsort_of_func f = match f with
			| Add | Sub | Mul | Div | Mod | Lt | Le | Gt | Ge | Eq | Ne -> SInt
			| Top | Bot | And | Or | Neg | Implies | Iff -> SBool
			| Exists | Forall | GFunc -> SWild 0	
	
	
	end

module Term = 
	functor (*(n : NumeralType)*) (s : SymbolType) ->
	struct
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
			| Var of s (* Variable symbols *)
			| Fx of func * term list (* Function application *)
		
		
		(* TERM CONSTRUCTORS *)

		let set_term_sort s t = match t with
			| Var (_,v) -> Var (s, v)
			| FunApp (GFunc, x) -> 
				let o, x = List.hd x, List.tl x in
				let d = signature_of_smap (sort_of_term o) in
				let o = Var (SMap (s :: List.tl d), name_of_var o) in
					FunApp (GFunc, o :: x)
			| _ -> t
		
		(*
		(* current number of wild sorts *)
		let var_count = ref 0
		
		let inc v = v := !v + 1; !v
		*)
		
		let mkNum n = Num n
		
		let mkVar v = Var v
		
		let mkTop () = Fx (Func.Top, [])
		
		let mkBot () = Fx (Func.Bot, [])
		
		let mkFx f x = Fx (f, x)
			(*match f with
			| GFunc -> (* replace the sort for operator so that any query sort_of_term is safe! *)
				let o, x = List.hd xs, List.tl xs in
				let sf = sort_of_term o in (* assume that o has unique sort identifier ==> can be reused *)
				let o = Var (SMap (sf :: (List.map sort_of_term x)), name_of_var o) in
					FunApp (GFunc, o :: x)
			| Exists | Forall -> FunApp (f, (set_term_sort SBool (List.hd xs)) :: (List.tl xs))
			| _ -> let xf = argsort_of_func f in FunApp (f, List.map (set_term_sort xf) xs)*)
		
		let mkBinFx f x1 x2 = mkFx f [x1; x2]
		
		let mkUnaFx f x = mkFx f [x]
		
		(* TERM UTILITIES *)
		
		let rec get_all_vars t = match t with
			| Num _ -> []
			| Var _ -> [t]
			| Fx (_, x) ->
				List.flatten (List.map get_all_vars x)
		
		let rec get_all_fx t = match t with
			| Num _ | Var _ -> []
			| Fx (f, x) ->
				let fapps = List.flatten (List.map get_all_fx x) in
				match f with
					| GFunc -> t :: fapps
					| _ -> fapps
		
		let is_gfx t = match t with
			| Fx (GFunc, _) -> true
			| _ -> false
			
		let get_functor_name t = match t with
			| Fx (GFunc, x) -> name_of_var (List.hd x)
			| _ -> failwith "[functor_name] : expect a function application"
		
		let get_fun_app_arg t = match t with
			| Fx (GFunc, x) -> List.tl x
			| _ -> failwith "[get_fun_app_arg] : expect a function application"
		
		(**
		 * Get all free variables in a term t (with duplicates)
		 *)
		let rec frv t = match t with
			| Num _ -> []
			| Var _ -> [t]
			| Fx (f, x) ->
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

	end;;