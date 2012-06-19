(**
 * Logical term
 *
 * @author Vu An Hoa 
 *)

(*type ground =
		| Top
		| Bot
		| Num of int*)

(* variable is just function *)
(* application with 0 argument *)
(* boolean true/false can be *)
(* represented by positive integers *)
(* and non-positive ones *)
type term =
	| Top (* true > 0 *)
	| Bot (* false <= 0 *)
	| Num of int (* numeral constant *)
(*		| Var of int (* variable *)*)
	| Fx of func * (term list)
		(* variable/function application *)
		(* Note: when func is a quantifier, the *)
		(* first term in the subsequent list    *)
		(* represents the main subformula and   *)
		(* the rests are quantified variables   *)

and func =
	(* basic arithmetic: *)
	(*  - addition and multiplication are *)
	(*    arbitrary a-ry                  *)
	(*  - the rest are all binary *)
	| Add
	| Sub 
	| Mul
	| Div 
	| Mod
	(* basic relation : equality, disequality, inequality *)
	| Eq 
	| Ne 
	| Lt 
	| Le 
(*		| Gt *)
(*		| Ge *)
	(* logical connectives: *)
	(*  - and/or are arbitrary a-ry *)
	(*  - neg is unary *)
	(*  - implies/iff are binary *)
	| And 
	| Or 
	| Neg 
	| Implies 
	| Iff
	(* quantifiers *)
	| Exists
	| Forall
	(* generic user-defined function of index      *)
	(* indexing convention:                        *)
	(*  - positive : logical symbols (variable)    *)
	(*  - negative : language parameters (constant *)
	(*                and defined functions)       *)
	| GF of int (* * Domain.domain *)
	
(* constructors *)

let mkTop () = Top

let mkBot () = Bot

let mkNum n = Num n

let mkVar v (* d *) = Fx (GF v, [])

let mkFx f x = Fx (f, x)

let mkBFx f x1 x2 = mkFx f [x1; x2]

let mkUFx f x = mkFx f [x]

(* compare *)

(**
 * Syntactical comparison of two terms
 * TODO implement
 *)
let compare t1 t2 = 0

(* query *)

(**
 * Check if a term is a ground term i.e.
 * contains no logical variable.
 *)
let rec is_ground t = match t with
	| Top
	| Bot
	| Num _ -> true
	| Fx (f, x) -> match f with
		| GF _ -> false
		| _ -> List.for_all is_ground x

(**
 * Check if a term is a logical variable
 *)
let is_var t = match t with
	| Fx (GF i, []) -> i >= 0
	| _ -> false

(* getter *)

(**
 * Get the index of the top level functor
 * symbol; return 0 on default
 *)
let get_index t = match t with
	| Fx (GF i, x) -> i
	| _ -> 0

(**
 * Get the list of top level quantified 
 * variables; should the top level is not
 * a quantification, return []
 *)
let rec get_top_qindex t = match t with
	| Fx (Exists, x)
	| Fx (Forall, x) -> 
		List.map get_index (List.tl x)
	| _ -> []

(**
 * Retrieve all indices occurred in a term.
 *)
let rec get_all_indices t = match t with
	| Top
	| Bot
	| Num _ -> []
	(* | Var v -> [t] *)
	| Fx (f, x) ->
		let r = List.map get_all_indices x in
		let r = List.flatten r in
		match f with
			| GF i -> i :: r
			| _ -> r

(**
 * Get all free variables in a term.
 *)
let rec get_free_vars t = match t with
	| Top
	| Bot
	| Num _ -> []
(*		| Var v -> [t]*)
	| Fx (f, x) ->
		let r = List.map get_free_vars x in
		let s = List.flatten r in
		match f with
			| Exists
			| Forall ->
				let qv = List.flatten (List.tl r) in
				let qf = List.hd r in
					GList.remove_all_eq (=) qf qv
			| GF i ->
				if (i >= 0) then
					i :: s
				else 
					s
			| _ -> s

(**
 * Get all free variables in a term.
 *)
let rec get_quantified_vars t = match t with
	| Top
	| Bot
	| Num _ -> []
(*		| Var v -> [t]*)
	| Fx (f, x) ->
		let r = List.map get_quantified_vars x in
		let s = List.flatten r in
		match f with
			| Exists
			| Forall ->
				let qv = List.flatten (List.tl r) in
				let qf = List.hd r in
					GList.remove_all_eq (=) qf qv
			| _ -> []

(**
 * Convert a formula term into a sentence
 * by prefixing it with forall quantification
 *)
let convert_to_sentence t =
	let fv = get_free_vars t in
	match fv with
		| [] -> t
		| _ ->
			let qv = List.map (fun i -> mkVar i) fv in
				Fx (Forall, t :: qv)

(* Term transform *)

(**
 * Reindex the term by replacing all symbol
 * i by j in the term t for all pair (i,j) 
 * as specified in the input list d.
 *)
let rec reindex d t = match t with
	| Top
	| Bot
	| Num _ -> t
	| Fx (f, x) -> 
		let x = List.map (reindex d) x in
		match f with
			| GF i -> 
				let j = try 
(*						let _  = print_string ("associating " ^ (string_of_int i) ^ " in dictionary ") in*)
(*						let _ = print_endline (String.concat ""                                         *)
(*							(List.map (fun (x,y) ->                                                       *)
(*								(string_of_int x) ^ " --> " ^ (string_of_int y)                             *)
(*								) d)) in                                                                    *)
(*						let t = List.assoc i d in                                                       *)
(*						let _ = print_endline ("result = " ^ (string_of_int t)) in                      *)
(*							t                                                                             *)
						List.assoc i d
					with 
						| Not_found -> i in
				Fx (GF j, x)
			| _ -> Fx (f, x)

(**
 * Standardize all variables in a term by 
 * making all of them different; assuming
 * the indexing convention.
 *)
let rec standardize qv i t = match t with
	| Top
	| Bot
	| Num _ -> (qv, i, t)
	| Fx (f, x) -> match f with
		| Exists
		| Forall -> 
			(* rename clashed symbols *)
			let qvs = get_top_qindex t in
(*				let _ = print_string "quantified vars : " in                             *)
(*				let _ = List.map (fun x -> print_string ((string_of_int x) ^ ",")) qvs in*)
(*				let _ = print_endline "" in                                              *)
			let clash_vars = GList.intersect_eq (=) qvs qv in
(*				let _ = print_string "clashed vars : " in                                       *)
(*				let _ = List.map (fun x -> print_string ((string_of_int x) ^ ",")) clash_vars in*)
(*				let _ = print_endline "" in                                                     *)
			let d = GList.mapi (fun j y -> (y, i + j)) clash_vars in
(*				let _ = print_string "dictionary : " in                                                                  *)
(*				let _ = List.map (fun (x,y) -> print_string ((string_of_int x) ^ " --> " ^ (string_of_int y) ^ ",")) d in*)
(*				let _ = print_endline "" in                                                                              *)
			let t = reindex d t in
			let qvs = get_top_qindex t in
(*				let _ = print_string "input collected quantified vars : " in             *)
(*				let _ = List.map (fun x -> print_string ((string_of_int x) ^ ",")) qv in *)
(*				let _ = print_endline "" in                                              *)
(*				let _ = print_string "new top level quantified vars : " in               *)
(*				let _ = List.map (fun x -> print_string ((string_of_int x) ^ ",")) qvs in*)
(*				let _ = print_endline "" in                                              *)
			let i = i + List.length d in
			(* add new quantified vars and standardize the main formula *)
			let qv = List.append qv qvs in
(*				let _ = print_string "new list of quantified vars : " in                *)
(*				let _ = List.map (fun x -> print_string ((string_of_int x) ^ ",")) qv in*)
(*				let _ = print_endline "" in                                             *)
			let x = match t with | Fx (_, x) -> x | _ -> x in
			let qv, i, rf = standardize qv i (List.hd x) in
				(qv, i, Fx (f, rf :: List.tl x))
		| _ ->
			let sx = List.fold_left (fun (qv, i, px) tx -> 
				let qvr, ir, tx = standardize qv i tx in
				let px = List.append px [tx] in
					(qvr, ir, px)) (qv, i, []) x in
			let qv, i, x = sx in
				(qv, i, Fx (f, x))

(**
 * Make free variables v_0, v_1, ...
 *)
let standardize t =
	(* select an appropriate starting point *)
	(* for variable renaming                *)
	let is = get_all_indices t in
	let i = List.fold_left max 0 is in
	(* standardize using earlier helper function *)
	let _,_,r = standardize [] (i + 1) t in
	(* rename variable to smallest 0 to num variables - 1 *)
		r

(**
 * Substitute simultaneously [v/vt]
 * for all pairs (v,vt) in binding list
 * where
 * v is the variable index to be 
 * substituted, vt is the term to
 * substitute it with.
 *)
let rec subst sb t = if sb = [] then t
	else match t with
		| Top
		| Bot
		| Num _ -> t
(*			| Var (_, v) -> begin   *)
(*				try                   *)
(*					List.assoc v stl    *)
(*				with                  *)
(*					| Not_found -> t end*)
		| Fx (f, x) -> match f with
			| Exists
			| Forall ->
				let fml = List.hd x in
				let qv = List.tl x in
				let qvi = List.map get_index qv in
				let sb = GList.remove_all_eq (fun (v,_) q -> v = q) sb qvi in
(*					let qvarsnames = List.map name_of_var qvars in*)
(*					let stl = GList.remove_all_eq (fun (v,_) q -> v = q) stl qvarsnames in*)
					Fx (f, (subst sb fml) :: qv)
			| GF i -> begin try
					List.assoc i sb
				with
					| Not_found -> 
						let x = List.map (subst sb) x in
							Fx (f, x) end
			| _ ->
				let x = List.map (subst sb) x in
					Fx (f, x)

(*

(* let fv t = (fv t) *)

(* methods *)

let id_of_var t = match t with
	| Var v -> v
	| _ -> failwith ("[id_of_var] : input term " ^ (string_of_term t) ^ " is not a var!")

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

(* generate domain unification constraints *)

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
*)