(**
 * Zeta theorem prover
 * Version 2.0
 *
 * @author Vu An Hoa
 *)

(* Useful list utilities *)

module GList = struct
	
	(**
	 * Partition elements of a list into 
	 * equivalence classes, assuming eqv
	 * is reflexive, symmetric, and 
	 * transitive.
	 * @param eqv indicate whether two 
	 * elements of the list are equivalent 
	 * i.e. belong to the same class
	 * @return a list of equivalence classes 
	 *)
	let rec group_elms eqv l = match l with
		| [] -> []
		| h :: t -> (* select elements in t that are in same class as h *)
			let ch,r = List.partition (eqv h) t in
			let cr = group_elms eqv r in (* partition the rest *)
				(h :: ch) :: cr
	
	(**
	 * Remove duplicates in a list.
	 *)
	let remove_dups_eq eq l =
		let eq_classes = group_elms eq l in
			List.map List.hd eq_classes
	
	(**
	 * Check if exists y in l such that [eq x y]
	 *)
	let memeq eq l x =
		try
			let _ = List.find (eq x) l in
				true
		with
			| Not_found -> false
	
	(**
	 * Check if for all y in l: [eq x y] does not hold
	 *)	
	let notmemeq eq l x = not (memeq eq l x)
		
	(**
	 * Compute l1 \ l2
	 *)
	let remove_all_eq eq l1 l2 =
		List.filter (notmemeq eq l2) l1
	
	(**
	 * Position-aware list map
	 *)		
	let mapi f l =
		let rec mapi_helper l i =
			match l with
				| [] -> []
				| h :: t -> (f i h) :: (mapi_helper t (i+1)) in
		mapi_helper l 0
		
	(**
	 * Check if the elements of l1 is a subset of l2
	 *)
	let subset_eq eq l1 l2 =
		List.for_all (memeq eq l2) l1

end

(* Main data structures for the formal (logical) language *)

module Domain = struct
	
	type domain =
		(* | SBool true/false *)
		| SInt	(* set of integers *)
		| SWild of int
						(* unknown domain, for domain estimation only *)
		| SMap of domain list
						(* map : tail -> head *)
	
	(* getters *)
	
	
	
	(* query *)
	
	let rec has_no_wild s = match s with
		| SInt -> true
		| SWild _ -> false
		| SMap d ->
			List.for_all has_no_wild d
	
	(* compare domains *)
	
	let rec eq_domain s1 s2 = 
		match (s1,s2) with
			| (SWild i, SWild j) -> i = j
			| (SInt, SInt) -> true
			(* | (SBool, SBool) -> true *)
			| (SMap d1, SMap d2) ->
					List.for_all2 eq_domain d1 d2
			| _ -> false
	
	(*(**
	 * Get the signature of a SMap sort
	 *)
	let signature_of_smap s = match s with
		| SMap d -> d
		| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

	(**
	 * Get the signature of a SMap sort
	 *)
	let signature_of_smap s = match s with
		| SMap d -> d
		| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

	(**
	 * Get the signature of a SMap sort
	 *)
	let signature_of_smap s = match s with
		| SMap d -> d
		| _ -> failwith "[signature_of_smap] : input sort is not a SMap"

	(* solve the swild domain constraints *)

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

	(**
	 * Solve for all SWild from the given list of unification constraints as input
	 * @return a list of pairs (i, d) to indicate domain (SWild i) must be unified with a ground domain d 
	 *)
	let solve_domains uni_constr =
		let soln, _ = List.split (List.map unify_sort_list uni_constr) in
		let soln = List.flatten soln in
		let soln, rem = subst_ground_sorts [] soln in
		let soln = List.sort (fun (x1,_) (x2,_) -> 
			match (x1, x2) with
				| (SWild i, SWild j) -> i - j
				| _ -> failwith "exception") soln in
			soln
	*)
end

module Term = struct
	
	(*type ground =
		| Top
		| Bot
		| Num of int*)

	type term =
		(* | Top (* true, use > 0 i.e. positive *) *)
		(* | Bot (* false, use <= 0 i.e. non-positive *) *)
		| Num of int (* numeral constant *)
		(* | Var of int *)
		| Fx of func * (term list)
						(* variable is just function *)
						(* application with 0 argument *)

	
	and func =
		| Add | Sub | Mul | Div | Mod
		| Eq | Ne | Lt | Le (* | Gt | Ge *)
		| And | Or | Neg | Implies | Iff
		| Exists | Forall
		| GFunc of int

	(* constructors *)
	
	let mkTop () = Top
	
	let mkBot () = Bot
	
	let mkNum n = Num n
	
	let mkVar v = Var v
	
	let mkFx f x = Fx (f, x)
	
	let mkBFx f x1 x2 = mkFx f [x1; x2]
	
	let mkUFx f x = mkFx f [x]
	
	(* compare *)
	
	(* getter *)
	
	let av t = match t with
		| Top
		| Bot
		| Num _ -> []
		| Var v -> [t]
		| Fx (_, x) ->
			List.flatten (List.map av x)
	
	(*let fv t = match t with
		| Top
		| Bot
		| Num _ -> []
		| Var v -> [t]
		| Fx (f, x) -> 
			let r = List.map fv x in
			match f with
				| Exists | Forall ->
					let q = List.flatten (List.tl r) in
						GList.remove eq_var (List.hd r) q
				| _ -> List.flatten r

	(*let fv t = (fv t)*)
	
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
	
end

(*
module Proof = struct
	
	(**
	 * Type for proof tree
	 *)
	type proof =
		| Hypothesis of term (* axiom is viewed as ambient hypotheses *)
		| Rewrite of proof_step (* Rewrite of the term into equivalent form *)
		| Induction of term * proof_step * proof_step (* induction on the first term, proof for base case and induction case *)
		| ModusPonen of proof_step * proof_step (* application of Modus Ponen {p, p -> q} |- q *)
	
	(**
	 * The first component is the target formula to obtain
	 * The second component is the proof for that formula
	 * To be revised as a record instead
	 *)
	and proof_step = term * proof
	
	let string_of_proof p = ""
	
end
*)

module TriaryLogic = struct
	
	type triary_bool =
		| True
		| False
		| Unknown
	
	let string_of_triary_bool b = match b with
		| True -> "true"
		| False -> "false"
		| Unknown -> "unknown"
	
	let negate_triary b = match b with
		| True -> False
		| False -> True
		| Unknown -> Unknown

end

module Context = struct
	
	open Domain
	open Term
	open TriaryLogic

	type context = {
			def_symbols : symbol list;
			axioms : term list;
			theorems : theorem list;
		}
		
	and symbol = {
			name : string;
			dom : domain;
		}
	
	and theorem = {
			content : term;
			proved_status : triary_bool;
		}
	
	
	
end

(* Output *)

module type BasePrinter = sig
	
	val print_domain : domain -> string
	
	val print_func : func -> string
	
	val top : string
	
	val bot : string
	
end

module StringBasePrinter : BasePrinter = struct
	
	let rec print_domain d = match d with
		| SWild i -> "X_" ^ (string_of_int i)
		| SInt -> "Z"
		| SMap d -> (String.concat "x" (List.map print_domain (List.tl d))) ^ "->" ^ (string_of_sort (List.hd d))
		| SBool -> "2"
	
	let print_func f = match f with
		| Add -> "+" | Sub -> "-" | Mul -> "*" 
		| Div -> "/" | Mod -> "mod"
		| Lt -> "<" | Le -> "<=" | Gt -> ">"
		| Ge -> ">=" | Eq -> "=" | Ne -> "!="
		| And -> " /\\ " 
		| Or -> " \\/ " | Neg -> "~" | Implies -> "->" 
		| Iff -> "<->" | Exists -> "E" | Forall -> "A"
		| GFunc -> ""
	
	let top = "T"
	
	let bot = "F"
	
end

module TexBasePrinter : BasePrinter = struct
	
	let rec print_domain d = match d with
		| SWild i -> "\\mathcal{X}_{" ^ (string_of_int i) ^ "}" 
		| SInt -> "\\mathbb{Z}"
		| SMap d -> (String.concat "\\times" (List.map print_domain (List.tl d))) ^
				" \\mapsto " ^ (print_domain (List.hd d))
		| SBool -> "\\mathbb{B}"
	
	let print_func f = match f with
		| Add -> "+" | Sub -> "-" | Mul -> "\\times"
		| Div -> "\\div" | Mod -> "\\bmod"
		| Lt -> "<" | Le -> "\\leq" | Gt -> ">"
		| Ge -> "\\geq" | Eq -> "=" | Ne -> "\\not="
		| And -> "\\land"
		| Or -> "\\lor" | Neg -> "\\neg"
		| Implies -> "\\rightarrow" | Iff -> "\\leftrightarrow"
		| Exists -> "\\exists" | Forall -> "\\forall"
		| GFunc -> ""

	let top = "\\top"
	
	let bot = "\\bot"
	
end

module type VarPrinter = sig
	
	val print_var : int -> string
	
end

module RawVarPrinter : VarPrinter = struct
	
	let print_var i =
		if (i < 0) then
			"F_" ^ (string_of_int (-i))
		else
			"x_" ^ (string_of_int i)
	
end

module StringVarPrinter : VarPrinter = struct
	
	let int_string_map : (int, string) Hashtbl.t = Hashtbl.create 10 
	
	let print_var i =
		try
			Hashtbl.find int_string_map i
		with
			| Not_found -> 
				RawVarPrinter.print_var i
	
end

module Printer (BP : BasePrinter) (VP : VarPrinter) = struct
	
	let rec print_term_helper pr_var p t  = match t with
		| Top -> BP.top
		| Bot -> BP.bot
		| Num i -> string_of_int i
		| Var (s, v) -> pr_var s v
		| FunApp (f, x) ->
			let pf = precedence_of f in
			let xp = match f with | GFunc -> 0 | _ -> pf in
			let sx = List.map (print_term_helper pr_var pr_func xp) x in
			let sf = pr_func f in
			let e = match f with
				| Exists | Forall -> sf ^ " " ^ (String.concat "," (List.tl sx)) ^ " : " ^ (List.hd sx)
				| GFunc -> (List.hd sx) ^ "[" ^ (String.concat "," (List.tl sx)) ^ "]"
				| Neg -> sf ^ " " ^ (List.hd sx)
				| _ -> String.concat (" " ^ sf ^ " ") sx in
			if (pf < p) then "(" ^ e ^ ")" else e
	
	let print_term pr_var t = print_term_helper pr_var 0 t
	
	(*let print_term t = ""
	
	let print_context c = ""*)
	
end

(**
 * Input lexing and parsing
 *)

(* TODO write lexer in ocaml when camlp supports it *)

(* module Token = struct
	
end

module Lexer = struct		

end *)

module Parser = struct
	
	open Camlp4
	open Ztoken
	(*open Zutils
	open Zsort
	open Zterm
	open Zlogic*)

	module ZGram = Camlp4.PreCast.MakeGram(Zlexer.Make(Ztoken))

	(* Global table to map string to int (id) *)
	
	let symbol_id_table = Hashtbl.create 100
	
	let f_index = ref 1;
	
	let v_index = ref 1;
	
	(* INPUT DATA STRUCTURE *)
	
	(*type defn =
		(*| Axiom of term*)
		| Symbol of term * term list * term list option
		| Theorem of term
	
	(* DEFINITION CONSTRUCTORS *)
	
	(*let mkAxiom t = Axiom t*)
	
	let mkSymbol l axms ind_hints = Symbol (l, axms, ind_hints)
		
	let mkTheorem t = Theorem t
	
	(* DEFINITION PRINTING *)
	
	(*let string_of_defn tp d = match d with
		(*| Axiom t -> "<b>Axiom</b> \\(" ^ (tp t) ^ "\\)<br>"*)
		(*| Symbol (s, sl, t) -> 
			"<b>Definition</b> <i>" ^ s ^ "</i>" ^ (match t with
				| Some t1 -> " := \\(" ^ (tp t1) ^ "\\)<br>"
				| None -> "<br>")*)
		| Symbol (l, a, t) -> "<b>Definition</b> Let \\(" ^ (tp l) ^ "\\) be such that " ^ (String.concat "<br />" (List.map tp a))
		| Theorem t -> "<b>Theorem</b> \\(" ^ (tp t)  ^ "\\)<br>"*)
	
	(* DEFINITION PROCESSING *)
	
	let get_symbol_name d = match d with
		| Symbol (l, _, _) -> (match l with
			| Var (_, v) -> v
			| FunApp (GFunc, x) -> name_of_var (List.hd x)
			| _ -> failwith "Expected a var/fun app")
		| _ -> failwith "Expect symbol defn"
	
	let get_defined_symbols defs =
		let res = List.map (fun d -> match d with
			| Symbol _ -> [get_symbol_name d]
			| _ -> []) defs in
			List.flatten res
	
	let get_defn_term d = match d with
		(*| Axiom t*)
		| Theorem t -> [t]
		| Symbol (l, a, _) -> a
	
	let get_all_terms defs =
		let res = List.map get_defn_term defs in
		let res = List.flatten res in
			res
	
	let transform_term_in_defn ff d = 
		match d with
		(*| Axiom t -> Axiom (ff t)*)
			| Symbol (l, a, t) -> Symbol (ff l, List.map ff a, t) 
			| Theorem t -> Theorem (ff t)
	
	let transform_term_in_defn_list ff defs =
		List.map (transform_term_in_defn ff) defs
	
	let map_defn ff d = match d with
		(*| Axiom t -> ff t*)
		| Symbol (l, a, t) -> (ff l) :: (List.map ff a)
		| Theorem t -> [ff t]
	
	let map_defn_list ff defs =
		List.map (map_defn ff) defs
	
	let infer_sorts defs =
		(* collect & group symbols by name *)
		let vss = map_defn_list collect_vars defs in
		let vss = List.flatten vss in
		let vss = List.map (GList.group_elms eq_var) vss in
		(* generate local sorts unification constraints *)
		let gen_loc_unif_constr sym_class =
			(name_of_var (List.hd sym_class), List.map sort_of_term sym_class) in
		let vss = List.map (fun cs -> 
			List.map gen_loc_unif_constr cs) vss in
		(* extract global sorts unification constraints *)
		let globsyms = get_defined_symbols defs in
		(*let _ = print_endline ("Defined symbols : [" ^ (String.concat ", " globsyms) ^ "]") in*)
		let glob_constr = List.map (fun s ->
			List.flatten (List.map (fun cs -> 
				try List.assoc s cs
				with Not_found -> []) vss)) globsyms in
		let loc_constr = List.map (fun cs ->
			List.filter (fun c -> 
				not (List.mem (fst c) globsyms)) cs) vss in
		let locsyms, loc_constr = List.split (List.flatten loc_constr) in
		(*let _ = List.map2 (fun s c -> 
			print_endline ("Unification constraint for global symbol " ^ s ^ " : {" ^ 
				(String.concat "," (List.map string_of_sort c)) ^
			"}")) globsyms glob_constr in
		let _ = List.map (fun c -> 
			print_endline ("Local unification constraint : {" ^ 
				(String.concat "," (List.map string_of_sort c)) ^
			"}")) loc_constr in*)
		let constr = List.append glob_constr loc_constr in
		(* solve the unification *)
		(*let _ = print_endline "Solution:" in
		let _ = List.map (fun (x, y) -> 
			print_endline ((string_of_sort x) ^ " --> " ^ (string_of_sort y))) soln in*)
		(* update symbols in all terms *)
		let defs = transform_term_in_defn_list 
			(fun t -> subst_sort_term soln t) defs in
		let sym_sort_table = Hashtbl.create 10 in
		let sym_sort = List.map (fun x -> List.fold_right subst_sort soln (List.hd x)) glob_constr in
		let _ = List.map2 (Hashtbl.add sym_sort_table) globsyms sym_sort in
		let sym_table = Hashtbl.create 10 in
		let _ = List.map (fun d -> match d with
			| Symbol (l, a, t) -> 
				let n = get_symbol_name d in
				let x = get_fun_app_arg l in
				let sinf = { name = n;
							symbol_sort = Hashtbl.find sym_sort_table n;
							axioms = (* Add forall to free variables *)
								(* List.map (fun t -> ) *) a;
							induction = match t with
								| Some t1 -> (* standardize inductions *)
									let stl = GList.mapi  
										(fun i y -> 
											let vi = Var (sort_of_term y, 
																		"$" ^ (string_of_int i)) in 
										(name_of_var y, vi)) x in
									List.map (subst stl) t1
								| None -> [];} in
					Hashtbl.add sym_table n sinf
			| _ -> ()) defs in
		(* universally quantified all the axioms *)
		let _ = Hashtbl.iter (fun x y -> 
			let axms = List.map (fun a ->
				let va = filter_defined_symbols sym_table (frv a) in
					FunApp (Forall, a :: va)) y.axioms in
			let _ = Hashtbl.remove sym_table x in
				Hashtbl.add sym_table x {y with axioms = axms}) 
			sym_table in
		(defs, sym_table)
	
	let get_theorems_list defs = 
		let is_theorem d = match d with
			| Theorem t -> true
			| _ -> false in
		let thms = List.filter is_theorem defs in
		let get_theorem_struct d = match d with
			| Theorem t -> { thm = t; proved = false; }
			| _ -> failwith "Theorem expected!" in
		let thms = List.map get_theorem_struct thms in
			thms
	*)
	
	(* GRAMMAR *)
	
	let zeta = ZGram.Entry.mk "zeta";;
	
	EXTEND ZGram GLOBAL : zeta;
	
	zeta : [[ t = LIST0 statement; `EOF -> t]];
	
	statement : [[
		(*`AXIOM; a = formula; `DOT -> mkAxiom a
		|*) h = symbol_defn_header; `BE; `SUCH; `THAT; 
			a = LIST1 formula SEP `SEMICOLON; `DOT -> 
				mkSymbol (fst h) a (snd h)
		(*| h = symbol_defn_header; `DEFEQ; 
			t = formula; `DOT -> 
				mkSymbol (fst h) (snd h) (Some t)*)
		| `THEOREM; t = formula; `DOT ->
			mkTheorem t ]];
	
	symbol_defn_header : [[
		`LET; a = OPT symbol_annotation; t = formula -> (t, a) ]];
	
	formula : [
		"implication and iff" RIGHTA
		[ t1 = SELF; `RIGHTARROW ; t2 = SELF -> mkBinTerm Implies t1 t2
		| t1 = SELF; `LEFTRIGHTARROW ; t2 = SELF -> mkBinTerm Iff t1 t2]
	| "disjunction" [ t1 = SELF; `OR; t2 = SELF -> mkBinTerm Or t1 t2]
	| "conjunction" [ t1 = SELF; `AND; t2 = SELF -> mkBinTerm And t1 t2]
	| "quantified formulas"
		[ `EXISTS; `OBRACE; qv = identifier_list; `CBRACE; t = SELF ->
				mkListTerm Exists (t::(List.map mkVar qv))
		| `FORALL; `OBRACE; qv = identifier_list; `CBRACE; t = SELF -> 
				mkListTerm Forall (t::(List.map mkVar qv)) ]
	| "negation" [`NOT; t = SELF -> mkUnaryTerm Neg t]
	| "standard equality/inequality"
		[ t1 = SELF; `EQ; t2 = SELF -> mkBinTerm Eq t1 t2
		| t1 = SELF; `GT; t2 = SELF -> mkBinTerm Gt t1 t2
		| t1 = SELF; `GTE; t2 = SELF -> mkBinTerm Ge t1 t2
		| t1 = SELF; `LT; t2 = SELF -> mkBinTerm Lt t1 t2
		| t1 = SELF; `LTE; t2 = SELF -> mkBinTerm Le t1 t2
		| t1 = SELF; `NEQ; t2 = SELF -> mkBinTerm Ne t1 t2]
	| "additive"
		[ t1 = SELF; `PLUS; t2 = SELF -> mkBinTerm Add t1 t2
		| t1 = SELF; `MINUS; t2 = SELF -> mkBinTerm Sub t1 t2]
	| "multiplicative"
		[ t1 = SELF; `STAR; t2 = SELF -> mkBinTerm Mul t1 t2
		| t1 = SELF; `DIV; t2 = SELF -> mkBinTerm Div t1 t2
		| t1 = SELF; `MOD; t2 = SELF -> mkBinTerm Mod t1 t2 ]
	| "base"
		[ s = identifier -> mkVar s
		| `NUMERAL i -> Num i
		| `FALSE -> mkBot ()
		| `TRUE -> mkTop ()
		| f = identifier; `OPAREN; x = LIST0 SELF SEP `COMMA; `CPAREN ->
			mkFx GFunc (mkVar f :: x)
		(*| f = identifier; `OSQUARE; x = LIST0 SELF SEP `COMMA; `CSQUARE ->
			mkListTerm GFunc (mkVar f::x)*)]
	| [ `OPAREN; t=SELF; `CPAREN -> t ]];
	
	identifier : [[ `IDENTIFIER s -> s ]];
	
	identifier_list : [[ idlist = LIST0 identifier SEP `COMMA -> idlist ]];
	
	symbol_annotation : [[ `OSQUARE; h = OPT induction_hints; `CSQUARE -> match h with None -> [] | Some t -> t]];
	
	induction_hints : [[ `INDUCTION; p = LIST1 formula SEP `COMMA -> p ]];
	
	END;;
			
	(**
	 * Parse an input stream and pre-process 
	 * to obtain information on defined 
	 * symbol and theorems.
	 *
	 * @return A hash table maps each symbol
	 * to its information structure and a
	 * list of theorems to be proved.
	 *)
	let parse n s =
		let defs = ZGram.parse zeta (PreCast.Loc.mk n) s in
		let defs, symtab = infer_sorts defs in
			(symtab, get_theorems_list defs)

end

(* Theorem proving : main program logic *)

module ExternalProver = struct

module Z3 = struct
	
	let print_z3_input = ref false
	
	(**
	 * Convert sort to Z3 sort
	 *)
	let rec z3sort ctx s = match s with
		| SWild _ -> failwith "[z3sort] wild sort cannot be translated to Z3"
		| SBool -> Z3.mk_bool_sort ctx
		| SInt -> Z3.mk_int_sort ctx
		| SMap d ->
			let doms = Array.of_list (List.tl d) in
			let syms = Array.mapi (fun i _ -> Z3.mk_string_symbol ctx ("Z" ^ (string_of_int i))) doms in
			let doms = Array.map (fun x -> z3sort ctx x) doms in
			let doms, _, _ = Z3.mk_tuple_sort ctx (Z3.mk_string_symbol ctx "smap") syms doms in
			let imgs = z3sort ctx (List.hd d) in
				Z3.mk_array_sort ctx doms imgs
				
	and z3constructor_of_dom ctx s = match s with
		| SMap d ->
			let doms = Array.of_list (List.tl d) in
			let syms = Array.mapi (fun i _ -> Z3.mk_string_symbol ctx ("Z" ^ (string_of_int i))) doms in
			let doms = Array.map (fun x -> z3sort ctx x) doms in
			let _,constr,_ = Z3.mk_tuple_sort ctx (Z3.mk_string_symbol ctx "smap") syms doms in
				constr
		| _ -> failwith "[z3sort_of_domain] : Unexpected sort"

	(**
	 * Assoc list to assoc func
	 * to Z3 AST constructors.
	 * Constructors with varied 
	 * number of arguments. 
	 *)
	let z3_array_constr =
		[(Add, Z3.mk_add);
		(Sub, Z3.mk_sub);
		(Mul, Z3.mk_mul);
		(And, Z3.mk_and);
		(Or, Z3.mk_or);
		(Ne, Z3.mk_distinct)]

	(**
	 * Binary constructors
	 *)
	let z3_bin_constr = 
		[(Div, Z3.mk_div);
		(Mod, Z3.mk_mod);
		(Lt, Z3.mk_lt);
		(Le, Z3.mk_le);
		(Gt, Z3.mk_gt);
		(Ge, Z3.mk_ge);
		(Eq, Z3.mk_eq);
		(Implies, Z3.mk_implies);
		(Iff, Z3.mk_iff)]
	
	(*let prepare_z3ast ctx ds t =
		(* prepare sorts for SMap domains & their constructors *)
		let vs = collect_vars t in
		let srts = List.map sort_of_term vs in
		let is_map_sort s = match s with | SMap _ -> true | _ -> false in
		let srts = List.filter is_map_sort srts in
		let srts = GList.remove_dups_eq eq_sort srts in
		
		(* produces functions applications for defined symbols *)
		let fas = List.map (fun (s,t) ->
			let ss = sort_of_symbol s t in
			let sd = domain_of ss in
			let sr = result_of ss in
			(s,Z3.mk_func_decl ctx (Z3.mk_string_symbol ctx s)
				sdom sres)) ds in
		
		
		(* prepare all symbols *)
		
			true*)
		
	(**
	 * Convert term to Z3 AST
	 *)
	let rec z3ast ctx (* ds *) t =
		(*let _ = print_endline ("[z3ast] " ^ (string_of_term t)) in*)
		match t with
			| Num i ->
				Z3.mk_int ctx i (Z3.mk_int_sort ctx)
			| Var (s, v) ->
				Z3.mk_const ctx (Z3.mk_string_symbol ctx v) (z3sort ctx s)
			| FunApp (f, x) ->
				let xs = List.map (z3ast ctx) x in
				match f with
					| Top -> Z3.mk_true ctx
					| Bot -> Z3.mk_false ctx
					| Neg -> Z3.mk_not ctx (List.hd xs)
					| Exists -> Z3.mk_exists_const ctx 0 (Array.of_list (List.map (Z3.to_app ctx) (List.tl xs))) [| |] (List.hd xs)
					| Forall -> Z3.mk_forall_const ctx 0 (Array.of_list (List.map (Z3.to_app ctx) (List.tl xs))) [| |] (List.hd xs)
					| Add | Sub | Mul | And | Or | Ne ->
						let z3constr = List.assoc f z3_array_constr in
							z3constr ctx (Array.of_list xs)
					| Div | Mod | Lt | Le | Gt | Ge | Eq | Implies | Iff ->
						let x0 = List.nth xs 0 in
						let x1 = List.nth xs 1 in
						let z3constr = List.assoc f z3_bin_constr in
							z3constr ctx x0 x1
					| GFunc ->
						let o, xs = List.hd xs, List.tl xs in
						let sf = sort_of_term (List.hd x) in
						let dc = z3constructor_of_dom ctx sf in
						(*let sf = Hashtbl.find (name_of_var o) in*)
							Z3.mk_select ctx o (Z3.mk_app ctx dc (Array.of_list xs))

	let z3lbool_to_triary_bool b =
		match b with
			| Z3.L_FALSE -> TBool.False
			| Z3.L_TRUE -> TBool.True
			| Z3.L_UNDEF -> TBool.Unknown

	let derive ts = match ts with
		| [] -> (TBool.True, []) (* \emptyset |- Top *)
		| h::rs ->
			let _ = if (!print_z3_input) then
				print_endline ("[Zexprf.Z3.derive]: input = {{{\n" ^ 
					(string_of_term h) ^ "\n}}}") in
			let ctx = Z3.mk_context_x [|
				("SOFT_TIMEOUT", "5000");
				("PULL_NESTED_QUANTIFIERS", "true");
				("PROOF_MODE","2") |] in
			(* assert constraints *)
			let z3hyps = List.map (z3ast ctx) rs in
			let z3conc = z3ast ctx (mkUnaryTerm Neg h) in
			let z3asserts = z3conc :: z3hyps in
			let _ = List.map (Z3.assert_cnstr ctx) z3asserts in
			let _ = if (!print_z3_input) then
				print_endline ("[Zexprf.Z3.derive]: Generated Z3 input = {{{\n" ^ 
					(String.concat "\n" (List.map (Z3.ast_to_string ctx) z3asserts)) ^ "}}}") in
			(* check and get proof *)
			let res = Z3.check ctx in
			let res = TBool.negate_triary (z3lbool_to_triary_bool res) in
			let _ = Z3.del_context(ctx) in
			let _ = if (!print_z3_input) then
				print_endline ("[Zexprf.Z3.derive]: output = " ^ (TBool.string_of_triary_bool res)) in
			(* currently, we do not parse the proof from Z3 *)
				(res, [])
end

(*module Reduce = struct
	
end*)

end

module Logic = struct
	
	module Skolemize = struct
		
		(**
		 * Introduce additional Skolem functions and constants to remove existential quantifiers
		 *)
		let skolemize st t =
			(st, t)
		
		
			
	end
	
	module Rewrite = struct
		(**
		 * Normalize term algebraically
		 *  - flatten associative operators
		 *  - make all quantified variables different
		 *  - re-order and simplify sub-terms
		 * TODO implement
		 *)
		let rec normalize t = match t with
			| Num _ | Var _ -> t
			| FunApp (f, x) -> 
				let nx = List.map normalize x in
				(match f with
					| And | Or ->
						let nx = List.map (fun y -> match y with
							| FunApp (f, x1) -> x1
							| _ -> [y]) nx in
						FunApp (f, (List.flatten nx))
					| _ -> t)

		
	end
	
	module Algebra = struct
		(**
		 * Simple algebraic equation solving facility
		 *)
		let solve_eq_constraints tl =
			tl
	end
	
	module Induction = struct
		
		let get_top_ind st t = match t with
			| FunApp (GFunc, fn::fa) -> begin
				try
					let s = Hashtbl.find st (name_of_var fn) in
					let rep = GList.mapi (fun i y -> ("$" ^ (string_of_int i), y)) fa in
						List.map (fun t -> subst rep t) s.induction
				with
					| Not_found -> [] end
			| _ -> []
			
		
		let get_induction_candidates st t =
			let vst = frv t in
			let fas = collect_fun_apps t in
			let ivals = List.map (get_top_ind st) fas in
			let ivals = List.flatten ivals in
			(* remove expression that contain quantified variables *)
			let ivals = List.filter (fun x -> GList.subset_eq eq_var (frv x) vst) ivals in
				ivals
				
		(* Give priority to the expressions in the consequence *)
		(*let get_induction_candidates st t =*)
				
		let make_induction_scheme st iv t =
			(*let _ = print_endline ("[make_induction_scheme]: " ^ (string_of_term_list tvars)) in*)
			(* base case *)
			let ivb = FunApp (Eq, [iv; Num 0]) in
			let fb = FunApp (Implies, [ivb; t]) in
			(* induction hypothesis *)
			let tvars = filter_defined_symbols st (frv t) in
			let nvars = List.map (fun x -> Var (sort_of_term x, "$" ^ (name_of_var x))) tvars in
			let stl = List.map2 (fun x y -> (name_of_var x, y)) tvars nvars in
			let tp = subst stl t in
			let hyp = FunApp (Lt, [(subst stl iv); iv]) in
			let ih = FunApp (Implies, [hyp; tp]) in
			let ih = FunApp (Forall, ih :: nvars) in
			let fi = FunApp (Implies, [ih; t]) in
				(fb, fi)
		
		let check_induction st t =
			let ivals = get_induction_candidates st t in
			let _ = print_endline ("[check_induction]: induction values { " ^ (string_of_term_list ivals) ^ " }") in
			match ivals with
				| [] -> print_endline "[check_induction]: no candidate found!"; TBool.Unknown
				| _ -> let iv = List.hd ivals in
					let fb, fi = make_induction_scheme st iv t in
					let _ = print_endline ("[check_induction]: base case " (*^ (string_of_term fb)*)) in
					match (check st fb) with
						| TBool.True ->
							let _ = print_endline ("[check_induction]: induction " (*^ (string_of_term fi)*)) in
							check st fi
						| _ -> TBool.Unknown

	end
	
	let check st t =
		fst (Zexprf.Z3.derive (t :: (get_all_axioms st)))		
	
	let verify_theorem st t =
		(*let _ = print_endline ("[verify_theorem]: " ^ (string_of_term t.thm)) in*)
		let validity = check st t.thm in
		let validity = match validity with
			| TBool.Unknown -> check_induction st t.thm
			| _ -> validity in
		{ t with proved = (validity = TBool.True) }
		(*let validity = match validity with
			| True -> print_endline "[verify_theorem]: derived"
			| False -> print_endline "[verify_theorem]: false"
			| Unknown -> 
				let _ = print_endline "[verify_theorem]: unknown -- try induction " in
				match (check_induction st t.thm) with
					| True -> print_endline "[verify_theorem]: valid"
					| _ -> print_endline "[verify_theorem]: unknown"*)
	
	(* INTERFACE TO OTHER MODULES *)
	
	let process_definitions (symtab, thms) =
		(*let _ = Hashtbl.iter (fun s si -> 
			print_endline ("symbol " ^ s);
			print_endline ("induction values : " ^ (String.concat "," (List.map string_of_term si.induction)))) symtab in*)
		let _ = List.map (verify_theorem symtab) thms in
			List.map (fun t -> "<b>Theorem:</b> \\(" ^ (latex_of_term t.thm) ^ "\\)<br />") thms

end

(* Program entry *)

let print_help_msg = ref false

let print_version = ref false

let usage = "zeta (source files)+"
	
let input_files = ref ([] : string list)

let add_source_file src =
	input_files := List.append !input_files [src]

let parse_file file_name = 
	let input_channel = open_in file_name in
	try
		(*print_endline ("Parsing " ^ file_name ^ " ...\n");*)
		let defs = Zparser.parse file_name (Stream.of_channel input_channel) in
		close_in input_channel;
		defs
	with End_of_file -> exit 0

let string_of_file fname =
	let chn = open_in fname in
	let len = in_channel_length chn in
	let str = String.make len ' ' in
	let _ = really_input chn str 0 len in
		(close_in chn; str)

(**
 * Command line options as in Arg.parse
 *)
let command_line_arg_speclist = [
	("-z3inp", Arg.Set Zexprf.Z3.print_z3_input, "Print Z3 input generated.");
	("-h", Arg.Set print_help_msg, "Print the help message.");
	("-v", Arg.Set print_version, "Print zeta version.")]
	
let main () =
	let _ = Arg.parse command_line_arg_speclist add_source_file usage in
	let _ = Z3.toggle_warning_messages false in
	let _ = print_endline ("Source files : {" ^ (String.concat ", " !input_files) ^ "}") in
	let defs = List.map parse_file !input_files in
	let output = List.map process_definitions defs in
	let output = List.flatten output in
	let html_template = Zutils.FileIO.string_of_file "template.html" in
	let outrexp = Str.regexp_string "$OUTPUT_CONTENT$" in
	let output = Str.global_replace outrexp (String.concat "" output) html_template in
	let chn = open_out "zeta.html" in
		output_string chn output
	
let _ = main ()