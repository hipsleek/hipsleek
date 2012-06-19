(**
 * This module implements all the logic of
 * the theorem prover in the form of goal
 * rewriting. We have a collection of 
 * rewriters which transform a term (formula)
 * into equivalent forms. For examples,
 * a normalizer rewrites A -> B to ~A \/ B;
 * an inductive rewriter converts 
 *
 *      forall n >= 0 : F(n) 
 * 
 * (where n is of type int) into
 * 
 *   F(0) /\ 
 *    (forall m < n : F(m)) -> F(n).
 *
 * The common signature of a rewriter is
 *
 *     term -> term * rewrite_log list
 *
 * to transform input term to target term
 * via a list indicating reason.
 *
 * @author Vu An Hoa
 *)

open Term
	
open Theory

(*type rewrite_reason =
	| Arithmetic (* arithmetical/algebraic rewrite*)
	| Tautology (* logical tautology *)
	(* | Definition *)
	| Induction of term

type rewrite = { 
		origin : term;
		target : term;
		reason : rewrite_reason;
	}*)

module Rewrite = struct
	
	(**
	 * Convert all inequality L < R and L <= R
	 * into 0 < R - L and 0 <= R - L
	 *)
	let rec normalize_inequality t = match t with
		| Top 
		| Bot 
		| Num _ -> t
		| Fx (f, x) -> match f with
			(*| Eq*)
			| Le 
			| Lt ->
				let lhs = List.nth x 0 in
				let rhs = List.nth x 1 in 
				let rsubl = Fx (Sub, [rhs; lhs]) in
					Fx (f, [Num 0; rsubl])
			| _ -> 
				Fx (f, List.map normalize_inequality x)
	
	(**
	 * Replace non-commutative (subtract and implication)
	 * operations by commutative ones.
	 *)
	let rec replace_uncomm t = match t with
		| Top 
		| Bot 
		| Num _ -> t
		| Fx (f, x) ->
			let x = List.map replace_uncomm x in
			match f with
				| Sub ->
					let a = List.nth x 0 in
						if (List.length x = 1) then
							(* unary minus case *)
							mkBFx Mul (mkNum (-1)) a
						else
							let b = List.nth x 1 in
								mkBFx Add a (mkBFx Mul (mkNum (-1)) b)
				| Implies ->
					let a = List.nth x 0 in
					let b = List.nth x 1 in
						mkBFx Or (mkUFx Neg a) b
				| Iff ->
					let a = List.nth x 0 in
					let b = List.nth x 1 in
					let aib = mkBFx Or (mkUFx Neg a) b in
					let bia = mkBFx Or (mkUFx Neg b) a in
						mkBFx And aib bia
				| _ -> mkFx f x

	module StringPrinter = Printing.Printer(Printing.StringBasePrinter)
	
	let print_inp_out s f t =
		let _ = print_endline (s ^ " input = " ^ (StringPrinter.print_term t)) in
		let r = f t in
		let _ = print_endline (s ^ "output = " ^ (StringPrinter.print_term r)) in
			r
	
(*		let replace_uncomm t =                           *)
(*			print_inp_out "replace_uncomm" replace_uncomm t*)
(*			let _ = print_endline ("input = " ^ (StringPrinter.print_term t)) in *)
(*			let t = replace_uncomm t in                                          *)
(*			let _ = print_endline ("output = " ^ (StringPrinter.print_term t)) in*)
(*				t                                                                  *)
	
	(**
	 * Collapse associative operations like AND, OR, +, * using associativity
	 *)
	let rec collapse_assoc t = match t with
		| Top 
		| Bot 
		| Num _ (* | Var _ *) -> t
		| Fx (f, x) -> 
			let x = List.map collapse_assoc x in
			match f with
				| And 
				| Or 
				| Add 
				| Mul ->
					let x = List.map (fun y -> match y with
						| Fx (f1, z) -> (*(match (f, f1) with
							| (And,And) 
							| (Or,Or)
							| (Add,Add) 
							| (Mul,Mul) -> z
							| _ -> [y])*)
							if (f1 = f) then 
								z 
							else
								[y]
						| _ -> [y]) x in
					mkFx f (List.flatten x)
				| _ -> mkFx f x

(*		let collapse_assoc t =                           *)
(*			print_inp_out "collapse_assoc" collapse_assoc t*)

	let rec compare_term t1 t2 = match t1 with
		| Top -> if t2 = Top then 0 else -1
		| Bot -> if t2 = Top then 1 else
			if t2 = Bot then 0 else -1
		| Num i -> (match t2 with
			| Num j -> i - j
			| _ -> -1)
		| Fx (f1, x1) -> match t2 with
			| Top | Bot | Num _ -> 1
			| Fx (f2, x2) -> 1
				

	(**
	 * Reorder sub-terms for all commutative functors.
	 *)
	let rec reorder_sub_terms t = match t with
		| Top 
		| Bot 
		| Num _ -> t
		| Fx (f, x) -> 
			let x = List.map reorder_sub_terms x in
			let x = List.sort compare_term x in
				Fx (f, x)

	(**
	 * Push negation toward the atomic.
	 *)
	let rec push_neg t = match t with
		| Top 
		| Bot 
		| Num _ -> t
		| Fx (f, x) -> match f with
			| Neg -> 
				let x = List.hd x in
				begin 
					match x with
					| Top -> Bot
					| Bot -> Top
					| Num _ -> failwith "Unexpected number in negation"
					| Fx (g, y) -> begin match g with
						| Neg -> (* double negation --> remove both *)
							let y = List.hd y in
								push_neg y
						| Exists | Forall ->
							let qv = List.tl y in
							let z = mkUFx Neg (List.hd y) in
							let z = push_neg z in
							let h = if (g = Forall) then 
									Exists
								else
									Forall in
								mkFx h (z :: qv)
						| And | Or -> 
							let z = List.map (mkUFx Neg) y in
							let z = List.map push_neg z in
							let h = if (g = And) then
									Or
								else 
									And in
								mkFx h z
						| Implies -> t (* TODO implement *)
						| Iff -> t (* TODO implement *)
						| _ -> t end
				end
			| _ -> 
				let x = List.map push_neg x in
					mkFx f x

	(**
	 * Simplify algebraic terms and equations
	 * making use of:
	 * (iii) unit element
	 *     0 + x = x + 0 = x
	 *     0 * x = x * 0 = 0
	 *     1 * x = x * 1 = x
	 * (iv) distributivity
	 *     c * x + d * x = (c + d) * x
	 *     
	 * TODO implement
	 *)
	let rec alg_simplify t = match t with
		| Top 
		| Bot 
		| Num _ -> t
		| Fx (f, x) -> 
			let x = List.map alg_simplify x in
			let x = match f with
					| Add -> List.filter (fun y -> not (y = Num 0)) x
					| Mul -> 
						let x = List.filter (fun y -> not (y = Num 1)) x in
						(try 
							List.find (fun y -> y = Num 0) x;
							[Num 0]
						with Not_found -> x)
					| _ -> x in
			match f with
				| Add -> (match x with
					| [] -> Num 0
					| [y] -> y
					| _ -> Fx (f, x))
				| Mul -> (match x with
					| [] -> Num 1
					| [Num 0] -> Num 0
					| [y] -> y
					| _ -> Fx (f, x))
				| _ -> Fx (f, x)
	
	(**
	 * Simplify algebraic equations
	 * 
	 * (i) integral domain property of Z
	 *     ab = 0 --> a = 0 \/ b = 0
	 * (ii) constant factorization
	 *     ab = n for numeral n --> 
	 *	   \/ {a = d & b = n / d : d divides n}
	 *
	 * TODO implement
	 *)
	let rec eqn_simplify t = match t with
		| _ -> t

	(*let rec logical_simplify t = match t with
		| _ -> t*)

	(**
	 * Normalize terms
	 * TODO implement
	 *)
	let rec normalize t =
		let t = replace_uncomm t in
		let t = collapse_assoc t in
		let t = push_neg t in
		let t = alg_simplify t in
			t
	
	(**
	 * General term rewriting rewriting
	 * TODO implement
	 *)
	let rec rewrite rs t = t

end

module PrenexNormalForm = struct
	
	let to_pnf t = match t with
		| Top
		| Bot
		| Num _ -> t
		| Fx (f, x) -> match f with
			| Exists -> t
			| Forall -> t
			| _ -> t
	
end
	
module Skolemize = struct
	
	(**
	 * Collect symbols and skolemize them.
	 * sc : list of universally quantified vars
	 * q  : boolean to indicate whether 
	 * we should take the dual quantifier
	 *
	 * @return the list of (i, [v]) to
	 * indicate that the variable i should
	 * be replaced by the Skolem function F[v]
	 * assume t has no -> and <->
	 *)
	let rec collect_skolem_function sc q t =
		match t with
			| Top
			| Bot
			| Num _ -> []
			| Fx (f, x) -> match f with
				| Exists ->
					let qv = List.map get_index (List.tl x) in
					let fml = List.hd x in
						if q then (* take dual --> forall --> add to current scope *)
							collect_skolem_function (List.append sc qv) q fml
						else (* add skolem function for all vars under this *)
							let r = collect_skolem_function sc q fml in
							let sk = List.map (fun x -> (x, sc)) qv in
								List.append sk r
				| Forall ->
					let qv = List.map get_index (List.tl x) in
					let fml = List.hd x in
						if q then (* skolemize if dual *)
							let r = collect_skolem_function sc q fml in
							let sk = List.map (fun x -> (x, sc)) qv in
								List.append sk r
						else (* no dual --> add new vars *)
							collect_skolem_function (List.append sc qv) q fml
				| And
				| Or ->
					let r = List.map (collect_skolem_function sc q) x in
						List.flatten r
				| Neg ->
					collect_skolem_function sc (not q) (List.hd x)
				| _ -> []

					
	(**
	 * Collect Skolem functions at the top level 
	 *)
	let collect_skolem_function t = 
		collect_skolem_function [] false t
	
	
	(**
	 * Helper function to remove all instances of 
	 * existential quantification in a formula
	 *)
	let rec remove_exists t = match t with
		| Top
		| Bot
		| Num _ -> t
		| Fx (f, x) -> match f with
			| Exists ->
				remove_exists (List.hd x)
			| _ ->
				let x = List.map remove_exists x in
					Fx (f, x)
	
	
	(**
	 * Introduce additional Skolem functions and 
	 * constants to remove existential quantifiers
	 *
	 * TODO implement
	 *)
	let skolemize c t =
		let sk = collect_skolem_function t in
		let sksts = GList.mapi (fun i (x, v) ->
			let ars = List.map mkVar v in
				(x, Fx (GF (c - i), ars))) sk in
		let rt = remove_exists t in
		let rt = subst sksts rt in
			(sksts, rt)
		
end

module DPLL = struct
	
	(**
	 * 
	 *)
	let rec apply_rule_one_literal t = match t with
		| _ -> t

	(**
	 * 
	 *)
	let rec apply_rule_affirmative_negative t = match t with
		| _ -> t

	(**
	 * 
	 *)
	let rec apply_atomic_elimination t = match t with
		| _ -> t
	
end

(*
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

*)

let preprocess_theorem thm =
	let t = thm.theorem_content in
	(*let t = Rewrite.normalize t in*)
	(*let _,t = Skolemize.skolemize (- 100) t in*)
	{
		thm with theorem_content = t;
	}
	
let prove_theorem thm =
	let t = thm.theorem_content in
		thm

let process_theory thry = {
	thry with
		theorems = List.map preprocess_theorem thry.theorems;
	}