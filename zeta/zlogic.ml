(**
 * Theorem proving facility.
 *
 * @author Vu An Hoa
 *)

open Zterm
open Zsort
open Zutils

(**
 * Record structure for symbols
 *)
type symbol = {
		name : string;
		symbol_sort : sort;    (* sort of this symbol *)
		axioms : term list;    (* list of defining axioms *)
		induction : term list; (* induction hints *)
	}
	
(**
 * Record structure for theorems
 *)
type theorem = {
		thm : term; (* content of theorem *)
		proved : bool; (* proved/unproved status *)
		(* TODO added user hints for theorem *)
	}
	
(**
 * Symbol database
 *)
type symbol_table = (string * symbol) list

let find_symbol st s =
	List.assoc s st

type axiom = {
		content : term;
		(* tactics, dependent symbols *)
	}

(**
 * System database
 *)
type context = {
		defined_symbol : string list;
		all_axioms : term list;
		theorems : term list;
		proved_theorems : term list;
	}

(* THEOREM PROVING *)

(*let assert_all_axioms ctx st =
	Hashtbl.iter (fun x y -> 
		let axms = y.axioms in
		(*let _ = List.map (fun a -> print_endline ("Add axiom " ^ (string_of_term a))) axms in*)
		let _ = List.map (fun a -> Z3.assert_cnstr ctx (z3ast ctx a)) axms in
			()) st*)

let get_all_axioms st =
	Hashtbl.fold (fun _ y axms -> List.append y.axioms axms) st []

(**
 * Introduce additional Skolem functions and constants to remove existential quantifiers
 *)
let skolemize st t =
	(st, t)
	
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

(**
 * Simple algebraic equation solving facility
 *)
let solve_eq_constraints tl =
	tl

let check st t =
	fst (Zexprf.Z3.derive (t :: (get_all_axioms st)))

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
