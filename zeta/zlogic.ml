(**
 * Theorem proving facility.
 *
 * @author Vu An Hoa
 *)

open Zterm
open Zsort
open Zutils

type triary_bool =
	| True | False | Unknown

type symbol = {
		name : string;
		symbol_sort : sort;    (* sort of this symbol *)
		axioms : term list;    (* list of defining axioms *)
		induction : term list; (* induction hints *)
	}

type theorem = {
		thm : term; (* content of theorem *)
		proved : bool; (* proved/unproved status *)
		(* TODO added user hints for theorem *)
	}

(* THEOREM PROVING *)

let assert_all_axioms ctx st =
	Hashtbl.iter (fun x y -> 
		let axms = y.axioms in
		(*let _ = List.map (fun a -> print_endline ("Add axiom " ^ (string_of_term a))) axms in*)
		let _ = List.map (fun a -> Z3.assert_cnstr ctx (z3ast ctx a)) axms in
			()) st

(*let value_of_z3lbool b =
	match b with
		| Z3.L_FALSE -> False
		| Z3.L_TRUE -> True
		| Z3.L_UNDEF -> Unknown

let negate b = match b with
	| True -> False
	| False -> True
	| Unknown -> Unknown*)

let negate_lbool b =
	match b with
		| Z3.L_FALSE -> Z3.L_TRUE
		| Z3.L_TRUE -> Z3.L_FALSE
		| Z3.L_UNDEF -> Z3.L_UNDEF 
						
let check st t = 
	let _ = print_endline ("[check]: " ^ (string_of_term  t)) in
	let ctx = Z3.mk_context_x [|("SOFT_TIMEOUT", "5000")|] in
	(* assert constraints *)
	let _ = assert_all_axioms ctx st in
	let t = mkUnaryTerm Neg t in
	let _ = Z3.assert_cnstr ctx (z3ast ctx t) in
	(* check and return *)
	let res = Z3.check ctx in
	let _ = print_endline ("[check]: " ^ match res with
		| Z3.L_FALSE -> "ok"
		| Z3.L_TRUE -> "fail"
		| Z3.L_UNDEF -> "unknown") in
		res
	
let get_induction_candidates st t =
	let fas = collect_fun_apps t in
	let ivals = List.map (fun x ->
		let fn = get_functor_name x in
		let fa = get_fun_app_arg x in
		try
			let s = Hashtbl.find st fn in
			let rep = mapi (fun i y -> ("$" ^ (string_of_int i), y)) fa in
				List.map (fun t -> subst rep t) s.induction
		with
			| Not_found -> []) fas in
	List.flatten ivals

let make_universal st t =
	let vs = filter_defined_symbols st (frv t) in
	let vs = remove_dups_eq eq_var vs in
		if vs = [] then t
		else 
			FunApp (Forall, t :: vs)

let make_induction_scheme st iv t =
	let tvars = filter_defined_symbols st (frv t) in
	let _ = print_endline ("[make_induction_scheme]: " ^ (string_of_term_list tvars)) in
	(* prepare induction formula *)
	(*let sivar = Var (SInt, "!ind") in
	let sivarbind = FunApp (Eq, [sivar; iv]) in
	let f = FunApp (Implies, [sivarbind; t]) in*)
	(* base case *)
	(*let fb = subst [("!ind", Num 0)] f in*)
	let fb = FunApp (Implies, [FunApp (Eq, [iv; Num 0]); t]) in
	(* induction hypothesis *)
	let nvars = List.map (fun x -> Var (sort_of_term x, "$" ^ (name_of_var x))) tvars in
	let stl = List.map2 (fun x y -> (name_of_var x, y)) tvars nvars in
	let _ = print_endline "[make_induction_scheme]: checkpoint 1 " in
	let tp = subst stl t in
	let _ = print_endline "[make_induction_scheme]: checkpoint 2 " in
	let hyp = FunApp (Lt, [(subst stl iv); iv]) in
	let _ = print_endline "[make_induction_scheme]: checkpoint 3 " in
	let ih = FunApp (Implies, [hyp; tp]) in
	let ih = FunApp (Forall, ih :: nvars) in
	let fi = FunApp (Implies, [ih; t]) in
		(fb, fi)

let check_induction st t =
	let ivals = get_induction_candidates st t in
	let _ = print_endline ("[check_induction]: induction values { " ^ (string_of_term_list ivals) ^ " }") in
	match ivals with
		| [] -> print_endline "[check_induction]: no candidate found!"; Z3.L_UNDEF
		| _ -> let iv = List.hd ivals in
			let fb, fi = make_induction_scheme st iv t in
			let _ = print_endline ("[check_induction]: base case " (*^ (string_of_term fb)*)) in
			match (check st fb) with
				| Z3.L_FALSE ->
					let _ = print_endline ("[check_induction]: induction " (*^ (string_of_term fi)*)) in
					check st fi
				| _ -> Z3.L_UNDEF

let verify_theorem st t =
	let _ = print_endline ("[verify_theorem]: " ^ (string_of_term t.thm)) in
	match check st t.thm with
		| Z3.L_FALSE -> print_endline "[verify_theorem]: valid"
		| Z3.L_TRUE -> print_endline "[verify_theorem]: invalid"
		| Z3.L_UNDEF -> 
			let _ = print_endline "[verify_theorem]: unknown -- try induction " in
			match (check_induction st t.thm) with
				| Z3.L_FALSE -> print_endline "[verify_theorem]: valid"
				| _ -> print_endline "[verify_theorem]: unknown"

(* INTERFACE TO OTHER MODULES *)

let process_definitions (symtab, thms) =
	let _ = Hashtbl.iter (fun s si -> 
		print_endline ("symbol " ^ s);
		print_endline ("induction values : " ^ (String.concat "," (List.map string_of_term si.induction)))) symtab in
	let _ = List.map (verify_theorem symtab) thms in
		List.map (fun t -> "\\(" ^ (latex_of_term t.thm) ^ "\\)") thms