(**
 * Module for external proof i.e.
 * checking validity by utilization
 * of existing SMT solver, CAS, etc.
 *
 * @author Vu An Hoa
 *)

open Zsort
open Zterm
open Zutils

(**
 * Enumeration of supported prover.
 *)
type prover =
	| Reduce
	| Z3

(**
 * Interface for external prover.
 *)
module type Exprf =
	sig
		
		(**
		 * Prove theorem G |- H where H 
		 * is the head of the input list
		 * and G is the rest of the input
		 * served as axiom/hypotheses.
		 * @return True/False/Unknown to
		 * indicate whether the external
		 * system can derive the theorem;
		 * together with the proof (if
		 * there is any).
		 *)
		val derive : term list -> TBool.triary_bool * term list
		
	end

(**
 * Module to interact with Z3 SMT solver.
 *)
module Z3 =
	struct
		
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
				let _, constr, _ = Z3.mk_tuple_sort ctx (Z3.mk_string_symbol ctx "smap") syms doms in
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
		
		(**
		 * Convert term to Z3 AST
		 *)
		let rec z3ast ctx t =
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

(**
 * An intelligent dispatcher that
 * send a formula to the external
 * solver (Z3, Reduce(Redlog), etc) 
 * based on the "nature" of the 
 * formula.
 *
 * TODO implement
 *)
module Intel =
	struct

		let select_prover st t = Z3
		
	end
	
(*let derive prv t = match prv with
	| Z3 -> Zexprf.Z3.derive t
	| Reduce -> failwith "[Zexprf.derive] : Reduce is currently unsupported."*)
