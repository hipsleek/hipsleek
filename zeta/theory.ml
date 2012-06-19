(**
 * A theory encapsulates all information
 * in the input file including: the defined
 * symbols, axioms and theorems that the
 * user wants to prove
 *
 * @author Vu An Hoa
 *)

open Domain
open Term
open TriaryLogic

type theory = {
		(* user defined symbols with axiomatization *)
		def_symbols : symbol list;
	
		(* additional axioms *)
		axioms : axiom list;
	
		(* theorems in the theory *)
		theorems : theorem list;
	}
	
and symbol = {
		symbol_name : string;
		symbol_id : int;
		symbol_domain : domain;
		symbol_hints : hint list;
	}
	
and hint =
	| Rewrite of term
	| Induction of term

and axiom = {
		(* name of the axiom for reference *)
		axiom_name : string;
		
		(* content of the axiom *)
		axiom_content : term;
		
		(* domain of the symbols occurred in the axiom *)
		axiom_symbol_domain : (int * domain) list;
	}

and theorem = {
		(* Name of the theorem for reference *)
		theorem_name : string;
	
		(* Theorem as parsed *)
		(*original_content : string;*)
		
		(* Normalized content of the theorem *)
		theorem_content : term;
		
		(* domain of variables *)
		theorem_symbol_domain : (int * domain) list;
		
		(* Indicate if the theorem is proved or disproved or unknown*)
		theorem_proved_status : triary_bool;
		
		(* Proof of the theorem, should it be provable by the system *)
		(* Proof is valid if the theorem_proved_status is Proved *)
		theorem_proof : Proof.proof_tree;
	}
	
let axiom_count = ref 0
	
let mkAxiom t = {
		axiom_name = "Axiom_1";
		axiom_content = t;
		axiom_symbol_domain = [];
	}
		
let theorem_count = ref 0

let mkThm t = {
		theorem_name = "Theorem_1";
		theorem_content = t;
		theorem_proved_status = Unknown;
		theorem_symbol_domain = [];
		theorem_proof = Proof.mkEmptyProofTree ();
	}

let symbol_count = ref 0

let mkSymbol s i = {
		symbol_name = s;
		symbol_id = i;
		symbol_domain = SWild 0;
		symbol_hints = [];
	}

(**
 * Batch transform all terms in a 
 * theory thry using a term transform
 * function f : term -> term.
 *)
let transform_all_terms f thry =
	{ thry with
		axioms = List.map (fun t ->
			{ t with 
				axiom_content = f t.axiom_content 
			}) thry.axioms;
		theorems = List.map (fun t ->
			{ t with 
				theorem_content = f t.theorem_content 
			}) thry.theorems; 
	}
