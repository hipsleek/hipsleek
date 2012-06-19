(**
 * Proof object
 *
 * @author Vu An Hoa
 *)

open Term
open Tree
	
(*type proof_step =
	| HYP 
		(* trivial as being hypothesis *)
	| RW of term * term
		(* rewrite *)
	| IND of term * proof * proof
		(* induction on a term; *)
		(* proof for base case and *)
		(* inductive case *)
	| MP of proof * proof
		(* application of Modus Ponen rule *)
		(* {p, p -> q} |- q *)
		
and proof = proof_step list

let mkEmptyProof () = []
*)

(**
 * Logical inference rule, function like
 * Coq's tactics.
 *)
type infer_rule = 
	| Hyp (* hypothesis *)
	| Rewrite (* rewrite rule, with two parameters [lhs; rhs] such that lhs = rhs or rhs = lhs is in hypotheses *)
	| Induction (* induction on a term, one parameter [N] indicating the term to do induction on *)
	| ModusPonens (* add b from [a, a->b] to hypothesis *)
	| LeapOfFaith (* by external system like Z3 *)

(**
 * Data type for a node in the proof tree
 *)
type proof_node = {
		(* hypotheses (including axioms and established theorems) *)
		context : term list;
		
		(* map symbols to their types *)
		symbol_domain : (int * Domain.domain) list;
		
		(* goal at the root node *)
		goal : term;
		
		(* inference rule to apply *)
		rule : infer_rule;
		
		(* parameters for rule                    *)
		(* for example, value to do induction on, *)
		(* equation to do rewrite, etc.           *)
		params : proof_node_param;
	}
	
and proof_node_param =
	| TermParam of term
	| ListParam of proof_node_param list

and proof_tree = proof_node tree

let mkEmptyProofTree () : proof_tree = 
	EmptyTree