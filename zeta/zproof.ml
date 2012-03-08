(**
 * Proof module to record the
 * proof steps for export and
 * proof checking.
 * @author Vu An Hoa
 *)

open Zterm

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