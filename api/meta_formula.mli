open Hipsleek_common

type antecedent
type consequent

(* This API currently does not expose some underlying features of the prover, including:
   - Variable permissions
   - Flow constraints
   - Structured specifications (for consequents)
*)

type t
(** Type to represent a metaformula. Currently, this contains a heap constraint and a pure logic constraint. *)

val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
val printer : t -> string
val to_sleek_formula : t -> Sleekcommons.meta_formula
val of_sleek_formula : Sleekcommons.meta_formula -> t

module Consequent : sig (* TODO give this a more descriptive name that refers to structured specifications somehow *)
  type t
  val of_antecedent : antecedent -> consequent
  val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
  val printer : t -> string
  val to_sleek_formula : t -> Sleekcommons.meta_formula
  val of_sleek_formula : Sleekcommons.meta_formula -> t
end

