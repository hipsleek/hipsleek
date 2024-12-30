open Hipsleek_common
(* This API currently does not expose some underlying features of the prover, including:
   - Variable permissions
   - Flow constraints
   - Structured specifications (for consequents)
*)

module Normal : sig
  type t
  (** Type to represent a metaformula. Currently, this contains a heap constraint and a pure logic constraint. *)

  val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
  val to_string : t -> string
  (** Output a string representation of this base formula. This is provided as a debugging aid;
      the format may change at any time. *)
  val to_sleek_formula : t -> Iformula.formula
  val of_sleek_formula : Iformula.formula -> t
  val of_sleek_cformula : Cformula.formula -> t
end

module Structured : sig
  type t
  (** Type to represent a metaformula with additional context to aid in proving. For more information, refer to
   the linked publication on structured specifications. *)
  val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
  val to_string : t -> string
  (** Output a string representation of this structured formula. This is provided as a debugging aid;
      the format may change at any time. *)
  val to_sleek_formula : t -> Iformula.struc_formula
  val of_sleek_formula : Iformula.struc_formula -> t
end

