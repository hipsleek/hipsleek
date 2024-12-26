type t = private
  | Empty
  | PointsTo of Identifier.t * string * Pure_expression.t list
  | SepConj of t * t

(* Heap formulae *)
val emp : t

val sep : t -> t -> t

val points_to_int : Identifier.t -> int -> t
(** [points_to_int s i] returns a heap formula denoting that a variable
    with the name [s] is pointing to the integer [i]. This is an alias for
    [points_to s "int_ptr" (intl i)], where the [int_ptr] view is a data type
    pointing to a single int.
  *)

val points_to : Identifier.t -> string -> Pure_expression.t list -> t
(** [points_to s1 s2 l] returns a heap formula denoting that a variable
    with the name [s1] is pointing to a [s2] heap node. [l] is the list of
    data fields of the heap node, or the parameters of the predicate.
*)

val to_sleek_formula : t -> Hipsleek_common.Iformula.h_formula
val of_sleek_formula : Hipsleek_common.Iformula.h_formula -> t
