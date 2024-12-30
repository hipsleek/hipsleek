type bin_predicate_kind = private
  | GreaterThan
  | GreaterThanEq
  | LessThan
  | LessThanEq
  | Equal

type t = private
  | Constant of bool
  | BinPredicate of bin_predicate_kind * Pure_expression.t * Pure_expression.t
  | Not of t
  | And of t * t
  | Or of t * t

val true_f : t
(** [true_f] is a true pure formula *)

val false_f : t
(** [false_f] is a false pure formula *)

val gt  : Pure_expression.t -> Pure_expression.t -> t
val gte : Pure_expression.t -> Pure_expression.t -> t
val lt  : Pure_expression.t -> Pure_expression.t -> t
val lte : Pure_expression.t -> Pure_expression.t -> t
val eq  : Pure_expression.t -> Pure_expression.t -> t

val not_f      : t -> t
val and_f      : t -> t -> t
val or_f      : t -> t -> t
val implies  : t -> t -> t
val iff      : t -> t -> t

val to_sleek_formula : t -> Hipsleek_common.Ipure_D.formula
(** Convert a formula to its internal SLEEK representation. *)

val of_sleek_formula : Hipsleek_common.Ipure_D.formula -> t
(** Convert a SLEEK formula to the API representation. *)

val of_sleek_cformula : Hipsleek_common.Cpure.formula -> t
