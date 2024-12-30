type t = private
  | Null
  | Var of Identifier.t
  | Intl of int
  | Floatl of float
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t

val null : t
val var : Identifier.t -> t

val intl : int -> t
val floatl : float -> t

val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t

(* TODO add strings, booleans, lists? *)

val to_sleek_expr : t -> Hipsleek_common.Ipure_D.exp
val of_sleek_expr : Hipsleek_common.Ipure_D.exp -> t
val of_sleek_cexpr : Hipsleek_common.Cpure.exp -> t
