type variable
  and pure_expr = private
    | Null
    | Var of variable
    | Intl of int
    | Floatl of float
    | Add of pure_expr * pure_expr
    | Sub of pure_expr * pure_expr
    | Mul of pure_expr * pure_expr
    | Div of pure_expr * pure_expr
  and bin_predicate_kind = private
    | GreaterThan
    | GreaterThanEq
    | LessThan
    | LessThanEq
    | Equal
  and pure_formula = private
    | Constant of bool
    | BinPredicate of bin_predicate_kind * pure_expr * pure_expr
    | Not of pure_formula
    | And of pure_formula * pure_formula
    | Or of pure_formula * pure_formula
  and heap_formula = private
  | Empty
  | PointsTo of variable * string * pure_expr list
  | SepConj of heap_formula * heap_formula
  and meta_formula
  and structured_meta_formula

module Identifier : sig
  type t = variable
  val make : string -> t
  val anon : unit -> t
  val primed : string -> t

  val is_primed : t -> bool
  val is_anon : t -> bool
  val to_string : t -> string

  val to_sleek_ident : t -> string * Hipsleek_common.VarGen.primed
  val of_sleek_spec_var : Hipsleek_common.Cpure.spec_var -> t
end


module Pure_expression : sig
  type t = pure_expr

  val null : pure_expr
  val var : variable -> pure_expr
  val intl : int -> pure_expr
  val floatl : float -> pure_expr

  val add : pure_expr -> pure_expr -> pure_expr
  val sub : pure_expr -> pure_expr -> pure_expr
  val mul : pure_expr -> pure_expr -> pure_expr
  val div : pure_expr -> pure_expr -> pure_expr

  (* TODO add strings, booleans, lists? *)

  val to_sleek_expr : t -> Hipsleek_common.Ipure_D.exp
  val of_sleek_cexpr : Hipsleek_common.Cpure.exp -> t
end

module Pure_formula : sig
  type t = pure_formula
  val true_f : t
  (** [true_f] is a true pure formula *)

  val false_f : t
  (** [false_f] is a false pure formula *)

  val gt  : pure_expr -> pure_expr -> t
  val gte : pure_expr -> pure_expr -> t
  val lt  : pure_expr -> pure_expr -> t
  val lte : pure_expr -> pure_expr -> t
  val eq  : Pure_expression.t -> pure_expr -> t

  val not_f      : t -> t
  val and_f      : t -> t -> t
  val or_f      : t -> t -> t
  val implies  : t -> t -> t
  val iff      : t -> t -> t

val to_sleek_formula : t -> Hipsleek_common.Ipure_D.formula
val of_sleek_cformula : Hipsleek_common.Cpure.formula -> t
end

module Heap_formula : sig
  type t = heap_formula
  (* Heap formulae *)
  val emp : t

  val sep : t -> t -> t

  val points_to_int : variable -> int -> t
  (** [points_to_int_f s i] returns a heap formula denoting that a variable
      with the name [s] is pointing to the integer [i].
  *)

  val points_to : variable -> string -> pure_expr list -> t
  (** [points_to_struct s1 s2 l] returns a heap formula denoting that a variable
      with the name [s1] is pointing to a [s2] heap node. [l] is the list of
      data fields of the heap node.
  *)

  val to_sleek_formula : t -> Hipsleek_common.Iformula.h_formula
  val of_sleek_cformula : Hipsleek_common.Cformula.h_formula -> t
end

open Hipsleek_common


(* This API currently does not expose some underlying features of the prover, including:
   - Variable permissions
   - Flow constraints
   - Structured specifications (for consequents)
*)

module Meta_formula : sig
  type t = meta_formula
  (** Type to represent a metaformula. Currently, this contains a heap constraint and a pure logic constraint. *)
  val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
  val to_string : t -> string
  (** Output a string representation of this base formula. This is provided as a debugging aid;
      the format may change at any time. *)
  val to_sleek_formula : t -> Iformula.formula
  val of_sleek_cformula : Cformula.formula -> t
  val to_string : t -> string
end

module Structured : sig
  type t = structured_meta_formula
  (** Type to represent a metaformula with additional context to aid in proving. For more information, refer to
   the linked publication on structured specifications. *)
  val of_heap_and_pure : Heap_formula.t -> Pure_formula.t -> t
  (** Output a string representation of this structured formula. This is provided as a debugging aid;
      the format may change at any time. *)
  val to_sleek_formula : t -> Iformula.struc_formula
end
