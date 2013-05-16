(*
  (guard,expr)
  add_guard :: pexpr -> pc -> pc
  rename    :: rename -> pc -> pc
  subs      :: subs -> pc -> pc
  drop_guard :: pc -> expr

*)
open Cpure
type ren = (spec_var * spec_var) list

module type ExprType = sig
  type t
  val and_op : t -> t -> t
  val rename : ren -> t -> t
  val string_of : t -> string
end;;

module Path = 
 functor (Guard:ExprType, Expr: ExprType) ->
   struct
     type t = (Guard.t, Expr.t) 
     let add_guard (x:Guard.t) ((g,e):t) =
       (Guard.and_op(x,g), e)
     let drop_guard ((g,e):t) = e
     let rename (r:ren) ((g,e):t) = (Guard.rename r g, Expr.rename r e)
     let string_of ((g,e):t) 
           = "PathCond("^(Guard.string_of g)^","^(Expr.string_of e)^")"
end;;
