(* Slicing Module *)

module type FORMULA_TYPE = 
sig
  type t
end;;

module type SLICE_TYPE =
sig
  type t
  val sameSlice: t -> t -> bool
  val isRelevant: t -> t -> bool
end;;

(* Slicing Framework *)
module SlicingFramework = 
  functor (Formula: FORMULA_TYPE) -> 
  functor (Slice: SLICE_TYPE) -> 
sig
  open Slice
  open Formula
  type s = Slice.t
  type f = Formula.t
  val split: f -> s list   
  val getCtr: s -> s list -> s list
end;;

(* Automatic Slicing *)
module AutoSlicing = 
struct

end;;

(* Annotated Slicing *)
module AnnoSlicing = 
struct
end;;

