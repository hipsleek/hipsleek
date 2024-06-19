type pe                                 (* pure expressions *)
type pf                                 (* pure formulae *)
type hf                                 (* heap formulae *)
type mf                                 (* meta formulae *)

(* Pure formulae *)
val null_pure_exp : unit -> pe
val var_pure_exp : string -> bool -> pe
val int_pure_exp : int -> pe
val add_pure_exp : pe -> pe -> pe

val bool_pure_f : bool -> pf
val gt_pure_f : pe -> pe -> pf
val eq_pure_f : pe -> pe -> pf

val and_f : pf -> pf -> pf
val or_f : pf -> pf -> pf
(* Heap formulae *)
val empty_heap_f : unit -> hf

val ante_f : hf -> pf -> mf list
val conseq_f : hf -> pf -> mf

val entail : mf list -> mf -> bool

val ante_printer : mf list -> string
val conseq_printer : mf -> string

