type pe                                 (* pure expressions *)
type pf                                 (* pure formulae *)
type hf                                 (* heap formulae *)
type mf                                 (* meta formulae *)

(* Relevant files:
  - ipure_D.ml (formula)
  - iformula.ml (struc_formula)
  - sleekcommons.ml (meta_formula)
  - sleekengine.ml (process_entail_check)
*)

(* meta formulae are formulae contains both heap formulae and pure formulae *)

(* Pure formulae *)

val null_pure_exp : pe
(** [null_pure_exp] is an expresion that represents a [null]
    value at program level *)

val var_pure_exp : string -> bool -> pe
(** [var_pure_exp s b] returns a variable with the name [s]. [b] is a boolean
    indicating whether this variable is a prime variable, i.e. the variable is
    the most recent (updated) value *)

val int_pure_exp : int -> pe
(** [int_pure_exp i] returns a expression with the value of the integer [i] *)

val float_pure_exp : float -> pe
(** [float_pure_exp i] returns a expression with the value of the float [i] *)

val add_pure_exp : pe -> pe -> pe
val sub_pure_exp : pe -> pe -> pe
val mul_pure_exp : pe -> pe -> pe
val div_pure_exp : pe -> pe -> pe

val true_f : pf
(** [true_f] is a true pure formula *)

val false_f : pf
(** [false_f] is a false pure formula *)

val gt_pure_f  : pe -> pe -> pf
val eq_pure_f  : pe -> pe -> pf
val lt_pure_f  : pe -> pe -> pf
val lte_pure_f : pe -> pe -> pf
val eq_pure_f  : pe -> pe -> pf

val not_f      : pf -> pf
val and_f.     : pf -> pf -> pf
val or_f       : pf -> pf -> pf
val implies_f  : pf -> pf -> pf
val iff_f      : pf -> pf -> pf

(* Heap formulae *)
val empty_heap_f : hf

(* val sep_conj_f : hf -> hf -> hf *)
(* val points_to_f : unit *)
(* TODO: figure out the type of this function *)

val ante_f : hf -> pf -> mf list
(** why is the returned value a list here? *)

val conseq_f : hf -> pf -> mf
val entail : mf list -> mf -> bool
(* TODO: change this later *)

val ante_printer : mf list -> string
val conseq_printer : mf -> string
