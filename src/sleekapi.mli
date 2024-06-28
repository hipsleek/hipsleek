type pe                                 (* pure expressions *)
type pf                                 (* pure formulae *)
type dd                                 (* data declarations *)
type hf                                 (* heap formulae *)
type mf                                 (* meta formulae *)

type typ =
  | Void
  | Bool
  | Float
  | Int
  | Named of string

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

val var_pure_exp : string -> pe
(** [var_pure_exp s b] returns a variable with the name [s]. 
    Whether is the variable primed is determined by whether is there a ' char at the end of the variable name *)

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
val gte_pure_f : pe -> pe -> pf
val lt_pure_f  : pe -> pe -> pf
val lte_pure_f : pe -> pe -> pf
val eq_pure_f  : pe -> pe -> pf

val not_f      : pf -> pf
val and_f      : pf -> pf -> pf
val or_f       : pf -> pf -> pf
val implies_f  : pf -> pf -> pf
val iff_f      : pf -> pf -> pf

(* Heap formulae *)
val data_decl : string -> ((typ * string) list) -> unit
(** [data_decl s l] is used to declare a data structure named [s].
    [l] is a list of pairs of the type and name of each field of the data
    structure.
    Returns true if declaration was successful, false otherwise.
 *)

val predicate_decl : string -> unit
(** [predicate_decl s] is used to declare a predicate.
    [s] is a string defining the predicate in sleek syntax.
    Returns true if declaration was successful, false otherwise.
*)

val empty_heap_f : hf
val false_heap_f : hf
val true_heap_f : hf

val sep_conj_f : hf -> hf -> hf

val points_to_int_f : string -> int -> hf
(** [points_to_int_f s i] returns a heap formula denoting that a variable
    with the name [s] is pointing to the integer [i].
    The variable is considered primed if there is a ' at the end of [s]
*)

val points_to_f : string -> string -> pe list -> hf
(** [points_to_f s1 s2 l] returns a heap formula denoting that a variable
    with the name [s1] is pointing to a [s2] heap node. [l] is the list of
    data fields of the heap node. 
    The variable is considered primed if there is a ' at the end of [s]
*)

(* val sep_conj_f : hf -> hf -> hf *)

val ante_f : hf -> pf -> mf list
val conseq_f : hf -> pf -> mf
val entail : mf list -> mf -> bool

val ante_printer : mf list -> string
val conseq_printer : mf -> string

val init : unit -> unit
