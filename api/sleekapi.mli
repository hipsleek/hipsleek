type pe                                 (* pure expressions *)
type pf                                 (* pure formulae *)
type dd                                 (* data declarations *)
type hf                                 (* heap formulae *)
type mf                                 (* meta formulae *)
type lfe                                (* list of failesc_context *)
type sf                                 (* struc formulae *)

type typ =
  | Void
  | Bool
  | Float
  | Int
  | Named of string

type param_modifier = 
  | NoMod
  | RefMod
  | CopyMod

type param = {
  param_type : typ;
  param_name : string;
  param_mod : param_modifier;
}

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

val top_level_decl : string -> unit
(** [top_level_decl s] is used to declare a data, predicate or lemma.
    [s] is a string defining the data, predicate or lemma in Sleek syntax.
    Returns true if declaration was successful, false otherwise.
*)

val data_decl_str : string -> unit
(** [data_decl_str s] is used to declare a data.
    [s] is a string defining the data.
    Returns true if declaration was successful, false otherwise.
*)


val predicate_decl : string -> unit
(** [predicate_decl s] is used to declare a predicate.
    [s] is a string defining the predicate in Sleek syntax.
    Returns true if declaration was successful, false otherwise.
*)

val lemma_decl : string -> unit
(** [lemma_decl s] is used to declare a lemma.
    [s] is a string defining the lemma in Sleek syntax.
*)

val spec_decl : string -> string -> param list -> sf 
(** [spec_decl s1 s2] is used to construct a formula from the specification
    [s2] of function [s1].
    [s1] is the function's name.
    [s2] is the specification of the function in Hip syntax.
    e.g. "requires true ensures true;"
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

val ante_f : hf -> pf -> mf
val conseq_f : hf -> pf -> mf
val entail : mf -> mf -> bool

val ante_printer : mf -> string
val conseq_printer : mf -> string

val init : unit -> unit
(** [init ()] initializes the api. This include processing the prelude file
    of the api which contains some primitive function and data declarations.
*)

val init_ctx : sf -> param list -> lfe
(** [init_ctx specs] returns a pair of context wrapping the pre-condition in
    [specs] and the post-condition in [specs].
 *)

(* - Normalize specs? (check check_pre_post_orig) *)
val check_pre_post : lfe -> sf -> bool -> param list -> string list -> lfe option
(** [check_pre_post ctx specs] checks whether the current context [ctx] entails 
    the pre-condition in [specs].
    If it does, then it will return Some poststate which is the composition
    of the residual heap state from proving that [ctx] entails the pre-condition
    in [specs] and the post condition in [specs].
    Otherwise, it will return None.
*)

val check_entail_post : lfe -> sf -> param list -> bool
(** [check_entail_post ctx specs] checks whether the current context [ctx] entails
    the post-condition in [specs].
    If it does, then it will return Some poststate which is the residual heap state
    from proving that [ctx] entails the post-condition in [specs].
    Otherwise, it will return None.
*)

val disj_of_ctx : lfe -> lfe -> lfe
(** [disj_of_ctx ctx1 ctx2] returns a context which is the disjunction of two
    contexts, [ctx1] and [ctx2].
*)

val add_cond_to_ctx : lfe -> string -> bool -> lfe
(** [add_cond_to_ctx ctx ident b] returns a context which is the result of adding
    the condition that the variable with the name [ident] has value [b] to the
    context [ctx].
*)

val upd_result_with_var : lfe -> typ -> string -> lfe
(** [upd_result_with_var ctx t ident] returns a context which is the result of
    updating context [ctx] with the condition that the variable with the name "res"
    is equal to the variable with the name [ident] and the type [t].
*)

val upd_result_with_int : lfe -> int -> lfe
(** [upd_result_with_int ctx i] returns a context which is the result of updating
    context [ctx] with the condition that the variable with the name "res" is equal
    to the integer [i].
*)

val upd_result_with_bool : lfe -> bool -> lfe
(** [upd_result_with_bool ctx b] returns a context which is the result of updating
    context [ctx] with the condition that the variable with the name "res" is equal
    to the boolean [b].
*)

val add_assign_to_ctx : lfe -> typ -> string -> lfe
(** [add_assign_to_ctx ctx t ident] returns a context which is the result of assigning
    the value of "res" to the variable with the name [ident] and the type [t] in the
    context [ctx].
*)
