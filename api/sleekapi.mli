type pe                                 (* pure expressions *)
type pf                                 (* pure formulae *)
type dd                                 (* data declarations *)
type hf                                 (* heap formulae *)
type mf                                 (* meta formulae *)
type lfe                                (* list of failesc_context *)
type sf                                 (* struc formulae *)

(* Relevant files:
  - ipure_D.ml (formula)
  - iformula.ml (struc_formula)
  - sleekcommons.ml (meta_formula)
  - sleekengine.ml (process_entail_check)
*)

(* meta formulae are formulae contains both heap formulae and pure formulae *)

type data
type predicate
type lemma
type top_level_decl =
  | Data of data
  | Pred of predicate
  | Lemma of lemma

type typ =
  | Void
  | Bool
  | Float
  | Int
  | Null
  | Named of string

type param_modifier =
  | NoMod (* Pass by value *)
  | RefMod (* Pass by ref (names) *)
  | CopyMod (* copy entire structure *)

type param = {
  param_type : typ;
  param_name : string;
  param_mod : param_modifier;
}

val parse_decl : string -> top_level_decl
(** [parse_decl s] parses the string [s] which is a top level declaration
    (e.g. data, predicate, lemma) written in Sleek syntax.
*)

val data_decl_cons : string -> ((typ * string) list) -> unit
(** [data_decl_cons s l] is used to declare a data structure named [s].
    [l] is a list of pairs of the type and name of each field of the data
    structure.
 *)

val data_decl : data -> unit
(** [data_decl_str d] is used to declare the data [d]. The data can be referred to
    using the [Named] constructor and the name of the data afterwards.
    e.g (Named "node") : typ
*)

val predicate_decl : predicate -> unit
(** [predicate_decl p] is used to declare a predicate [p]. The predicate can be
    referred to in specifications and lemmas using the name of the predicate
    afterwards.
*)

val lemma_decl : lemma -> bool -> unit
(** [lemma_decl l prove_lemma] is used to declare a lemma [l]. The lemma can be
    used during entailment checking.
    (e.g. [check_pre_post] and [check_entail])
    [prove_lemma] denotes whether the lemma should be proven.
*)

module EntailmentProver :
  sig
    (* Pure formulae *)
    val null_pure_exp : pe
    (** [null_pure_exp] is an expresion that represents a [null]
        value at program level *)

    val var_pure_exp : string -> pe
    (** [var_pure_exp s b] returns a variable with the name [s].
        Whether is the variable primed is determined by whether is there a ' char at
        the end of the variable name *)

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
  end

module ForwardVerifier :
  sig
    val init : string list -> unit
    (** [init files_names] initializes the api. This includes parsing the ss files in
        [files_names].
        Data, predicate, lemma declarations and function definitions inside of these
        ss files will be processed and they can be referred to by name afterwards.
        (e.g. in check_pre_post_str)
    *)

    (* Do note that some function names cause [spec_decl] to fail silently.
       (e.g. function names with "$" symbol, like "add___$")
       If [spec_decl] is not behaving as expected, do try printing the specification
       formula returned from [spec_decl] using [string_of_sf] and manually inspect it.
    *)
    val spec_decl : string -> string -> param list -> typ -> bool -> sf
    (** [spec_decl s1 s2 params t is_rec] is used to construct a specification formula
        from a function specification containing pre and post-conditions.
        [s1] is the function's name.
        [s2] is the function specification in Hip syntax.
        e.g. "requires true ensures true;"
        [params] is the list of parameters of the function.
        [t] is the return type of the function.
        [is_rec] denotes whether the function is recursive.
    *)

    val init_ctx : sf -> lfe
    (** [init_ctx specs] returns a context wrapping the pre-condition in [specs].
    *)

    val check_pre_post : lfe -> sf -> string list -> lfe option
    (** [check_pre_post ctx specs args] checks whether the context [ctx] entails the
        pre-condition in the specification [specs].
        If it does, then it will return Some poststate which is the composition of the
        residual heap state from the entailment checking and the post condition in the
        specification [specs].
        Otherwise, it will return None.
        [args] is the list of arguments to the function with the specification [specs].
    *)

    val check_pre_post_str : lfe -> string -> string list -> lfe option
    (** [check_pre_post_str ctx f args] checks whether the context [ctx] entails the
        pre-condition in the specification of the function [f].
        If it does, then it will return Some poststate which is the composition of the
        residual heap state from the entailment checking and the post condition in the
        specification of the function [f].
        Otherwise, it will return None.
        [args] is the list of arguments to the function [f].
    *)

    val check_entail_post : lfe -> sf -> bool
    (** [check_entail_post ctx specs] checks whether the current context [ctx] entails
        the post-condition in the specification [specs].
        If it does, then it will return Some poststate which is the residual heap state
        from proving that [ctx] entails the post-condition in the specification [specs].
        Otherwise, it will return None.
    *)

    val disj_of_ctx : lfe -> lfe -> lfe
    (** [disj_of_ctx ctx1 ctx2] returns a context which is the disjunction of two
        contexts, [ctx1] and [ctx2].
    *)

    val add_cond_to_ctx : lfe -> string -> bool -> lfe
    (** [add_cond_to_ctx ctx ident b] returns a context which is the result of adding
        the condition that the variable [ident] has value [b] to the context [ctx].
    *)

    val upd_result_with_var : lfe -> typ -> string -> lfe
    (** [upd_result_with_var ctx t ident] returns a context which is the result of
        updating context [ctx] with the condition that the variable "res" is equal to
        the variable [ident] of type [t].
    *)

    val upd_result_with_int : lfe -> int -> lfe
    (** [upd_result_with_int ctx i] returns a context which is the result of updating
        context [ctx] with the condition that the variable "res" is equal to the integer
        [i].
    *)

    val upd_result_with_bool : lfe -> bool -> lfe
    (** [upd_result_with_bool ctx b] returns a context which is the result of updating
        context [ctx] with the condition that the variable "res" is equal to the
        boolean [b].
    *)

    val upd_result_with_null : lfe -> lfe
    (** [upd_result_with_null ctx] returns a context which is the result of updating
        context [ctx] with the condition that the variables "res" is equal to "null".
    *)

    val add_assign_to_ctx : lfe -> typ -> string -> lfe
    (** [add_assign_to_ctx ctx t ident] returns a context which is the result of
        assigning the value of "res" to the variable [ident] and the type [t] in the
        context [ctx].
    *)

    val data_field_read : lfe -> typ -> string -> string -> lfe
    (** [data_field_read ctx t ident f] returns a context which is the result of
        updating context [ctx] with the condition that the variable "res" is equal to
        the field [f] of the variable [ident] of type [t].
    *)

    val data_field_update : lfe -> typ -> string -> string -> string -> lfe
    (** [data_field_update ctx t ident f rhs] returns a context which is the result of
        assigning the value of the variable [rhs] to the field [f] of the variable
        [ident] of type [t] in the context [ctx].
    *)

    val add_heap_node_to_ctx : lfe -> typ -> string list -> lfe
    (** [add_heap_node_to_ctx ctx t lvars] constructs a new heap node of type [t] with
        fields [lvars] and returns a context which is the result of adding the new heap
        node to the context [ctx].
    *)

    val string_of_sf : sf -> string
    val string_of_lfe : lfe -> string
  end

