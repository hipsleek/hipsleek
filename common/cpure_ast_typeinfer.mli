(**
  A fully typed version of a subset of the Cpure AST.
  While the current AST does support some type inference, it only
  annotates SpecVars. The types in this module are useful when
  full type information is needed (e.g. when converting a Cpure
  formula into SMTLIB format.)
 *)
open Globals

type loc = VarGen.loc [@opaque]
and spec_var = Cpure.spec_var [@opaque]
and typ = Globals.typ [@opaque]
  (* | Prim of prim_type *)
(* The following is a replica of types that represent the AST of Cpure.formulas,
   with a type parameter to support annotations. We use this annotation to store
   inferred types.*)
and 'a exp =
  | Null of loc
  | Var of (spec_var * loc)
    (* 'a *)
  | IConst of (int * loc)
    (* int *)
  | FConst of (float * loc)
  | Add of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Subtract of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Mult of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Div of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Max of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  | Min of ('a exp_annot * 'a exp_annot * loc)
    (* number; forces arguments to both be number *)
  (* 'a list, forces arguments to be 'a *)
  | List of ('a exp_annot list * loc)
  | ListCons of ('a exp_annot * 'a exp_annot * loc) (* 'a -> 'a list -> 'a list *' *)
  | ListHead of ('a exp_annot * loc) (* 'a list -> 'a *)
  | ListTail of ('a exp_annot * loc) (* 'a list -> 'a list *)
  | ListLength of ('a exp_annot * loc) (* 'a list -> int *)
  | ListAppend of ('a exp_annot list * loc) (*'a list list -> 'a list? *)
  | ListReverse of ('a exp_annot * loc) (* 'a list -> 'a list *)
  (* | StrConst of (string * loc) *)
  (* | StrAppend of ('a exp_annot list * loc) *)
  | ArrayAt of (spec_var * ('a exp_annot list) * loc)      (* An Hoa : array access *)
  | Func of (spec_var * ('a exp_annot list) * loc) (* 'a -> 'b, forces body to be 'b and forces any arguments applied to be 'a *)
  (* Template 'a exp_annot *)
  | Template of 'a template
  and 'a template = {
    (* a + bx + cy + dz *)
    templ_id: spec_var;
    templ_args: 'a exp_annot list; (*    [x, y, z] *)
    templ_unks: 'a exp_annot list; (* [a, b, c, d] *)
    templ_body: 'a exp_annot option;
    templ_pos: loc;
  }
and 'a exp_annot = ('a exp * 'a)

(** While p_formulas and formulas can be all annotated as having type Bool, we allow annotations
    on them for completeness. *)
and 'a p_formula =
  | BConst of (bool * loc)
  | BVar of (spec_var * loc)
  | Lt of ('a exp_annot * 'a exp_annot * loc)
  | Lte of ('a exp_annot * 'a exp_annot * loc)
  | Gt of ('a exp_annot * 'a exp_annot * loc)
  | Gte of ('a exp_annot * 'a exp_annot * loc)
  | Eq of ('a exp_annot * 'a exp_annot * loc) (* these two could be arithmetic or pointer or bag or list *)
  | Neq of ('a exp_annot * 'a exp_annot * loc)
  | EqMax of ('a exp_annot * 'a exp_annot * 'a exp_annot * loc) (* first is max of second and third *)
  | EqMin of ('a exp_annot * 'a exp_annot * 'a exp_annot * loc) (* first is min of second and third *)
  (* bag formulas *)
  | BagIn of (spec_var * 'a exp_annot * loc)
  | BagNotIn of (spec_var * 'a exp_annot * loc)
  | BagSub of ('a exp_annot * 'a exp_annot * loc)
  | BagMin of (spec_var * spec_var * loc)
  | BagMax of (spec_var * spec_var * loc)

  | ListIn of ('a exp_annot * 'a exp_annot * loc)
  | ListNotIn of ('a exp_annot * 'a exp_annot * loc)
  | ListAllN of ('a exp_annot * 'a exp_annot * loc)
  | ListPerm of ('a exp_annot * 'a exp_annot * loc)
  | RelForm of (spec_var * ('a exp_annot list) * loc)
  | ImmRel of ('a p_formula_annot * 'a imm_ann * loc) (* RelForm * cond * pos *)
  and 'a imm_ann =
    | PostImm of 'a p_formula_annot  (* unknown precondition, need to be inferred *)
    | PreImm of 'a p_formula_annot (* unknown postcondition, need to be inferred *)
  and 'a p_formula_annot = ('a p_formula * 'a)
  and formula_label = int * string
  and 'a formula =
    | BForm of ('a b_formula_annot * (formula_label option))
    (* | Pure_Baga of (spec_var list) *)
    (* ADDR[a,b] <==> a>0 & b>0 > a!=b *)
    (* | BagaF of (spec_var list * 'a formula_annot) *)
    | And of ('a formula_annot * 'a formula_annot * loc)
    | Or of ('a formula_annot * 'a formula_annot * (formula_label option) * loc)
    | Not of ('a formula_annot * (formula_label option) * loc)
    | Forall of (spec_var * 'a formula_annot * (formula_label option) * loc)
    | Exists of (spec_var * 'a formula_annot * (formula_label option) * loc)

  (** This type is part of the untyped AST's own annotations. For the annotated b_formula, use b_formula_annot. *)
  and 'a bf_annot = (bool * int * ('a exp_annot list))
  and 'a b_formula = ('a p_formula_annot * ('a bf_annot option))
  and 'a b_formula_annot = ('a b_formula * 'a)
  and 'a formula_annot = ('a formula * 'a)

(** Useful for converting a list of results from type checking into a single Option. *)
val lift_option_from_list : 'a option list -> 'a list option

(** Convert a Cpure AST into one with complete types. Raises Invalid_argument
    upon typecheck failure. *)
val infer_cpure_types : Cpure.formula -> typ formula_annot
