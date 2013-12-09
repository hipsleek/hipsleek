type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

val plus : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

val psucc : positive -> positive

val pplus : positive -> positive -> positive

val pplus_carry : positive -> positive -> positive

val pdouble_minus_one : positive -> positive

type positive_mask =
| IsNul
| IsPos of positive
| IsNeg

val pdouble_plus_one_mask : positive_mask -> positive_mask

val pdouble_mask : positive_mask -> positive_mask

val pdouble_minus_two : positive -> positive_mask

val pminus_mask : positive -> positive -> positive_mask

val pminus_mask_carry : positive -> positive -> positive_mask

val pminus : positive -> positive -> positive

val pmult : positive -> positive -> positive

val pcompare : positive -> positive -> comparison -> comparison

type z =
| Z0
| Zpos of positive
| Zneg of positive

val zplus : z -> z -> z

val zopp : z -> z

val zminus : z -> z -> z

val zmult : z -> z -> z

val zcompare : z -> z -> comparison

val iter_pos : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1

val zpower_pos : z -> positive -> z

val zpower : z -> z -> z

module type SV = 
 sig 
  val is_eq : char list -> char list -> bool
 end

module InfSolver : 
 functor (Coq_sv:SV) ->
 sig 
  val coq_Z_of_bool : bool -> z
  
  val coq_Z_of_ascii : char -> z
  
  val coq_Z_of_0 : z
  
  val coq_Z_of_digit : char -> z option
  
  val coq_Z_of_string' : char list -> z -> z option
  
  val coq_Z_of_string : char list -> z option
  
  type 'const_type coq_ZExp =
  | ZExp_Var of char list
  | ZExp_Const of 'const_type
  | ZExp_Add of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Sub of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Mult of char list * 'const_type coq_ZExp
  
  val coq_ZExp_rect :
    (char list -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
    coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2 ->
    'a2) -> (char list -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp -> 'a2
  
  val coq_ZExp_rec :
    (char list -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
    coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2 ->
    'a2) -> (char list -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp -> 'a2
  
  type 'const_type coq_ZBF =
  | ZBF_Const of bool
  | ZBF_Lt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Lte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Eq of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Neq of 'const_type coq_ZExp * 'const_type coq_ZExp
  
  val coq_ZBF_rect :
    (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1
    coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2)
    -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2
  
  val coq_ZBF_rec :
    (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1
    coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2)
    -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2
  
  type 'const_type coq_ZF =
  | ZF_BF of 'const_type coq_ZBF
  | ZF_And of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Or of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Not of 'const_type coq_ZF
  | ZF_Forall_Fin of char list * 'const_type coq_ZF
  | ZF_Exists_Fin of char list * 'const_type coq_ZF
  | ZF_Forall of char list * 'const_type coq_ZF
  | ZF_Exists of char list * 'const_type coq_ZF
  
  val coq_ZF_rect :
    ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
    -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF -> 'a2
    -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1
    coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
    (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2
  
  val coq_ZF_rec :
    ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
    -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF -> 'a2
    -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1
    coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
    (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2
  
  type coq_ZE =
  | ZE_Fin of char list
  | ZE_Inf
  | ZE_NegInf
  
  val coq_ZE_rect : (char list -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val coq_ZE_rec : (char list -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val mkOr : coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val mkAnd : coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val subs_Exp :
    (char list, coq_ZE) prod -> coq_ZE coq_ZExp -> coq_ZE coq_ZExp
  
  val subs_BF : (char list, coq_ZE) prod -> coq_ZE coq_ZBF -> coq_ZE coq_ZBF
  
  val subs_F : (char list, coq_ZE) prod -> coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val convert_Exp : coq_ZE coq_ZExp -> z coq_ZExp
  
  val convert_BF : coq_ZE coq_ZBF -> z coq_ZBF
  
  val convert_ZE_to_Z : coq_ZE coq_ZF -> z coq_ZF
  
  val convert_Exp_string : coq_ZE coq_ZExp -> char list coq_ZExp
  
  val convert_BF_string : coq_ZE coq_ZBF -> char list coq_ZBF
  
  val convert_ZE_to_string : coq_ZE coq_ZF -> char list coq_ZF
  
  val num_of_quant : coq_ZE coq_ZF -> nat
  
  val elim_quant_metric : coq_ZE coq_ZF -> nat
  
  val elim_quant_F :
    (coq_ZE coq_ZF -> coq_ZE coq_ZF) -> coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val elim_quant_terminate : coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val elim_quant : coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  type coq_R_elim_quant =
  | R_elim_quant_0 of coq_ZE coq_ZF * char list * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant * coq_ZE coq_ZF * coq_R_elim_quant
     * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_1 of coq_ZE coq_ZF * char list * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant * coq_ZE coq_ZF * coq_R_elim_quant
     * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_2 of coq_ZE coq_ZF * coq_ZE coq_ZF * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_3 of coq_ZE coq_ZF * coq_ZE coq_ZF * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_4 of coq_ZE coq_ZF * coq_ZE coq_ZF * coq_ZE coq_ZF
     * coq_R_elim_quant
  | R_elim_quant_5 of coq_ZE coq_ZF * char list * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_6 of coq_ZE coq_ZF * char list * coq_ZE coq_ZF
     * coq_ZE coq_ZF * coq_R_elim_quant
  | R_elim_quant_7 of coq_ZE coq_ZF * coq_ZE coq_ZF
  
  val coq_R_elim_quant_rect :
    (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
    coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
    char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant ->
    'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE
    coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE
    coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1
    -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1)
    -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
    coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) ->
    (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> __ -> 'a1) -> coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1
  
  val coq_R_elim_quant_rec :
    (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
    coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
    char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant ->
    'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE
    coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE
    coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1
    -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1)
    -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
    coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
    coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) ->
    (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> __ -> 'a1) -> coq_ZE coq_ZF ->
    coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1
  
  val elim_quant_rect :
    (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1
    -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 ->
    'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE
    coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __
    -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ ->
    'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> __ -> 'a1) ->
    coq_ZE coq_ZF -> 'a1
  
  val elim_quant_rec :
    (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1
    -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 ->
    'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE
    coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
    __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __
    -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ ->
    'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> __ -> 'a1) ->
    coq_ZE coq_ZF -> 'a1
  
  val coq_R_elim_quant_correct :
    coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_R_elim_quant
  
  val norm_Exp : coq_ZE coq_ZExp -> coq_ZE coq_ZExp
  
  val norm_inf_neginf : coq_ZE coq_ZExp -> coq_ZE coq_ZBF -> coq_ZE coq_ZBF
  
  val norm_BF : coq_ZE coq_ZBF -> coq_ZE coq_ZBF
  
  val norm_F : coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val transform_ZE_to_Z : coq_ZE coq_ZF -> z coq_ZF
  
  val transform_ZE_to_string : coq_ZE coq_ZF -> char list coq_ZF
 end

