type __ = Obj.t

type unit0 =
| Tt

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sumor =
| Inleft of 'a
| Inright

val plus : nat -> nat -> nat

val minus : nat -> nat -> nat

val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
 end

module Coq_Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive, mask) prod
    -> (positive, mask) prod
  
  val sqrtrem : positive -> (positive, mask) prod
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod
  
  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
  
  val eq_dec : positive -> positive -> bool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val max_dec : positive -> positive -> bool
    
    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1
    
    val min_dec : positive -> positive -> bool
   end
  
  val max_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : positive -> positive -> bool
  
  val min_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : positive -> positive -> bool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> nat
  
  val pos_div_eucl : positive -> n -> (n, n) prod
  
  val div_eucl : n -> n -> (n, n) prod
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> (n, (n, n) prod) prod
  
  val sqrtrem : n -> (n, n) prod
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> nat -> n
  
  val shiftr_nat : n -> nat -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> nat -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> nat
  
  val of_nat : nat -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> bool
  
  val discr : n -> positive sumor
  
  val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> bool
    
    val min_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> bool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> bool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> bool
 end

module Z : 
 sig 
  type t = z
  
  val zero : z
  
  val one : z
  
  val two : z
  
  val double : z -> z
  
  val succ_double : z -> z
  
  val pred_double : z -> z
  
  val pos_sub : positive -> positive -> z
  
  val add : z -> z -> z
  
  val opp : z -> z
  
  val succ : z -> z
  
  val pred : z -> z
  
  val sub : z -> z -> z
  
  val mul : z -> z -> z
  
  val pow_pos : z -> positive -> z
  
  val pow : z -> z -> z
  
  val square : z -> z
  
  val compare : z -> z -> comparison
  
  val sgn : z -> z
  
  val leb : z -> z -> bool
  
  val ltb : z -> z -> bool
  
  val geb : z -> z -> bool
  
  val gtb : z -> z -> bool
  
  val eqb : z -> z -> bool
  
  val max : z -> z -> z
  
  val min : z -> z -> z
  
  val abs : z -> z
  
  val abs_nat : z -> nat
  
  val abs_N : z -> n
  
  val to_nat : z -> nat
  
  val to_N : z -> n
  
  val of_nat : nat -> z
  
  val of_N : n -> z
  
  val to_pos : z -> positive
  
  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : positive -> z -> (z, z) prod
  
  val div_eucl : z -> z -> (z, z) prod
  
  val div : z -> z -> z
  
  val modulo : z -> z -> z
  
  val quotrem : z -> z -> (z, z) prod
  
  val quot : z -> z -> z
  
  val rem : z -> z -> z
  
  val even : z -> bool
  
  val odd : z -> bool
  
  val div2 : z -> z
  
  val quot2 : z -> z
  
  val log2 : z -> z
  
  val sqrtrem : z -> (z, z) prod
  
  val sqrt : z -> z
  
  val gcd : z -> z -> z
  
  val ggcd : z -> z -> (z, (z, z) prod) prod
  
  val testbit : z -> z -> bool
  
  val shiftl : z -> z -> z
  
  val shiftr : z -> z -> z
  
  val coq_lor : z -> z -> z
  
  val coq_land : z -> z -> z
  
  val ldiff : z -> z -> z
  
  val coq_lxor : z -> z -> z
  
  val eq_dec : z -> z -> bool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : z -> z -> reflect
  
  val ltb_spec0 : z -> z -> reflect
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : z -> z
  
  val log2_up : z -> z
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : z -> z -> z
      
      val modulo : z -> z -> z
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : z -> z -> z
  
  val eqb_spec : z -> z -> reflect
  
  val b2z : bool -> z
  
  val setbit : z -> z -> z
  
  val clearbit : z -> z -> z
  
  val lnot : z -> z
  
  val ones : z -> z
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : z -> z -> bool
    
    val min_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : z -> z -> bool
   end
  
  val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : z -> z -> bool
  
  val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : z -> z -> bool
 end

val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

val div0 : nat -> nat -> nat

val modulo0 : nat -> nat -> nat

val z_le_dec : z -> z -> bool

module type VARIABLE = 
 sig 
  type var 
  
  val var_eq_dec : var -> var -> bool
 end

module type SEM_VAL = 
 sig 
  type coq_Val 
  
  val val_eq_dec : coq_Val -> coq_Val -> bool
  
  val truth_and : coq_Val -> coq_Val -> coq_Val
  
  val truth_or : coq_Val -> coq_Val -> coq_Val
  
  val truth_not : coq_Val -> coq_Val
  
  val coq_Top : coq_Val
  
  val coq_Btm : coq_Val
 end

module Three_Val_NoneError : 
 sig 
  type coq_Val_Impl =
  | VTrue
  | VFalse
  | VError
  
  val coq_Val_Impl_rect : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1
  
  val coq_Val_Impl_rec : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1
  
  type coq_Val = coq_Val_Impl
  
  val val_eq_dec : coq_Val -> coq_Val -> bool
  
  val coq_Top : coq_Val_Impl
  
  val coq_Btm : coq_Val_Impl
  
  val truth_not : coq_Val_Impl -> coq_Val_Impl
  
  val truth_and : coq_Val -> coq_Val -> coq_Val_Impl
  
  val truth_or : coq_Val -> coq_Val -> coq_Val_Impl
 end

module type NUMBER = 
 sig 
  type coq_A 
  
  val coq_Const0 : coq_A
  
  val num_eq_dec : coq_A -> coq_A -> bool
  
  val num_neg : coq_A -> coq_A
  
  val num_plus : coq_A -> coq_A -> coq_A
 end

module ZInfinity : 
 sig 
  type coq_ZE =
  | ZE_Fin of z
  | ZE_Inf
  | ZE_NegInf
  
  val coq_ZE_rect : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val coq_ZE_rec : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val coq_ZE_eq_dec : coq_ZE -> coq_ZE -> bool
  
  val coq_ZEneg : coq_ZE -> coq_ZE
  
  type coq_A = coq_ZE option
  
  val coq_Const0 : coq_ZE option
  
  val num_eq_dec : coq_A -> coq_A -> bool
  
  val num_neg : coq_ZE option -> coq_ZE option
  
  val num_plus : coq_ZE option -> coq_ZE option -> coq_ZE option
 end

module ZNumLattice : 
 sig 
  type coq_A = z
  
  val coq_Const0 : z
  
  val num_eq_dec : z -> z -> bool
  
  val num_neg : coq_A -> z
  
  val num_plus : coq_A -> coq_A -> z
 end

module FinLeqRelation : 
 functor (VAL:SEM_VAL) ->
 sig 
  val num_leq : ZNumLattice.coq_A -> ZNumLattice.coq_A -> VAL.coq_Val
 end

module NoneError3ValRel : 
 sig 
  val noneVal : Three_Val_NoneError.coq_Val_Impl
 end

module InfLeqRelation : 
 functor (VAL:SEM_VAL) ->
 functor (S:sig 
  val noneVal : VAL.coq_Val
 end) ->
 sig 
  val num_leq : ZInfinity.coq_A -> ZInfinity.coq_A -> VAL.coq_Val
 end

module type SEMANTICS_INPUT = 
 sig 
  module N : 
   NUMBER
  
  type coq_Q 
  
  type coq_QT 
  
  val conv : coq_Q -> coq_QT -> N.coq_A
 end

module PureInfinity : 
 sig 
  module N : 
   sig 
    type coq_ZE = ZInfinity.coq_ZE =
    | ZE_Fin of z
    | ZE_Inf
    | ZE_NegInf
    
    val coq_ZE_rect : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
    
    val coq_ZE_rec : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
    
    val coq_ZE_eq_dec : coq_ZE -> coq_ZE -> bool
    
    val coq_ZEneg : coq_ZE -> coq_ZE
    
    type coq_A = coq_ZE option
    
    val coq_Const0 : coq_ZE option
    
    val num_eq_dec : coq_A -> coq_A -> bool
    
    val num_neg : coq_ZE option -> coq_ZE option
    
    val num_plus : coq_ZE option -> coq_ZE option -> coq_ZE option
   end
  
  type coq_AQ =
  | Q_Z
  | Q_ZE
  
  val coq_AQ_rect : 'a1 -> 'a1 -> coq_AQ -> 'a1
  
  val coq_AQ_rec : 'a1 -> 'a1 -> coq_AQ -> 'a1
  
  type coq_Q = coq_AQ
  
  type coq_QT = __
  
  val conv : coq_Q -> coq_QT -> N.coq_A
 end

module PureInt : 
 sig 
  module N : 
   sig 
    type coq_A = z
    
    val coq_Const0 : z
    
    val num_eq_dec : z -> z -> bool
    
    val num_neg : coq_A -> z
    
    val num_plus : coq_A -> coq_A -> z
   end
  
  type coq_Q = unit0
  
  type coq_QT = z
  
  val conv : coq_Q -> coq_QT -> coq_QT
 end

module IntToInfinity : 
 sig 
  module N : 
   sig 
    type coq_ZE = ZInfinity.coq_ZE =
    | ZE_Fin of z
    | ZE_Inf
    | ZE_NegInf
    
    val coq_ZE_rect : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
    
    val coq_ZE_rec : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
    
    val coq_ZE_eq_dec : coq_ZE -> coq_ZE -> bool
    
    val coq_ZEneg : coq_ZE -> coq_ZE
    
    type coq_A = coq_ZE option
    
    val coq_Const0 : coq_ZE option
    
    val num_eq_dec : coq_A -> coq_A -> bool
    
    val num_neg : coq_ZE option -> coq_ZE option
    
    val num_plus : coq_ZE option -> coq_ZE option -> coq_ZE option
   end
  
  type coq_Q = unit0
  
  type coq_QT = z
  
  val conv : coq_Q -> coq_QT -> N.coq_ZE option
 end

module type ZERO_FIN = 
 sig 
  val zero_times : ZNumLattice.coq_A -> ZNumLattice.coq_A
 end

module FinZero : 
 sig 
  val zero_times : ZNumLattice.coq_A -> z
 end

module type ZERO_INF = 
 sig 
  val zero_times : ZInfinity.coq_A -> ZInfinity.coq_A
 end

module InfZeroAll : 
 sig 
  val zero_times : ZInfinity.coq_A -> ZInfinity.coq_ZE option
 end

module ArithSemantics : 
 functor (I:SEMANTICS_INPUT) ->
 functor (V:VARIABLE) ->
 functor (VAL:SEM_VAL) ->
 functor (L:sig 
  val num_leq : I.N.coq_A -> I.N.coq_A -> VAL.coq_Val
 end) ->
 functor (ZT:sig 
  val zero_times : I.N.coq_A -> I.N.coq_A
 end) ->
 sig 
  type coq_ZExp =
  | ZExp_Var of V.var
  | ZExp_Const of I.N.coq_A
  | ZExp_Add of coq_ZExp * coq_ZExp
  | ZExp_Inv of coq_ZExp
  | ZExp_Sub of coq_ZExp * coq_ZExp
  | ZExp_Mult of z * coq_ZExp
  
  val coq_ZExp_rect :
    (V.var -> 'a1) -> (I.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp ->
    'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp
    -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp -> 'a1
  
  val coq_ZExp_rec :
    (V.var -> 'a1) -> (I.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp ->
    'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp
    -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp -> 'a1
  
  type coq_ZBF =
  | ZBF_Const of VAL.coq_Val
  | ZBF_Lt of coq_ZExp * coq_ZExp
  | ZBF_Lte of coq_ZExp * coq_ZExp
  | ZBF_Gt of coq_ZExp * coq_ZExp
  | ZBF_Gte of coq_ZExp * coq_ZExp
  | ZBF_Eq of coq_ZExp * coq_ZExp
  | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
  | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
  | ZBF_Neq of coq_ZExp * coq_ZExp
  
  val coq_ZBF_rect :
    (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1)
    -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
  
  val coq_ZBF_rec :
    (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
    coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1)
    -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
  
  type coq_ZF =
  | ZF_BF of coq_ZBF
  | ZF_And of coq_ZF * coq_ZF
  | ZF_Or of coq_ZF * coq_ZF
  | ZF_Imp of coq_ZF * coq_ZF
  | ZF_Not of coq_ZF
  | ZF_Forall of V.var * I.coq_Q * coq_ZF
  | ZF_Exists of V.var * I.coq_Q * coq_ZF
  
  val coq_ZF_rect :
    (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF ->
    'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1)
    -> (coq_ZF -> 'a1 -> 'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1)
    -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
  
  val coq_ZF_rec :
    (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF ->
    'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1)
    -> (coq_ZF -> 'a1 -> 'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1)
    -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
  
  val num_mult_nat : nat -> I.N.coq_A -> I.N.coq_A
  
  val num_mult : z -> I.N.coq_A -> I.N.coq_A
  
  val subst_exp : (V.var, I.N.coq_A) prod -> coq_ZExp -> coq_ZExp
  
  val subst_bf : (V.var, I.N.coq_A) prod -> coq_ZBF -> coq_ZBF
  
  val substitute : (V.var, I.N.coq_A) prod -> coq_ZF -> coq_ZF
  
  val dexp2ZE : coq_ZExp -> I.N.coq_A
  
  val dzbf2bool : coq_ZBF -> VAL.coq_Val
  
  val length_zform : coq_ZF -> nat
  
  type coq_Input =
  | Sat of coq_ZF
  | DisSat of coq_ZF
  | Udtmd of coq_ZF
  
  val coq_Input_rect :
    (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input -> 'a1
  
  val coq_Input_rec :
    (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input -> 'a1
  
  val length_input : coq_Input -> nat
  
  val eliminateMinMax : coq_ZBF -> coq_ZF
 end

module InfSolver : 
 functor (Coq_sv:VARIABLE) ->
 functor (VAL:SEM_VAL) ->
 functor (S:sig 
  val noneVal : VAL.coq_Val
 end) ->
 functor (FZT:ZERO_FIN) ->
 functor (IZT:ZERO_INF) ->
 sig 
  module InfRel : 
   sig 
    val num_leq : ZInfinity.coq_A -> ZInfinity.coq_A -> VAL.coq_Val
   end
  
  module FinRel : 
   sig 
    val num_leq : ZNumLattice.coq_A -> ZNumLattice.coq_A -> VAL.coq_Val
   end
  
  module IA : 
   sig 
    type coq_ZExp =
    | ZExp_Var of Coq_sv.var
    | ZExp_Const of PureInfinity.N.coq_A
    | ZExp_Add of coq_ZExp * coq_ZExp
    | ZExp_Inv of coq_ZExp
    | ZExp_Sub of coq_ZExp * coq_ZExp
    | ZExp_Mult of z * coq_ZExp
    
    val coq_ZExp_rect :
      (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
      'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
      -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
      coq_ZExp -> 'a1
    
    val coq_ZExp_rec :
      (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
      'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
      -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
      coq_ZExp -> 'a1
    
    type coq_ZBF =
    | ZBF_Const of VAL.coq_Val
    | ZBF_Lt of coq_ZExp * coq_ZExp
    | ZBF_Lte of coq_ZExp * coq_ZExp
    | ZBF_Gt of coq_ZExp * coq_ZExp
    | ZBF_Gte of coq_ZExp * coq_ZExp
    | ZBF_Eq of coq_ZExp * coq_ZExp
    | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Neq of coq_ZExp * coq_ZExp
    
    val coq_ZBF_rect :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    val coq_ZBF_rec :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    type coq_ZF =
    | ZF_BF of coq_ZBF
    | ZF_And of coq_ZF * coq_ZF
    | ZF_Or of coq_ZF * coq_ZF
    | ZF_Imp of coq_ZF * coq_ZF
    | ZF_Not of coq_ZF
    | ZF_Forall of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
    | ZF_Exists of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
    
    val coq_ZF_rect :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInfinity.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInfinity.coq_Q -> coq_ZF ->
      'a1 -> 'a1) -> coq_ZF -> 'a1
    
    val coq_ZF_rec :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInfinity.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInfinity.coq_Q -> coq_ZF ->
      'a1 -> 'a1) -> coq_ZF -> 'a1
    
    val num_mult_nat : nat -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
    
    val num_mult : z -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
    
    val subst_exp :
      (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
    
    val subst_bf :
      (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
    
    val substitute :
      (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
    
    val dexp2ZE : coq_ZExp -> PureInfinity.N.coq_A
    
    val dzbf2bool : coq_ZBF -> VAL.coq_Val
    
    val length_zform : coq_ZF -> nat
    
    type coq_Input =
    | Sat of coq_ZF
    | DisSat of coq_ZF
    | Udtmd of coq_ZF
    
    val coq_Input_rect :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val coq_Input_rec :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val length_input : coq_Input -> nat
    
    val eliminateMinMax : coq_ZBF -> coq_ZF
   end
  
  module FA : 
   sig 
    type coq_ZExp =
    | ZExp_Var of Coq_sv.var
    | ZExp_Const of PureInt.N.coq_A
    | ZExp_Add of coq_ZExp * coq_ZExp
    | ZExp_Inv of coq_ZExp
    | ZExp_Sub of coq_ZExp * coq_ZExp
    | ZExp_Mult of z * coq_ZExp
    
    val coq_ZExp_rect :
      (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 ->
      coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1
      -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp
      -> 'a1
    
    val coq_ZExp_rec :
      (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 ->
      coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1
      -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp
      -> 'a1
    
    type coq_ZBF =
    | ZBF_Const of VAL.coq_Val
    | ZBF_Lt of coq_ZExp * coq_ZExp
    | ZBF_Lte of coq_ZExp * coq_ZExp
    | ZBF_Gt of coq_ZExp * coq_ZExp
    | ZBF_Gte of coq_ZExp * coq_ZExp
    | ZBF_Eq of coq_ZExp * coq_ZExp
    | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Neq of coq_ZExp * coq_ZExp
    
    val coq_ZBF_rect :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    val coq_ZBF_rec :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    type coq_ZF =
    | ZF_BF of coq_ZBF
    | ZF_And of coq_ZF * coq_ZF
    | ZF_Or of coq_ZF * coq_ZF
    | ZF_Imp of coq_ZF * coq_ZF
    | ZF_Not of coq_ZF
    | ZF_Forall of Coq_sv.var * PureInt.coq_Q * coq_ZF
    | ZF_Exists of Coq_sv.var * PureInt.coq_Q * coq_ZF
    
    val coq_ZF_rect :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInt.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInt.coq_Q -> coq_ZF -> 'a1
      -> 'a1) -> coq_ZF -> 'a1
    
    val coq_ZF_rec :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInt.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> PureInt.coq_Q -> coq_ZF -> 'a1
      -> 'a1) -> coq_ZF -> 'a1
    
    val num_mult_nat : nat -> PureInt.N.coq_A -> PureInt.N.coq_A
    
    val num_mult : z -> PureInt.N.coq_A -> PureInt.N.coq_A
    
    val subst_exp :
      (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZExp -> coq_ZExp
    
    val subst_bf : (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZBF -> coq_ZBF
    
    val substitute : (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZF -> coq_ZF
    
    val dexp2ZE : coq_ZExp -> PureInt.N.coq_A
    
    val dzbf2bool : coq_ZBF -> VAL.coq_Val
    
    val length_zform : coq_ZF -> nat
    
    type coq_Input =
    | Sat of coq_ZF
    | DisSat of coq_ZF
    | Udtmd of coq_ZF
    
    val coq_Input_rect :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val coq_Input_rec :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val length_input : coq_Input -> nat
    
    val eliminateMinMax : coq_ZBF -> coq_ZF
   end
  
  module I2F : 
   sig 
    type coq_ZExp =
    | ZExp_Var of Coq_sv.var
    | ZExp_Const of IntToInfinity.N.coq_A
    | ZExp_Add of coq_ZExp * coq_ZExp
    | ZExp_Inv of coq_ZExp
    | ZExp_Sub of coq_ZExp * coq_ZExp
    | ZExp_Mult of z * coq_ZExp
    
    val coq_ZExp_rect :
      (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
      'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
      -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
      coq_ZExp -> 'a1
    
    val coq_ZExp_rec :
      (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
      'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
      -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
      coq_ZExp -> 'a1
    
    type coq_ZBF =
    | ZBF_Const of VAL.coq_Val
    | ZBF_Lt of coq_ZExp * coq_ZExp
    | ZBF_Lte of coq_ZExp * coq_ZExp
    | ZBF_Gt of coq_ZExp * coq_ZExp
    | ZBF_Gte of coq_ZExp * coq_ZExp
    | ZBF_Eq of coq_ZExp * coq_ZExp
    | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
    | ZBF_Neq of coq_ZExp * coq_ZExp
    
    val coq_ZBF_rect :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    val coq_ZBF_rec :
      (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
      coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
      'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
    
    type coq_ZF =
    | ZF_BF of coq_ZBF
    | ZF_And of coq_ZF * coq_ZF
    | ZF_Or of coq_ZF * coq_ZF
    | ZF_Imp of coq_ZF * coq_ZF
    | ZF_Not of coq_ZF
    | ZF_Forall of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
    | ZF_Exists of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
    
    val coq_ZF_rect :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> IntToInfinity.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> IntToInfinity.coq_Q -> coq_ZF
      -> 'a1 -> 'a1) -> coq_ZF -> 'a1
    
    val coq_ZF_rec :
      (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
      -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
      'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> IntToInfinity.coq_Q ->
      coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var -> IntToInfinity.coq_Q -> coq_ZF
      -> 'a1 -> 'a1) -> coq_ZF -> 'a1
    
    val num_mult_nat : nat -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
    
    val num_mult : z -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
    
    val subst_exp :
      (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
    
    val subst_bf :
      (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
    
    val substitute :
      (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
    
    val dexp2ZE : coq_ZExp -> IntToInfinity.N.coq_A
    
    val dzbf2bool : coq_ZBF -> VAL.coq_Val
    
    val length_zform : coq_ZF -> nat
    
    type coq_Input =
    | Sat of coq_ZF
    | DisSat of coq_ZF
    | Udtmd of coq_ZF
    
    val coq_Input_rect :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val coq_Input_rec :
      (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
      'a1
    
    val length_input : coq_Input -> nat
    
    val eliminateMinMax : coq_ZBF -> coq_ZF
   end
  
  val inf_trans_exp : IA.coq_ZExp -> I2F.coq_ZExp
  
  val inf_trans_bf : IA.coq_ZBF -> I2F.coq_ZBF
  
  val inf_trans : IA.coq_ZF -> I2F.coq_ZF
  
  val embed : VAL.coq_Val -> FA.coq_ZF
  
  val coq_FATrue : FA.coq_ZF
  
  val coq_FAFalse : FA.coq_ZF
  
  val coq_FANone : FA.coq_ZF
  
  val proj : IntToInfinity.N.coq_A -> z
  
  val int_trans_exp : I2F.coq_ZExp -> FA.coq_ZExp
  
  val int_trans_bf : I2F.coq_ZBF -> FA.coq_ZF
  
  val int_trans : I2F.coq_ZF -> FA.coq_ZF
  
  val coq_T : IA.coq_ZF -> FA.coq_ZF
 end

module ThreeValuedSimp : 
 functor (Coq_sv:VARIABLE) ->
 functor (FZT:ZERO_FIN) ->
 functor (IZT:ZERO_INF) ->
 sig 
  module InfS : 
   sig 
    module InfRel : 
     sig 
      val num_leq :
        ZInfinity.coq_A -> ZInfinity.coq_A -> Three_Val_NoneError.coq_Val
     end
    
    module FinRel : 
     sig 
      val num_leq :
        ZNumLattice.coq_A -> ZNumLattice.coq_A -> Three_Val_NoneError.coq_Val
     end
    
    module IA : 
     sig 
      type coq_ZExp =
      | ZExp_Var of Coq_sv.var
      | ZExp_Const of PureInfinity.N.coq_A
      | ZExp_Add of coq_ZExp * coq_ZExp
      | ZExp_Inv of coq_ZExp
      | ZExp_Sub of coq_ZExp * coq_ZExp
      | ZExp_Mult of z * coq_ZExp
      
      val coq_ZExp_rect :
        (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
        'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
        (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1
        -> 'a1) -> coq_ZExp -> 'a1
      
      val coq_ZExp_rec :
        (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
        'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
        (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1
        -> 'a1) -> coq_ZExp -> 'a1
      
      type coq_ZBF =
      | ZBF_Const of Three_Val_NoneError.coq_Val
      | ZBF_Lt of coq_ZExp * coq_ZExp
      | ZBF_Lte of coq_ZExp * coq_ZExp
      | ZBF_Gt of coq_ZExp * coq_ZExp
      | ZBF_Gte of coq_ZExp * coq_ZExp
      | ZBF_Eq of coq_ZExp * coq_ZExp
      | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Neq of coq_ZExp * coq_ZExp
      
      val coq_ZBF_rect :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      val coq_ZBF_rec :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      type coq_ZF =
      | ZF_BF of coq_ZBF
      | ZF_And of coq_ZF * coq_ZF
      | ZF_Or of coq_ZF * coq_ZF
      | ZF_Imp of coq_ZF * coq_ZF
      | ZF_Not of coq_ZF
      | ZF_Forall of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
      | ZF_Exists of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
      
      val coq_ZF_rect :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val coq_ZF_rec :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val num_mult_nat : nat -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
      
      val num_mult : z -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
      
      val subst_exp :
        (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
      
      val subst_bf :
        (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
      
      val substitute :
        (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
      
      val dexp2ZE : coq_ZExp -> PureInfinity.N.coq_A
      
      val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
      
      val length_zform : coq_ZF -> nat
      
      type coq_Input =
      | Sat of coq_ZF
      | DisSat of coq_ZF
      | Udtmd of coq_ZF
      
      val coq_Input_rect :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val coq_Input_rec :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val length_input : coq_Input -> nat
      
      val eliminateMinMax : coq_ZBF -> coq_ZF
     end
    
    module FA : 
     sig 
      type coq_ZExp =
      | ZExp_Var of Coq_sv.var
      | ZExp_Const of PureInt.N.coq_A
      | ZExp_Add of coq_ZExp * coq_ZExp
      | ZExp_Inv of coq_ZExp
      | ZExp_Sub of coq_ZExp * coq_ZExp
      | ZExp_Mult of z * coq_ZExp
      
      val coq_ZExp_rect :
        (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1
        -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
        -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
        coq_ZExp -> 'a1
      
      val coq_ZExp_rec :
        (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1
        -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
        -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) ->
        coq_ZExp -> 'a1
      
      type coq_ZBF =
      | ZBF_Const of Three_Val_NoneError.coq_Val
      | ZBF_Lt of coq_ZExp * coq_ZExp
      | ZBF_Lte of coq_ZExp * coq_ZExp
      | ZBF_Gt of coq_ZExp * coq_ZExp
      | ZBF_Gte of coq_ZExp * coq_ZExp
      | ZBF_Eq of coq_ZExp * coq_ZExp
      | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Neq of coq_ZExp * coq_ZExp
      
      val coq_ZBF_rect :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      val coq_ZBF_rec :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      type coq_ZF =
      | ZF_BF of coq_ZBF
      | ZF_And of coq_ZF * coq_ZF
      | ZF_Or of coq_ZF * coq_ZF
      | ZF_Imp of coq_ZF * coq_ZF
      | ZF_Not of coq_ZF
      | ZF_Forall of Coq_sv.var * PureInt.coq_Q * coq_ZF
      | ZF_Exists of Coq_sv.var * PureInt.coq_Q * coq_ZF
      
      val coq_ZF_rect :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val coq_ZF_rec :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val num_mult_nat : nat -> PureInt.N.coq_A -> PureInt.N.coq_A
      
      val num_mult : z -> PureInt.N.coq_A -> PureInt.N.coq_A
      
      val subst_exp :
        (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZExp -> coq_ZExp
      
      val subst_bf : (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZBF -> coq_ZBF
      
      val substitute : (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZF -> coq_ZF
      
      val dexp2ZE : coq_ZExp -> PureInt.N.coq_A
      
      val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
      
      val length_zform : coq_ZF -> nat
      
      type coq_Input =
      | Sat of coq_ZF
      | DisSat of coq_ZF
      | Udtmd of coq_ZF
      
      val coq_Input_rect :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val coq_Input_rec :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val length_input : coq_Input -> nat
      
      val eliminateMinMax : coq_ZBF -> coq_ZF
     end
    
    module I2F : 
     sig 
      type coq_ZExp =
      | ZExp_Var of Coq_sv.var
      | ZExp_Const of IntToInfinity.N.coq_A
      | ZExp_Add of coq_ZExp * coq_ZExp
      | ZExp_Inv of coq_ZExp
      | ZExp_Sub of coq_ZExp * coq_ZExp
      | ZExp_Mult of z * coq_ZExp
      
      val coq_ZExp_rect :
        (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
        'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
        (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1
        -> 'a1) -> coq_ZExp -> 'a1
      
      val coq_ZExp_rec :
        (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp ->
        'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
        (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1
        -> 'a1) -> coq_ZExp -> 'a1
      
      type coq_ZBF =
      | ZBF_Const of Three_Val_NoneError.coq_Val
      | ZBF_Lt of coq_ZExp * coq_ZExp
      | ZBF_Lte of coq_ZExp * coq_ZExp
      | ZBF_Gt of coq_ZExp * coq_ZExp
      | ZBF_Gte of coq_ZExp * coq_ZExp
      | ZBF_Eq of coq_ZExp * coq_ZExp
      | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
      | ZBF_Neq of coq_ZExp * coq_ZExp
      
      val coq_ZBF_rect :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      val coq_ZBF_rec :
        (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1)
        -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
        (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1
      
      type coq_ZF =
      | ZF_BF of coq_ZBF
      | ZF_And of coq_ZF * coq_ZF
      | ZF_Or of coq_ZF * coq_ZF
      | ZF_Imp of coq_ZF * coq_ZF
      | ZF_Not of coq_ZF
      | ZF_Forall of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
      | ZF_Exists of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
      
      val coq_ZF_rect :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val coq_ZF_rec :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
        (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
        -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
        IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
      
      val num_mult_nat :
        nat -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
      
      val num_mult : z -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
      
      val subst_exp :
        (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
      
      val subst_bf :
        (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
      
      val substitute :
        (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
      
      val dexp2ZE : coq_ZExp -> IntToInfinity.N.coq_A
      
      val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
      
      val length_zform : coq_ZF -> nat
      
      type coq_Input =
      | Sat of coq_ZF
      | DisSat of coq_ZF
      | Udtmd of coq_ZF
      
      val coq_Input_rect :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val coq_Input_rec :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1
      
      val length_input : coq_Input -> nat
      
      val eliminateMinMax : coq_ZBF -> coq_ZF
     end
    
    val inf_trans_exp : IA.coq_ZExp -> I2F.coq_ZExp
    
    val inf_trans_bf : IA.coq_ZBF -> I2F.coq_ZBF
    
    val inf_trans : IA.coq_ZF -> I2F.coq_ZF
    
    val embed : Three_Val_NoneError.coq_Val -> FA.coq_ZF
    
    val coq_FATrue : FA.coq_ZF
    
    val coq_FAFalse : FA.coq_ZF
    
    val coq_FANone : FA.coq_ZF
    
    val proj : IntToInfinity.N.coq_A -> z
    
    val int_trans_exp : I2F.coq_ZExp -> FA.coq_ZExp
    
    val int_trans_bf : I2F.coq_ZBF -> FA.coq_ZF
    
    val int_trans : I2F.coq_ZF -> FA.coq_ZF
    
    val coq_T : IA.coq_ZF -> FA.coq_ZF
   end
  
  type coq_SimpResult =
  | EQ_TRUE
  | EQ_FALSE
  | EQ_ERROR
  | OTHER
  
  val coq_SimpResult_rect :
    InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
    'a1) -> coq_SimpResult -> 'a1
  
  val coq_SimpResult_rec :
    InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
    'a1) -> coq_SimpResult -> 'a1
  
  val judge : InfS.FA.coq_ZF -> coq_SimpResult
  
  val simplify : InfS.FA.coq_ZF -> InfS.FA.coq_ZF
 end

module type STRVAR = 
 sig 
  type var 
  
  val var_eq_dec : var -> var -> bool
  
  val var2string : var -> char list
  
  val string2var : char list -> var
 end

module InfSolverExtract : 
 functor (Coq_sv:STRVAR) ->
 sig 
  module Three_Val : 
   sig 
    type coq_Val_Impl =
    | VTrue
    | VFalse
    | VError
    
    val coq_Val_Impl_rect : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1
    
    val coq_Val_Impl_rec : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1
    
    type coq_Val = coq_Val_Impl
    
    val val_eq_dec : coq_Val -> coq_Val -> bool
    
    val coq_Top : coq_Val_Impl
    
    val coq_Btm : coq_Val_Impl
    
    val truth_not : coq_Val_Impl -> coq_Val_Impl
    
    val truth_and : coq_Val -> coq_Val -> coq_Val_Impl
    
    val truth_or : coq_Val -> coq_Val -> coq_Val_Impl
   end
  
  module SIM : 
   sig 
    module InfS : 
     sig 
      module InfRel : 
       sig 
        val num_leq :
          ZInfinity.coq_A -> ZInfinity.coq_A -> Three_Val_NoneError.coq_Val
       end
      
      module FinRel : 
       sig 
        val num_leq :
          ZNumLattice.coq_A -> ZNumLattice.coq_A ->
          Three_Val_NoneError.coq_Val
       end
      
      module IA : 
       sig 
        type coq_ZExp =
        | ZExp_Var of Coq_sv.var
        | ZExp_Const of PureInfinity.N.coq_A
        | ZExp_Add of coq_ZExp * coq_ZExp
        | ZExp_Inv of coq_ZExp
        | ZExp_Sub of coq_ZExp * coq_ZExp
        | ZExp_Mult of z * coq_ZExp
        
        val coq_ZExp_rect :
          (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
          (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp ->
          'a1 -> 'a1) -> coq_ZExp -> 'a1
        
        val coq_ZExp_rec :
          (Coq_sv.var -> 'a1) -> (PureInfinity.N.coq_A -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
          (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp ->
          'a1 -> 'a1) -> coq_ZExp -> 'a1
        
        type coq_ZBF =
        | ZBF_Const of Three_Val_NoneError.coq_Val
        | ZBF_Lt of coq_ZExp * coq_ZExp
        | ZBF_Lte of coq_ZExp * coq_ZExp
        | ZBF_Gt of coq_ZExp * coq_ZExp
        | ZBF_Gte of coq_ZExp * coq_ZExp
        | ZBF_Eq of coq_ZExp * coq_ZExp
        | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Neq of coq_ZExp * coq_ZExp
        
        val coq_ZBF_rect :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        val coq_ZBF_rec :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        type coq_ZF =
        | ZF_BF of coq_ZBF
        | ZF_And of coq_ZF * coq_ZF
        | ZF_Or of coq_ZF * coq_ZF
        | ZF_Imp of coq_ZF * coq_ZF
        | ZF_Not of coq_ZF
        | ZF_Forall of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
        | ZF_Exists of Coq_sv.var * PureInfinity.coq_Q * coq_ZF
        
        val coq_ZF_rect :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val coq_ZF_rec :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val num_mult_nat :
          nat -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
        
        val num_mult : z -> PureInfinity.N.coq_A -> PureInfinity.N.coq_A
        
        val subst_exp :
          (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
        
        val subst_bf :
          (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
        
        val substitute :
          (Coq_sv.var, PureInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
        
        val dexp2ZE : coq_ZExp -> PureInfinity.N.coq_A
        
        val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
        
        val length_zform : coq_ZF -> nat
        
        type coq_Input =
        | Sat of coq_ZF
        | DisSat of coq_ZF
        | Udtmd of coq_ZF
        
        val coq_Input_rect :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val coq_Input_rec :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val length_input : coq_Input -> nat
        
        val eliminateMinMax : coq_ZBF -> coq_ZF
       end
      
      module FA : 
       sig 
        type coq_ZExp =
        | ZExp_Var of Coq_sv.var
        | ZExp_Const of PureInt.N.coq_A
        | ZExp_Add of coq_ZExp * coq_ZExp
        | ZExp_Inv of coq_ZExp
        | ZExp_Sub of coq_ZExp * coq_ZExp
        | ZExp_Mult of z * coq_ZExp
        
        val coq_ZExp_rect :
          (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1
          -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1)
          -> coq_ZExp -> 'a1
        
        val coq_ZExp_rec :
          (Coq_sv.var -> 'a1) -> (PureInt.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1
          -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1)
          -> coq_ZExp -> 'a1
        
        type coq_ZBF =
        | ZBF_Const of Three_Val_NoneError.coq_Val
        | ZBF_Lt of coq_ZExp * coq_ZExp
        | ZBF_Lte of coq_ZExp * coq_ZExp
        | ZBF_Gt of coq_ZExp * coq_ZExp
        | ZBF_Gte of coq_ZExp * coq_ZExp
        | ZBF_Eq of coq_ZExp * coq_ZExp
        | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Neq of coq_ZExp * coq_ZExp
        
        val coq_ZBF_rect :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        val coq_ZBF_rec :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        type coq_ZF =
        | ZF_BF of coq_ZBF
        | ZF_And of coq_ZF * coq_ZF
        | ZF_Or of coq_ZF * coq_ZF
        | ZF_Imp of coq_ZF * coq_ZF
        | ZF_Not of coq_ZF
        | ZF_Forall of Coq_sv.var * PureInt.coq_Q * coq_ZF
        | ZF_Exists of Coq_sv.var * PureInt.coq_Q * coq_ZF
        
        val coq_ZF_rect :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val coq_ZF_rec :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          PureInt.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val num_mult_nat : nat -> PureInt.N.coq_A -> PureInt.N.coq_A
        
        val num_mult : z -> PureInt.N.coq_A -> PureInt.N.coq_A
        
        val subst_exp :
          (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZExp -> coq_ZExp
        
        val subst_bf :
          (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZBF -> coq_ZBF
        
        val substitute :
          (Coq_sv.var, PureInt.N.coq_A) prod -> coq_ZF -> coq_ZF
        
        val dexp2ZE : coq_ZExp -> PureInt.N.coq_A
        
        val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
        
        val length_zform : coq_ZF -> nat
        
        type coq_Input =
        | Sat of coq_ZF
        | DisSat of coq_ZF
        | Udtmd of coq_ZF
        
        val coq_Input_rect :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val coq_Input_rec :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val length_input : coq_Input -> nat
        
        val eliminateMinMax : coq_ZBF -> coq_ZF
       end
      
      module I2F : 
       sig 
        type coq_ZExp =
        | ZExp_Var of Coq_sv.var
        | ZExp_Const of IntToInfinity.N.coq_A
        | ZExp_Add of coq_ZExp * coq_ZExp
        | ZExp_Inv of coq_ZExp
        | ZExp_Sub of coq_ZExp * coq_ZExp
        | ZExp_Mult of z * coq_ZExp
        
        val coq_ZExp_rect :
          (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
          (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp ->
          'a1 -> 'a1) -> coq_ZExp -> 'a1
        
        val coq_ZExp_rec :
          (Coq_sv.var -> 'a1) -> (IntToInfinity.N.coq_A -> 'a1) -> (coq_ZExp
          -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) ->
          (coq_ZExp -> 'a1 -> coq_ZExp -> 'a1 -> 'a1) -> (z -> coq_ZExp ->
          'a1 -> 'a1) -> coq_ZExp -> 'a1
        
        type coq_ZBF =
        | ZBF_Const of Three_Val_NoneError.coq_Val
        | ZBF_Lt of coq_ZExp * coq_ZExp
        | ZBF_Lte of coq_ZExp * coq_ZExp
        | ZBF_Gt of coq_ZExp * coq_ZExp
        | ZBF_Gte of coq_ZExp * coq_ZExp
        | ZBF_Eq of coq_ZExp * coq_ZExp
        | ZBF_Eq_Max of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Eq_Min of coq_ZExp * coq_ZExp * coq_ZExp
        | ZBF_Neq of coq_ZExp * coq_ZExp
        
        val coq_ZBF_rect :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        val coq_ZBF_rec :
          (Three_Val_NoneError.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp ->
          'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
          coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) ->
          coq_ZBF -> 'a1
        
        type coq_ZF =
        | ZF_BF of coq_ZBF
        | ZF_And of coq_ZF * coq_ZF
        | ZF_Or of coq_ZF * coq_ZF
        | ZF_Imp of coq_ZF * coq_ZF
        | ZF_Not of coq_ZF
        | ZF_Forall of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
        | ZF_Exists of Coq_sv.var * IntToInfinity.coq_Q * coq_ZF
        
        val coq_ZF_rect :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val coq_ZF_rec :
          (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) ->
          (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF
          -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> (Coq_sv.var ->
          IntToInfinity.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1
        
        val num_mult_nat :
          nat -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
        
        val num_mult : z -> IntToInfinity.N.coq_A -> IntToInfinity.N.coq_A
        
        val subst_exp :
          (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZExp -> coq_ZExp
        
        val subst_bf :
          (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZBF -> coq_ZBF
        
        val substitute :
          (Coq_sv.var, IntToInfinity.N.coq_A) prod -> coq_ZF -> coq_ZF
        
        val dexp2ZE : coq_ZExp -> IntToInfinity.N.coq_A
        
        val dzbf2bool : coq_ZBF -> Three_Val_NoneError.coq_Val
        
        val length_zform : coq_ZF -> nat
        
        type coq_Input =
        | Sat of coq_ZF
        | DisSat of coq_ZF
        | Udtmd of coq_ZF
        
        val coq_Input_rect :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val coq_Input_rec :
          (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input
          -> 'a1
        
        val length_input : coq_Input -> nat
        
        val eliminateMinMax : coq_ZBF -> coq_ZF
       end
      
      val inf_trans_exp : IA.coq_ZExp -> I2F.coq_ZExp
      
      val inf_trans_bf : IA.coq_ZBF -> I2F.coq_ZBF
      
      val inf_trans : IA.coq_ZF -> I2F.coq_ZF
      
      val embed : Three_Val_NoneError.coq_Val -> FA.coq_ZF
      
      val coq_FATrue : FA.coq_ZF
      
      val coq_FAFalse : FA.coq_ZF
      
      val coq_FANone : FA.coq_ZF
      
      val proj : IntToInfinity.N.coq_A -> z
      
      val int_trans_exp : I2F.coq_ZExp -> FA.coq_ZExp
      
      val int_trans_bf : I2F.coq_ZBF -> FA.coq_ZF
      
      val int_trans : I2F.coq_ZF -> FA.coq_ZF
      
      val coq_T : IA.coq_ZF -> FA.coq_ZF
     end
    
    type coq_SimpResult =
    | EQ_TRUE
    | EQ_FALSE
    | EQ_ERROR
    | OTHER
    
    val coq_SimpResult_rect :
      InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> coq_SimpResult -> 'a1
    
    val coq_SimpResult_rec :
      InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> coq_SimpResult -> 'a1
    
    val judge : InfS.FA.coq_ZF -> coq_SimpResult
    
    val simplify : InfS.FA.coq_ZF -> InfS.FA.coq_ZF
   end
  
  val coq_Z_of_bool : bool -> z
  
  val coq_Z_of_ascii : char -> z
  
  val coq_Z_of_0 : z
  
  val coq_Z_of_digit : char -> z option
  
  val coq_Z_of_string' : char list -> z -> z option
  
  val coq_Z_of_string : char list -> z
  
  val natToDigit : nat -> char
  
  val writeNatAux : nat -> nat -> char list -> char list
  
  val writeNat : nat -> char list
  
  val string_of_Z : z -> char list
  
  type 'const_type coq_ZExp =
  | ZExp_Var of Coq_sv.var
  | ZExp_Const of 'const_type
  | ZExp_Add of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Sub of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Mult of Coq_sv.var * 'const_type coq_ZExp
  
  val coq_ZExp_rect :
    (Coq_sv.var -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
    coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2 ->
    'a2) -> (Coq_sv.var -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp -> 'a2
  
  val coq_ZExp_rec :
    (Coq_sv.var -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
    coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2 ->
    'a2) -> (Coq_sv.var -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp -> 'a2
  
  type 'const_type coq_ZBF =
  | ZBF_Const of bool
  | ZBF_Lt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Lte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Eq of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Eq_Max of 'const_type coq_ZExp * 'const_type coq_ZExp
     * 'const_type coq_ZExp
  | ZBF_Eq_Min of 'const_type coq_ZExp * 'const_type coq_ZExp
     * 'const_type coq_ZExp
  | ZBF_Neq of 'const_type coq_ZExp * 'const_type coq_ZExp
  
  val coq_ZBF_rect :
    (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1
    coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2)
    -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
    -> 'a2) -> 'a1 coq_ZBF -> 'a2
  
  val coq_ZBF_rec :
    (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1
    coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2)
    -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
    -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
    -> 'a2) -> 'a1 coq_ZBF -> 'a2
  
  type 'const_type coq_ZF =
  | ZF_BF of 'const_type coq_ZBF
  | ZF_And of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Or of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Not of 'const_type coq_ZF
  | ZF_Forall_Fin of Coq_sv.var * 'const_type coq_ZF
  | ZF_Exists_Fin of Coq_sv.var * 'const_type coq_ZF
  | ZF_Forall of Coq_sv.var * 'const_type coq_ZF
  | ZF_Exists of Coq_sv.var * 'const_type coq_ZF
  
  val coq_ZF_rect :
    ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
    -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF -> 'a2
    -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1
    coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
    (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2
  
  val coq_ZF_rec :
    ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
    -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF -> 'a2
    -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1
    coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
    (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2
  
  type coq_ZE =
  | ZE_Fin of Coq_sv.var
  | ZE_Inf
  | ZE_NegInf
  
  val coq_ZE_rect : (Coq_sv.var -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val coq_ZE_rec : (Coq_sv.var -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1
  
  val convert_ZF_to_IAZF_Exp : coq_ZE coq_ZExp -> SIM.InfS.IA.coq_ZExp
  
  val convert_ZF_to_IAZF_BF : coq_ZE coq_ZBF -> SIM.InfS.IA.coq_ZBF
  
  val convert_ZF_to_IAZF : coq_ZE coq_ZF -> SIM.InfS.IA.coq_ZF
  
  val convert_FAZF_to_ZF_Exp : SIM.InfS.FA.coq_ZExp -> Coq_sv.var coq_ZExp
  
  val convert_FAZF_to_ZF_BF : SIM.InfS.FA.coq_ZBF -> Coq_sv.var coq_ZBF
  
  val convert_FAZF_to_ZF : SIM.InfS.FA.coq_ZF -> Coq_sv.var coq_ZF
  
  val transform_ZE_to_string : coq_ZE coq_ZF -> Coq_sv.var coq_ZF
  
  val transform_ZE_to_string_simplify : coq_ZE coq_ZF -> Coq_sv.var coq_ZF
 end

