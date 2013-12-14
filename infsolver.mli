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
  
  val num_of_exps_base : coq_ZE coq_ZExp -> nat
  
  val num_of_exps : coq_ZE coq_ZBF -> nat
  
  val norm_BF_metric : coq_ZE coq_ZBF -> nat
  
  val norm_BF_min_max_aux : coq_ZE coq_ZBF -> coq_ZE coq_ZBF
  
  val norm_BF : coq_ZE coq_ZBF -> coq_ZE coq_ZBF
  
  val norm_F : coq_ZE coq_ZF -> coq_ZE coq_ZF
  
  val transform_ZE_to_Z : coq_ZE coq_ZF -> z coq_ZF
  
  val transform_ZE_to_string : coq_ZE coq_ZF -> char list coq_ZF
 end

