type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

type positive =
| XI of positive
| XO of positive
| XH

(** val psucc : positive -> positive **)

let rec psucc = function
| XI p -> XO (psucc p)
| XO p -> XI p
| XH -> XO XH

(** val pplus : positive -> positive -> positive **)

let rec pplus x y =
  match x with
  | XI p ->
    (match y with
     | XI q -> XO (pplus_carry p q)
     | XO q -> XI (pplus p q)
     | XH -> XO (psucc p))
  | XO p ->
    (match y with
     | XI q -> XI (pplus p q)
     | XO q -> XO (pplus p q)
     | XH -> XI p)
  | XH ->
    (match y with
     | XI q -> XO (psucc q)
     | XO q -> XI q
     | XH -> XO XH)

(** val pplus_carry : positive -> positive -> positive **)

and pplus_carry x y =
  match x with
  | XI p ->
    (match y with
     | XI q -> XI (pplus_carry p q)
     | XO q -> XO (pplus_carry p q)
     | XH -> XI (psucc p))
  | XO p ->
    (match y with
     | XI q -> XO (pplus_carry p q)
     | XO q -> XI (pplus p q)
     | XH -> XO (psucc p))
  | XH ->
    (match y with
     | XI q -> XI (psucc q)
     | XO q -> XO (psucc q)
     | XH -> XI XH)

(** val pdouble_minus_one : positive -> positive **)

let rec pdouble_minus_one = function
| XI p -> XI (XO p)
| XO p -> XI (pdouble_minus_one p)
| XH -> XH

type positive_mask =
| IsNul
| IsPos of positive
| IsNeg

(** val pdouble_plus_one_mask : positive_mask -> positive_mask **)

let pdouble_plus_one_mask = function
| IsNul -> IsPos XH
| IsPos p -> IsPos (XI p)
| IsNeg -> IsNeg

(** val pdouble_mask : positive_mask -> positive_mask **)

let pdouble_mask = function
| IsPos p -> IsPos (XO p)
| x0 -> x0

(** val pdouble_minus_two : positive -> positive_mask **)

let pdouble_minus_two = function
| XI p -> IsPos (XO (XO p))
| XO p -> IsPos (XO (pdouble_minus_one p))
| XH -> IsNul

(** val pminus_mask : positive -> positive -> positive_mask **)

let rec pminus_mask x y =
  match x with
  | XI p ->
    (match y with
     | XI q -> pdouble_mask (pminus_mask p q)
     | XO q -> pdouble_plus_one_mask (pminus_mask p q)
     | XH -> IsPos (XO p))
  | XO p ->
    (match y with
     | XI q -> pdouble_plus_one_mask (pminus_mask_carry p q)
     | XO q -> pdouble_mask (pminus_mask p q)
     | XH -> IsPos (pdouble_minus_one p))
  | XH ->
    (match y with
     | XH -> IsNul
     | _ -> IsNeg)

(** val pminus_mask_carry : positive -> positive -> positive_mask **)

and pminus_mask_carry x y =
  match x with
  | XI p ->
    (match y with
     | XI q -> pdouble_plus_one_mask (pminus_mask_carry p q)
     | XO q -> pdouble_mask (pminus_mask p q)
     | XH -> IsPos (pdouble_minus_one p))
  | XO p ->
    (match y with
     | XI q -> pdouble_mask (pminus_mask_carry p q)
     | XO q -> pdouble_plus_one_mask (pminus_mask_carry p q)
     | XH -> pdouble_minus_two p)
  | XH -> IsNeg

(** val pminus : positive -> positive -> positive **)

let pminus x y =
  match pminus_mask x y with
  | IsPos z0 -> z0
  | _ -> XH

(** val pmult : positive -> positive -> positive **)

let rec pmult x y =
  match x with
  | XI p -> pplus y (XO (pmult p y))
  | XO p -> XO (pmult p y)
  | XH -> y

(** val pcompare : positive -> positive -> comparison -> comparison **)

let rec pcompare x y r =
  match x with
  | XI p ->
    (match y with
     | XI q -> pcompare p q r
     | XO q -> pcompare p q Gt
     | XH -> Gt)
  | XO p ->
    (match y with
     | XI q -> pcompare p q Lt
     | XO q -> pcompare p q r
     | XH -> Gt)
  | XH ->
    (match y with
     | XH -> r
     | _ -> Lt)

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val zplus : z -> z -> z **)

let zplus x y =
  match x with
  | Z0 -> y
  | Zpos x' ->
    (match y with
     | Z0 -> Zpos x'
     | Zpos y' -> Zpos (pplus x' y')
     | Zneg y' ->
       (match pcompare x' y' Eq with
        | Eq -> Z0
        | Lt -> Zneg (pminus y' x')
        | Gt -> Zpos (pminus x' y')))
  | Zneg x' ->
    (match y with
     | Z0 -> Zneg x'
     | Zpos y' ->
       (match pcompare x' y' Eq with
        | Eq -> Z0
        | Lt -> Zpos (pminus y' x')
        | Gt -> Zneg (pminus x' y'))
     | Zneg y' -> Zneg (pplus x' y'))

(** val zopp : z -> z **)

let zopp = function
| Z0 -> Z0
| Zpos x0 -> Zneg x0
| Zneg x0 -> Zpos x0

(** val zminus : z -> z -> z **)

let zminus m n =
  zplus m (zopp n)

(** val zmult : z -> z -> z **)

let zmult x y =
  match x with
  | Z0 -> Z0
  | Zpos x' ->
    (match y with
     | Z0 -> Z0
     | Zpos y' -> Zpos (pmult x' y')
     | Zneg y' -> Zneg (pmult x' y'))
  | Zneg x' ->
    (match y with
     | Z0 -> Z0
     | Zpos y' -> Zneg (pmult x' y')
     | Zneg y' -> Zpos (pmult x' y'))

(** val zcompare : z -> z -> comparison **)

let zcompare x y =
  match x with
  | Z0 ->
    (match y with
     | Z0 -> Eq
     | Zpos y' -> Lt
     | Zneg y' -> Gt)
  | Zpos x' ->
    (match y with
     | Zpos y' -> pcompare x' y' Eq
     | _ -> Gt)
  | Zneg x' ->
    (match y with
     | Zneg y' -> compOpp (pcompare x' y' Eq)
     | _ -> Lt)

(** val iter_pos : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_pos n f x =
  match n with
  | XI n' -> f (iter_pos n' f (iter_pos n' f x))
  | XO n' -> iter_pos n' f (iter_pos n' f x)
  | XH -> f x

(** val zpower_pos : z -> positive -> z **)

let zpower_pos z0 n =
  iter_pos n (fun x -> zmult z0 x) (Zpos XH)

(** val zpower : z -> z -> z **)

let zpower x = function
| Z0 -> Zpos XH
| Zpos p -> zpower_pos x p
| Zneg p -> Z0

module type SV = 
 sig 
  val is_eq : char list -> char list -> bool
 end

module InfSolver = 
 functor (Coq_sv:SV) ->
 struct 
  (** val coq_Z_of_bool : bool -> z **)
  
  let coq_Z_of_bool = function
  | true -> Zpos XH
  | false -> Z0
  
  (** val coq_Z_of_ascii : char -> z **)
  
  let coq_Z_of_ascii a =
    (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b1 b2 b3 b4 b5 b6 b7 b8 ->
      zplus (coq_Z_of_bool b1)
        (zmult (Zpos (XO XH))
          (zplus (coq_Z_of_bool b2)
            (zmult (Zpos (XO XH))
              (zplus (coq_Z_of_bool b3)
                (zmult (Zpos (XO XH))
                  (zplus (coq_Z_of_bool b4)
                    (zmult (Zpos (XO XH))
                      (zplus (coq_Z_of_bool b5)
                        (zmult (Zpos (XO XH))
                          (zplus (coq_Z_of_bool b6)
                            (zmult (Zpos (XO XH))
                              (zplus (coq_Z_of_bool b7)
                                (zmult (Zpos (XO XH)) (coq_Z_of_bool b8)))))))))))))))
      a
  
  (** val coq_Z_of_0 : z **)
  
  let coq_Z_of_0 =
    Zpos (XO (XO (XO (XO (XI XH)))))
  
  (** val coq_Z_of_digit : char -> z option **)
  
  let coq_Z_of_digit a =
    let v = zminus (coq_Z_of_ascii a) coq_Z_of_0 in
    (match zcompare v Z0 with
     | Eq -> Some v
     | Lt -> None
     | Gt ->
       (match zcompare v (Zpos (XO (XI (XO XH)))) with
        | Lt -> Some v
        | _ -> None))
  
  (** val coq_Z_of_string' : char list -> z -> z option **)
  
  let rec coq_Z_of_string' a n =
    match a with
    | [] -> None
    | a0::s' ->
      (match coq_Z_of_digit a0 with
       | Some va ->
         (match coq_Z_of_string' s' (zplus n (Zpos XH)) with
          | Some vs ->
            Some (zplus (zmult va (zpower (Zpos (XO (XI (XO XH)))) n)) vs)
          | None -> Some va)
       | None -> None)
  
  (** val coq_Z_of_string : char list -> z option **)
  
  let coq_Z_of_string a =
    coq_Z_of_string' a Z0
  
  type 'const_type coq_ZExp =
  | ZExp_Var of char list
  | ZExp_Const of 'const_type
  | ZExp_Add of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Sub of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZExp_Mult of char list * 'const_type coq_ZExp
  
  (** val coq_ZExp_rect :
      (char list -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
      coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2
      -> 'a2) -> (char list -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp ->
      'a2 **)
  
  let rec coq_ZExp_rect f f0 f1 f2 f3 = function
  | ZExp_Var s -> f s
  | ZExp_Const y -> f0 y
  | ZExp_Add (z1, z2) ->
    f1 z1 (coq_ZExp_rect f f0 f1 f2 f3 z1) z2
      (coq_ZExp_rect f f0 f1 f2 f3 z2)
  | ZExp_Sub (z1, z2) ->
    f2 z1 (coq_ZExp_rect f f0 f1 f2 f3 z1) z2
      (coq_ZExp_rect f f0 f1 f2 f3 z2)
  | ZExp_Mult (s, z1) -> f3 s z1 (coq_ZExp_rect f f0 f1 f2 f3 z1)
  
  (** val coq_ZExp_rec :
      (char list -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
      coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2
      -> 'a2) -> (char list -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp ->
      'a2 **)
  
  let rec coq_ZExp_rec f f0 f1 f2 f3 = function
  | ZExp_Var s -> f s
  | ZExp_Const y -> f0 y
  | ZExp_Add (z1, z2) ->
    f1 z1 (coq_ZExp_rec f f0 f1 f2 f3 z1) z2 (coq_ZExp_rec f f0 f1 f2 f3 z2)
  | ZExp_Sub (z1, z2) ->
    f2 z1 (coq_ZExp_rec f f0 f1 f2 f3 z1) z2 (coq_ZExp_rec f f0 f1 f2 f3 z2)
  | ZExp_Mult (s, z1) -> f3 s z1 (coq_ZExp_rec f f0 f1 f2 f3 z1)
  
  type 'const_type coq_ZBF =
  | ZBF_Const of bool
  | ZBF_Lt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Lte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gt of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Gte of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Eq of 'const_type coq_ZExp * 'const_type coq_ZExp
  | ZBF_Neq of 'const_type coq_ZExp * 'const_type coq_ZExp
  
  (** val coq_ZBF_rect :
      (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
      -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
      ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
      -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2 **)
  
  let coq_ZBF_rect f f0 f1 f2 f3 f4 f5 = function
  | ZBF_Const x -> f x
  | ZBF_Lt (x, x0) -> f0 x x0
  | ZBF_Lte (x, x0) -> f1 x x0
  | ZBF_Gt (x, x0) -> f2 x x0
  | ZBF_Gte (x, x0) -> f3 x x0
  | ZBF_Eq (x, x0) -> f4 x x0
  | ZBF_Neq (x, x0) -> f5 x x0
  
  (** val coq_ZBF_rec :
      (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
      -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
      ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
      -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2 **)
  
  let coq_ZBF_rec f f0 f1 f2 f3 f4 f5 = function
  | ZBF_Const x -> f x
  | ZBF_Lt (x, x0) -> f0 x x0
  | ZBF_Lte (x, x0) -> f1 x x0
  | ZBF_Gt (x, x0) -> f2 x x0
  | ZBF_Gte (x, x0) -> f3 x x0
  | ZBF_Eq (x, x0) -> f4 x x0
  | ZBF_Neq (x, x0) -> f5 x x0
  
  type 'const_type coq_ZF =
  | ZF_BF of 'const_type coq_ZBF
  | ZF_And of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Or of 'const_type coq_ZF * 'const_type coq_ZF
  | ZF_Not of 'const_type coq_ZF
  | ZF_Forall_Fin of char list * 'const_type coq_ZF
  | ZF_Exists_Fin of char list * 'const_type coq_ZF
  | ZF_Forall of char list * 'const_type coq_ZF
  | ZF_Exists of char list * 'const_type coq_ZF
  
  (** val coq_ZF_rect :
      ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
      -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF ->
      'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (char list ->
      'a1 coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
      (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2 **)
  
  let rec coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | ZF_BF z1 -> f z1
  | ZF_And (z1, z2) ->
    f0 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1) z2
      (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z2)
  | ZF_Or (z1, z2) ->
    f1 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1) z2
      (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z2)
  | ZF_Not z1 -> f2 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Forall_Fin (s, z1) -> f3 s z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Exists_Fin (s, z1) -> f4 s z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Forall (s, z1) -> f5 s z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Exists (s, z1) -> f6 s z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
  
  (** val coq_ZF_rec :
      ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
      -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF ->
      'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (char list ->
      'a1 coq_ZF -> 'a2 -> 'a2) -> (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) ->
      (char list -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2 **)
  
  let rec coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | ZF_BF z1 -> f z1
  | ZF_And (z1, z2) ->
    f0 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1) z2
      (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z2)
  | ZF_Or (z1, z2) ->
    f1 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1) z2
      (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z2)
  | ZF_Not z1 -> f2 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Forall_Fin (s, z1) -> f3 s z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Exists_Fin (s, z1) -> f4 s z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Forall (s, z1) -> f5 s z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
  | ZF_Exists (s, z1) -> f6 s z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
  
  type coq_ZE =
  | ZE_Fin of char list
  | ZE_Inf
  | ZE_NegInf
  
  (** val coq_ZE_rect : (char list -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)
  
  let coq_ZE_rect f f0 f1 = function
  | ZE_Fin x -> f x
  | ZE_Inf -> f0
  | ZE_NegInf -> f1
  
  (** val coq_ZE_rec : (char list -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)
  
  let coq_ZE_rec f f0 f1 = function
  | ZE_Fin x -> f x
  | ZE_Inf -> f0
  | ZE_NegInf -> f1
  
  (** val mkOr : coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let rec mkOr f1 f2 =
    match f1 with
    | ZF_BF b1 ->
      (match f2 with
       | ZF_BF b2 ->
         (match b1 with
          | ZBF_Const c -> if c then f1 else f2
          | _ ->
            (match b2 with
             | ZBF_Const c -> if c then f2 else f1
             | _ -> ZF_Or (f1, f2)))
       | _ -> ZF_Or (f1, f2))
    | _ -> ZF_Or (f1, f2)
  
  (** val mkAnd : coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let rec mkAnd f1 f2 =
    match f1 with
    | ZF_BF b1 ->
      (match f2 with
       | ZF_BF b2 ->
         (match b1 with
          | ZBF_Const c -> if negb c then f1 else f2
          | _ ->
            (match b2 with
             | ZBF_Const c -> if negb c then f2 else f1
             | _ -> ZF_And (f1, f2)))
       | _ -> ZF_And (f1, f2))
    | _ -> ZF_And (f1, f2)
  
  (** val subs_Exp :
      (char list, coq_ZE) prod -> coq_ZE coq_ZExp -> coq_ZE coq_ZExp **)
  
  let rec subs_Exp p exp = match exp with
  | ZExp_Var v -> if Coq_sv.is_eq (fst p) v then ZExp_Const (snd p) else exp
  | ZExp_Const z0 -> exp
  | ZExp_Add (e1, e2) -> ZExp_Add ((subs_Exp p e1), (subs_Exp p e2))
  | ZExp_Sub (e1, e2) -> ZExp_Sub ((subs_Exp p e1), (subs_Exp p e2))
  | ZExp_Mult (s, e) -> ZExp_Mult (s, (subs_Exp p e))
  
  (** val subs_BF :
      (char list, coq_ZE) prod -> coq_ZE coq_ZBF -> coq_ZE coq_ZBF **)
  
  let rec subs_BF p bf = match bf with
  | ZBF_Const b -> bf
  | ZBF_Lt (e1, e2) -> ZBF_Lt ((subs_Exp p e1), (subs_Exp p e2))
  | ZBF_Lte (e1, e2) -> ZBF_Lte ((subs_Exp p e1), (subs_Exp p e2))
  | ZBF_Gt (e1, e2) -> ZBF_Gt ((subs_Exp p e1), (subs_Exp p e2))
  | ZBF_Gte (e1, e2) -> ZBF_Gte ((subs_Exp p e1), (subs_Exp p e2))
  | ZBF_Eq (e1, e2) -> ZBF_Eq ((subs_Exp p e1), (subs_Exp p e2))
  | ZBF_Neq (e1, e2) -> ZBF_Neq ((subs_Exp p e1), (subs_Exp p e2))
  
  (** val subs_F :
      (char list, coq_ZE) prod -> coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let rec subs_F p f = match f with
  | ZF_BF bf -> ZF_BF (subs_BF p bf)
  | ZF_And (f1, f2) -> mkAnd (subs_F p f1) (subs_F p f2)
  | ZF_Or (f1, f2) -> mkOr (subs_F p f1) (subs_F p f2)
  | ZF_Not g -> ZF_Not (subs_F p g)
  | ZF_Forall_Fin (v, g) ->
    if Coq_sv.is_eq (fst p) v then f else ZF_Forall_Fin (v, (subs_F p g))
  | ZF_Exists_Fin (v, g) ->
    if Coq_sv.is_eq (fst p) v then f else ZF_Exists_Fin (v, (subs_F p g))
  | ZF_Forall (v, g) ->
    if Coq_sv.is_eq (fst p) v then f else ZF_Forall (v, (subs_F p g))
  | ZF_Exists (v, g) ->
    if Coq_sv.is_eq (fst p) v then f else ZF_Exists (v, (subs_F p g))
  
  (** val convert_Exp : coq_ZE coq_ZExp -> z coq_ZExp **)
  
  let rec convert_Exp = function
  | ZExp_Var v -> ZExp_Var v
  | ZExp_Const c ->
    (match c with
     | ZE_Fin v ->
       let x =
         match coq_Z_of_string v with
         | Some n -> n
         | None -> Z0
       in
       ZExp_Const x
     | ZE_Inf ->
       ZExp_Var
         ('Z'::('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[])))))))))
     | ZE_NegInf ->
       ZExp_Var
         ('Z'::('N'::('e'::('g'::('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[])))))))))))))
  | ZExp_Add (e1, e2) -> ZExp_Add ((convert_Exp e1), (convert_Exp e2))
  | ZExp_Sub (e1, e2) -> ZExp_Sub ((convert_Exp e1), (convert_Exp e2))
  | ZExp_Mult (s, e) -> ZExp_Mult (s, (convert_Exp e))
  
  (** val convert_BF : coq_ZE coq_ZBF -> z coq_ZBF **)
  
  let rec convert_BF = function
  | ZBF_Const b -> ZBF_Const b
  | ZBF_Lt (e1, e2) -> ZBF_Lt ((convert_Exp e1), (convert_Exp e2))
  | ZBF_Lte (e1, e2) -> ZBF_Lte ((convert_Exp e1), (convert_Exp e2))
  | ZBF_Gt (e1, e2) -> ZBF_Gt ((convert_Exp e1), (convert_Exp e2))
  | ZBF_Gte (e1, e2) -> ZBF_Gte ((convert_Exp e1), (convert_Exp e2))
  | ZBF_Eq (e1, e2) -> ZBF_Eq ((convert_Exp e1), (convert_Exp e2))
  | ZBF_Neq (e1, e2) -> ZBF_Neq ((convert_Exp e1), (convert_Exp e2))
  
  (** val convert_ZE_to_Z : coq_ZE coq_ZF -> z coq_ZF **)
  
  let rec convert_ZE_to_Z = function
  | ZF_BF bf -> ZF_BF (convert_BF bf)
  | ZF_And (f1, f2) -> ZF_And ((convert_ZE_to_Z f1), (convert_ZE_to_Z f2))
  | ZF_Or (f1, f2) -> ZF_Or ((convert_ZE_to_Z f1), (convert_ZE_to_Z f2))
  | ZF_Not g -> ZF_Not (convert_ZE_to_Z g)
  | ZF_Forall_Fin (v, g) -> ZF_Forall_Fin (v, (convert_ZE_to_Z g))
  | ZF_Exists_Fin (v, g) -> ZF_Exists_Fin (v, (convert_ZE_to_Z g))
  | ZF_Forall (v, g) -> ZF_Forall (v, (convert_ZE_to_Z g))
  | ZF_Exists (v, g) -> ZF_Exists (v, (convert_ZE_to_Z g))
  
  (** val convert_Exp_string : coq_ZE coq_ZExp -> char list coq_ZExp **)
  
  let rec convert_Exp_string = function
  | ZExp_Var v -> ZExp_Var v
  | ZExp_Const c ->
    (match c with
     | ZE_Fin v -> ZExp_Const v
     | ZE_Inf ->
       ZExp_Var
         ('Z'::('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[])))))))))
     | ZE_NegInf ->
       ZExp_Var
         ('Z'::('N'::('e'::('g'::('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[])))))))))))))
  | ZExp_Add (e1, e2) ->
    ZExp_Add ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZExp_Sub (e1, e2) ->
    ZExp_Sub ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZExp_Mult (s, e) -> ZExp_Mult (s, (convert_Exp_string e))
  
  (** val convert_BF_string : coq_ZE coq_ZBF -> char list coq_ZBF **)
  
  let rec convert_BF_string = function
  | ZBF_Const b -> ZBF_Const b
  | ZBF_Lt (e1, e2) ->
    ZBF_Lt ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZBF_Lte (e1, e2) ->
    ZBF_Lte ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZBF_Gt (e1, e2) ->
    ZBF_Gt ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZBF_Gte (e1, e2) ->
    ZBF_Gte ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZBF_Eq (e1, e2) ->
    ZBF_Eq ((convert_Exp_string e1), (convert_Exp_string e2))
  | ZBF_Neq (e1, e2) ->
    ZBF_Neq ((convert_Exp_string e1), (convert_Exp_string e2))
  
  (** val convert_ZE_to_string : coq_ZE coq_ZF -> char list coq_ZF **)
  
  let rec convert_ZE_to_string = function
  | ZF_BF bf -> ZF_BF (convert_BF_string bf)
  | ZF_And (f1, f2) ->
    ZF_And ((convert_ZE_to_string f1), (convert_ZE_to_string f2))
  | ZF_Or (f1, f2) ->
    ZF_Or ((convert_ZE_to_string f1), (convert_ZE_to_string f2))
  | ZF_Not g -> ZF_Not (convert_ZE_to_string g)
  | ZF_Forall_Fin (v, g) -> ZF_Forall_Fin (v, (convert_ZE_to_string g))
  | ZF_Exists_Fin (v, g) -> ZF_Exists_Fin (v, (convert_ZE_to_string g))
  | ZF_Forall (v, g) -> ZF_Forall (v, (convert_ZE_to_string g))
  | ZF_Exists (v, g) -> ZF_Exists (v, (convert_ZE_to_string g))
  
  (** val num_of_quant : coq_ZE coq_ZF -> nat **)
  
  let rec num_of_quant = function
  | ZF_BF bf -> S O
  | ZF_And (f1, f2) -> plus (num_of_quant f1) (num_of_quant f2)
  | ZF_Or (f1, f2) -> plus (num_of_quant f1) (num_of_quant f2)
  | ZF_Not g -> plus (S O) (num_of_quant g)
  | ZF_Forall_Fin (v, g) -> plus (S O) (num_of_quant g)
  | ZF_Exists_Fin (v, g) -> plus (S O) (num_of_quant g)
  | ZF_Forall (v, g) -> plus (S O) (num_of_quant g)
  | ZF_Exists (v, g) -> plus (S O) (num_of_quant g)
  
  (** val elim_quant_metric : coq_ZE coq_ZF -> nat **)
  
  let elim_quant_metric f =
    num_of_quant f
  
  (** val elim_quant_F :
      (coq_ZE coq_ZF -> coq_ZE coq_ZF) -> coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let elim_quant_F elim_quant0 f = match f with
  | ZF_BF z0 -> f
  | ZF_And (f1, f2) -> mkAnd (elim_quant0 f1) (elim_quant0 f2)
  | ZF_Or (f1, f2) -> mkOr (elim_quant0 f1) (elim_quant0 f2)
  | ZF_Not g -> ZF_Not (elim_quant0 g)
  | ZF_Forall_Fin (v, g) -> ZF_Forall_Fin (v, (elim_quant0 g))
  | ZF_Exists_Fin (v, g) -> ZF_Exists_Fin (v, (elim_quant0 g))
  | ZF_Forall (v, g) ->
    mkAnd (ZF_Forall_Fin (v, (elim_quant0 g)))
      (mkAnd (subs_F (Pair (v, ZE_Inf)) (elim_quant0 g))
        (subs_F (Pair (v, ZE_NegInf)) (elim_quant0 g)))
  | ZF_Exists (v, g) ->
    mkOr (ZF_Exists_Fin (v, (elim_quant0 g)))
      (mkOr (subs_F (Pair (v, ZE_Inf)) (elim_quant0 g))
        (subs_F (Pair (v, ZE_NegInf)) (elim_quant0 g)))
  
  (** val elim_quant_terminate : coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let rec elim_quant_terminate = function
  | ZF_BF z0 -> ZF_BF z0
  | ZF_And (f1, f2) ->
    mkAnd (elim_quant_terminate f1) (elim_quant_terminate f2)
  | ZF_Or (f1, f2) ->
    mkOr (elim_quant_terminate f1) (elim_quant_terminate f2)
  | ZF_Not g -> ZF_Not (elim_quant_terminate g)
  | ZF_Forall_Fin (v, g) -> ZF_Forall_Fin (v, (elim_quant_terminate g))
  | ZF_Exists_Fin (v, g) -> ZF_Exists_Fin (v, (elim_quant_terminate g))
  | ZF_Forall (v, g) ->
    let rec_res = elim_quant_terminate g in
    mkAnd (ZF_Forall_Fin (v, rec_res))
      (mkAnd (subs_F (Pair (v, ZE_Inf)) rec_res)
        (subs_F (Pair (v, ZE_NegInf)) rec_res))
  | ZF_Exists (v, g) ->
    let rec_res = elim_quant_terminate g in
    mkOr (ZF_Exists_Fin (v, rec_res))
      (mkOr (subs_F (Pair (v, ZE_Inf)) rec_res)
        (subs_F (Pair (v, ZE_NegInf)) rec_res))
  
  (** val elim_quant : coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let elim_quant x =
    elim_quant_terminate x
  
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
  
  (** val coq_R_elim_quant_rect :
      (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
      char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant
      -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list ->
      coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1)
      -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF
      -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF
      -> __ -> __ -> 'a1) -> coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 **)
  
  let rec coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f7 z0 = function
  | R_elim_quant_0 (f8, v, g, res1, r0, res0, r1, res, r2) ->
    f f8 v g __ res1 r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res1 r0) res0 r1
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res0 r1) res r2
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res r2)
  | R_elim_quant_1 (f8, v, g, res1, r0, res0, r1, res, r2) ->
    f0 f8 v g __ res1 r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res1 r0) res0 r1
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res0 r1) res r2
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res r2)
  | R_elim_quant_2 (f8, f9, f10, res0, r0, res, r1) ->
    f1 f8 f9 f10 __ res0 r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f9 res0 r0) res r1
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f10 res r1)
  | R_elim_quant_3 (f8, f9, f10, res0, r0, res, r1) ->
    f2 f8 f9 f10 __ res0 r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f9 res0 r0) res r1
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f10 res r1)
  | R_elim_quant_4 (f8, g, res, r0) ->
    f3 f8 g __ res r0 (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_5 (f8, v, g, res, r0) ->
    f4 f8 v g __ res r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_6 (f8, v, g, res, r0) ->
    f5 f8 v g __ res r0
      (coq_R_elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_7 (f8, _x) -> f6 f8 _x __ __
  
  (** val coq_R_elim_quant_rec :
      (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
      char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant
      -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 ->
      'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list ->
      coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF -> coq_R_elim_quant -> 'a1 -> 'a1)
      -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> coq_ZE coq_ZF
      -> coq_R_elim_quant -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF
      -> __ -> __ -> 'a1) -> coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_R_elim_quant -> 'a1 **)
  
  let rec coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 f7 z0 = function
  | R_elim_quant_0 (f8, v, g, res1, r0, res0, r1, res, r2) ->
    f f8 v g __ res1 r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res1 r0) res0 r1
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res0 r1) res r2
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res r2)
  | R_elim_quant_1 (f8, v, g, res1, r0, res0, r1, res, r2) ->
    f0 f8 v g __ res1 r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res1 r0) res0 r1
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res0 r1) res r2
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res r2)
  | R_elim_quant_2 (f8, f9, f10, res0, r0, res, r1) ->
    f1 f8 f9 f10 __ res0 r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 f9 res0 r0) res r1
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 f10 res r1)
  | R_elim_quant_3 (f8, f9, f10, res0, r0, res, r1) ->
    f2 f8 f9 f10 __ res0 r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 f9 res0 r0) res r1
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 f10 res r1)
  | R_elim_quant_4 (f8, g, res, r0) ->
    f3 f8 g __ res r0 (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_5 (f8, v, g, res, r0) ->
    f4 f8 v g __ res r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_6 (f8, v, g, res, r0) ->
    f5 f8 v g __ res r0
      (coq_R_elim_quant_rec f f0 f1 f2 f3 f4 f5 f6 g res r0)
  | R_elim_quant_7 (f8, _x) -> f6 f8 _x __ __
  
  (** val elim_quant_rect :
      (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1
      -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 ->
      'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF
      -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ ->
      __ -> 'a1) -> coq_ZE coq_ZF -> 'a1 **)
  
  let rec elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 f7 =
    let f8 = f6 f7 in
    let f9 = f5 f7 in
    let f10 = f4 f7 in
    let f11 = f3 f7 in
    let f12 = f2 f7 in
    let f13 = f1 f7 in
    let f14 = f0 f7 in
    let f15 = f f7 in
    (match f7 with
     | ZF_BF z0 -> let _x = ZF_BF z0 in f8 _x __ __
     | ZF_And (z0, z1) ->
       let f16 = f13 z0 z1 __ in
       let f17 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
       in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z1 in f17 hrec
     | ZF_Or (z0, z1) ->
       let f16 = f12 z0 z1 __ in
       let f17 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
       in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z1 in f17 hrec
     | ZF_Not z0 ->
       let f16 = f11 z0 __ in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
     | ZF_Forall_Fin (s, z0) ->
       let f16 = f10 s z0 __ in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
     | ZF_Exists_Fin (s, z0) ->
       let f16 = f9 s z0 __ in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
     | ZF_Forall (s, z0) ->
       let f16 = f15 s z0 __ in
       let f17 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
       in
       let f18 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f17 hrec
       in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f18 hrec
     | ZF_Exists (s, z0) ->
       let f16 = f14 s z0 __ in
       let f17 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f16 hrec
       in
       let f18 =
         let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f17 hrec
       in
       let hrec = elim_quant_rect f f0 f1 f2 f3 f4 f5 f6 z0 in f18 hrec)
  
  (** val elim_quant_rec :
      (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1
      -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE coq_ZF -> __ -> 'a1 ->
      'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_ZE coq_ZF
      -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF ->
      coq_ZE coq_ZF -> __ -> 'a1 -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> char list -> coq_ZE
      coq_ZF -> __ -> 'a1 -> 'a1) -> (coq_ZE coq_ZF -> coq_ZE coq_ZF -> __ ->
      __ -> 'a1) -> coq_ZE coq_ZF -> 'a1 **)
  
  let elim_quant_rec =
    elim_quant_rect
  
  (** val coq_R_elim_quant_correct :
      coq_ZE coq_ZF -> coq_ZE coq_ZF -> coq_R_elim_quant **)
  
  let coq_R_elim_quant_correct x res =
    elim_quant_rect (fun y y0 y1 _ y3 y4 y5 z0 _ -> R_elim_quant_0 (y, y0,
      y1, (elim_quant y1), (y3 (elim_quant y1) __), (elim_quant y1),
      (y4 (elim_quant y1) __), (elim_quant y1), (y5 (elim_quant y1) __)))
      (fun y y0 y1 _ y3 y4 y5 z0 _ -> R_elim_quant_1 (y, y0, y1,
      (elim_quant y1), (y3 (elim_quant y1) __), (elim_quant y1),
      (y4 (elim_quant y1) __), (elim_quant y1), (y5 (elim_quant y1) __)))
      (fun y y0 y1 _ y3 y4 z0 _ -> R_elim_quant_2 (y, y0, y1,
      (elim_quant y0), (y3 (elim_quant y0) __), (elim_quant y1),
      (y4 (elim_quant y1) __))) (fun y y0 y1 _ y3 y4 z0 _ -> R_elim_quant_3
      (y, y0, y1, (elim_quant y0), (y3 (elim_quant y0) __), (elim_quant y1),
      (y4 (elim_quant y1) __))) (fun y y0 _ y2 z0 _ -> R_elim_quant_4 (y, y0,
      (elim_quant y0), (y2 (elim_quant y0) __))) (fun y y0 y1 _ y3 z0 _ ->
      R_elim_quant_5 (y, y0, y1, (elim_quant y1), (y3 (elim_quant y1) __)))
      (fun y y0 y1 _ y3 z0 _ -> R_elim_quant_6 (y, y0, y1, (elim_quant y1),
      (y3 (elim_quant y1) __))) (fun y y0 _ _ z0 _ -> R_elim_quant_7 (y, y0))
      x res __
  
  (** val norm_Exp : coq_ZE coq_ZExp -> coq_ZE coq_ZExp **)
  
  let rec norm_Exp exp = match exp with
  | ZExp_Add (e1, e2) ->
    let e1n = norm_Exp e1 in
    let e2n = norm_Exp e2 in
    (match e1n with
     | ZExp_Const c ->
       (match e2n with
        | ZExp_Const c0 ->
          (match c with
           | ZE_Fin s ->
             (match c0 with
              | ZE_Fin s0 -> exp
              | x -> ZExp_Const x)
           | ZE_Inf ->
             (match c0 with
              | ZE_NegInf -> exp
              | _ -> ZExp_Const ZE_Inf)
           | ZE_NegInf ->
             (match c0 with
              | ZE_Inf -> exp
              | _ -> ZExp_Const ZE_NegInf))
        | _ ->
          (match c with
           | ZE_Fin s -> exp
           | x -> ZExp_Const x))
     | _ ->
       (match e2n with
        | ZExp_Const c ->
          (match c with
           | ZE_Fin s -> exp
           | x -> ZExp_Const x)
        | _ -> exp))
  | ZExp_Sub (e1, e2) ->
    let e1n = norm_Exp e1 in
    let e2n = norm_Exp e2 in
    (match e1n with
     | ZExp_Const c ->
       (match e2n with
        | ZExp_Const c0 ->
          (match c with
           | ZE_Fin s ->
             (match c0 with
              | ZE_Fin s0 -> exp
              | ZE_Inf -> ZExp_Const ZE_NegInf
              | ZE_NegInf -> ZExp_Const ZE_Inf)
           | ZE_Inf ->
             (match c0 with
              | ZE_Inf -> exp
              | _ -> ZExp_Const ZE_Inf)
           | ZE_NegInf ->
             (match c0 with
              | ZE_NegInf -> exp
              | _ -> ZExp_Const ZE_NegInf))
        | _ ->
          (match c with
           | ZE_Fin s -> exp
           | x -> ZExp_Const x))
     | _ ->
       (match e2n with
        | ZExp_Const c ->
          (match c with
           | ZE_Fin s -> exp
           | ZE_Inf -> ZExp_Const ZE_NegInf
           | ZE_NegInf -> ZExp_Const ZE_Inf)
        | _ -> exp))
  | ZExp_Mult (s, e) ->
    let ef = norm_Exp e in
    (match ef with
     | ZExp_Const c ->
       (match c with
        | ZE_Fin s0 -> exp
        | _ -> ef)
     | _ -> exp)
  | _ -> exp
  
  (** val norm_inf_neginf :
      coq_ZE coq_ZExp -> coq_ZE coq_ZBF -> coq_ZE coq_ZBF **)
  
  let rec norm_inf_neginf e norm_bf =
    match e with
    | ZExp_Add (a1, a2) ->
      (match a1 with
       | ZExp_Const c1 ->
         (match a2 with
          | ZExp_Const c2 ->
            (match c1 with
             | ZE_Fin s -> norm_bf
             | ZE_Inf ->
               (match c2 with
                | ZE_NegInf -> ZBF_Const false
                | _ -> norm_bf)
             | ZE_NegInf ->
               (match c2 with
                | ZE_Inf -> ZBF_Const false
                | _ -> norm_bf))
          | _ -> norm_bf)
       | _ -> norm_bf)
    | ZExp_Sub (a1, a2) ->
      (match a1 with
       | ZExp_Const c1 ->
         (match a2 with
          | ZExp_Const c2 ->
            (match c1 with
             | ZE_Fin s -> norm_bf
             | ZE_Inf ->
               (match c2 with
                | ZE_Inf -> ZBF_Const false
                | _ -> norm_bf)
             | ZE_NegInf ->
               (match c2 with
                | ZE_NegInf -> ZBF_Const false
                | _ -> norm_bf))
          | _ -> norm_bf)
       | _ -> norm_bf)
    | _ -> norm_bf
  
  (** val norm_BF : coq_ZE coq_ZBF -> coq_ZE coq_ZBF **)
  
  let rec norm_BF bf =
    let norm_bf =
      match bf with
      | ZBF_Const b -> bf
      | ZBF_Lt (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | ZE_Inf -> ZBF_Const true
                  | ZE_NegInf -> ZBF_Const false)
               | ZE_Inf -> ZBF_Const false
               | ZE_NegInf ->
                 (match c0 with
                  | ZE_NegInf -> ZBF_Const false
                  | _ -> ZBF_Const true))
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const false
               | ZE_NegInf -> ZBF_Const true))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const true
               | ZE_NegInf -> ZBF_Const false)
            | _ -> bf))
      | ZBF_Lte (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | ZE_Inf -> ZBF_Const true
                  | ZE_NegInf -> ZBF_Const false)
               | ZE_Inf ->
                 (match c0 with
                  | ZE_Inf -> ZBF_Const true
                  | _ -> ZBF_Const false)
               | ZE_NegInf -> ZBF_Const true)
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const false
               | ZE_NegInf -> ZBF_Const true))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const true
               | ZE_NegInf -> ZBF_Const false)
            | _ -> bf))
      | ZBF_Gt (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | ZE_Inf -> ZBF_Const false
                  | ZE_NegInf -> ZBF_Const true)
               | ZE_Inf ->
                 (match c0 with
                  | ZE_Inf -> ZBF_Const false
                  | _ -> ZBF_Const true)
               | ZE_NegInf -> ZBF_Const false)
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const true
               | ZE_NegInf -> ZBF_Const false))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const false
               | ZE_NegInf -> ZBF_Const true)
            | _ -> bf))
      | ZBF_Gte (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | ZE_Inf -> ZBF_Const false
                  | ZE_NegInf -> ZBF_Const true)
               | ZE_Inf -> ZBF_Const true
               | ZE_NegInf ->
                 (match c0 with
                  | ZE_NegInf -> ZBF_Const true
                  | _ -> ZBF_Const false))
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const true
               | ZE_NegInf -> ZBF_Const false))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | ZE_Inf -> ZBF_Const false
               | ZE_NegInf -> ZBF_Const true)
            | _ -> bf))
      | ZBF_Eq (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | _ -> ZBF_Const false)
               | ZE_Inf ->
                 (match c0 with
                  | ZE_Inf -> ZBF_Const true
                  | _ -> ZBF_Const false)
               | ZE_NegInf ->
                 (match c0 with
                  | ZE_NegInf -> ZBF_Const true
                  | _ -> ZBF_Const false))
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | _ -> ZBF_Const false))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | _ -> ZBF_Const false)
            | _ -> bf))
      | ZBF_Neq (e1, e2) ->
        (match norm_Exp e1 with
         | ZExp_Const c ->
           (match norm_Exp e2 with
            | ZExp_Const c0 ->
              (match c with
               | ZE_Fin s ->
                 (match c0 with
                  | ZE_Fin s0 -> bf
                  | _ -> ZBF_Const true)
               | ZE_Inf ->
                 (match c0 with
                  | ZE_Inf -> ZBF_Const false
                  | _ -> ZBF_Const true)
               | ZE_NegInf ->
                 (match c0 with
                  | ZE_NegInf -> ZBF_Const false
                  | _ -> ZBF_Const true))
            | _ ->
              (match c with
               | ZE_Fin s -> bf
               | _ -> ZBF_Const true))
         | _ ->
           (match norm_Exp e2 with
            | ZExp_Const c ->
              (match c with
               | ZE_Fin s -> bf
               | _ -> ZBF_Const true)
            | _ -> bf))
    in
    (match norm_bf with
     | ZBF_Const b -> norm_bf
     | ZBF_Lt (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b then norm_inf_neginf e2 norm_bf else ZBF_Const false
        | _ -> norm_inf_neginf e2 norm_bf)
     | ZBF_Lte (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b then norm_inf_neginf e2 norm_bf else ZBF_Const false
        | _ -> norm_inf_neginf e2 norm_bf)
     | ZBF_Gt (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b then norm_inf_neginf e2 norm_bf else ZBF_Const false
        | _ -> norm_inf_neginf e2 norm_bf)
     | ZBF_Gte (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b then norm_inf_neginf e2 norm_bf else ZBF_Const false
        | _ -> norm_inf_neginf e2 norm_bf)
     | ZBF_Eq (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b then norm_inf_neginf e2 norm_bf else ZBF_Const false
        | _ -> norm_inf_neginf e2 norm_bf)
     | ZBF_Neq (e1, e2) ->
       (match norm_inf_neginf e1 norm_bf with
        | ZBF_Const b ->
          if b
          then (match norm_inf_neginf e2 norm_bf with
                | ZBF_Const b0 -> if b0 then norm_bf else ZBF_Const true
                | _ -> norm_bf)
          else ZBF_Const true
        | _ ->
          (match norm_inf_neginf e2 norm_bf with
           | ZBF_Const b -> if b then norm_bf else ZBF_Const true
           | _ -> norm_bf)))
  
  (** val norm_F : coq_ZE coq_ZF -> coq_ZE coq_ZF **)
  
  let rec norm_F = function
  | ZF_BF bf -> ZF_BF (norm_BF bf)
  | ZF_And (f1, f2) -> mkAnd (norm_F f1) (norm_F f2)
  | ZF_Or (f1, f2) -> mkOr (norm_F f1) (norm_F f2)
  | ZF_Not g -> ZF_Not (norm_F g)
  | ZF_Forall_Fin (v, g) -> ZF_Forall_Fin (v, (norm_F g))
  | ZF_Exists_Fin (v, g) -> ZF_Exists_Fin (v, (norm_F g))
  | ZF_Forall (v, g) -> ZF_Forall (v, (norm_F g))
  | ZF_Exists (v, g) -> ZF_Exists (v, (norm_F g))
  
  (** val transform_ZE_to_Z : coq_ZE coq_ZF -> z coq_ZF **)
  
  let transform_ZE_to_Z f =
    convert_ZE_to_Z (norm_F (elim_quant f))
  
  (** val transform_ZE_to_string : coq_ZE coq_ZF -> char list coq_ZF **)
  
  let transform_ZE_to_string f =
    convert_ZE_to_string (norm_F (elim_quant f))
 end

