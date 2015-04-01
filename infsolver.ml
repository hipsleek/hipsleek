type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
  | Tt

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

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
  | Some a -> Some (f a)
  | None -> None

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

type compareSpecT =
  | CompEqT
  | CompLtT
  | CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
  | Eq -> CompEqT
  | Lt -> CompLtT
  | Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
(* singleton inductive, whose constructor was exist *)

type 'a sumor =
  | Inleft of 'a
  | Inright

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
  | O -> m
  | S p -> S (plus p m)

(** val minus : nat -> nat -> nat **)

let rec minus n0 m =
  match n0 with
  | O -> n0
  | S k ->
    (match m with
     | O -> n0
     | S l -> minus k l)

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  match n0 with
  | O -> x
  | S n' -> f (nat_iter n' f x)

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

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
  | true -> ReflectT
  | false -> ReflectF

module Pos = 
struct 
  type t = positive

  (** val succ : positive -> positive **)

  let rec succ = function
    | XI p -> XO (succ p)
    | XO p -> XI p
    | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
    | XI p -> XI (XO p)
    | XO p -> XI (pred_double p)
    | XH -> XH

  (** val pred : positive -> positive **)

  let pred = function
    | XI p -> XO p
    | XO p -> pred_double p
    | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
    | XI p -> Npos (XO p)
    | XO p -> Npos (pred_double p)
    | XH -> N0

  type mask =
    | IsNul
    | IsPos of positive
    | IsNeg

  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
    | IsNul -> f
    | IsPos x -> f0 x
    | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
    | IsNul -> f
    | IsPos x -> f0 x
    | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
    | IsNul -> IsPos XH
    | IsPos p -> IsPos (XI p)
    | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
    | IsPos p -> IsPos (XO p)
    | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
    | XI p -> IsPos (XO (XO p))
    | XO p -> IsPos (XO (pred_double p))
    | XH -> IsNul

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
    | IsPos q ->
      (match q with
       | XH -> IsNul
       | _ -> IsPos (pred q))
    | _ -> IsNeg

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x y =
    iter y (mul x) XH

  (** val square : positive -> positive **)

  let rec square = function
    | XI p0 -> XI (XO (add (square p0) p0))
    | XO p0 -> XO (XO (square p0))
    | XH -> XH

  (** val div2 : positive -> positive **)

  let div2 = function
    | XI p0 -> p0
    | XO p0 -> p0
    | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
    | XI p0 -> succ p0
    | XO p0 -> p0
    | XH -> XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
    | XI p0 -> S (size_nat p0)
    | XO p0 -> S (size_nat p0)
    | XH -> S O

  (** val size : positive -> positive **)

  let rec size = function
    | XI p0 -> succ (size p0)
    | XO p0 -> succ (size p0)
    | XH -> XH

  (** val compare_cont : positive -> positive -> comparison -> comparison **)

  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare x y =
    compare_cont x y Eq

  (** val min : positive -> positive -> positive **)

  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : positive -> positive -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)

  let sqrtrem_step f g = function
    | Pair (s, y) ->
      (match y with
       | IsPos r ->
         let s' = XI (XO s) in
         let r' = g (f r) in
         if leb s' r'
         then Pair ((XI s), (sub_mask r' s'))
         else Pair ((XO s), (IsPos r'))
       | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))

  (** val sqrtrem : positive -> (positive, mask) prod **)

  let rec sqrtrem = function
    | XI p0 ->
      (match p0 with
       | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
       | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
       | XH -> Pair (XH, (IsPos (XO XH))))
    | XO p0 ->
      (match p0 with
       | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
       | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
       | XH -> Pair (XH, (IsPos XH)))
    | XH -> Pair (XH, IsNul)

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n0 a b =
    match n0 with
    | O -> Pair (XH, (Pair (a, b)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n1 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
    | N0 -> Npos XH
    | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
    | N0 -> N0
    | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val shiftl_nat : positive -> nat -> positive **)

  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p

  (** val shiftr_nat : positive -> nat -> positive **)

  let shiftr_nat p n0 =
    nat_iter n0 div2 p

  (** val shiftl : positive -> n -> positive **)

  let shiftl p = function
    | N0 -> p
    | Npos n1 -> iter n1 (fun x -> XO x) p

  (** val shiftr : positive -> n -> positive **)

  let shiftr p = function
    | N0 -> p
    | Npos n1 -> iter n1 div2 p

  (** val testbit_nat : positive -> nat -> bool **)

  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op plus x (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
    | O -> XH
    | S x ->
      (match x with
       | O -> XH
       | S n1 -> succ (of_nat x))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
    | O -> XH
    | S x -> succ (of_succ_nat x)
end

module Coq_Pos = 
struct 
  type t = positive

  (** val succ : positive -> positive **)

  let rec succ = function
    | XI p -> XO (succ p)
    | XO p -> XI p
    | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
    | XI p -> XI (XO p)
    | XO p -> XI (pred_double p)
    | XH -> XH

  (** val pred : positive -> positive **)

  let pred = function
    | XI p -> XO p
    | XO p -> pred_double p
    | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
    | XI p -> Npos (XO p)
    | XO p -> Npos (pred_double p)
    | XH -> N0

  type mask = Pos.mask =
    | IsNul
    | IsPos of positive
    | IsNeg

  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
    | IsNul -> f
    | IsPos x -> f0 x
    | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
    | IsNul -> f
    | IsPos x -> f0 x
    | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
    | IsNul -> IsPos XH
    | IsPos p -> IsPos (XI p)
    | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
    | IsPos p -> IsPos (XO p)
    | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
    | XI p -> IsPos (XO (XO p))
    | XO p -> IsPos (XO (pred_double p))
    | XH -> IsNul

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
    | IsPos q ->
      (match q with
       | XH -> IsNul
       | _ -> IsPos (pred q))
    | _ -> IsNeg

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x y =
    iter y (mul x) XH

  (** val square : positive -> positive **)

  let rec square = function
    | XI p0 -> XI (XO (add (square p0) p0))
    | XO p0 -> XO (XO (square p0))
    | XH -> XH

  (** val div2 : positive -> positive **)

  let div2 = function
    | XI p0 -> p0
    | XO p0 -> p0
    | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
    | XI p0 -> succ p0
    | XO p0 -> p0
    | XH -> XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
    | XI p0 -> S (size_nat p0)
    | XO p0 -> S (size_nat p0)
    | XH -> S O

  (** val size : positive -> positive **)

  let rec size = function
    | XI p0 -> succ (size p0)
    | XO p0 -> succ (size p0)
    | XH -> XH

  (** val compare_cont : positive -> positive -> comparison -> comparison **)

  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare x y =
    compare_cont x y Eq

  (** val min : positive -> positive -> positive **)

  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : positive -> positive -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)

  let sqrtrem_step f g = function
    | Pair (s, y) ->
      (match y with
       | IsPos r ->
         let s' = XI (XO s) in
         let r' = g (f r) in
         if leb s' r'
         then Pair ((XI s), (sub_mask r' s'))
         else Pair ((XO s), (IsPos r'))
       | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))

  (** val sqrtrem : positive -> (positive, mask) prod **)

  let rec sqrtrem = function
    | XI p0 ->
      (match p0 with
       | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
       | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
       | XH -> Pair (XH, (IsPos (XO XH))))
    | XO p0 ->
      (match p0 with
       | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
       | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
       | XH -> Pair (XH, (IsPos XH)))
    | XH -> Pair (XH, IsNul)

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n0 a b =
    match n0 with
    | O -> Pair (XH, (Pair (a, b)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n1 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
    | N0 -> Npos XH
    | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
    | N0 -> N0
    | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val shiftl_nat : positive -> nat -> positive **)

  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p

  (** val shiftr_nat : positive -> nat -> positive **)

  let shiftr_nat p n0 =
    nat_iter n0 div2 p

  (** val shiftl : positive -> n -> positive **)

  let shiftl p = function
    | N0 -> p
    | Npos n1 -> iter n1 (fun x -> XO x) p

  (** val shiftr : positive -> n -> positive **)

  let shiftr p = function
    | N0 -> p
    | Npos n1 -> iter n1 div2 p

  (** val testbit_nat : positive -> nat -> bool **)

  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op plus x (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
    | O -> XH
    | S x ->
      (match x with
       | O -> XH
       | S n1 -> succ (of_nat x))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
    | O -> XH
    | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)

  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)

  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let peano_rec =
    peano_rect

  type coq_PeanoView =
    | PeanoOne
    | PeanoSucc of positive * coq_PeanoView

  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rect f f0 p = function
    | PeanoOne -> f
    | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)

  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rec f f0 p = function
    | PeanoOne -> f
    | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)

  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xO p = function
    | PeanoOne -> PeanoSucc (XH, PeanoOne)
    | PeanoSucc (p0, q0) ->
      PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))

  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xI p = function
    | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
    | PeanoSucc (p0, q0) ->
      PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))

  (** val peanoView : positive -> coq_PeanoView **)

  let rec peanoView = function
    | XI p0 -> peanoView_xI p0 (peanoView p0)
    | XO p0 -> peanoView_xO p0 (peanoView p0)
    | XH -> PeanoOne

  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_iter a f p = function
    | PeanoOne -> a
    | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)

  (** val eqb_spec : positive -> positive -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val switch_Eq : comparison -> comparison -> comparison **)

  let switch_Eq c = function
    | Eq -> c
    | x -> x

  (** val mask2cmp : mask -> comparison **)

  let mask2cmp = function
    | IsNul -> Eq
    | IsPos p0 -> Gt
    | IsNeg -> Lt

  (** val leb_spec0 : positive -> positive -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : positive -> positive -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_Tac = 
  struct 

  end

  module Private_Dec = 
  struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : positive -> positive -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false

    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : positive -> positive -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
  end

  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : positive -> positive -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : positive -> positive -> bool **)

  let min_dec =
    Private_Dec.min_dec
end

module N = 
struct 
  type t = n

  (** val zero : n **)

  let zero =
    N0

  (** val one : n **)

  let one =
    Npos XH

  (** val two : n **)

  let two =
    Npos (XO XH)

  (** val succ_double : n -> n **)

  let succ_double = function
    | N0 -> Npos XH
    | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
    | N0 -> N0
    | Npos p -> Npos (XO p)

  (** val succ : n -> n **)

  let succ = function
    | N0 -> Npos XH
    | Npos p -> Npos (Coq_Pos.succ p)

  (** val pred : n -> n **)

  let pred = function
    | N0 -> N0
    | Npos p -> Coq_Pos.pred_N p

  (** val succ_pos : n -> positive **)

  let succ_pos = function
    | N0 -> XH
    | Npos p -> Coq_Pos.succ p

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')

  (** val eqb : n -> n -> bool **)

  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : n -> n -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val min : n -> n -> n **)

  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0

  (** val max : n -> n -> n **)

  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'

  (** val div2 : n -> n **)

  let div2 = function
    | N0 -> N0
    | Npos p0 ->
      (match p0 with
       | XI p -> Npos p
       | XO p -> Npos p
       | XH -> N0)

  (** val even : n -> bool **)

  let even = function
    | N0 -> true
    | Npos p ->
      (match p with
       | XO p0 -> true
       | _ -> false)

  (** val odd : n -> bool **)

  let odd n0 =
    negb (even n0)

  (** val pow : n -> n -> n **)

  let pow n0 = function
    | N0 -> Npos XH
    | Npos p0 ->
      (match n0 with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.pow q p0))

  (** val square : n -> n **)

  let square = function
    | N0 -> N0
    | Npos p -> Npos (Coq_Pos.square p)

  (** val log2 : n -> n **)

  let log2 = function
    | N0 -> N0
    | Npos p0 ->
      (match p0 with
       | XI p -> Npos (Coq_Pos.size p)
       | XO p -> Npos (Coq_Pos.size p)
       | XH -> N0)

  (** val size : n -> n **)

  let size = function
    | N0 -> N0
    | Npos p -> Npos (Coq_Pos.size p)

  (** val size_nat : n -> nat **)

  let size_nat = function
    | N0 -> O
    | Npos p -> Coq_Pos.size_nat p

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r'
      then Pair ((succ_double q), (sub r' b))
      else Pair ((double q), r')
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val div_eucl : n -> n -> (n, n) prod **)

  let div_eucl a b =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> Pair (N0, a)
       | Npos p -> pos_div_eucl na b)

  (** val div : n -> n -> n **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : n -> n -> n **)

  let modulo a b =
    snd (div_eucl a b)

  (** val gcd : n -> n -> n **)

  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))

  (** val ggcd : n -> n -> (n, (n, n) prod) prod **)

  let ggcd a b =
    match a with
    | N0 -> Pair (b, (Pair (N0, (Npos XH))))
    | Npos p ->
      (match b with
       | N0 -> Pair (a, (Pair ((Npos XH), N0)))
       | Npos q ->
         let Pair (g, p0) = Coq_Pos.ggcd p q in
         let Pair (aa, bb) = p0 in
         Pair ((Npos g), (Pair ((Npos aa), (Npos bb)))))

  (** val sqrtrem : n -> (n, n) prod **)

  let sqrtrem = function
    | N0 -> Pair (N0, N0)
    | Npos p ->
      let Pair (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> Pair ((Npos s), (Npos r))
       | _ -> Pair ((Npos s), N0))

  (** val sqrt : n -> n **)

  let sqrt = function
    | N0 -> N0
    | Npos p -> Npos (Coq_Pos.sqrt p)

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)

  (** val shiftl_nat : n -> nat -> n **)

  let shiftl_nat a n0 =
    nat_iter n0 double a

  (** val shiftr_nat : n -> nat -> n **)

  let shiftr_nat a n0 =
    nat_iter n0 div2 a

  (** val shiftl : n -> n -> n **)

  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)

  (** val shiftr : n -> n -> n **)

  let shiftr a = function
    | N0 -> a
    | Npos p -> Coq_Pos.iter p div2 a

  (** val testbit_nat : n -> nat -> bool **)

  let testbit_nat = function
    | N0 -> (fun x -> false)
    | Npos p -> Coq_Pos.testbit_nat p

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0

  (** val to_nat : n -> nat **)

  let to_nat = function
    | N0 -> O
    | Npos p -> Coq_Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
    | O -> N0
    | S n' -> Npos (Coq_Pos.of_succ_nat n')

  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x

  (** val eq_dec : n -> n -> bool **)

  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)

  (** val discr : n -> positive sumor **)

  let discr = function
    | N0 -> Inright
    | Npos p -> Inleft p

  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
         | XI p1 -> fS2' p1 (f p1)
         | XO p1 -> f2' p1 (f p1)
         | XH -> fS2 N0 f0
       in f p)

  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let binary_rec =
    binary_rect

  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)

  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let peano_rec =
    peano_rect

  (** val leb_spec0 : n -> n -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : n -> n -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_BootStrap = 
  struct 

  end

  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let recursion x =
    peano_rect x

  module Private_OrderTac = 
  struct 
    module IsTotal = 
    struct 

    end

    module Tac = 
    struct 

    end
  end

  module Private_NZPow = 
  struct 

  end

  module Private_NZSqrt = 
  struct 

  end

  (** val sqrt_up : n -> n **)

  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0

  (** val log2_up : n -> n **)

  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0

  module Private_NZDiv = 
  struct 

  end

  (** val lcm : n -> n -> n **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : n -> n -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> n **)

  let b2n = function
    | true -> Npos XH
    | false -> N0

  (** val setbit : n -> n -> n **)

  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)

  (** val clearbit : n -> n -> n **)

  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)

  (** val ones : n -> n **)

  let ones n0 =
    pred (shiftl (Npos XH) n0)

  (** val lnot : n -> n -> n **)

  let lnot a n0 =
    coq_lxor a (ones n0)

  module Private_Tac = 
  struct 

  end

  module Private_Dec = 
  struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : n -> n -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false

    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : n -> n -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
  end

  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : n -> n -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : n -> n -> bool **)

  let min_dec =
    Private_Dec.min_dec
end

module Z = 
struct 
  type t = z

  (** val zero : z **)

  let zero =
    Z0

  (** val one : z **)

  let one =
    Zpos XH

  (** val two : z **)

  let two =
    Zpos (XO XH)

  (** val double : z -> z **)

  let double = function
    | Z0 -> Z0
    | Zpos p -> Zpos (XO p)
    | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
    | Z0 -> Zpos XH
    | Zpos p -> Zpos (XI p)
    | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
    | Z0 -> Zneg XH
    | Zpos p -> Zpos (Coq_Pos.pred_double p)
    | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
    | Z0 -> Z0
    | Zpos x0 -> Zneg x0
    | Zneg x0 -> Zpos x0

  (** val succ : z -> z **)

  let succ x =
    add x (Zpos XH)

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 n0 =
    Coq_Pos.iter n0 (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
    | Z0 -> Zpos XH
    | Zpos p -> pow_pos x p
    | Zneg p -> Z0

  (** val square : z -> z **)

  let square = function
    | Z0 -> Z0
    | Zpos p -> Zpos (Coq_Pos.square p)
    | Zneg p -> Zpos (Coq_Pos.square p)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos y' -> Lt
       | Zneg y' -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
    | Z0 -> Z0
    | Zpos p -> Zpos XH
    | Zneg p -> Zneg XH

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val geb : z -> z -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos p ->
      (match y with
       | Zpos q -> Coq_Pos.eqb p q
       | _ -> false)
    | Zneg p ->
      (match y with
       | Zneg q -> Coq_Pos.eqb p q
       | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val min : z -> z -> z **)

  let min n0 m =
    match compare n0 m with
    | Gt -> m
    | _ -> n0

  (** val abs : z -> z **)

  let abs = function
    | Zneg p -> Zpos p
    | x -> x

  (** val abs_nat : z -> nat **)

  let abs_nat = function
    | Z0 -> O
    | Zpos p -> Coq_Pos.to_nat p
    | Zneg p -> Coq_Pos.to_nat p

  (** val abs_N : z -> n **)

  let abs_N = function
    | Z0 -> N0
    | Zpos p -> Npos p
    | Zneg p -> Npos p

  (** val to_nat : z -> nat **)

  let to_nat = function
    | Zpos p -> Coq_Pos.to_nat p
    | _ -> O

  (** val to_N : z -> n **)

  let to_N = function
    | Zpos p -> Npos p
    | _ -> N0

  (** val of_nat : nat -> z **)

  let of_nat = function
    | O -> Z0
    | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
    | N0 -> Z0
    | Npos p -> Zpos p

  (** val to_pos : z -> positive **)

  let to_pos = function
    | Zpos p -> p
    | _ -> XH

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter p f x
    | _ -> x

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH ->
      if leb (Zpos (XO XH)) b
      then Pair (Z0, (Zpos XH))
      else Pair ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos p -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos p ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, x) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (x, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val even : z -> bool **)

  let even = function
    | Z0 -> true
    | Zpos p ->
      (match p with
       | XO p0 -> true
       | _ -> false)
    | Zneg p ->
      (match p with
       | XO p0 -> true
       | _ -> false)

  (** val odd : z -> bool **)

  let odd = function
    | Z0 -> false
    | Zpos p ->
      (match p with
       | XO p0 -> false
       | _ -> true)
    | Zneg p ->
      (match p with
       | XO p0 -> false
       | _ -> true)

  (** val div2 : z -> z **)

  let div2 = function
    | Z0 -> Z0
    | Zpos p ->
      (match p with
       | XH -> Z0
       | _ -> Zpos (Coq_Pos.div2 p))
    | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val quot2 : z -> z **)

  let quot2 = function
    | Z0 -> Z0
    | Zpos p ->
      (match p with
       | XH -> Z0
       | _ -> Zpos (Coq_Pos.div2 p))
    | Zneg p ->
      (match p with
       | XH -> Z0
       | _ -> Zneg (Coq_Pos.div2 p))

  (** val log2 : z -> z **)

  let log2 = function
    | Zpos p0 ->
      (match p0 with
       | XI p -> Zpos (Coq_Pos.size p)
       | XO p -> Zpos (Coq_Pos.size p)
       | XH -> Z0)
    | _ -> Z0

  (** val sqrtrem : z -> (z, z) prod **)

  let sqrtrem = function
    | Zpos p ->
      let Pair (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> Pair ((Zpos s), (Zpos r))
       | _ -> Pair ((Zpos s), Z0))
    | _ -> Pair (Z0, Z0)

  (** val sqrt : z -> z **)

  let sqrt = function
    | Zpos p -> Zpos (Coq_Pos.sqrt p)
    | _ -> Z0

  (** val gcd : z -> z -> z **)

  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))

  (** val testbit : z -> z -> bool **)

  let testbit a = function
    | Z0 -> odd a
    | Zpos p ->
      (match a with
       | Z0 -> false
       | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
       | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
    | Zneg p -> false

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
    | Z0 -> a
    | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
    | Zneg p -> Coq_Pos.iter p div2 a

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val ldiff : z -> z -> z **)

  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)

  module Private_BootStrap = 
  struct 

  end

  (** val leb_spec0 : z -> z -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : z -> z -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac = 
  struct 
    module IsTotal = 
    struct 

    end

    module Tac = 
    struct 

    end
  end

  (** val sqrt_up : z -> z **)

  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0

  (** val log2_up : z -> z **)

  let log2_up a =
    match compare (Zpos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0

  module Private_NZDiv = 
  struct 

  end

  module Private_Div = 
  struct 
    module Quot2Div = 
    struct 
      (** val div : z -> z -> z **)

      let div =
        quot

      (** val modulo : z -> z -> z **)

      let modulo =
        rem
    end

    module NZQuot = 
    struct 

    end
  end

  (** val lcm : z -> z -> z **)

  let lcm a b =
    abs (mul a (div b (gcd a b)))

  (** val eqb_spec : z -> z -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2z : bool -> z **)

  let b2z = function
    | true -> Zpos XH
    | false -> Z0

  (** val setbit : z -> z -> z **)

  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)

  (** val clearbit : z -> z -> z **)

  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)

  (** val lnot : z -> z **)

  let lnot a =
    pred (opp a)

  (** val ones : z -> z **)

  let ones n0 =
    pred (shiftl (Zpos XH) n0)

  module Private_Tac = 
  struct 

  end

  module Private_Dec = 
  struct 
    (** val max_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : z -> z -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false

    (** val min_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : z -> z -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
  end

  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : z -> z -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : z -> z -> bool **)

  let min_dec =
    Private_Dec.min_dec
end

(** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

let rec divmod x y q u =
  match x with
  | O -> Pair (q, u)
  | S x' ->
    (match u with
     | O -> divmod x' y (S q) y
     | S u' -> divmod x' y q u')

(** val div0 : nat -> nat -> nat **)

let div0 x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

(** val modulo0 : nat -> nat -> nat **)

let modulo0 x y = match y with
  | O -> y
  | S y' -> minus y' (snd (divmod x y' O y'))

(** val z_le_dec : z -> z -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

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

module Three_Val_NoneError = 
struct 
  type coq_Val_Impl =
    | VTrue
    | VFalse
    | VError

  (** val coq_Val_Impl_rect : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1 **)

  let coq_Val_Impl_rect f f0 f1 = function
    | VTrue -> f
    | VFalse -> f0
    | VError -> f1

  (** val coq_Val_Impl_rec : 'a1 -> 'a1 -> 'a1 -> coq_Val_Impl -> 'a1 **)

  let coq_Val_Impl_rec f f0 f1 = function
    | VTrue -> f
    | VFalse -> f0
    | VError -> f1

  type coq_Val = coq_Val_Impl

  (** val val_eq_dec : coq_Val -> coq_Val -> bool **)

  let val_eq_dec v1 v2 =
    match v1 with
    | VTrue ->
      (match v2 with
       | VTrue -> true
       | _ -> false)
    | VFalse ->
      (match v2 with
       | VFalse -> true
       | _ -> false)
    | VError ->
      (match v2 with
       | VError -> true
       | _ -> false)

  (** val coq_Top : coq_Val_Impl **)

  let coq_Top =
    VTrue

  (** val coq_Btm : coq_Val_Impl **)

  let coq_Btm =
    VFalse

  (** val truth_not : coq_Val_Impl -> coq_Val_Impl **)

  let truth_not = function
    | VTrue -> VFalse
    | VFalse -> VTrue
    | VError -> VError

  (** val truth_and : coq_Val -> coq_Val -> coq_Val_Impl **)

  let truth_and v1 v2 =
    match v1 with
    | VTrue -> v2
    | VFalse ->
      (match v2 with
       | VError -> VError
       | _ -> VFalse)
    | VError -> VError

  (** val truth_or : coq_Val -> coq_Val -> coq_Val_Impl **)

  let truth_or v1 v2 =
    match v1 with
    | VTrue ->
      (match v2 with
       | VError -> VError
       | _ -> VTrue)
    | VFalse -> v2
    | VError -> VError
end

module type NUMBER = 
sig 
  type coq_A 

  val coq_Const0 : coq_A

  val num_eq_dec : coq_A -> coq_A -> bool

  val num_neg : coq_A -> coq_A

  val num_plus : coq_A -> coq_A -> coq_A
end

module ZInfinity = 
struct 
  type coq_ZE =
    | ZE_Fin of z
    | ZE_Inf
    | ZE_NegInf

  (** val coq_ZE_rect : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)

  let coq_ZE_rect f f0 f1 = function
    | ZE_Fin x -> f x
    | ZE_Inf -> f0
    | ZE_NegInf -> f1

  (** val coq_ZE_rec : (z -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)

  let coq_ZE_rec f f0 f1 = function
    | ZE_Fin x -> f x
    | ZE_Inf -> f0
    | ZE_NegInf -> f1

  (** val coq_ZE_eq_dec : coq_ZE -> coq_ZE -> bool **)

  let coq_ZE_eq_dec ze1 ze2 =
    match ze1 with
    | ZE_Fin z0 ->
      (match ze2 with
       | ZE_Fin z1 -> Z.eq_dec z0 z1
       | _ -> false)
    | ZE_Inf ->
      (match ze2 with
       | ZE_Inf -> true
       | _ -> false)
    | ZE_NegInf ->
      (match ze2 with
       | ZE_NegInf -> true
       | _ -> false)

  (** val coq_ZEneg : coq_ZE -> coq_ZE **)

  let coq_ZEneg = function
    | ZE_Fin z0 -> ZE_Fin (Z.opp z0)
    | ZE_Inf -> ZE_NegInf
    | ZE_NegInf -> ZE_Inf

  type coq_A = coq_ZE option

  (** val coq_Const0 : coq_ZE option **)

  let coq_Const0 =
    Some (ZE_Fin Z0)

  (** val num_eq_dec : coq_A -> coq_A -> bool **)

  let num_eq_dec n1 n2 =
    match n1 with
    | Some z0 ->
      (match n2 with
       | Some z1 -> coq_ZE_eq_dec z0 z1
       | None -> false)
    | None ->
      (match n2 with
       | Some z0 -> false
       | None -> true)

  (** val num_neg : coq_ZE option -> coq_ZE option **)

  let num_neg =
    option_map coq_ZEneg

  (** val num_plus : coq_ZE option -> coq_ZE option -> coq_ZE option **)

  let num_plus ze1 ze2 =
    match ze1 with
    | Some z0 ->
      (match z0 with
       | ZE_Fin z1 ->
         (match ze2 with
          | Some z2 ->
            (match z2 with
             | ZE_Fin z3 -> Some (ZE_Fin (Z.add z1 z3))
             | x -> Some x)
          | None -> None)
       | ZE_Inf ->
         (match ze2 with
          | Some z1 ->
            (match z1 with
             | ZE_NegInf -> None
             | _ -> Some ZE_Inf)
          | None -> None)
       | ZE_NegInf ->
         (match ze2 with
          | Some z1 ->
            (match z1 with
             | ZE_Inf -> None
             | _ -> Some ZE_NegInf)
          | None -> None))
    | None -> None
end

module ZNumLattice = 
struct 
  type coq_A = z

  (** val coq_Const0 : z **)

  let coq_Const0 =
    Z0

  (** val num_eq_dec : z -> z -> bool **)

  let num_eq_dec =
    Z.eq_dec

  (** val num_neg : coq_A -> z **)

  let num_neg x =
    Z.sub Z0 x

  (** val num_plus : coq_A -> coq_A -> z **)

  let num_plus x y =
    Z.add x y
end

module FinLeqRelation = 
  functor (VAL:SEM_VAL) ->
  struct 
    (** val num_leq : ZNumLattice.coq_A -> ZNumLattice.coq_A -> VAL.coq_Val **)

    let num_leq x y =
      if z_le_dec x y then VAL.coq_Top else VAL.coq_Btm
  end

module NoneError3ValRel = 
struct 
  (** val noneVal : Three_Val_NoneError.coq_Val_Impl **)

  let noneVal =
    Three_Val_NoneError.VError
end

module InfLeqRelation = 
  functor (VAL:SEM_VAL) ->
  functor (S:sig 
             val noneVal : VAL.coq_Val
           end) ->
  struct 
    (** val num_leq : ZInfinity.coq_A -> ZInfinity.coq_A -> VAL.coq_Val **)

    let num_leq ze1 ze2 =
      match ze1 with
      | Some x ->
        (match x with
         | ZInfinity.ZE_Fin z1 ->
           (match ze2 with
            | Some z0 ->
              (match z0 with
               | ZInfinity.ZE_Fin z2 ->
                 if z_le_dec z1 z2 then VAL.coq_Top else VAL.coq_Btm
               | ZInfinity.ZE_Inf -> VAL.coq_Top
               | ZInfinity.ZE_NegInf ->
                 if ZInfinity.coq_ZE_eq_dec x ZInfinity.ZE_NegInf
                 then VAL.coq_Top
                 else VAL.coq_Btm)
            | None -> S.noneVal)
         | ZInfinity.ZE_Inf ->
           (match ze2 with
            | Some x0 ->
              (match x0 with
               | ZInfinity.ZE_Inf -> VAL.coq_Top
               | _ ->
                 if ZInfinity.coq_ZE_eq_dec x0 ZInfinity.ZE_Inf
                 then VAL.coq_Top
                 else VAL.coq_Btm)
            | None -> S.noneVal)
         | ZInfinity.ZE_NegInf ->
           (match ze2 with
            | Some z0 -> VAL.coq_Top
            | None -> S.noneVal))
      | None -> S.noneVal
  end

module type SEMANTICS_INPUT = 
sig 
  module N : 
    NUMBER

  type coq_Q 

  type coq_QT 

  val conv : coq_Q -> coq_QT -> N.coq_A
end

module PureInfinity = 
struct 
  module N = ZInfinity

  type coq_AQ =
    | Q_Z
    | Q_ZE

  (** val coq_AQ_rect : 'a1 -> 'a1 -> coq_AQ -> 'a1 **)

  let coq_AQ_rect f f0 = function
    | Q_Z -> f
    | Q_ZE -> f0

  (** val coq_AQ_rec : 'a1 -> 'a1 -> coq_AQ -> 'a1 **)

  let coq_AQ_rec f f0 = function
    | Q_Z -> f
    | Q_ZE -> f0

  type coq_Q = coq_AQ

  type coq_QT = __

  (** val conv : coq_Q -> coq_QT -> N.coq_A **)

  let conv q x =
    match q with
    | Q_Z -> Some (N.ZE_Fin (Obj.magic x))
    | Q_ZE -> Some (Obj.magic x)
end

module PureInt = 
struct 
  module N = ZNumLattice

  type coq_Q = unit0

  type coq_QT = z

  (** val conv : coq_Q -> coq_QT -> coq_QT **)

  let conv q x =
    x
end

module IntToInfinity = 
struct 
  module N = ZInfinity

  type coq_Q = unit0

  type coq_QT = z

  (** val conv : coq_Q -> coq_QT -> N.coq_ZE option **)

  let conv q x =
    Some (N.ZE_Fin x)
end

module type ZERO_FIN = 
sig 
  val zero_times : ZNumLattice.coq_A -> ZNumLattice.coq_A
end

module FinZero = 
struct 
  (** val zero_times : ZNumLattice.coq_A -> z **)

  let zero_times x =
    Z0
end

module type ZERO_INF = 
sig 
  val zero_times : ZInfinity.coq_A -> ZInfinity.coq_A
end

module InfZeroAll = 
struct 
  (** val zero_times : ZInfinity.coq_A -> ZInfinity.coq_ZE option **)

  let zero_times x =
    Some (ZInfinity.ZE_Fin Z0)
end

module ArithSemantics = 
  functor (I:SEMANTICS_INPUT) ->
  functor (V:VARIABLE) ->
  functor (VAL:SEM_VAL) ->
  functor (L:sig 
             val num_leq : I.N.coq_A -> I.N.coq_A -> VAL.coq_Val
           end) ->
  functor (ZT:sig 
             val zero_times : I.N.coq_A -> I.N.coq_A
           end) ->
  struct 
    type coq_ZExp =
      | ZExp_Var of V.var
      | ZExp_Const of I.N.coq_A
      | ZExp_Add of coq_ZExp * coq_ZExp
      | ZExp_Inv of coq_ZExp
      | ZExp_Sub of coq_ZExp * coq_ZExp
      | ZExp_Mult of z * coq_ZExp

    (** val coq_ZExp_rect :
        (V.var -> 'a1) -> (I.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp ->
        'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp
        -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp -> 'a1 **)

    let rec coq_ZExp_rect f f0 f1 f2 f3 f4 = function
      | ZExp_Var v -> f v
      | ZExp_Const a -> f0 a
      | ZExp_Add (z1, z2) ->
        f1 z1 (coq_ZExp_rect f f0 f1 f2 f3 f4 z1) z2
          (coq_ZExp_rect f f0 f1 f2 f3 f4 z2)
      | ZExp_Inv z1 -> f2 z1 (coq_ZExp_rect f f0 f1 f2 f3 f4 z1)
      | ZExp_Sub (z1, z2) ->
        f3 z1 (coq_ZExp_rect f f0 f1 f2 f3 f4 z1) z2
          (coq_ZExp_rect f f0 f1 f2 f3 f4 z2)
      | ZExp_Mult (z1, z2) -> f4 z1 z2 (coq_ZExp_rect f f0 f1 f2 f3 f4 z2)

    (** val coq_ZExp_rec :
        (V.var -> 'a1) -> (I.N.coq_A -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp ->
        'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> 'a1) -> (coq_ZExp -> 'a1 -> coq_ZExp
        -> 'a1 -> 'a1) -> (z -> coq_ZExp -> 'a1 -> 'a1) -> coq_ZExp -> 'a1 **)

    let rec coq_ZExp_rec f f0 f1 f2 f3 f4 = function
      | ZExp_Var v -> f v
      | ZExp_Const a -> f0 a
      | ZExp_Add (z1, z2) ->
        f1 z1 (coq_ZExp_rec f f0 f1 f2 f3 f4 z1) z2
          (coq_ZExp_rec f f0 f1 f2 f3 f4 z2)
      | ZExp_Inv z1 -> f2 z1 (coq_ZExp_rec f f0 f1 f2 f3 f4 z1)
      | ZExp_Sub (z1, z2) ->
        f3 z1 (coq_ZExp_rec f f0 f1 f2 f3 f4 z1) z2
          (coq_ZExp_rec f f0 f1 f2 f3 f4 z2)
      | ZExp_Mult (z1, z2) -> f4 z1 z2 (coq_ZExp_rec f f0 f1 f2 f3 f4 z2)

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

    (** val coq_ZBF_rect :
        (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
        'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1 **)

    let coq_ZBF_rect f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | ZBF_Const x -> f x
      | ZBF_Lt (x, x0) -> f0 x x0
      | ZBF_Lte (x, x0) -> f1 x x0
      | ZBF_Gt (x, x0) -> f2 x x0
      | ZBF_Gte (x, x0) -> f3 x x0
      | ZBF_Eq (x, x0) -> f4 x x0
      | ZBF_Eq_Max (x, x0, x1) -> f5 x x0 x1
      | ZBF_Eq_Min (x, x0, x1) -> f6 x x0 x1
      | ZBF_Neq (x, x0) -> f7 x x0

    (** val coq_ZBF_rec :
        (VAL.coq_Val -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp ->
        coq_ZExp -> coq_ZExp -> 'a1) -> (coq_ZExp -> coq_ZExp -> coq_ZExp ->
        'a1) -> (coq_ZExp -> coq_ZExp -> 'a1) -> coq_ZBF -> 'a1 **)

    let coq_ZBF_rec f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | ZBF_Const x -> f x
      | ZBF_Lt (x, x0) -> f0 x x0
      | ZBF_Lte (x, x0) -> f1 x x0
      | ZBF_Gt (x, x0) -> f2 x x0
      | ZBF_Gte (x, x0) -> f3 x x0
      | ZBF_Eq (x, x0) -> f4 x x0
      | ZBF_Eq_Max (x, x0, x1) -> f5 x x0 x1
      | ZBF_Eq_Min (x, x0, x1) -> f6 x x0 x1
      | ZBF_Neq (x, x0) -> f7 x x0

    type coq_ZF =
      | ZF_BF of coq_ZBF
      | ZF_And of coq_ZF * coq_ZF
      | ZF_Or of coq_ZF * coq_ZF
      | ZF_Imp of coq_ZF * coq_ZF
      | ZF_Not of coq_ZF
      | ZF_Forall of V.var * I.coq_Q * coq_ZF
      | ZF_Exists of V.var * I.coq_Q * coq_ZF

    (** val coq_ZF_rect :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
        -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
        'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 ->
        'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1 **)

    let rec coq_ZF_rect f f0 f1 f2 f3 f4 f5 = function
      | ZF_BF z1 -> f z1
      | ZF_And (z1, z2) ->
        f0 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Or (z1, z2) ->
        f1 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Imp (z1, z2) ->
        f2 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Not z1 -> f3 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1)
      | ZF_Forall (v, q, z1) -> f4 v q z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1)
      | ZF_Exists (v, q, z1) -> f5 v q z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 z1)

    (** val coq_ZF_rec :
        (coq_ZBF -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF
        -> 'a1 -> coq_ZF -> 'a1 -> 'a1) -> (coq_ZF -> 'a1 -> coq_ZF -> 'a1 ->
        'a1) -> (coq_ZF -> 'a1 -> 'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 ->
        'a1) -> (V.var -> I.coq_Q -> coq_ZF -> 'a1 -> 'a1) -> coq_ZF -> 'a1 **)

    let rec coq_ZF_rec f f0 f1 f2 f3 f4 f5 = function
      | ZF_BF z1 -> f z1
      | ZF_And (z1, z2) ->
        f0 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Or (z1, z2) ->
        f1 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Imp (z1, z2) ->
        f2 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1) z2
          (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z2)
      | ZF_Not z1 -> f3 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1)
      | ZF_Forall (v, q, z1) -> f4 v q z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1)
      | ZF_Exists (v, q, z1) -> f5 v q z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 z1)

    (** val num_mult_nat : nat -> I.N.coq_A -> I.N.coq_A **)

    let rec num_mult_nat n0 x =
      match n0 with
      | O -> ZT.zero_times x
      | S n1 ->
        (match n1 with
         | O -> x
         | S n2 -> I.N.num_plus x (num_mult_nat n1 x))

    (** val num_mult : z -> I.N.coq_A -> I.N.coq_A **)

    let num_mult z0 exp =
      match z0 with
      | Z0 -> ZT.zero_times exp
      | Zpos x -> num_mult_nat (Coq_Pos.to_nat x) exp
      | Zneg x -> I.N.num_neg (num_mult_nat (Coq_Pos.to_nat x) exp)

    (** val subst_exp : (V.var, I.N.coq_A) prod -> coq_ZExp -> coq_ZExp **)

    let rec subst_exp p exp = match exp with
      | ZExp_Var v -> if V.var_eq_dec (fst p) v then ZExp_Const (snd p) else exp
      | ZExp_Const a -> exp
      | ZExp_Add (e1, e2) -> ZExp_Add ((subst_exp p e1), (subst_exp p e2))
      | ZExp_Inv e -> ZExp_Inv (subst_exp p e)
      | ZExp_Sub (e1, e2) -> ZExp_Sub ((subst_exp p e1), (subst_exp p e2))
      | ZExp_Mult (n0, e) -> ZExp_Mult (n0, (subst_exp p e))

    (** val subst_bf : (V.var, I.N.coq_A) prod -> coq_ZBF -> coq_ZBF **)

    let rec subst_bf p bf = match bf with
      | ZBF_Const v -> bf
      | ZBF_Lt (e1, e2) -> ZBF_Lt ((subst_exp p e1), (subst_exp p e2))
      | ZBF_Lte (e1, e2) -> ZBF_Lte ((subst_exp p e1), (subst_exp p e2))
      | ZBF_Gt (e1, e2) -> ZBF_Gt ((subst_exp p e1), (subst_exp p e2))
      | ZBF_Gte (e1, e2) -> ZBF_Gte ((subst_exp p e1), (subst_exp p e2))
      | ZBF_Eq (e1, e2) -> ZBF_Eq ((subst_exp p e1), (subst_exp p e2))
      | ZBF_Eq_Max (e1, e2, e3) ->
        ZBF_Eq_Max ((subst_exp p e1), (subst_exp p e2), (subst_exp p e3))
      | ZBF_Eq_Min (e1, e2, e3) ->
        ZBF_Eq_Min ((subst_exp p e1), (subst_exp p e2), (subst_exp p e3))
      | ZBF_Neq (e1, e2) -> ZBF_Neq ((subst_exp p e1), (subst_exp p e2))

    (** val substitute : (V.var, I.N.coq_A) prod -> coq_ZF -> coq_ZF **)

    let rec substitute p form = match form with
      | ZF_BF bf -> ZF_BF (subst_bf p bf)
      | ZF_And (f1, f2) -> ZF_And ((substitute p f1), (substitute p f2))
      | ZF_Or (f1, f2) -> ZF_Or ((substitute p f1), (substitute p f2))
      | ZF_Imp (f1, f2) -> ZF_Imp ((substitute p f1), (substitute p f2))
      | ZF_Not f -> ZF_Not (substitute p f)
      | ZF_Forall (v, q, f) ->
        if V.var_eq_dec (fst p) v
        then form
        else ZF_Forall (v, q, (substitute p f))
      | ZF_Exists (v, q, f) ->
        if V.var_eq_dec (fst p) v
        then form
        else ZF_Exists (v, q, (substitute p f))

    (** val dexp2ZE : coq_ZExp -> I.N.coq_A **)

    let rec dexp2ZE = function
      | ZExp_Var v -> I.N.coq_Const0
      | ZExp_Const z0 -> z0
      | ZExp_Add (e1, e2) -> I.N.num_plus (dexp2ZE e1) (dexp2ZE e2)
      | ZExp_Inv e -> I.N.num_neg (dexp2ZE e)
      | ZExp_Sub (e1, e2) -> I.N.num_plus (dexp2ZE e1) (I.N.num_neg (dexp2ZE e2))
      | ZExp_Mult (z0, e) -> num_mult z0 (dexp2ZE e)

    (** val dzbf2bool : coq_ZBF -> VAL.coq_Val **)

    let rec dzbf2bool = function
      | ZBF_Const b -> b
      | ZBF_Lt (e1, e2) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in
        VAL.truth_and (L.num_leq v1 v2) (VAL.truth_not (L.num_leq v2 v1))
      | ZBF_Lte (e1, e2) -> L.num_leq (dexp2ZE e1) (dexp2ZE e2)
      | ZBF_Gt (e1, e2) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in
        VAL.truth_and (L.num_leq v2 v1) (VAL.truth_not (L.num_leq v1 v2))
      | ZBF_Gte (e1, e2) -> L.num_leq (dexp2ZE e2) (dexp2ZE e1)
      | ZBF_Eq (e1, e2) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in VAL.truth_and (L.num_leq v1 v2) (L.num_leq v2 v1)
      | ZBF_Eq_Max (e1, e2, e3) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in
        let v3 = dexp2ZE e3 in
        VAL.truth_or
          (VAL.truth_and (L.num_leq v3 v2)
             (VAL.truth_and (L.num_leq v1 v2) (L.num_leq v2 v1)))
          (VAL.truth_and (L.num_leq v2 v3)
             (VAL.truth_and (L.num_leq v1 v3) (L.num_leq v3 v1)))
      | ZBF_Eq_Min (e1, e2, e3) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in
        let v3 = dexp2ZE e3 in
        VAL.truth_or
          (VAL.truth_and (L.num_leq v3 v2)
             (VAL.truth_and (L.num_leq v1 v3) (L.num_leq v3 v1)))
          (VAL.truth_and (L.num_leq v2 v3)
             (VAL.truth_and (L.num_leq v1 v2) (L.num_leq v2 v1)))
      | ZBF_Neq (e1, e2) ->
        let v1 = dexp2ZE e1 in
        let v2 = dexp2ZE e2 in
        VAL.truth_not (VAL.truth_and (L.num_leq v1 v2) (L.num_leq v2 v1))

    (** val length_zform : coq_ZF -> nat **)

    let rec length_zform = function
      | ZF_BF z0 -> S O
      | ZF_And (f1, f2) -> S (plus (length_zform f1) (length_zform f2))
      | ZF_Or (f1, f2) -> S (plus (length_zform f1) (length_zform f2))
      | ZF_Imp (f1, f2) -> S (plus (length_zform f1) (length_zform f2))
      | ZF_Not f -> S (length_zform f)
      | ZF_Forall (v, q, f) -> S (length_zform f)
      | ZF_Exists (v, q, f) -> S (length_zform f)

    type coq_Input =
      | Sat of coq_ZF
      | DisSat of coq_ZF
      | Udtmd of coq_ZF

    (** val coq_Input_rect :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1 **)

    let coq_Input_rect f f0 f1 = function
      | Sat x -> f x
      | DisSat x -> f0 x
      | Udtmd x -> f1 x

    (** val coq_Input_rec :
        (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> (coq_ZF -> 'a1) -> coq_Input ->
        'a1 **)

    let coq_Input_rec f f0 f1 = function
      | Sat x -> f x
      | DisSat x -> f0 x
      | Udtmd x -> f1 x

    (** val length_input : coq_Input -> nat **)

    let length_input = function
      | Sat f -> length_zform f
      | DisSat f -> length_zform f
      | Udtmd f -> length_zform f

    (** val eliminateMinMax : coq_ZBF -> coq_ZF **)

    let eliminateMinMax bf = match bf with
      | ZBF_Eq_Max (e1, e2, e3) ->
        ZF_Or ((ZF_And ((ZF_BF (ZBF_Eq (e1, e2))), (ZF_BF (ZBF_Lte (e3, e2))))),
               (ZF_And ((ZF_BF (ZBF_Eq (e1, e3))), (ZF_BF (ZBF_Lte (e2, e3))))))
      | ZBF_Eq_Min (e1, e2, e3) ->
        ZF_Or ((ZF_And ((ZF_BF (ZBF_Eq (e1, e2))), (ZF_BF (ZBF_Lte (e2, e3))))),
               (ZF_And ((ZF_BF (ZBF_Eq (e1, e3))), (ZF_BF (ZBF_Lte (e3, e2))))))
      | _ -> ZF_BF bf
  end

module InfSolver = 
  functor (Coq_sv:VARIABLE) ->
  functor (VAL:SEM_VAL) ->
  functor (S:sig 
             val noneVal : VAL.coq_Val
           end) ->
  functor (FZT:ZERO_FIN) ->
  functor (IZT:ZERO_INF) ->
  struct 
    module InfRel = InfLeqRelation(VAL)(S)

    module FinRel = FinLeqRelation(VAL)

    module IA = ArithSemantics(PureInfinity)(Coq_sv)(VAL)(InfRel)(IZT)

    module FA = ArithSemantics(PureInt)(Coq_sv)(VAL)(FinRel)(FZT)

    module I2F = ArithSemantics(IntToInfinity)(Coq_sv)(VAL)(InfRel)(IZT)

    (** val inf_trans_exp : IA.coq_ZExp -> I2F.coq_ZExp **)

    let rec inf_trans_exp = function
      | IA.ZExp_Var v -> I2F.ZExp_Var v
      | IA.ZExp_Const a -> I2F.ZExp_Const (Obj.magic a)
      | IA.ZExp_Add (e1, e2) ->
        I2F.ZExp_Add ((inf_trans_exp e1), (inf_trans_exp e2))
      | IA.ZExp_Inv e -> I2F.ZExp_Inv (inf_trans_exp e)
      | IA.ZExp_Sub (e1, e2) ->
        I2F.ZExp_Sub ((inf_trans_exp e1), (inf_trans_exp e2))
      | IA.ZExp_Mult (z0, e) -> I2F.ZExp_Mult (z0, (inf_trans_exp e))

    (** val inf_trans_bf : IA.coq_ZBF -> I2F.coq_ZBF **)

    let inf_trans_bf = function
      | IA.ZBF_Const b -> I2F.ZBF_Const b
      | IA.ZBF_Lt (f1, f2) -> I2F.ZBF_Lt ((inf_trans_exp f1), (inf_trans_exp f2))
      | IA.ZBF_Lte (f1, f2) ->
        I2F.ZBF_Lte ((inf_trans_exp f1), (inf_trans_exp f2))
      | IA.ZBF_Gt (f1, f2) -> I2F.ZBF_Gt ((inf_trans_exp f1), (inf_trans_exp f2))
      | IA.ZBF_Gte (f1, f2) ->
        I2F.ZBF_Gte ((inf_trans_exp f1), (inf_trans_exp f2))
      | IA.ZBF_Eq (f1, f2) -> I2F.ZBF_Eq ((inf_trans_exp f1), (inf_trans_exp f2))
      | IA.ZBF_Eq_Max (f1, f2, f3) ->
        I2F.ZBF_Eq_Max ((inf_trans_exp f1), (inf_trans_exp f2),
                        (inf_trans_exp f3))
      | IA.ZBF_Eq_Min (f1, f2, f3) ->
        I2F.ZBF_Eq_Min ((inf_trans_exp f1), (inf_trans_exp f2),
                        (inf_trans_exp f3))
      | IA.ZBF_Neq (f1, f2) ->
        I2F.ZBF_Neq ((inf_trans_exp f1), (inf_trans_exp f2))

    (** val inf_trans : IA.coq_ZF -> I2F.coq_ZF **)

    let rec inf_trans x =
      let x0 = fun y -> inf_trans y in
      (match x with
       | IA.ZF_BF bf -> I2F.ZF_BF (inf_trans_bf bf)
       | IA.ZF_And (f1, f2) -> I2F.ZF_And ((x0 f1), (x0 f2))
       | IA.ZF_Or (f1, f2) -> I2F.ZF_Or ((x0 f1), (x0 f2))
       | IA.ZF_Imp (f1, f2) -> I2F.ZF_Imp ((x0 f1), (x0 f2))
       | IA.ZF_Not f' -> I2F.ZF_Not (x0 f')
       | IA.ZF_Forall (v, q, f') ->
         (match q with
          | PureInfinity.Q_Z -> I2F.ZF_Forall (v, Tt, (x0 f'))
          | PureInfinity.Q_ZE ->
            I2F.ZF_And ((I2F.ZF_Forall (v, Tt, (x0 f'))), (I2F.ZF_And
                                                             ((x0
                                                                 (IA.substitute (Pair (v, (Some (Obj.magic ZInfinity.ZE_Inf))))
                                                                    f')),
                                                              (x0
                                                                 (IA.substitute (Pair (v, (Some
                                                                                             (Obj.magic ZInfinity.ZE_NegInf)))) f'))))))
       | IA.ZF_Exists (v, q, f') ->
         (match q with
          | PureInfinity.Q_Z -> I2F.ZF_Exists (v, Tt, (x0 f'))
          | PureInfinity.Q_ZE ->
            I2F.ZF_Or ((I2F.ZF_Exists (v, Tt, (x0 f'))), (I2F.ZF_Or
                                                            ((x0
                                                                (IA.substitute (Pair (v, (Some (Obj.magic ZInfinity.ZE_Inf))))
                                                                   f')),
                                                             (x0
                                                                (IA.substitute (Pair (v, (Some
                                                                                            (Obj.magic ZInfinity.ZE_NegInf)))) f')))))))

    (** val embed : VAL.coq_Val -> FA.coq_ZF **)

    let embed v =
      FA.ZF_BF (FA.ZBF_Const v)

    (** val coq_FATrue : FA.coq_ZF **)

    let coq_FATrue =
      embed VAL.coq_Top

    (** val coq_FAFalse : FA.coq_ZF **)

    let coq_FAFalse =
      embed VAL.coq_Btm

    (** val coq_FANone : FA.coq_ZF **)

    let coq_FANone =
      embed S.noneVal

    (** val proj : IntToInfinity.N.coq_A -> z **)

    let proj = function
      | Some z1 ->
        (match z1 with
         | IntToInfinity.N.ZE_Fin x -> x
         | _ -> Z0)
      | None -> Z0

    (** val int_trans_exp : I2F.coq_ZExp -> FA.coq_ZExp **)

    let rec int_trans_exp = function
      | I2F.ZExp_Var v -> FA.ZExp_Var v
      | I2F.ZExp_Const a -> FA.ZExp_Const (proj a)
      | I2F.ZExp_Add (e1, e2) ->
        FA.ZExp_Add ((int_trans_exp e1), (int_trans_exp e2))
      | I2F.ZExp_Inv e -> FA.ZExp_Inv (int_trans_exp e)
      | I2F.ZExp_Sub (e1, e2) ->
        FA.ZExp_Sub ((int_trans_exp e1), (int_trans_exp e2))
      | I2F.ZExp_Mult (z0, e) -> FA.ZExp_Mult (z0, (int_trans_exp e))

    (** val int_trans_bf : I2F.coq_ZBF -> FA.coq_ZF **)

    let int_trans_bf = function
      | I2F.ZBF_Const f -> FA.ZF_BF (FA.ZBF_Const f)
      | I2F.ZBF_Lt (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Lt ((int_trans_exp e1), (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FAFalse
                    else coq_FATrue
                  | IntToInfinity.N.ZE_NegInf -> coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some z0 ->
                 (match z0 with
                  | IntToInfinity.N.ZE_Inf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FAFalse
                    else coq_FATrue
                  | _ -> coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_NegInf
                 then coq_FAFalse
                 else coq_FATrue
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Lte (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Lte ((int_trans_exp e1),
                                          (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf -> coq_FATrue
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 (match x0 with
                  | IntToInfinity.N.ZE_Inf -> coq_FATrue
                  | _ ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_Inf
                    then coq_FATrue
                    else coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some z0 -> coq_FATrue
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Gt (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Gt ((int_trans_exp e1), (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf -> coq_FAFalse
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FAFalse
                    else coq_FATrue)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_Inf
                 then coq_FAFalse
                 else coq_FATrue
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some z0 ->
                 (match z0 with
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FAFalse
                    else coq_FATrue
                  | _ -> coq_FAFalse)
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Gte (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Gte ((int_trans_exp e1),
                                          (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FATrue
                    else coq_FAFalse
                  | IntToInfinity.N.ZE_NegInf -> coq_FATrue)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some z0 -> coq_FATrue
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 (match x0 with
                  | IntToInfinity.N.ZE_NegInf -> coq_FATrue
                  | _ ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else coq_FAFalse)
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Eq (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1), (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FATrue
                    else coq_FAFalse
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 (match x0 with
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else coq_FAFalse
                  | _ ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_Inf
                    then coq_FATrue
                    else coq_FAFalse)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_NegInf
                 then coq_FATrue
                 else coq_FAFalse
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Eq_Max (e1, e2, e3) ->
        (match I2F.dexp2ZE e1 with
         | Some z0 ->
           (match z0 with
            | IntToInfinity.N.ZE_Fin z1 ->
              (match I2F.dexp2ZE e2 with
               | Some y ->
                 (match y with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    (match I2F.dexp2ZE e3 with
                     | Some z3 ->
                       (match z3 with
                        | IntToInfinity.N.ZE_Fin z4 ->
                          FA.ZF_BF (FA.ZBF_Eq_Max ((int_trans_exp e1),
                                                   (int_trans_exp e2), (int_trans_exp e3)))
                        | IntToInfinity.N.ZE_Inf -> coq_FAFalse
                        | IntToInfinity.N.ZE_NegInf ->
                          (match y with
                           | IntToInfinity.N.ZE_Fin z4 ->
                             FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1),
                                                  (int_trans_exp e2)))
                           | _ -> coq_FAFalse))
                     | None -> coq_FANone)
                  | IntToInfinity.N.ZE_Inf ->
                    (match I2F.dexp2ZE e3 with
                     | Some y0 ->
                       (match y0 with
                        | IntToInfinity.N.ZE_NegInf ->
                          (match y with
                           | IntToInfinity.N.ZE_Fin z2 ->
                             FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1),
                                                  (int_trans_exp e2)))
                           | _ -> coq_FAFalse)
                        | _ -> coq_FAFalse)
                     | None -> coq_FANone)
                  | IntToInfinity.N.ZE_NegInf ->
                    (match I2F.dexp2ZE e3 with
                     | Some y0 ->
                       (match y0 with
                        | IntToInfinity.N.ZE_Fin z2 ->
                          FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1),
                                               (int_trans_exp e3)))
                        | _ -> coq_FAFalse)
                     | None -> coq_FANone))
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x ->
                 (match I2F.dexp2ZE e3 with
                  | Some y ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FATrue
                    else if ZInfinity.coq_ZE_eq_dec (Obj.magic y)
                        ZInfinity.ZE_Inf
                    then coq_FATrue
                    else coq_FAFalse
                  | None -> coq_FANone)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x ->
                 (match I2F.dexp2ZE e3 with
                  | Some y ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then if ZInfinity.coq_ZE_eq_dec (Obj.magic y)
                        ZInfinity.ZE_NegInf
                      then coq_FATrue
                      else coq_FAFalse
                    else coq_FAFalse
                  | None -> coq_FANone)
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Eq_Min (e1, e2, e3) ->
        (match I2F.dexp2ZE e1 with
         | Some z0 ->
           (match z0 with
            | IntToInfinity.N.ZE_Fin z1 ->
              (match I2F.dexp2ZE e2 with
               | Some y ->
                 (match y with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    (match I2F.dexp2ZE e3 with
                     | Some z3 ->
                       (match z3 with
                        | IntToInfinity.N.ZE_Fin z4 ->
                          FA.ZF_BF (FA.ZBF_Eq_Min ((int_trans_exp e1),
                                                   (int_trans_exp e2), (int_trans_exp e3)))
                        | IntToInfinity.N.ZE_Inf ->
                          (match y with
                           | IntToInfinity.N.ZE_Fin z4 ->
                             FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1),
                                                  (int_trans_exp e2)))
                           | _ -> coq_FAFalse)
                        | IntToInfinity.N.ZE_NegInf -> coq_FAFalse)
                     | None -> coq_FANone)
                  | IntToInfinity.N.ZE_Inf ->
                    (match I2F.dexp2ZE e3 with
                     | Some y0 ->
                       (match y0 with
                        | IntToInfinity.N.ZE_NegInf -> coq_FAFalse
                        | _ ->
                          (match y0 with
                           | IntToInfinity.N.ZE_Fin z2 ->
                             FA.ZF_BF (FA.ZBF_Eq ((int_trans_exp e1),
                                                  (int_trans_exp e3)))
                           | _ -> coq_FAFalse))
                     | None -> coq_FANone)
                  | IntToInfinity.N.ZE_NegInf ->
                    (match I2F.dexp2ZE e3 with
                     | Some y0 -> coq_FAFalse
                     | None -> coq_FANone))
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x ->
                 (match I2F.dexp2ZE e3 with
                  | Some y ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then if ZInfinity.coq_ZE_eq_dec (Obj.magic y)
                        ZInfinity.ZE_Inf
                      then coq_FATrue
                      else coq_FAFalse
                    else coq_FAFalse
                  | None -> coq_FANone)
               | None -> coq_FANone)
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x ->
                 (match I2F.dexp2ZE e3 with
                  | Some y ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else if ZInfinity.coq_ZE_eq_dec (Obj.magic y)
                        ZInfinity.ZE_NegInf
                    then coq_FATrue
                    else coq_FAFalse
                  | None -> coq_FANone)
               | None -> coq_FANone))
         | None -> coq_FANone)
      | I2F.ZBF_Neq (e1, e2) ->
        (match I2F.dexp2ZE e1 with
         | Some x ->
           (match x with
            | IntToInfinity.N.ZE_Fin z0 ->
              (match I2F.dexp2ZE e2 with
               | Some z1 ->
                 (match z1 with
                  | IntToInfinity.N.ZE_Fin z2 ->
                    FA.ZF_BF (FA.ZBF_Neq ((int_trans_exp e1),
                                          (int_trans_exp e2)))
                  | IntToInfinity.N.ZE_Inf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_Inf
                    then coq_FAFalse
                    else coq_FATrue
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FAFalse
                    else coq_FATrue)
               | None -> embed (VAL.truth_not S.noneVal))
            | IntToInfinity.N.ZE_Inf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 (match x0 with
                  | IntToInfinity.N.ZE_NegInf ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x) ZInfinity.ZE_NegInf
                    then coq_FAFalse
                    else coq_FATrue
                  | _ ->
                    if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_Inf
                    then coq_FAFalse
                    else coq_FATrue)
               | None -> embed (VAL.truth_not S.noneVal))
            | IntToInfinity.N.ZE_NegInf ->
              (match I2F.dexp2ZE e2 with
               | Some x0 ->
                 if ZInfinity.coq_ZE_eq_dec (Obj.magic x0) ZInfinity.ZE_NegInf
                 then coq_FAFalse
                 else coq_FATrue
               | None -> embed (VAL.truth_not S.noneVal)))
         | None -> embed (VAL.truth_not S.noneVal))

    (** val int_trans : I2F.coq_ZF -> FA.coq_ZF **)

    let rec int_trans = function
      | I2F.ZF_BF bf -> int_trans_bf bf
      | I2F.ZF_And (f1, f2) -> FA.ZF_And ((int_trans f1), (int_trans f2))
      | I2F.ZF_Or (f1, f2) -> FA.ZF_Or ((int_trans f1), (int_trans f2))
      | I2F.ZF_Imp (f1, f2) -> FA.ZF_Imp ((int_trans f1), (int_trans f2))
      | I2F.ZF_Not f -> FA.ZF_Not (int_trans f)
      | I2F.ZF_Forall (v, q, f) -> FA.ZF_Forall (v, q, (int_trans f))
      | I2F.ZF_Exists (v, q, f) -> FA.ZF_Exists (v, q, (int_trans f))

    (** val coq_T : IA.coq_ZF -> FA.coq_ZF **)

    let coq_T f =
      int_trans (inf_trans f)
  end

module ThreeValuedSimp = 
  functor (Coq_sv:VARIABLE) ->
  functor (FZT:ZERO_FIN) ->
  functor (IZT:ZERO_INF) ->
  struct 
    module InfS = InfSolver(Coq_sv)(Three_Val_NoneError)(NoneError3ValRel)(FZT)(IZT)

    type coq_SimpResult =
      | EQ_TRUE
      | EQ_FALSE
      | EQ_ERROR
      | OTHER

    (** val coq_SimpResult_rect :
        InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
        'a1) -> coq_SimpResult -> 'a1 **)

    let coq_SimpResult_rect f f0 f1 f2 f3 = function
      | EQ_TRUE -> f0 __
      | EQ_FALSE -> f1 __
      | EQ_ERROR -> f2 __
      | OTHER -> f3 __

    (** val coq_SimpResult_rec :
        InfS.FA.coq_ZF -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> (__ ->
        'a1) -> coq_SimpResult -> 'a1 **)

    let coq_SimpResult_rec f f0 f1 f2 f3 = function
      | EQ_TRUE -> f0 __
      | EQ_FALSE -> f1 __
      | EQ_ERROR -> f2 __
      | OTHER -> f3 __

    (** val judge : InfS.FA.coq_ZF -> coq_SimpResult **)

    let judge = function
      | InfS.FA.ZF_BF z0 ->
        (match z0 with
         | InfS.FA.ZBF_Const v ->
           (match v with
            | Three_Val_NoneError.VTrue -> EQ_TRUE
            | Three_Val_NoneError.VFalse -> EQ_FALSE
            | Three_Val_NoneError.VError -> EQ_ERROR)
         | _ -> OTHER)
      | _ -> OTHER

    (** val simplify : InfS.FA.coq_ZF -> InfS.FA.coq_ZF **)

    let rec simplify = function
      | InfS.FA.ZF_BF bf -> InfS.FA.eliminateMinMax bf
      | InfS.FA.ZF_And (f1, f2) ->
        (match judge (simplify f1) with
         | EQ_TRUE ->
           (match judge (simplify f2) with
            | EQ_FALSE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse)
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> simplify f2)
         | EQ_FALSE ->
           (match judge (simplify f2) with
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse))
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER ->
           (match judge (simplify f2) with
            | EQ_TRUE -> simplify f1
            | EQ_FALSE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse)
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | OTHER -> InfS.FA.ZF_And ((simplify f1), (simplify f2))))
      | InfS.FA.ZF_Or (f1, f2) ->
        (match judge (simplify f1) with
         | EQ_TRUE ->
           (match judge (simplify f2) with
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue))
         | EQ_FALSE ->
           (match judge (simplify f2) with
            | EQ_TRUE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> simplify f2)
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER ->
           (match judge (simplify f2) with
            | EQ_TRUE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
            | EQ_FALSE -> simplify f1
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | OTHER -> InfS.FA.ZF_Or ((simplify f1), (simplify f2))))
      | InfS.FA.ZF_Imp (f1, f2) ->
        (match judge (simplify f1) with
         | EQ_TRUE ->
           (match judge (simplify f2) with
            | EQ_TRUE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> simplify f2)
         | EQ_FALSE ->
           (match judge (simplify f2) with
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | _ -> InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue))
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER ->
           (match judge (simplify f2) with
            | EQ_TRUE ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
            | EQ_FALSE -> InfS.FA.ZF_Not (simplify f1)
            | EQ_ERROR ->
              InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
            | OTHER -> InfS.FA.ZF_Imp ((simplify f1), (simplify f2))))
      | InfS.FA.ZF_Not f ->
        (match judge (simplify f) with
         | EQ_TRUE ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse)
         | EQ_FALSE ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER -> InfS.FA.ZF_Not (simplify f))
      | InfS.FA.ZF_Forall (v, q, f) ->
        (match judge (simplify f) with
         | EQ_TRUE -> InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
         | EQ_FALSE ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse)
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER -> InfS.FA.ZF_Forall (v, q, (simplify f)))
      | InfS.FA.ZF_Exists (v, q, f) ->
        (match judge (simplify f) with
         | EQ_TRUE -> InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VTrue)
         | EQ_FALSE ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VFalse)
         | EQ_ERROR ->
           InfS.FA.ZF_BF (InfS.FA.ZBF_Const Three_Val_NoneError.VError)
         | OTHER -> InfS.FA.ZF_Exists (v, q, (simplify f)))
  end

module type STRVAR = 
sig 
  type var 

  val var_eq_dec : var -> var -> bool

  val var2string : var -> char list

  val string2var : char list -> var
end

module InfSolverExtract = 
  functor (Coq_sv:STRVAR) ->
  struct 
    module Three_Val = Three_Val_NoneError

    module SIM = ThreeValuedSimp(Coq_sv)(FinZero)(InfZeroAll)

    (** val coq_Z_of_bool : bool -> z **)

    let coq_Z_of_bool = function
      | true -> Zpos XH
      | false -> Z0

    (** val coq_Z_of_ascii : char -> z **)

    let coq_Z_of_ascii a =
      (* If this appears, you're using Ascii internals. Please don't *) 
      (fun f c -> let n = Char.code c in 
        let h i = (n land (1 lsl i)) <> 0 in 
        f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b1 b2 b3 b4 b5 b6 b7 b8 ->
           Z.add (coq_Z_of_bool b1)
             (Z.mul (Zpos (XO XH))
                (Z.add (coq_Z_of_bool b2)
                   (Z.mul (Zpos (XO XH))
                      (Z.add (coq_Z_of_bool b3)
                         (Z.mul (Zpos (XO XH))
                            (Z.add (coq_Z_of_bool b4)
                               (Z.mul (Zpos (XO XH))
                                  (Z.add (coq_Z_of_bool b5)
                                     (Z.mul (Zpos (XO XH))
                                        (Z.add (coq_Z_of_bool b6)
                                           (Z.mul (Zpos (XO XH))
                                              (Z.add (coq_Z_of_bool b7)
                                                 (Z.mul (Zpos (XO XH)) (coq_Z_of_bool b8)))))))))))))))
        a

    (** val coq_Z_of_0 : z **)

    let coq_Z_of_0 =
      Zpos (XO (XO (XO (XO (XI XH)))))

    (** val coq_Z_of_digit : char -> z option **)

    let coq_Z_of_digit a =
      let v = Z.sub (coq_Z_of_ascii a) coq_Z_of_0 in
      (match Z.compare v Z0 with
       | Eq -> Some v
       | Lt -> None
       | Gt ->
         (match Z.compare v (Zpos (XO (XI (XO XH)))) with
          | Lt -> Some v
          | _ -> None))

    (** val coq_Z_of_string' : char list -> z -> z option **)

    let rec coq_Z_of_string' a n0 =
      match a with
      | [] -> None
      | a0::s' ->
        (match coq_Z_of_digit a0 with
         | Some va ->
           (match coq_Z_of_string' s' (Z.add n0 (Zpos XH)) with
            | Some vs ->
              Some (Z.add (Z.mul va (Z.pow (Zpos (XO (XI (XO XH)))) n0)) vs)
            | None -> Some va)
         | None -> None)

    (** val coq_Z_of_string : char list -> z **)

    let coq_Z_of_string a =
      match coq_Z_of_string' a Z0 with
      | Some z0 -> z0
      | None -> Z0

    (** val natToDigit : nat -> char **)

    let natToDigit = function
      | O -> '0'
      | S n1 ->
        (match n1 with
         | O -> '1'
         | S n2 ->
           (match n2 with
            | O -> '2'
            | S n3 ->
              (match n3 with
               | O -> '3'
               | S n4 ->
                 (match n4 with
                  | O -> '4'
                  | S n5 ->
                    (match n5 with
                     | O -> '5'
                     | S n6 ->
                       (match n6 with
                        | O -> '6'
                        | S n7 ->
                          (match n7 with
                           | O -> '7'
                           | S n8 ->
                             (match n8 with
                              | O -> '8'
                              | S n9 -> '9'))))))))

    (** val writeNatAux : nat -> nat -> char list -> char list **)

    let rec writeNatAux time n0 acc =
      let acc' =
        (natToDigit (modulo0 n0 (S (S (S (S (S (S (S (S (S (S O))))))))))))::acc
      in
      (match time with
       | O -> acc'
       | S time' ->
         (match div0 n0 (S (S (S (S (S (S (S (S (S (S O)))))))))) with
          | O -> acc'
          | S n1 -> writeNatAux time' (S n1) acc'))

    (** val writeNat : nat -> char list **)

    let writeNat n0 =
      writeNatAux n0 n0 []

    (** val string_of_Z : z -> char list **)

    let string_of_Z n0 =
      writeNat (Z.abs_nat n0)

    type 'const_type coq_ZExp =
      | ZExp_Var of Coq_sv.var
      | ZExp_Const of 'const_type
      | ZExp_Add of 'const_type coq_ZExp * 'const_type coq_ZExp
      | ZExp_Sub of 'const_type coq_ZExp * 'const_type coq_ZExp
      | ZExp_Mult of Coq_sv.var * 'const_type coq_ZExp

    (** val coq_ZExp_rect :
        (Coq_sv.var -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
        coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2
        -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp
        -> 'a2 **)

    let rec coq_ZExp_rect f f0 f1 f2 f3 = function
      | ZExp_Var v -> f v
      | ZExp_Const y -> f0 y
      | ZExp_Add (z1, z2) ->
        f1 z1 (coq_ZExp_rect f f0 f1 f2 f3 z1) z2
          (coq_ZExp_rect f f0 f1 f2 f3 z2)
      | ZExp_Sub (z1, z2) ->
        f2 z1 (coq_ZExp_rect f f0 f1 f2 f3 z1) z2
          (coq_ZExp_rect f f0 f1 f2 f3 z2)
      | ZExp_Mult (v, z1) -> f3 v z1 (coq_ZExp_rect f f0 f1 f2 f3 z1)

    (** val coq_ZExp_rec :
        (Coq_sv.var -> 'a2) -> ('a1 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1
        coq_ZExp -> 'a2 -> 'a2) -> ('a1 coq_ZExp -> 'a2 -> 'a1 coq_ZExp -> 'a2
        -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZExp -> 'a2 -> 'a2) -> 'a1 coq_ZExp
        -> 'a2 **)

    let rec coq_ZExp_rec f f0 f1 f2 f3 = function
      | ZExp_Var v -> f v
      | ZExp_Const y -> f0 y
      | ZExp_Add (z1, z2) ->
        f1 z1 (coq_ZExp_rec f f0 f1 f2 f3 z1) z2 (coq_ZExp_rec f f0 f1 f2 f3 z2)
      | ZExp_Sub (z1, z2) ->
        f2 z1 (coq_ZExp_rec f f0 f1 f2 f3 z1) z2 (coq_ZExp_rec f f0 f1 f2 f3 z2)
      | ZExp_Mult (v, z1) -> f3 v z1 (coq_ZExp_rec f f0 f1 f2 f3 z1)

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

    (** val coq_ZBF_rect :
        (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
        -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
        ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
        -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
        ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
        -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2 **)

    let coq_ZBF_rect f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | ZBF_Const x -> f x
      | ZBF_Lt (x, x0) -> f0 x x0
      | ZBF_Lte (x, x0) -> f1 x x0
      | ZBF_Gt (x, x0) -> f2 x x0
      | ZBF_Gte (x, x0) -> f3 x x0
      | ZBF_Eq (x, x0) -> f4 x x0
      | ZBF_Eq_Max (x, x0, x1) -> f5 x x0 x1
      | ZBF_Eq_Min (x, x0, x1) -> f6 x x0 x1
      | ZBF_Neq (x, x0) -> f7 x x0

    (** val coq_ZBF_rec :
        (bool -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
        -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
        ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp
        -> 'a2) -> ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) ->
        ('a1 coq_ZExp -> 'a1 coq_ZExp -> 'a1 coq_ZExp -> 'a2) -> ('a1 coq_ZExp
        -> 'a1 coq_ZExp -> 'a2) -> 'a1 coq_ZBF -> 'a2 **)

    let coq_ZBF_rec f f0 f1 f2 f3 f4 f5 f6 f7 = function
      | ZBF_Const x -> f x
      | ZBF_Lt (x, x0) -> f0 x x0
      | ZBF_Lte (x, x0) -> f1 x x0
      | ZBF_Gt (x, x0) -> f2 x x0
      | ZBF_Gte (x, x0) -> f3 x x0
      | ZBF_Eq (x, x0) -> f4 x x0
      | ZBF_Eq_Max (x, x0, x1) -> f5 x x0 x1
      | ZBF_Eq_Min (x, x0, x1) -> f6 x x0 x1
      | ZBF_Neq (x, x0) -> f7 x x0

    type 'const_type coq_ZF =
      | ZF_BF of 'const_type coq_ZBF
      | ZF_And of 'const_type coq_ZF * 'const_type coq_ZF
      | ZF_Or of 'const_type coq_ZF * 'const_type coq_ZF
      | ZF_Not of 'const_type coq_ZF
      | ZF_Forall_Fin of Coq_sv.var * 'const_type coq_ZF
      | ZF_Exists_Fin of Coq_sv.var * 'const_type coq_ZF
      | ZF_Forall of Coq_sv.var * 'const_type coq_ZF
      | ZF_Exists of Coq_sv.var * 'const_type coq_ZF

    (** val coq_ZF_rect :
        ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
        -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF ->
        'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var
        -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 ->
        'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2 **)

    let rec coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 = function
      | ZF_BF z1 -> f z1
      | ZF_And (z1, z2) ->
        f0 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1) z2
          (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z2)
      | ZF_Or (z1, z2) ->
        f1 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1) z2
          (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z2)
      | ZF_Not z1 -> f2 z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Forall_Fin (v, z1) -> f3 v z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Exists_Fin (v, z1) -> f4 v z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Forall (v, z1) -> f5 v z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Exists (v, z1) -> f6 v z1 (coq_ZF_rect f f0 f1 f2 f3 f4 f5 f6 z1)

    (** val coq_ZF_rec :
        ('a1 coq_ZBF -> 'a2) -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2)
        -> ('a1 coq_ZF -> 'a2 -> 'a1 coq_ZF -> 'a2 -> 'a2) -> ('a1 coq_ZF ->
        'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var
        -> 'a1 coq_ZF -> 'a2 -> 'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 ->
        'a2) -> (Coq_sv.var -> 'a1 coq_ZF -> 'a2 -> 'a2) -> 'a1 coq_ZF -> 'a2 **)

    let rec coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 = function
      | ZF_BF z1 -> f z1
      | ZF_And (z1, z2) ->
        f0 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1) z2
          (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z2)
      | ZF_Or (z1, z2) ->
        f1 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1) z2
          (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z2)
      | ZF_Not z1 -> f2 z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Forall_Fin (v, z1) -> f3 v z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Exists_Fin (v, z1) -> f4 v z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Forall (v, z1) -> f5 v z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)
      | ZF_Exists (v, z1) -> f6 v z1 (coq_ZF_rec f f0 f1 f2 f3 f4 f5 f6 z1)

    type coq_ZE =
      | ZE_Fin of Coq_sv.var
      | ZE_Inf
      | ZE_NegInf

    (** val coq_ZE_rect :
        (Coq_sv.var -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)

    let coq_ZE_rect f f0 f1 = function
      | ZE_Fin x -> f x
      | ZE_Inf -> f0
      | ZE_NegInf -> f1

    (** val coq_ZE_rec : (Coq_sv.var -> 'a1) -> 'a1 -> 'a1 -> coq_ZE -> 'a1 **)

    let coq_ZE_rec f f0 f1 = function
      | ZE_Fin x -> f x
      | ZE_Inf -> f0
      | ZE_NegInf -> f1

    (** val convert_ZF_to_IAZF_Exp :
        coq_ZE coq_ZExp -> SIM.InfS.IA.coq_ZExp **)

    let rec convert_ZF_to_IAZF_Exp = function
      | ZExp_Var v -> SIM.InfS.IA.ZExp_Var v
      | ZExp_Const c ->
        (match c with
         | ZE_Fin v ->
           SIM.InfS.IA.ZExp_Const (Some (PureInfinity.N.ZE_Fin
                                           (coq_Z_of_string (Coq_sv.var2string v))))
         | ZE_Inf -> SIM.InfS.IA.ZExp_Const (Some PureInfinity.N.ZE_Inf)
         | ZE_NegInf -> SIM.InfS.IA.ZExp_Const (Some PureInfinity.N.ZE_NegInf))
      | ZExp_Add (e1, e2) ->
        SIM.InfS.IA.ZExp_Add ((convert_ZF_to_IAZF_Exp e1),
                              (convert_ZF_to_IAZF_Exp e2))
      | ZExp_Sub (e1, e2) ->
        SIM.InfS.IA.ZExp_Sub ((convert_ZF_to_IAZF_Exp e1),
                              (convert_ZF_to_IAZF_Exp e2))
      | ZExp_Mult (s, e) ->
        SIM.InfS.IA.ZExp_Mult ((coq_Z_of_string (Coq_sv.var2string s)),
                               (convert_ZF_to_IAZF_Exp e))

    (** val convert_ZF_to_IAZF_BF : coq_ZE coq_ZBF -> SIM.InfS.IA.coq_ZBF **)

    let rec convert_ZF_to_IAZF_BF = function
      | ZBF_Const b ->
        if b
        then SIM.InfS.IA.ZBF_Const (Obj.magic Three_Val.VTrue)
        else SIM.InfS.IA.ZBF_Const (Obj.magic Three_Val.VFalse)
      | ZBF_Lt (e1, e2) ->
        SIM.InfS.IA.ZBF_Lt ((convert_ZF_to_IAZF_Exp e1),
                            (convert_ZF_to_IAZF_Exp e2))
      | ZBF_Lte (e1, e2) ->
        SIM.InfS.IA.ZBF_Lte ((convert_ZF_to_IAZF_Exp e1),
                             (convert_ZF_to_IAZF_Exp e2))
      | ZBF_Gt (e1, e2) ->
        SIM.InfS.IA.ZBF_Gt ((convert_ZF_to_IAZF_Exp e1),
                            (convert_ZF_to_IAZF_Exp e2))
      | ZBF_Gte (e1, e2) ->
        SIM.InfS.IA.ZBF_Gte ((convert_ZF_to_IAZF_Exp e1),
                             (convert_ZF_to_IAZF_Exp e2))
      | ZBF_Eq (e1, e2) ->
        SIM.InfS.IA.ZBF_Eq ((convert_ZF_to_IAZF_Exp e1),
                            (convert_ZF_to_IAZF_Exp e2))
      | ZBF_Eq_Max (e1, e2, e3) ->
        SIM.InfS.IA.ZBF_Eq_Max ((convert_ZF_to_IAZF_Exp e1),
                                (convert_ZF_to_IAZF_Exp e2), (convert_ZF_to_IAZF_Exp e3))
      | ZBF_Eq_Min (e1, e2, e3) ->
        SIM.InfS.IA.ZBF_Eq_Min ((convert_ZF_to_IAZF_Exp e1),
                                (convert_ZF_to_IAZF_Exp e2), (convert_ZF_to_IAZF_Exp e3))
      | ZBF_Neq (e1, e2) ->
        SIM.InfS.IA.ZBF_Neq ((convert_ZF_to_IAZF_Exp e1),
                             (convert_ZF_to_IAZF_Exp e2))

    (** val convert_ZF_to_IAZF : coq_ZE coq_ZF -> SIM.InfS.IA.coq_ZF **)

    let rec convert_ZF_to_IAZF = function
      | ZF_BF bf -> SIM.InfS.IA.ZF_BF (convert_ZF_to_IAZF_BF bf)
      | ZF_And (f1, f2) ->
        SIM.InfS.IA.ZF_And ((convert_ZF_to_IAZF f1), (convert_ZF_to_IAZF f2))
      | ZF_Or (f1, f2) ->
        SIM.InfS.IA.ZF_Or ((convert_ZF_to_IAZF f1), (convert_ZF_to_IAZF f2))
      | ZF_Not g -> SIM.InfS.IA.ZF_Not (convert_ZF_to_IAZF g)
      | ZF_Forall_Fin (v, g) ->
        SIM.InfS.IA.ZF_Forall (v, PureInfinity.Q_Z, (convert_ZF_to_IAZF g))
      | ZF_Exists_Fin (v, g) ->
        SIM.InfS.IA.ZF_Exists (v, PureInfinity.Q_Z, (convert_ZF_to_IAZF g))
      | ZF_Forall (v, g) ->
        SIM.InfS.IA.ZF_Forall (v, PureInfinity.Q_ZE, (convert_ZF_to_IAZF g))
      | ZF_Exists (v, g) ->
        SIM.InfS.IA.ZF_Exists (v, PureInfinity.Q_ZE, (convert_ZF_to_IAZF g))

    (** val convert_FAZF_to_ZF_Exp :
        SIM.InfS.FA.coq_ZExp -> Coq_sv.var coq_ZExp **)

    let rec convert_FAZF_to_ZF_Exp = function
      | SIM.InfS.FA.ZExp_Var v -> ZExp_Var v
      | SIM.InfS.FA.ZExp_Const c ->
        ZExp_Const (Coq_sv.string2var (string_of_Z c))
      | SIM.InfS.FA.ZExp_Add (e1, e2) ->
        ZExp_Add ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZExp_Inv e ->
        ZExp_Sub ((ZExp_Const (Coq_sv.string2var (string_of_Z Z0))),
                  (convert_FAZF_to_ZF_Exp e))
      | SIM.InfS.FA.ZExp_Sub (e1, e2) ->
        ZExp_Sub ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZExp_Mult (c, e) ->
        ZExp_Mult ((Coq_sv.string2var (string_of_Z c)),
                   (convert_FAZF_to_ZF_Exp e))

    (** val convert_FAZF_to_ZF_BF :
        SIM.InfS.FA.coq_ZBF -> Coq_sv.var coq_ZBF **)

    let rec convert_FAZF_to_ZF_BF = function
      | SIM.InfS.FA.ZBF_Const b ->
        (match b with
         | Three_Val_NoneError.VTrue -> ZBF_Const true
         | _ -> ZBF_Const false)
      | SIM.InfS.FA.ZBF_Lt (e1, e2) ->
        ZBF_Lt ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZBF_Lte (e1, e2) ->
        ZBF_Lte ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZBF_Gt (e1, e2) ->
        ZBF_Gt ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZBF_Gte (e1, e2) ->
        ZBF_Gte ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZBF_Eq (e1, e2) ->
        ZBF_Eq ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))
      | SIM.InfS.FA.ZBF_Eq_Max (e1, e2, e3) ->
        ZBF_Eq_Max ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2),
                    (convert_FAZF_to_ZF_Exp e3))
      | SIM.InfS.FA.ZBF_Eq_Min (e1, e2, e3) ->
        ZBF_Eq_Min ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2),
                    (convert_FAZF_to_ZF_Exp e3))
      | SIM.InfS.FA.ZBF_Neq (e1, e2) ->
        ZBF_Neq ((convert_FAZF_to_ZF_Exp e1), (convert_FAZF_to_ZF_Exp e2))

    (** val convert_FAZF_to_ZF : SIM.InfS.FA.coq_ZF -> Coq_sv.var coq_ZF **)

    let rec convert_FAZF_to_ZF = function
      | SIM.InfS.FA.ZF_BF bf -> ZF_BF (convert_FAZF_to_ZF_BF bf)
      | SIM.InfS.FA.ZF_And (f1, f2) ->
        ZF_And ((convert_FAZF_to_ZF f1), (convert_FAZF_to_ZF f2))
      | SIM.InfS.FA.ZF_Or (f1, f2) ->
        ZF_Or ((convert_FAZF_to_ZF f1), (convert_FAZF_to_ZF f2))
      | SIM.InfS.FA.ZF_Imp (f1, f2) ->
        ZF_Or ((ZF_Not (convert_FAZF_to_ZF f1)), (convert_FAZF_to_ZF f2))
      | SIM.InfS.FA.ZF_Not g -> ZF_Not (convert_FAZF_to_ZF g)
      | SIM.InfS.FA.ZF_Forall (v, q, g) ->
        ZF_Forall_Fin (v, (convert_FAZF_to_ZF g))
      | SIM.InfS.FA.ZF_Exists (v, q, g) ->
        ZF_Exists_Fin (v, (convert_FAZF_to_ZF g))

    (** val transform_ZE_to_string : coq_ZE coq_ZF -> Coq_sv.var coq_ZF **)

    let transform_ZE_to_string f =
      convert_FAZF_to_ZF (SIM.InfS.coq_T (convert_ZF_to_IAZF f))

    (** val transform_ZE_to_string_simplify :
        coq_ZE coq_ZF -> Coq_sv.var coq_ZF **)

    let transform_ZE_to_string_simplify f =
      convert_FAZF_to_ZF (SIM.simplify (SIM.InfS.coq_T (convert_ZF_to_IAZF f)))
  end

