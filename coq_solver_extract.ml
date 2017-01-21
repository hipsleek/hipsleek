type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| x,y -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| y :: l'0 -> (fun x -> x + 1) (length l'0)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l0 m =
  match l0 with
  | [] -> m
  | a0 :: l1 -> a0 :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : int -> int -> int **)

let rec plus n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    m)
    (fun p -> (fun x -> x + 1)
    (plus p m))
    n0

(** val mult : int -> int -> int **)

let rec mult n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    0)
    (fun p ->
    plus m (mult p m))
    n0

(** val minus : int -> int -> int **)

let rec minus n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    n0)
    (fun k ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      n0)
      (fun l0 ->
      minus k l0)
      m)
    n0

(** val max : int -> int -> int **)

let rec max n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    m)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      n0)
      (fun m' -> (fun x -> x + 1)
      (max n' m'))
      m)
    n0

(** val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n0

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a0 = function
| [] -> false
| y :: l1 -> let s0 = h y a0 in if s0 then true else in_dec h a0 l1

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l0 l'0 =
  match l0 with
  | [] -> l'0
  | a0 :: l1 -> rev_append l1 (a0 :: l'0)

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec2 l0 l'0 =
  match l0 with
  | [] ->
    (match l'0 with
     | [] -> true
     | a0 :: l1 -> false)
  | y :: l1 ->
    (match l'0 with
     | [] -> false
     | a0 :: l2 -> if eq_dec2 y a0 then list_eq_dec eq_dec2 l1 l2 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a0 :: t0 -> (f a0) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l0 a0 =
  match l0 with
  | [] -> a0
  | b0 :: t0 -> fold_left f t0 (f a0 b0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b0 :: t0 -> f b0 (fold_right f a0 t0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l1 -> if f x then x :: (filter f l1) else filter f l1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module type EqLtLe = 
 sig 
  type t 
 end

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module type OrderedType' = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module OT_to_Full = 
 functor (O:OrderedType') ->
 struct 
  type t = O.t
  
  (** val compare : t -> t -> comparison **)
  
  let compare =
    O.compare
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    O.eq_dec
 end

module MakeOrderTac = 
 functor (O:EqLtLe) ->
 functor (P:sig 
  
 end) ->
 struct 
  
 end

module OT_to_OrderTac = 
 functor (OT:OrderedType) ->
 struct 
  module OTF = OT_to_Full(OT)
  
  module TO = 
   struct 
    type t = OTF.t
    
    (** val compare : t -> t -> comparison **)
    
    let compare =
      OTF.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts = 
 functor (O:OrderedType') ->
 struct 
  module OrderTac = OT_to_OrderTac(O)
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> bool **)
  
  let lt_dec x y =
    let c0 = compareSpec2Type (O.compare x y) in
    (match c0 with
     | CompLtT -> true
     | _ -> false)
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    if eq_dec x y then true else false
 end

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
    | IsPos z -> z
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
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> (fun x -> x + 1) (size_nat p0)
  | XO p0 -> (fun x -> x + 1) (size_nat p0)
  | XH -> (fun x -> x + 1) 0
  
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
      (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
      positive*mask **)
  
  let sqrtrem_step f g = function
  | s0,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s0) in
       let r' = g (f r) in
       if leb s' r' then (XI s0),(sub_mask r' s') else (XO s0),(IsPos r')
     | _ -> (XO s0),(sub_mask (g (f XH)) (XO (XO XH))))
  
  (** val sqrtrem : positive -> positive*mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a0 b0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a0 with
      | XI a' ->
        (match b0 with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a0
            | Lt -> gcdn n1 (sub b' a') a0
            | Gt -> gcdn n1 (sub a' b') b0)
         | XO b1 -> gcdn n1 a0 b1
         | XH -> XH)
      | XO a22 ->
        (match b0 with
         | XI p -> gcdn n1 a22 b0
         | XO b1 -> XO (gcdn n1 a22 b1)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a0 b0 =
    gcdn (plus (size_nat a0) (size_nat b0)) a0 b0
  
  (** val ggcdn :
      int -> positive -> positive -> positive*(positive*positive) **)
  
  let rec ggcdn n0 a0 b0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH,(a0,b0))
      (fun n1 ->
      match a0 with
      | XI a' ->
        (match b0 with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a0,(XH,XH)
            | Lt ->
              let g,p = ggcdn n1 (sub b' a') a0 in
              let ba,aa = p in g,(aa,(add aa (XO ba)))
            | Gt ->
              let g,p = ggcdn n1 (sub a' b') b0 in
              let ab,bb = p in g,((add bb (XO ab)),bb))
         | XO b1 ->
           let g,p = ggcdn n1 a0 b1 in let aa,bb = p in g,(aa,(XO bb))
         | XH -> XH,(a0,XH))
      | XO a22 ->
        (match b0 with
         | XI p ->
           let g,p0 = ggcdn n1 a22 b0 in let aa,bb = p0 in g,((XO aa),bb)
         | XO b1 -> let g,p = ggcdn n1 a22 b1 in (XO g),p
         | XH -> XH,(a0,XH))
      | XH -> XH,(XH,b0))
      n0
  
  (** val ggcd : positive -> positive -> positive*(positive*positive) **)
  
  let ggcd a0 b0 =
    ggcdn (plus (size_nat a0) (size_nat b0)) a0 b0
  
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
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
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
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
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
  
  let rec iter_op op p a0 =
    match p with
    | XI p0 -> op a0 (iter_op op p0 (op a0 a0))
    | XO p0 -> iter_op op p0 (op a0 a0)
    | XH -> a0
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x ((fun x -> x + 1) 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
  
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
  
  let rec peano_rect a0 f p =
    let f2 =
      peano_rect (f XH a0) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a0)
  
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
  
  let rec coq_PeanoView_iter a0 f p = function
  | PeanoOne -> a0
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a0 f p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c0 = function
  | Eq -> c0
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
      let c0 = compareSpec2Type (compare n0 m) in
      (match c0 with
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
      let c0 = compareSpec2Type (compare n0 m) in
      (match c0 with
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

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> Some
      false)
      (fun m0 -> Some
      true)
      m)
    (fun n1 ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      None)
      (fun m0 ->
      lt_eq_lt_dec n1 m0)
      m)
    n0

(** val le_lt_dec : int -> int -> bool **)

let rec le_lt_dec n0 m =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ ->
    true)
    (fun n1 ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      false)
      (fun m0 ->
      le_lt_dec n1 m0)
      m)
    n0

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec n0 m =
  le_lt_dec n0 m

(** val le_dec : int -> int -> bool **)

let le_dec n0 m =
  le_gt_dec n0 m

(** val lt_dec0 : int -> int -> bool **)

let lt_dec0 n0 m =
  le_dec ((fun x -> x + 1) n0) m

type 't perm_alg =
  't -> 't -> 't -> 't -> 't -> __ -> __ -> 't*__
  (* singleton inductive, whose constructor was mkPerm *)

type 'a sep_alg =
  'a -> 'a
  (* singleton inductive, whose constructor was mkSep *)

type 'a sing_alg =
  'a
  (* singleton inductive, whose constructor was mkSing *)

type 'a eqDec = 'a -> 'a -> bool

(** val eq_dec0 : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let eq_dec0 eqDec1 =
  eqDec1

(** val nat_eq_dec : int eqDec **)

let nat_eq_dec a0 a' =
  let s0 = lt_eq_lt_dec a0 a' in
  (match s0 with
   | Some s1 -> if s1 then false else true
   | None -> false)

module type BOOLEAN_ALGEBRA = 
 sig 
  type t 
  
  val top : t
  
  val bot : t
  
  val lub : t -> t -> t
  
  val glb : t -> t -> t
  
  val comp : t -> t
 end

type 'a heightable = { height : ('a -> int); is_height_zero : ('a -> bool) }

(** val height : 'a1 heightable -> 'a1 -> int **)

let height x = x.height

(** val is_height_zero : 'a1 heightable -> 'a1 -> bool **)

let is_height_zero x = x.is_height_zero

type 'a is_height_zero_spec = 'a -> bool

(** val list_height : 'a1 heightable -> 'a1 list -> int **)

let list_height h lA =
  fold_right max 0 (map h.height lA)

(** val list_heightable : 'a1 heightable -> 'a1 list heightable **)

let list_heightable h =
  { height = (list_height h); is_height_zero = (fun a0 ->
    let rec f = function
    | [] -> true
    | y :: l1 -> if h.is_height_zero y then f l1 else false
    in f a0) }

type 'a decomposible =
  'a -> 'a*'a
  (* singleton inductive, whose constructor was Decomposible *)

(** val decompose : 'a1 decomposible -> 'a1 -> 'a1*'a1 **)

let decompose decomposible0 =
  decomposible0

type 'a roundableLeft =
  int -> 'a -> 'a option
  (* singleton inductive, whose constructor was RoundableLeft *)

(** val roundL : 'a1 roundableLeft -> int -> 'a1 -> 'a1 option **)

let roundL roundableLeft0 =
  roundableLeft0

type 'a roundableRight =
  int -> 'a -> 'a option
  (* singleton inductive, whose constructor was RoundableRight *)

(** val roundR : 'a1 roundableRight -> int -> 'a1 -> 'a1 option **)

let roundR roundableRight0 =
  roundableRight0

type 'a avgable =
  int -> 'a -> 'a -> 'a option
  (* singleton inductive, whose constructor was Avgable *)

(** val avg :
    'a1
    avgable
    ->
    int
    ->
    'a1
    ->
    'a1
    ->
    'a1
    option **)

let avg avgable0 =
  avgable0

module BA_Facts = 
 functor (BA:BOOLEAN_ALGEBRA) ->
 struct 
  type t
    =
    BA.t
  
  (** val top :
      t **)
  
  let top =
    BA.top
  
  (** val bot :
      t **)
  
  let bot =
    BA.bot
  
  (** val lub :
      t
      ->
      t
      ->
      t **)
  
  let lub =
    BA.lub
  
  (** val glb :
      t
      ->
      t
      ->
      t **)
  
  let glb =
    BA.glb
  
  (** val comp :
      t
      ->
      t **)
  
  let comp =
    BA.comp
  
  (** val pa :
      t
      perm_alg **)
  
  let pa a0 b0 c0 d0 e0 _ _ =
    (lub
      b0
      c0),__
  
  (** val sa :
      t
      sep_alg **)
  
  let sa x =
    bot
  
  (** val singa :
      t
      sing_alg **)
  
  let singa =
    bot
 end

module Share = 
 struct 
  type coq_ShareTree =
  | Leaf of bool
  | Node of coq_ShareTree
     * coq_ShareTree
  
  (** val coq_ShareTree_rect :
      (bool
      ->
      'a1)
      ->
      (coq_ShareTree
      ->
      'a1
      ->
      coq_ShareTree
      ->
      'a1
      ->
      'a1)
      ->
      coq_ShareTree
      ->
      'a1 **)
  
  let rec coq_ShareTree_rect f f0 = function
  | Leaf b0 ->
    f
      b0
  | Node (s1,
          s2) ->
    f0
      s1
      (coq_ShareTree_rect
        f
        f0
        s1)
      s2
      (coq_ShareTree_rect
        f
        f0
        s2)
  
  (** val coq_ShareTree_rec :
      (bool
      ->
      'a1)
      ->
      (coq_ShareTree
      ->
      'a1
      ->
      coq_ShareTree
      ->
      'a1
      ->
      'a1)
      ->
      coq_ShareTree
      ->
      'a1 **)
  
  let rec coq_ShareTree_rec f f0 = function
  | Leaf b0 ->
    f
      b0
  | Node (s1,
          s2) ->
    f0
      s1
      (coq_ShareTree_rec
        f
        f0
        s1)
      s2
      (coq_ShareTree_rec
        f
        f0
        s2)
  
  (** val union_tree :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec union_tree x y =
    match x with
    | Leaf b0 ->
      if b0
      then Leaf
             true
      else y
    | Node (l1,
            r1) ->
      (match y with
       | Leaf b0 ->
         if b0
         then Leaf
                true
         else x
       | Node (l2,
               r2) ->
         Node
           ((union_tree
              l1
              l2),
           (union_tree
             r1
             r2)))
  
  (** val intersect_tree :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec intersect_tree x y =
    match x with
    | Leaf b0 ->
      if b0
      then y
      else Leaf
             false
    | Node (l1,
            r1) ->
      (match y with
       | Leaf b0 ->
         if b0
         then x
         else Leaf
                false
       | Node (l2,
               r2) ->
         Node
           ((intersect_tree
              l1
              l2),
           (intersect_tree
             r1
             r2)))
  
  (** val comp_tree :
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec comp_tree = function
  | Leaf b0 ->
    Leaf
      (negb
        b0)
  | Node (l0,
          r) ->
    Node
      ((comp_tree
         l0),
      (comp_tree
        r))
  
  (** val mkCanon :
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec mkCanon = function
  | Leaf b0 ->
    Leaf
      b0
  | Node (l0,
          r) ->
    let l'0 =
      mkCanon
        l0
    in
    let r' =
      mkCanon
        r
    in
    (match l'0 with
     | Leaf b1 ->
       (match r' with
        | Leaf b2 ->
          if bool_dec
               b1
               b2
          then Leaf
                 b1
          else Node
                 (l'0,
                 r')
        | Node (s0,
                s1) ->
          Node
            (l'0,
            r'))
     | Node (s0,
             s1) ->
       Node
         (l'0,
         r'))
  
  (** val relativ_tree :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec relativ_tree z a0 =
    match z with
    | Leaf b0 ->
      if b0
      then a0
      else Leaf
             false
    | Node (l0,
            r) ->
      Node
        ((relativ_tree
           l0
           a0),
        (relativ_tree
          r
          a0))
  
  (** val nonEmpty_dec :
      coq_ShareTree
      ->
      bool **)
  
  let rec nonEmpty_dec = function
  | Leaf b0 ->
    if b0
    then true
    else false
  | Node (s1,
          s2) ->
    if nonEmpty_dec
         s1
    then true
    else nonEmpty_dec
           s2
  
  (** val nonFull_dec :
      coq_ShareTree
      ->
      bool **)
  
  let rec nonFull_dec = function
  | Leaf b0 ->
    if b0
    then false
    else true
  | Node (s1,
          s2) ->
    if nonFull_dec
         s1
    then true
    else nonFull_dec
           s2
  
  type coq_Sctx =
  | NodeB of coq_Sctx
     * coq_Sctx
  | NodeR of coq_ShareTree
     * coq_Sctx
  | NodeL of coq_Sctx
     * coq_ShareTree
  | Hole
  
  (** val coq_Sctx_rect :
      (coq_Sctx
      ->
      'a1
      ->
      coq_Sctx
      ->
      'a1
      ->
      'a1)
      ->
      (coq_ShareTree
      ->
      coq_Sctx
      ->
      'a1
      ->
      'a1)
      ->
      (coq_Sctx
      ->
      'a1
      ->
      coq_ShareTree
      ->
      'a1)
      ->
      'a1
      ->
      coq_Sctx
      ->
      'a1 **)
  
  let rec coq_Sctx_rect f f0 f1 f2 = function
  | NodeB (s1,
           s2) ->
    f
      s1
      (coq_Sctx_rect
        f
        f0
        f1
        f2
        s1)
      s2
      (coq_Sctx_rect
        f
        f0
        f1
        f2
        s2)
  | NodeR (s1,
           s2) ->
    f0
      s1
      s2
      (coq_Sctx_rect
        f
        f0
        f1
        f2
        s2)
  | NodeL (s1,
           s2) ->
    f1
      s1
      (coq_Sctx_rect
        f
        f0
        f1
        f2
        s1)
      s2
  | Hole ->
    f2
  
  (** val coq_Sctx_rec :
      (coq_Sctx
      ->
      'a1
      ->
      coq_Sctx
      ->
      'a1
      ->
      'a1)
      ->
      (coq_ShareTree
      ->
      coq_Sctx
      ->
      'a1
      ->
      'a1)
      ->
      (coq_Sctx
      ->
      'a1
      ->
      coq_ShareTree
      ->
      'a1)
      ->
      'a1
      ->
      coq_Sctx
      ->
      'a1 **)
  
  let rec coq_Sctx_rec f f0 f1 f2 = function
  | NodeB (s1,
           s2) ->
    f
      s1
      (coq_Sctx_rec
        f
        f0
        f1
        f2
        s1)
      s2
      (coq_Sctx_rec
        f
        f0
        f1
        f2
        s2)
  | NodeR (s1,
           s2) ->
    f0
      s1
      s2
      (coq_Sctx_rec
        f
        f0
        f1
        f2
        s2)
  | NodeL (s1,
           s2) ->
    f1
      s1
      (coq_Sctx_rec
        f
        f0
        f1
        f2
        s1)
      s2
  | Hole ->
    f2
  
  (** val coq_Sctx_app :
      coq_Sctx
      ->
      coq_Sctx
      ->
      coq_Sctx **)
  
  let rec coq_Sctx_app c1 c2 =
    match c1 with
    | NodeB (l0,
             r) ->
      NodeB
        ((coq_Sctx_app
           l0
           c2),
        (coq_Sctx_app
          r
          c2))
    | NodeR (l0,
             r) ->
      NodeR
        (l0,
        (coq_Sctx_app
          r
          c2))
    | NodeL (l0,
             r) ->
      NodeL
        ((coq_Sctx_app
           l0
           c2),
        r)
    | Hole ->
      c2
  
  (** val fill :
      coq_Sctx
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec fill c0 x =
    match c0 with
    | NodeB (l0,
             r) ->
      Node
        ((fill
           l0
           x),
        (fill
          r
          x))
    | NodeR (l0,
             r) ->
      Node
        (l0,
        (fill
          r
          x))
    | NodeL (l0,
             r) ->
      Node
        ((fill
           l0
           x),
        r)
    | Hole ->
      x
  
  (** val to_Sctx :
      coq_ShareTree
      ->
      coq_Sctx **)
  
  let rec to_Sctx = function
  | Leaf b0 ->
    if b0
    then Hole
    else assert false
           (* absurd case *)
  | Node (l0,
          r) ->
    if nonEmpty_dec
         l0
    then if nonEmpty_dec
              r
         then NodeB
                ((to_Sctx
                   l0),
                (to_Sctx
                  r))
         else NodeL
                ((to_Sctx
                   l0),
                r)
    else if nonEmpty_dec
              r
         then NodeR
                (l0,
                (to_Sctx
                  r))
         else assert false
                (* absurd case *)
  
  type canonTree
    =
    coq_ShareTree
  
  (** val shareTree_dec_eq :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      bool **)
  
  let rec shareTree_dec_eq s0 y0 =
    match s0 with
    | Leaf b0 ->
      (match y0 with
       | Leaf b1 ->
         bool_dec
           b0
           b1
       | Node (s1,
               s2) ->
         false)
    | Node (s1,
            s2) ->
      (match y0 with
       | Leaf b0 ->
         false
       | Node (s3,
               s4) ->
         if shareTree_dec_eq
              s1
              s3
         then shareTree_dec_eq
                s2
                s4
         else false)
  
  (** val canonTree_eq_dec :
      canonTree
      ->
      canonTree
      ->
      bool **)
  
  let canonTree_eq_dec x y =
    shareTree_dec_eq
      x
      y
  
  (** val coq_EqDec_canonTree :
      canonTree
      eqDec **)
  
  let coq_EqDec_canonTree =
    canonTree_eq_dec
  
  module BA = 
   struct 
    type t
      =
      canonTree
    
    (** val lub :
        canonTree
        ->
        canonTree
        ->
        canonTree **)
    
    let lub x y =
      mkCanon
        (union_tree
          x
          y)
    
    (** val glb :
        canonTree
        ->
        canonTree
        ->
        canonTree **)
    
    let glb x y =
      mkCanon
        (intersect_tree
          x
          y)
    
    (** val top :
        canonTree **)
    
    let top =
      Leaf
        true
    
    (** val bot :
        canonTree **)
    
    let bot =
      Leaf
        false
    
    (** val comp :
        canonTree
        ->
        canonTree **)
    
    let comp x =
      comp_tree
        x
   end
  
  module BAF = BA_Facts(BA)
  
  type t
    =
    BA.t
  
  (** val top :
      t **)
  
  let top =
    BA.top
  
  (** val bot :
      t **)
  
  let bot =
    BA.bot
  
  (** val lub :
      t
      ->
      t
      ->
      t **)
  
  let lub =
    BA.lub
  
  (** val glb :
      t
      ->
      t
      ->
      t **)
  
  let glb =
    BA.glb
  
  (** val comp :
      t
      ->
      t **)
  
  let comp =
    BA.comp
  
  (** val pa :
      t
      perm_alg **)
  
  let pa =
    BAF.pa
  
  (** val sa :
      t
      sep_alg **)
  
  let sa x =
    bot
  
  (** val singa :
      t
      sing_alg **)
  
  let singa =
    bot
  
  (** val rel :
      t
      ->
      t
      ->
      t **)
  
  let rel a0 x = match x with
  | Leaf b0 ->
    if b0
    then a0
    else Leaf
           false
  | Node (s0,
          s1) ->
    relativ_tree
      a0
      x
  
  (** val rel_classification :
      t
      ->
      t
      ->
      bool **)
  
  let rel_classification a0 = function
  | Leaf b0 ->
    if b0
    then false
    else true
  | Node (x1,
          x2) ->
    false
  
  (** val leftTree :
      canonTree **)
  
  let leftTree =
    Node
      ((Leaf
      true),
      (Leaf
      false))
  
  (** val rightTree :
      canonTree **)
  
  let rightTree =
    Node
      ((Leaf
      false),
      (Leaf
      true))
  
  (** val split :
      canonTree
      ->
      t*t **)
  
  let split x =
    (match leftTree with
     | Leaf b0 ->
       if b0
       then x
       else Leaf
              false
     | Node (s0,
             s1) ->
       relativ_tree
         x
         leftTree),(match rightTree with
                    | Leaf b0 ->
                      if b0
                      then x
                      else Leaf
                             false
                    | Node (s0,
                            s1) ->
                      relativ_tree
                        x
                        rightTree)
  
  (** val split_tok1 :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec split_tok1 n0 = function
  | Leaf b0 ->
    Leaf
      false
  | Node (s0,
          t2) ->
    (match s0 with
     | Leaf b0 ->
       if b0
       then ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
               (fun _ ->
               Node
               ((Leaf
               true),
               (Leaf
               false)))
               (fun n' ->
               Node
               ((Leaf
               true),
               (split_tok1
                 n'
                 t2)))
               n0)
       else Node
              ((Leaf
              false),
              (split_tok1
                n0
                t2))
     | Node (s1,
             s2) ->
       Leaf
         false)
  
  (** val split_tok2 :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec split_tok2 n0 x = match x with
  | Leaf b0 ->
    x
  | Node (s0,
          t2) ->
    (match s0 with
     | Leaf b0 ->
       if b0
       then ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
               (fun _ ->
               Node
               ((Leaf
               false),
               t2))
               (fun n' ->
               Node
               ((Leaf
               false),
               (split_tok2
                 n'
                 t2)))
               n0)
       else Node
              ((Leaf
              false),
              (split_tok2
                n0
                t2))
     | Node (s1,
             s2) ->
       x)
  
  (** val split_token :
      int
      ->
      t
      ->
      t*t **)
  
  let split_token n0 tok =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      bot,tok)
      (fun n' ->
      (mkCanon
        (split_tok1
          n'
          tok)),(mkCanon
                  (split_tok2
                    n'
                    tok)))
      n0
  
  (** val new_fac :
      int
      ->
      coq_ShareTree **)
  
  let rec new_fac n0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      Node
      ((Leaf
      false),
      (Leaf
      true)))
      (fun n' ->
      Node
      ((Leaf
      false),
      (new_fac
        n')))
      n0
  
  (** val create_tok1 :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec create_tok1 n0 x = match x with
  | Leaf b0 ->
    if b0
    then new_fac
           n0
    else x
  | Node (s0,
          t2) ->
    (match s0 with
     | Leaf b0 ->
       if b0
       then ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
               (fun _ ->
               Node
               ((Leaf
               false),
               t2))
               (fun n' ->
               Node
               ((Leaf
               false),
               (create_tok1
                 n'
                 t2)))
               n0)
       else Node
              ((Leaf
              false),
              (create_tok1
                n0
                t2))
     | Node (s1,
             s2) ->
       x)
  
  (** val create_tok2 :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree **)
  
  let rec create_tok2 n0 = function
  | Leaf b0 ->
    if b0
    then comp_tree
           (new_fac
             n0)
    else Leaf
           false
  | Node (s0,
          t2) ->
    (match s0 with
     | Leaf b0 ->
       if b0
       then ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
               (fun _ ->
               Node
               ((Leaf
               true),
               (Leaf
               false)))
               (fun n' ->
               Node
               ((Leaf
               true),
               (create_tok2
                 n'
                 t2)))
               n0)
       else Node
              ((Leaf
              false),
              (create_tok2
                n0
                t2))
     | Node (s1,
             s2) ->
       Leaf
         false)
  
  (** val create_token :
      int
      ->
      t
      ->
      t*t **)
  
  let create_token n0 fac =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      fac,bot)
      (fun n' ->
      (mkCanon
        (create_tok1
          n'
          fac)),(mkCanon
                  (create_tok2
                    n'
                    fac)))
      n0
  
  (** val coq_EqDec_share :
      t
      eqDec **)
  
  let coq_EqDec_share =
    coq_EqDec_canonTree
  
  (** val tree_decompose :
      canonTree
      ->
      canonTree*canonTree **)
  
  let tree_decompose = function
  | Leaf b0 ->
    (Leaf
      b0),(Leaf
      b0)
  | Node (t1,
          t2) ->
    t1,t2
  
  (** val decompose_tree :
      t
      decomposible **)
  
  let decompose_tree =
    tree_decompose
  
  (** val tree_heightP :
      coq_ShareTree
      ->
      int **)
  
  let rec tree_heightP = function
  | Leaf b0 ->
    0
  | Node (l0,
          r) ->
    plus
      (max
        (tree_heightP
          l0)
        (tree_heightP
          r))
      ((fun x -> x + 1)
      0)
  
  (** val tree_height :
      canonTree
      ->
      int **)
  
  let tree_height t0 =
    tree_heightP
      t0
  
  (** val tree_height_zero :
      canonTree
      ->
      bool **)
  
  let tree_height_zero = function
  | Leaf b0 ->
    true
  | Node (x1,
          x2) ->
    false
  
  (** val tree_heightable :
      t
      heightable **)
  
  let tree_heightable =
    { height =
      tree_height;
      is_height_zero =
      tree_height_zero }
  
  (** val unrel_F :
      (t
      ->
      t
      ->
      t)
      ->
      t
      ->
      t
      ->
      t **)
  
  let unrel_F unrel0 t1 t2 =
    match t1 with
    | Leaf b0 ->
      t2
    | Node (s0,
            s1) ->
      let ltr1,rtr1 =
        decompose
          decompose_tree
          t1
      in
      let ltr2,rtr2 =
        decompose
          decompose_tree
          t2
      in
      (match ltr1 with
       | Leaf b0 ->
         if b0
         then ltr2
         else unrel0
                rtr1
                rtr2
       | Node (s2,
               s3) ->
         unrel0
           ltr1
           ltr2)
  
  (** val unrel_terminate :
      t
      ->
      t
      ->
      t **)
  
  let rec unrel_terminate t1 t2 =
    match t1 with
    | Leaf b0 ->
      t2
    | Node (s0,
            s1) ->
      let ltr1,rtr1 =
        decompose
          decompose_tree
          (Node
          (s0,
          s1))
      in
      let ltr2,rtr2 =
        decompose
          decompose_tree
          t2
      in
      (match ltr1 with
       | Leaf b0 ->
         if b0
         then ltr2
         else unrel_terminate
                rtr1
                rtr2
       | Node (s2,
               s3) ->
         unrel_terminate
           (Node
           (s2,
           s3))
           ltr2)
  
  (** val unrel :
      t
      ->
      t
      ->
      t **)
  
  let rec unrel t1 t2 =
    match t1 with
    | Leaf b0 ->
      t2
    | Node (s0,
            s1) ->
      let ltr1,rtr1 =
        decompose
          decompose_tree
          (Node
          (s0,
          s1))
      in
      let ltr2,rtr2 =
        decompose
          decompose_tree
          t2
      in
      (match ltr1 with
       | Leaf b0 ->
         if b0
         then ltr2
         else unrel
                rtr1
                rtr2
       | Node (s2,
               s3) ->
         unrel
           (Node
           (s2,
           s3))
           ltr2)
  
  (** val coq_Lsh :
      t **)
  
  let coq_Lsh =
    fst
      ((match leftTree with
        | Leaf b0 ->
          if b0
          then top
          else Leaf
                 false
        | Node (s0,
                s1) ->
          relativ_tree
            top
            leftTree),(match rightTree with
                       | Leaf b0 ->
                         if b0
                         then top
                         else Leaf
                                false
                       | Node (s0,
                               s1) ->
                         relativ_tree
                           top
                           rightTree))
  
  (** val coq_Rsh :
      t **)
  
  let coq_Rsh =
    snd
      ((match leftTree with
        | Leaf b0 ->
          if b0
          then top
          else Leaf
                 false
        | Node (s0,
                s1) ->
          relativ_tree
            top
            leftTree),(match rightTree with
                       | Leaf b0 ->
                         if b0
                         then top
                         else Leaf
                                false
                       | Node (s0,
                               s1) ->
                         relativ_tree
                           top
                           rightTree))
  
  (** val splice :
      t
      ->
      t
      ->
      t **)
  
  let splice a0 b0 =
    lub
      (match a0 with
       | Leaf b1 ->
         if b1
         then coq_Lsh
         else Leaf
                false
       | Node (s0,
               s1) ->
         relativ_tree
           coq_Lsh
           a0)
      (match b0 with
       | Leaf b1 ->
         if b1
         then coq_Rsh
         else Leaf
                false
       | Node (s0,
               s1) ->
         relativ_tree
           coq_Rsh
           b0)
  
  (** val mkFull :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree
      option **)
  
  let rec mkFull d0 t0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      match t0 with
      | Leaf b0 ->
        Some
          (Leaf
          b0)
      | Node (l0,
              r) ->
        None)
      (fun n0 ->
      match t0 with
      | Leaf b0 ->
        (match mkFull
                 n0
                 (Leaf
                 b0) with
         | Some t1 ->
           Some
             (Node
             (t1,
             t1))
         | None ->
           None)
      | Node (l0,
              r) ->
        let o =
          mkFull
            n0
            l0
        in
        let o0 =
          mkFull
            n0
            r
        in
        (match o with
         | Some t1 ->
           (match o0 with
            | Some t2 ->
              Some
                (Node
                (t1,
                t2))
            | None ->
              None)
         | None ->
           None))
      d0
  
  (** val tree_round_leftP :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree
      option **)
  
  let rec tree_round_leftP n0 t0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      None)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ ->
        match t0 with
        | Leaf b0 ->
          None
        | Node (s0,
                s1) ->
          (match s0 with
           | Leaf b1 ->
             (match s1 with
              | Leaf b2 ->
                Some
                  (Leaf
                  b1)
              | Node (s2,
                      s3) ->
                None)
           | Node (s2,
                   s3) ->
             None))
        (fun n1 ->
        match t0 with
        | Leaf b0 ->
          Some
            (Leaf
            b0)
        | Node (t1,
                t2) ->
          let o =
            tree_round_leftP
              n'
              t1
          in
          let o0 =
            tree_round_leftP
              n'
              t2
          in
          (match o with
           | Some t1' ->
             (match o0 with
              | Some t2' ->
                Some
                  (Node
                  (t1',
                  t2'))
              | None ->
                None)
           | None ->
             None))
        n')
      n0
  
  (** val tree_round_left :
      int
      ->
      canonTree
      ->
      canonTree
      option **)
  
  let tree_round_left n0 t0 =
    match mkFull
            n0
            t0 with
    | Some t' ->
      (match tree_round_leftP
               n0
               t' with
       | Some t'' ->
         Some
           (mkCanon
             t'')
       | None ->
         None)
    | None ->
      None
  
  (** val roundableL_tree :
      t
      roundableLeft **)
  
  let roundableL_tree =
    tree_round_left
  
  (** val tree_round_rightP :
      int
      ->
      coq_ShareTree
      ->
      coq_ShareTree
      option **)
  
  let rec tree_round_rightP n0 t0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      None)
      (fun n' ->
      (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
        (fun _ ->
        match t0 with
        | Leaf b0 ->
          None
        | Node (s0,
                s1) ->
          (match s0 with
           | Leaf b1 ->
             (match s1 with
              | Leaf b2 ->
                Some
                  (Leaf
                  b2)
              | Node (s2,
                      s3) ->
                None)
           | Node (s2,
                   s3) ->
             None))
        (fun n1 ->
        match t0 with
        | Leaf b0 ->
          Some
            (Leaf
            b0)
        | Node (t1,
                t2) ->
          let o =
            tree_round_rightP
              n'
              t1
          in
          let o0 =
            tree_round_rightP
              n'
              t2
          in
          (match o with
           | Some t1' ->
             (match o0 with
              | Some t2' ->
                Some
                  (Node
                  (t1',
                  t2'))
              | None ->
                None)
           | None ->
             None))
        n')
      n0
  
  (** val tree_round_right :
      int
      ->
      canonTree
      ->
      canonTree
      option **)
  
  let tree_round_right n0 t0 =
    match mkFull
            n0
            t0 with
    | Some t' ->
      (match tree_round_rightP
               n0
               t' with
       | Some t'' ->
         Some
           (mkCanon
             t'')
       | None ->
         None)
    | None ->
      None
  
  (** val roundableR_tree :
      t
      roundableRight **)
  
  let roundableR_tree =
    tree_round_right
  
  (** val tree_avgP :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      coq_ShareTree
      option **)
  
  let rec tree_avgP t1 t2 =
    match t1 with
    | Leaf b1 ->
      (match t2 with
       | Leaf b2 ->
         Some
           (Node
           ((Leaf
           b1),
           (Leaf
           b2)))
       | Node (s0,
               s1) ->
         None)
    | Node (t11,
            t12) ->
      (match t2 with
       | Leaf b0 ->
         None
       | Node (t21,
               t22) ->
         let o =
           tree_avgP
             t11
             t21
         in
         let o0 =
           tree_avgP
             t12
             t22
         in
         (match o with
          | Some t1' ->
            (match o0 with
             | Some t2' ->
               Some
                 (Node
                 (t1',
                 t2'))
             | None ->
               None)
          | None ->
            None))
  
  (** val tree_avg :
      int
      ->
      canonTree
      ->
      canonTree
      ->
      canonTree
      option **)
  
  let tree_avg n0 t1 t2 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      None)
      (fun n' ->
      let o =
        mkFull
          n'
          t1
      in
      let o0 =
        mkFull
          n'
          t2
      in
      (match o with
       | Some t1' ->
         (match o0 with
          | Some t2' ->
            (match tree_avgP
                     t1'
                     t2' with
             | Some t' ->
               Some
                 (mkCanon
                   t')
             | None ->
               None)
          | None ->
            None)
       | None ->
         None))
      n0
  
  (** val avgable_tree :
      t
      avgable **)
  
  let avgable_tree n0 t1 t2 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      None)
      (fun n' ->
      let o =
        mkFull
          n'
          t1
      in
      let o0 =
        mkFull
          n'
          t2
      in
      (match o with
       | Some t1' ->
         (match o0 with
          | Some t2' ->
            (match tree_avgP
                     t1'
                     t2' with
             | Some t' ->
               Some
                 (mkCanon
                   t')
             | None ->
               None)
          | None ->
            None)
       | None ->
         None))
      n0
  
  (** val recompose :
      (canonTree*canonTree)
      ->
      canonTree **)
  
  let recompose = function
  | t1,t2 ->
    (match t1 with
     | Leaf b1 ->
       (match t2 with
        | Leaf b2 ->
          if bool_dec
               b1
               b2
          then Leaf
                 b1
          else Node
                 ((Leaf
                 b1),
                 (Leaf
                 b2))
        | Node (x21,
                x22) ->
          Node
            ((Leaf
            b1),
            (Node
            (x21,
            x22))))
     | Node (x11,
             x12) ->
       Node
         ((Node
         (x11,
         x12)),
         t2))
  
  (** val internal_eq_rew_dep :
      'a1
      ->
      'a2
      ->
      'a1
      ->
      'a2 **)
  
  let internal_eq_rew_dep x f y =
    f
  
  (** val is_height_zero :
      t
      ->
      bool **)
  
  let is_height_zero = function
  | Leaf b0 ->
    true
  | Node (x1,
          x2) ->
    false
  
  (** val countBLeafST :
      int
      ->
      coq_ShareTree
      ->
      int **)
  
  let rec countBLeafST n0 s0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      match s0 with
      | Leaf b0 ->
        if b0
        then (fun x -> x + 1)
               0
        else 0
      | Node (s1,
              s2) ->
        0)
      (fun n' ->
      match s0 with
      | Leaf b0 ->
        if b0
        then plus
               (countBLeafST
                 n'
                 (Leaf
                 true))
               (countBLeafST
                 n'
                 (Leaf
                 true))
        else 0
      | Node (s1,
              s2) ->
        plus
          (countBLeafST
            n'
            s1)
          (countBLeafST
            n'
            s2))
      n0
  
  (** val countBLeafCT :
      int
      ->
      canonTree
      ->
      int **)
  
  let countBLeafCT n0 s0 =
    countBLeafST
      n0
      s0
  
  (** val power :
      int
      ->
      int
      ->
      int **)
  
  let rec power base exp =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun x -> x + 1)
      0)
      (fun n0 ->
      mult
        base
        (power
          base
          n0))
      exp
  
  (** val share_metric :
      int
      ->
      canonTree
      ->
      int **)
  
  let share_metric n0 s0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      0)
      (fun n1 ->
      if le_dec
           (tree_heightable.height
             s0)
           n1
      then plus
             (countBLeafCT
               n1
               s0)
             ((fun x -> x + 1)
             0)
      else 0)
      n0
  
  (** val shareTreeOrd_dec :
      coq_ShareTree
      ->
      coq_ShareTree
      ->
      bool **)
  
  let rec shareTreeOrd_dec s0 t2 =
    match s0 with
    | Leaf b0 ->
      if b0
      then let rec f = function
           | Leaf b1 ->
             if b1
             then true
             else false
           | Node (s2,
                   s3) ->
             if f
                  s2
             then f
                    s3
             else false
           in f
                t2
      else true
    | Node (s1,
            s2) ->
      (match t2 with
       | Leaf b0 ->
         if b0
         then true
         else let iHt1_1 =
                shareTreeOrd_dec
                  s1
                  (Leaf
                  false)
              in
              let iHt1_2 =
                shareTreeOrd_dec
                  s2
                  (Leaf
                  false)
              in
              if iHt1_1
              then iHt1_2
              else false
       | Node (t2_1,
               t2_2) ->
         let iHt1_1 =
           shareTreeOrd_dec
             s1
             t2_1
         in
         let iHt1_2 =
           shareTreeOrd_dec
             s2
             t2_2
         in
         if iHt1_1
         then iHt1_2
         else false)
  
  (** val leq_dec :
      t
      ->
      t
      ->
      bool **)
  
  let leq_dec x y =
    shareTreeOrd_dec
      x
      y
  
  (** val height_zero_eq :
      t
      ->
      bool **)
  
  let height_zero_eq = function
  | Leaf b0 ->
    if b0
    then true
    else false
  | Node (x1,
          x2) ->
    assert false
      (* absurd case *)
  
  (** val add :
      canonTree
      ->
      canonTree
      ->
      canonTree
      option **)
  
  let add x y =
    if eq_dec0
         coq_EqDec_share
         (glb
           x
           y)
         bot
    then Some
           (lub
             x
             y)
    else None
  
  (** val sub :
      canonTree
      ->
      canonTree
      ->
      canonTree
      option **)
  
  let sub x y =
    if eq_dec0
         coq_EqDec_share
         (glb
           x
           y)
         y
    then Some
           (glb
             x
             (comp
               y))
    else None
 end

module Coq_Share = Share

type share
  =
  Coq_Share.t

(** val emptyshare :
    share **)

let emptyshare =
  Coq_Share.bot

type 'a ord =
| Build_Ord

(** val nat_ord :
    int
    ord **)

let nat_ord =
  Build_Ord

type 'a bA = { top0 : 'a;
               bot0 : 'a;
               lub0 : ('a
                      ->
                      'a
                      ->
                      'a);
               glb0 : ('a
                      ->
                      'a
                      ->
                      'a);
               comp0 : ('a
                       ->
                       'a) }

(** val top0 :
    'a1
    ord
    ->
    'a1
    bA
    ->
    'a1 **)

let top0 _ x = x.top0

(** val bot0 :
    'a1
    ord
    ->
    'a1
    bA
    ->
    'a1 **)

let bot0 _ x = x.bot0

(** val lub0 :
    'a1
    ord
    ->
    'a1
    bA
    ->
    'a1
    ->
    'a1
    ->
    'a1 **)

let lub0 _ x = x.lub0

(** val glb0 :
    'a1
    ord
    ->
    'a1
    bA
    ->
    'a1
    ->
    'a1
    ->
    'a1 **)

let glb0 _ x = x.glb0

(** val comp0 :
    'a1
    ord
    ->
    'a1
    bA
    ->
    'a1
    ->
    'a1 **)

let comp0 _ x = x.comp0

(** val share_ba :
    share
    bA **)

let share_ba =
  { top0 =
    Coq_Share.top;
    bot0 =
    Coq_Share.bot;
    lub0 =
    Coq_Share.lub;
    glb0 =
    Coq_Share.glb;
    comp0 =
    Coq_Share.comp }

type ('a,
      'b,
      'c) getable =
  'a
  ->
  'b
  ->
  'c
  (* singleton inductive, whose constructor was Getable *)

(** val get :
    ('a1,
    'a2,
    'a3)
    getable
    ->
    'a1
    ->
    'a2
    ->
    'a3 **)

let get getable0 =
  getable0

type ('a,
      'b) evalable =
| Evalable

(** val override :
    'a1
    eqDec
    ->
    ('a1
    ->
    'a2)
    ->
    ('a1
    ->
    'a2)
    ->
    'a1
    list
    ->
    'a1
    ->
    'a2 **)

let override h ctx ctx' evars =
  fold_right
    (fun e0 rho a' ->
    if eq_dec0
         h
         e0
         a'
    then ctx'
           e0
    else rho
           a')
    ctx
    evars

type ('a,
      'b) varsable =
  'a
  ->
  'b
  list
  (* singleton inductive, whose constructor was Varsable *)

(** val vars :
    ('a1,
    'a2)
    varsable
    ->
    'a1
    ->
    'a2
    list **)

let vars varsable1 =
  varsable1

(** val vars_list :
    ('a1,
    'a2)
    varsable
    ->
    'a1
    list
    ->
    'a2
    list **)

let vars_list h =
  fold_right
    (fun a0 l'0 ->
    app
      (vars
        h
        a0)
      l'0)
    []

(** val varsable_list :
    ('a1,
    'a2)
    varsable
    ->
    ('a1
    list,
    'a2)
    varsable **)

let varsable_list h =
  vars_list
    h

type ('a,
      'b) cheightable =
  'a
  ->
  'b
  ->
  int
  (* singleton inductive, whose constructor was Cheightable *)

(** val cheight :
    ('a1,
    'a2)
    cheightable
    ->
    'a1
    ->
    'a2
    ->
    int **)

let cheight cheightable0 =
  cheightable0

(** val list_cheight :
    ('a1,
    'a2)
    cheightable
    ->
    'a1
    ->
    'a2
    list
    ->
    int **)

let list_cheight h a0 lB =
  fold_right
    max
    0
    (map
      (cheight
        h
        a0)
      lB)

(** val list_cheightable :
    ('a1,
    'a2)
    cheightable
    ->
    ('a1,
    'a2
    list)
    cheightable **)

let list_cheightable h =
  list_cheight
    h

module type SV = 
 sig 
  type t 
  
  val t_eq_dec :
    t
    eqDec
  
  val t_ord :
    t
    ord
  
  val t_lt_dec :
    t
    ->
    t
    ->
    bool
  
  val t_leq_dec :
    t
    ->
    t
    ->
    bool
 end

module Coq_sv_nat = 
 struct 
  type t
    =
    int
  
  (** val t_eq_dec :
      t
      eqDec **)
  
  let t_eq_dec =
    nat_eq_dec
  
  (** val t_ord :
      t
      ord **)
  
  let t_ord =
    nat_ord
  
  (** val t_lt_dec :
      t
      ->
      t
      ->
      bool **)
  
  let t_lt_dec x y =
    lt_dec0
      x
      y
  
  (** val t_leq_dec :
      t
      ->
      t
      ->
      bool **)
  
  let t_leq_dec =
    le_dec
 end

type ('a,
      'b) objectT =
| Vobject of 'a
| Cobject of 'b

(** val objectT_eq_dec :
    'a1
    eqDec
    ->
    'a2
    eqDec
    ->
    ('a1,
    'a2)
    objectT
    eqDec **)

let objectT_eq_dec h h0 a0 a' =
  match a0 with
  | Vobject a22 ->
    (match a' with
     | Vobject a23 ->
       eq_dec0
         h
         a22
         a23
     | Cobject b0 ->
       false)
  | Cobject b0 ->
    (match a' with
     | Vobject a22 ->
       false
     | Cobject b1 ->
       eq_dec0
         h0
         b0
         b1)

(** val obj_vars :
    (('a1,
    'a2)
    objectT,
    'a1)
    varsable **)

let obj_vars = function
| Vobject a0 ->
  a0 :: []
| Cobject b0 ->
  []

module type DOMAIN = 
 sig 
  type e 
  
  val e_eq_dec :
    e
    eqDec
  
  val e_height :
    e
    heightable
  
  val bot :
    e
 end

module Share_Domain = 
 struct 
  type e
    =
    share
  
  (** val e_eq_dec :
      e
      eqDec **)
  
  let e_eq_dec =
    Obj.magic
      Share.coq_EqDec_share
  
  (** val e_height :
      e
      heightable **)
  
  let e_height =
    Obj.magic
      Share.tree_heightable
  
  (** val bot :
      Coq_Share.t **)
  
  let bot =
    Coq_Share.bot
 end

module Bool_Domain = 
 struct 
  type e
    =
    bool
  
  (** val e_eq_dec :
      e
      eqDec **)
  
  let e_eq_dec =
    bool_dec
  
  (** val e_height :
      e
      heightable **)
  
  let e_height =
    { height =
      (fun e0 ->
      0);
      is_height_zero =
      (fun a0 ->
      true) }
  
  (** val bot :
      bool **)
  
  let bot =
    false
 end

module Equation_system = 
 functor (Coq_sv:SV) ->
 functor (Coq_dom':DOMAIN) ->
 struct 
  module Coq_dom = Coq_dom'
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  (** val var_eq_dec :
      var
      eqDec **)
  
  let var_eq_dec =
    Coq_sv.t_eq_dec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  (** val equality_eq_dec :
      equality
      eqDec **)
  
  let equality_eq_dec a0 a' =
    let o,o0 =
      a0
    in
    let o1,o2 =
      a'
    in
    let s0 =
      eq_dec0
        (objectT_eq_dec
          var_eq_dec
          Coq_dom'.e_eq_dec)
        o
        o1
    in
    if s0
    then eq_dec0
           (objectT_eq_dec
             var_eq_dec
             Coq_dom'.e_eq_dec)
           o0
           o2
    else false
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  (** val equation_eq_dec :
      equation
      eqDec **)
  
  let equation_eq_dec a0 a' =
    let p,x =
      a0
    in
    let o,o0 =
      p
    in
    let p0,x0 =
      a'
    in
    let o2,o3 =
      p0
    in
    let s0 =
      eq_dec0
        (objectT_eq_dec
          var_eq_dec
          Coq_dom'.e_eq_dec)
        o
        o2
    in
    if s0
    then let s1 =
           eq_dec0
             (objectT_eq_dec
               var_eq_dec
               Coq_dom'.e_eq_dec)
             o0
             o3
         in
         if s1
         then eq_dec0
                (objectT_eq_dec
                  var_eq_dec
                  Coq_dom'.e_eq_dec)
                x
                x0
         else false
    else false
  
  type nequation
    =
    equation*unit
  
  (** val nequation_eq_dec :
      nequation
      eqDec **)
  
  let nequation_eq_dec a0 a' =
    let e0,x =
      a0
    in
    let p,x0 =
      e0
    in
    let o,o0 =
      p
    in
    let e1,x1 =
      a'
    in
    let p0,x2 =
      e1
    in
    let o2,o3 =
      p0
    in
    let s0 =
      eq_dec0
        (objectT_eq_dec
          var_eq_dec
          Coq_dom'.e_eq_dec)
        o
        o2
    in
    if s0
    then let s1 =
           eq_dec0
             (objectT_eq_dec
               var_eq_dec
               Coq_dom'.e_eq_dec)
             o0
             o3
         in
         if s1
         then eq_dec0
                (objectT_eq_dec
                  var_eq_dec
                  Coq_dom'.e_eq_dec)
                x0
                x2
         else false
    else false
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  (** val sat_equation_system_rect :
      (equality
      list
      ->
      equation
      list
      ->
      nequation
      list
      ->
      'a1)
      ->
      sat_equation_system
      ->
      'a1 **)
  
  let sat_equation_system_rect f s0 =
    let { sat_equalities =
      x;
      sat_equations =
      x0;
      sat_nequations =
      x1 } =
      s0
    in
    f
      x
      x0
      x1
  
  (** val sat_equation_system_rec :
      (equality
      list
      ->
      equation
      list
      ->
      nequation
      list
      ->
      'a1)
      ->
      sat_equation_system
      ->
      'a1 **)
  
  let sat_equation_system_rec f s0 =
    let { sat_equalities =
      x;
      sat_equations =
      x0;
      sat_nequations =
      x1 } =
      s0
    in
    f
      x
      x0
      x1
  
  (** val sat_equalities :
      sat_equation_system
      ->
      equality
      list **)
  
  let sat_equalities s0 =
    s0.sat_equalities
  
  (** val sat_equations :
      sat_equation_system
      ->
      equation
      list **)
  
  let sat_equations s0 =
    s0.sat_equations
  
  (** val sat_nequations :
      sat_equation_system
      ->
      nequation
      list **)
  
  let sat_nequations s0 =
    s0.sat_nequations
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  (** val impl_equation_system_rect :
      (var
      list
      ->
      equality
      list
      ->
      equation
      list
      ->
      nequation
      list
      ->
      'a1)
      ->
      impl_equation_system
      ->
      'a1 **)
  
  let impl_equation_system_rect f i =
    let { impl_exvars =
      x;
      impl_equalities =
      x0;
      impl_equations =
      x1;
      impl_nequations =
      x2 } =
      i
    in
    f
      x
      x0
      x1
      x2
  
  (** val impl_equation_system_rec :
      (var
      list
      ->
      equality
      list
      ->
      equation
      list
      ->
      nequation
      list
      ->
      'a1)
      ->
      impl_equation_system
      ->
      'a1 **)
  
  let impl_equation_system_rec f i =
    let { impl_exvars =
      x;
      impl_equalities =
      x0;
      impl_equations =
      x1;
      impl_nequations =
      x2 } =
      i
    in
    f
      x
      x0
      x1
      x2
  
  (** val impl_exvars :
      impl_equation_system
      ->
      var
      list **)
  
  let impl_exvars i =
    i.impl_exvars
  
  (** val impl_equalities :
      impl_equation_system
      ->
      equality
      list **)
  
  let impl_equalities i =
    i.impl_equalities
  
  (** val impl_equations :
      impl_equation_system
      ->
      equation
      list **)
  
  let impl_equations i =
    i.impl_equations
  
  (** val impl_nequations :
      impl_equation_system
      ->
      nequation
      list **)
  
  let impl_nequations i =
    i.impl_nequations
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  (** val object_get :
      (context,
      coq_object,
      s)
      getable **)
  
  let object_get ctx = function
  | Vobject v0 ->
    ctx
      v0
  | Cobject c0 ->
    c0
  
  (** val eval_equality :
      (context,
      equality)
      evalable **)
  
  let eval_equality =
    Evalable
  
  (** val eval_equation :
      (context,
      equation)
      evalable **)
  
  let eval_equation =
    Evalable
  
  (** val eval_nequation :
      (context,
      nequation)
      evalable **)
  
  let eval_nequation =
    Evalable
  
  (** val evalable_sat_equation_system :
      (context,
      sat_equation_system)
      evalable **)
  
  let evalable_sat_equation_system =
    Evalable
  
  (** val ies2ses :
      impl_equation_system
      ->
      sat_equation_system **)
  
  let ies2ses ies =
    { sat_equalities =
      (impl_equalities
        ies);
      sat_equations =
      (impl_equations
        ies);
      sat_nequations =
      (impl_nequations
        ies) }
  
  (** val evalable_impl_equation_system :
      (context,
      impl_equation_system)
      evalable **)
  
  let evalable_impl_equation_system =
    Evalable
  
  (** val evalable_impl_system :
      (context,
      impl_system)
      evalable **)
  
  let evalable_impl_system =
    Evalable
 end

module System_Features = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   DOMAIN
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 struct 
  (** val object_height : Coq_es.coq_object heightable **)
  
  let object_height =
    { height = (fun obj ->
      match obj with
      | Vobject v0 -> 0
      | Cobject c0 -> Coq_es.Coq_dom.e_height.height c0); is_height_zero =
      (fun a0 ->
      match a0 with
      | Vobject a22 -> true
      | Cobject b0 -> Coq_es.Coq_dom.e_height.is_height_zero b0) }
  
  (** val equality_h : Coq_es.equality -> int **)
  
  let equality_h = function
  | o1,o2 -> max (object_height.height o1) (object_height.height o2)
  
  (** val equality_h_zero : Coq_es.equality is_height_zero_spec **)
  
  let equality_h_zero = function
  | o,o0 ->
    let s0 = object_height.is_height_zero o in
    if s0 then object_height.is_height_zero o0 else false
  
  (** val equality_height : Coq_es.equality heightable **)
  
  let equality_height =
    { height = equality_h; is_height_zero = equality_h_zero }
  
  (** val equation_h : Coq_es.equation -> int **)
  
  let equation_h = function
  | p,o3 ->
    let o1,o2 = p in
    max (max (object_height.height o1) (object_height.height o2))
      (object_height.height o3)
  
  (** val equation_h_zero : Coq_es.equation is_height_zero_spec **)
  
  let equation_h_zero = function
  | p,x ->
    let o,o0 = p in
    let s0 = object_height.is_height_zero o in
    if s0
    then let s1 = object_height.is_height_zero o0 in
         if s1 then object_height.is_height_zero x else false
    else false
  
  (** val equation_height : Coq_es.equation heightable **)
  
  let equation_height =
    { height = equation_h; is_height_zero = equation_h_zero }
  
  (** val nequation_h : Coq_es.nequation -> int **)
  
  let nequation_h = function
  | e0,u ->
    let p,o3 = e0 in
    let o1,o2 = p in
    max (max (object_height.height o1) (object_height.height o2))
      (object_height.height o3)
  
  (** val nequation_h_zero : Coq_es.nequation is_height_zero_spec **)
  
  let nequation_h_zero = function
  | e0,x ->
    let p,x0 = e0 in
    let o,o0 = p in
    let s0 = object_height.is_height_zero o in
    if s0
    then let s1 = object_height.is_height_zero o0 in
         if s1 then object_height.is_height_zero x0 else false
    else false
  
  (** val nequation_height : Coq_es.nequation heightable **)
  
  let nequation_height =
    { height = nequation_h; is_height_zero = nequation_h_zero }
  
  (** val ses_h : Coq_es.sat_equation_system -> int **)
  
  let ses_h ses =
    max
      ((list_heightable equality_height).height (Coq_es.sat_equalities ses))
      (max
        ((list_heightable equation_height).height (Coq_es.sat_equations ses))
        ((list_heightable nequation_height).height
          (Coq_es.sat_nequations ses)))
  
  (** val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec **)
  
  let ses_h_zero a0 =
    let { Coq_es.sat_equalities = l1; Coq_es.sat_equations = l2;
      Coq_es.sat_nequations = l3 } = a0
    in
    let s0 = (list_heightable equality_height).is_height_zero l1 in
    if s0
    then let s1 = (list_heightable equation_height).is_height_zero l2 in
         if s1
         then (list_heightable nequation_height).is_height_zero l3
         else false
    else false
  
  (** val ses_height : Coq_es.sat_equation_system heightable **)
  
  let ses_height =
    { height = ses_h; is_height_zero = ses_h_zero }
  
  (** val ies_h : Coq_es.impl_equation_system -> int **)
  
  let ies_h ies =
    max
      ((list_heightable equality_height).height (Coq_es.impl_equalities ies))
      (max
        ((list_heightable equation_height).height
          (Coq_es.impl_equations ies))
        ((list_heightable nequation_height).height
          (Coq_es.impl_nequations ies)))
  
  (** val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec **)
  
  let ies_h_zero a0 =
    let { Coq_es.impl_exvars = l1; Coq_es.impl_equalities = l2;
      Coq_es.impl_equations = l3; Coq_es.impl_nequations = l4 } = a0
    in
    let s0 = (list_heightable equality_height).is_height_zero l2 in
    if s0
    then let s1 = (list_heightable equation_height).is_height_zero l3 in
         if s1
         then (list_heightable nequation_height).is_height_zero l4
         else false
    else false
  
  (** val ies_height : Coq_es.impl_equation_system heightable **)
  
  let ies_height =
    { height = ies_h; is_height_zero = ies_h_zero }
  
  (** val is_h : Coq_es.impl_system -> int **)
  
  let is_h is =
    max (ies_height.height (fst is)) (ies_height.height (snd is))
  
  (** val is_h_zero : Coq_es.impl_system is_height_zero_spec **)
  
  let is_h_zero = function
  | es1,es2 ->
    let s0 = ies_height.is_height_zero es1 in
    if s0 then ies_height.is_height_zero es2 else false
  
  (** val is_height : Coq_es.impl_system heightable **)
  
  let is_height =
    { height = is_h; is_height_zero = is_h_zero }
  
  (** val var_cheight : (Coq_es.context, Coq_es.var) cheightable **)
  
  let var_cheight x x0 =
    Coq_es.Coq_dom.e_height.height (x x0)
  
  (** val object_cheight :
      (Coq_es.context, Coq_es.coq_object) cheightable **)
  
  let object_cheight ctx = function
  | Vobject v0 -> cheight var_cheight ctx v0
  | Cobject c0 -> 0
  
  (** val equality_cheight :
      (Coq_es.context, Coq_es.equality) cheightable **)
  
  let equality_cheight x = function
  | o,o0 -> max (cheight object_cheight x o) (cheight object_cheight x o0)
  
  (** val equation_cheight :
      (Coq_es.context, Coq_es.equation) cheightable **)
  
  let equation_cheight x = function
  | p,x1 ->
    let o,o0 = p in
    max (cheight object_cheight x o)
      (max (cheight object_cheight x o0) (cheight object_cheight x x1))
  
  (** val nequation_cheight :
      (Coq_es.context, Coq_es.nequation) cheightable **)
  
  let nequation_cheight x = function
  | e0,x1 ->
    let p,x2 = e0 in
    let o,o0 = p in
    max (cheight object_cheight x o)
      (max (cheight object_cheight x o0) (cheight object_cheight x x2))
  
  (** val ses_cheight :
      (Coq_es.context, Coq_es.sat_equation_system) cheightable **)
  
  let ses_cheight ctx ses =
    let { Coq_es.sat_equalities = a0; Coq_es.sat_equations = b0;
      Coq_es.sat_nequations = c0 } = ses
    in
    max (cheight (list_cheightable equality_cheight) ctx a0)
      (max (cheight (list_cheightable equation_cheight) ctx b0)
        (cheight (list_cheightable nequation_cheight) ctx c0))
  
  (** val ies_cheight :
      (Coq_es.context, Coq_es.impl_equation_system) cheightable **)
  
  let ies_cheight ctx ies =
    let { Coq_es.impl_exvars = a0; Coq_es.impl_equalities = b0;
      Coq_es.impl_equations = c0; Coq_es.impl_nequations = d0 } = ies
    in
    max (cheight (list_cheightable equality_cheight) ctx b0)
      (max (cheight (list_cheightable equation_cheight) ctx c0)
        (cheight (list_cheightable nequation_cheight) ctx d0))
  
  (** val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable **)
  
  let is_cheight ctx = function
  | es1,es2 ->
    max (cheight ies_cheight ctx es1) (cheight ies_cheight ctx es2)
  
  (** val object_vars : (Coq_es.coq_object, Coq_es.var) varsable **)
  
  let object_vars =
    obj_vars
  
  (** val equality_vars : (Coq_es.equality, Coq_es.var) varsable **)
  
  let equality_vars = function
  | o,o0 -> app (vars object_vars o) (vars object_vars o0)
  
  (** val equation_vars : (Coq_es.equation, Coq_es.var) varsable **)
  
  let equation_vars = function
  | p,x0 ->
    let o,o0 = p in
    app (vars object_vars o)
      (app (vars object_vars o0) (vars object_vars x0))
  
  (** val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable **)
  
  let nequation_vars = function
  | e0,x0 ->
    let p,x1 = e0 in
    let o,o0 = p in
    app (vars object_vars o)
      (app (vars object_vars o0) (vars object_vars x1))
  
  (** val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable **)
  
  let ses_vars x =
    let { Coq_es.sat_equalities = a0; Coq_es.sat_equations = b0;
      Coq_es.sat_nequations = c0 } = x
    in
    app (vars (varsable_list equality_vars) a0)
      (app (vars (varsable_list equation_vars) b0)
        (vars (varsable_list nequation_vars) c0))
  
  (** val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable **)
  
  let ies_vars x =
    let { Coq_es.impl_exvars = a0; Coq_es.impl_equalities = b0;
      Coq_es.impl_equations = c0; Coq_es.impl_nequations = d0 } = x
    in
    app a0
      (app (vars (varsable_list equality_vars) b0)
        (app (vars (varsable_list equation_vars) c0)
          (vars (varsable_list nequation_vars) d0)))
  
  (** val is_vars : (Coq_es.impl_system, Coq_es.var) varsable **)
  
  let is_vars = function
  | es1,es2 -> app (vars ies_vars es1) (vars ies_vars es2)
  
  (** val vheight : Coq_es.var -> int **)
  
  let vheight v0 =
    0
  
  (** val vheight_zero : Coq_es.var is_height_zero_spec **)
  
  let vheight_zero a0 =
    true
  
  (** val height_var : Coq_es.var heightable **)
  
  let height_var =
    { height = vheight; is_height_zero = vheight_zero }
  
  (** val varsable_var : (Coq_es.var, Coq_es.var) varsable **)
  
  let varsable_var x =
    x :: []
  
  (** val replace_ses_nequations :
      Coq_es.sat_equation_system -> Coq_es.nequation list ->
      Coq_es.sat_equation_system **)
  
  let replace_ses_nequations ses l0 =
    { Coq_es.sat_equalities = (Coq_es.sat_equalities ses);
      Coq_es.sat_equations = (Coq_es.sat_equations ses);
      Coq_es.sat_nequations = l0 }
  
  (** val replace_ies_nequations :
      Coq_es.impl_equation_system -> Coq_es.nequation list ->
      Coq_es.impl_equation_system **)
  
  let replace_ies_nequations ies l0 =
    { Coq_es.impl_exvars = (Coq_es.impl_exvars ies); Coq_es.impl_equalities =
      (Coq_es.impl_equalities ies); Coq_es.impl_equations =
      (Coq_es.impl_equations ies); Coq_es.impl_nequations = l0 }
  
  (** val replace_is_nequations :
      Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
      Coq_es.impl_system **)
  
  let replace_is_nequations is l1 l2 =
    let ies1,ies2 = is in
    (replace_ies_nequations ies1 l1),(replace_ies_nequations ies2 l2)
 end

type ('a, 'b) result =
| Absurd
| Simpler of 'b
| Same of 'a

module type SIMPL_DOM_SPEC = 
 sig 
  module Coq_dom : 
   DOMAIN
  
  val top : Coq_dom.e
  
  val add : Coq_dom.e -> Coq_dom.e -> Coq_dom.e option
  
  val sub : Coq_dom.e -> Coq_dom.e -> Coq_dom.e option
 end

module Share_Simpl_Spec = 
 struct 
  module Coq_dom = Share_Domain
  
  (** val top : Coq_Share.t **)
  
  let top =
    Coq_Share.top
  
  (** val add :
      Coq_Share.canonTree -> Coq_Share.canonTree -> Coq_Share.canonTree
      option **)
  
  let add =
    Coq_Share.add
  
  (** val sub :
      Coq_Share.canonTree -> Coq_Share.canonTree -> Coq_Share.canonTree
      option **)
  
  let sub =
    Coq_Share.sub
 end

module Bool_Simpl_Spec = 
 struct 
  module Coq_dom = Bool_Domain
  
  (** val top : bool **)
  
  let top =
    true
  
  (** val add : Coq_dom.e -> Coq_dom.e -> Coq_dom.e option **)
  
  let add b1 b2 =
    if b1 then if b2 then None else Some true else Some b2
  
  (** val sub : Coq_dom.e -> Coq_dom.e -> Coq_dom.e option **)
  
  let sub b1 = function
  | true -> if b1 then Some false else None
  | false -> Some b1
 end

module Simplifier = 
 functor (Coq_sv:SV) ->
 functor (Coq_dom':DOMAIN) ->
 functor (Coq_es:sig 
  module Coq_dom : 
    sig 
    type e = Coq_dom'.e
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_dom'.e
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_spec:SIMPL_DOM_SPEC with module Coq_dom = Coq_dom') ->
 struct 
  module Coq_sys_features = System_Features(Coq_sv)(Coq_es)
  
  type substitution = (Coq_es.var*Coq_es.coq_object)
  
  (** val sbst_var : substitution -> Coq_es.var **)
  
  let sbst_var sbst =
    fst sbst
  
  (** val sbst_object : substitution -> Coq_es.coq_object **)
  
  let sbst_object sbst =
    snd sbst
  
  (** val mkCsubstitution : Coq_es.var -> Coq_es.s -> substitution **)
  
  let mkCsubstitution x sh =
    x,(Cobject sh)
  
  (** val mkVsubstitution : Coq_es.var -> Coq_es.var -> substitution **)
  
  let mkVsubstitution x y =
    x,(Vobject y)
  
  (** val dec_eq_substitution : substitution eqDec **)
  
  let dec_eq_substitution a0 a' =
    let v0,o = a0 in
    let v1,o0 = a' in
    if eq_dec0 Coq_es.var_eq_dec v0 v1
    then eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Coq_dom'.e_eq_dec) o o0
    else false
  
  (** val evalable_substitution : (Coq_es.context, substitution) evalable **)
  
  let evalable_substitution =
    Evalable
  
  (** val vars_subst : substitution -> Coq_es.var list **)
  
  let vars_subst subst0 =
    (sbst_var subst0) :: (vars Coq_sys_features.object_vars
                           (sbst_object subst0))
  
  (** val varsable_subst : (substitution, Coq_es.var) varsable **)
  
  let varsable_subst =
    vars_subst
  
  type ('a, 'b) substable =
    substitution -> 'a -> 'b
    (* singleton inductive, whose constructor was Substable *)
  
  (** val substable_rect :
      ((substitution -> 'a1 -> 'a2) -> 'a3) -> ('a1, 'a2) substable -> 'a3 **)
  
  let substable_rect f s0 =
    f s0
  
  (** val substable_rec :
      ((substitution -> 'a1 -> 'a2) -> 'a3) -> ('a1, 'a2) substable -> 'a3 **)
  
  let substable_rec f s0 =
    f s0
  
  (** val subst : ('a1, 'a2) substable -> substitution -> 'a1 -> 'a2 **)
  
  let subst substable0 =
    substable0
  
  (** val subst_object :
      substitution -> Coq_es.coq_object -> Coq_es.coq_object **)
  
  let subst_object sbst fp' =
    let x,fp = sbst in
    (match fp' with
     | Vobject v0 ->
       if eq_dec0 Coq_es.var_eq_dec x v0 then fp else Vobject v0
     | Cobject c0 -> Cobject c0)
  
  (** val substable_object :
      (Coq_es.coq_object, Coq_es.coq_object) substable **)
  
  let substable_object =
    subst_object
  
  (** val upd_subst : Coq_es.context -> substitution -> Coq_es.context **)
  
  let upd_subst ctx sbst a' =
    if eq_dec0 Coq_es.var_eq_dec (sbst_var sbst) a'
    then get Coq_es.object_get ctx (sbst_object sbst)
    else ctx a'
  
  (** val subst_substitution :
      substitution -> substitution -> (substitution, unit) result **)
  
  let subst_substitution sbst sbst' =
    let x,o = sbst in
    let x',o' = sbst' in
    if eq_dec0 Coq_es.var_eq_dec x x'
    then (match o with
          | Vobject v1 ->
            (match o' with
             | Vobject v2 ->
               if eq_dec0 Coq_es.var_eq_dec v1 v2
               then Simpler ()
               else Same (mkVsubstitution v1 v2)
             | Cobject c2 -> Same (mkCsubstitution v1 c2))
          | Cobject c1 ->
            (match o' with
             | Vobject v2 -> Same (mkCsubstitution v2 c1)
             | Cobject c2 ->
               if eq_dec0 Coq_dom'.e_eq_dec c1 c2 then Simpler () else Absurd))
    else (match subst substable_object sbst o' with
          | Vobject v2' ->
            if eq_dec0 Coq_es.var_eq_dec x' v2'
            then Simpler ()
            else Same (mkVsubstitution x' v2')
          | Cobject c2' -> Same (mkCsubstitution x' c2'))
  
  (** val substable_substitution :
      (substitution, (substitution, unit) result) substable **)
  
  let substable_substitution =
    subst_substitution
  
  (** val simpl_equation :
      Coq_es.equation -> (Coq_es.equation, (unit, (substitution,
      substitution*substitution) sum) sum) result **)
  
  let simpl_equation eqn = match eqn with
  | p,o ->
    let o0,o1 = p in
    (match o0 with
     | Vobject v1 ->
       (match o1 with
        | Vobject v2 ->
          (match o with
           | Vobject v3 ->
             if eq_dec0 Coq_es.var_eq_dec v1 v3
             then Simpler (Inr (Inl (mkCsubstitution v2 Coq_dom'.bot)))
             else if eq_dec0 Coq_es.var_eq_dec v2 v3
                  then Simpler (Inr (Inl (mkCsubstitution v1 Coq_dom'.bot)))
                  else if eq_dec0 Coq_es.var_eq_dec v1 v2
                       then Simpler (Inr (Inr
                              ((mkCsubstitution v1 Coq_dom'.bot),(mkCsubstitution
                                                                   v3
                                                                   Coq_dom'.bot))))
                       else Same eqn
           | Cobject c3 ->
             if eq_dec0 Coq_dom'.e_eq_dec c3 Coq_dom'.bot
             then if eq_dec0 Coq_es.var_eq_dec v1 v2
                  then Simpler (Inr (Inl (mkCsubstitution v1 Coq_dom'.bot)))
                  else Simpler (Inr (Inr
                         ((mkCsubstitution v1 Coq_dom'.bot),(mkCsubstitution
                                                              v2
                                                              Coq_dom'.bot))))
             else if eq_dec0 Coq_es.var_eq_dec v1 v2
                  then Absurd
                  else Same eqn)
        | Cobject c2 ->
          (match o with
           | Vobject v3 ->
             if eq_dec0 Coq_dom'.e_eq_dec c2 Coq_dom'.bot
             then if eq_dec0 Coq_es.var_eq_dec v1 v3
                  then Simpler (Inl ())
                  else Simpler (Inr (Inl (mkVsubstitution v1 v3)))
             else if eq_dec0 Coq_dom'.e_eq_dec c2 Coq_spec.top
                  then Simpler (Inr (Inr
                         ((mkCsubstitution v1 Coq_dom'.bot),(mkCsubstitution
                                                              v3
                                                              Coq_spec.top))))
                  else Same eqn
           | Cobject c3 ->
             (match Coq_spec.sub c3 c2 with
              | Some c1 -> Simpler (Inr (Inl (mkCsubstitution v1 c1)))
              | None -> Absurd)))
     | Cobject c1 ->
       (match o1 with
        | Vobject v2 ->
          (match o with
           | Vobject v3 ->
             if eq_dec0 Coq_dom'.e_eq_dec c1 Coq_dom'.bot
             then if eq_dec0 Coq_es.var_eq_dec v2 v3
                  then Simpler (Inl ())
                  else Simpler (Inr (Inl (mkVsubstitution v2 v3)))
             else if eq_dec0 Coq_dom'.e_eq_dec c1 Coq_spec.top
                  then Simpler (Inr (Inr
                         ((mkCsubstitution v2 Coq_dom'.bot),(mkCsubstitution
                                                              v3
                                                              Coq_spec.top))))
                  else Same eqn
           | Cobject c3 ->
             (match Coq_spec.sub c3 c1 with
              | Some c2 -> Simpler (Inr (Inl (mkCsubstitution v2 c2)))
              | None -> Absurd))
        | Cobject c2 ->
          (match o with
           | Vobject v3 ->
             (match Coq_spec.add c1 c2 with
              | Some c3 -> Simpler (Inr (Inl (mkCsubstitution v3 c3)))
              | None -> Absurd)
           | Cobject c3 ->
             (match Coq_spec.add c1 c2 with
              | Some c3' ->
                if eq_dec0 Coq_dom'.e_eq_dec c3 c3'
                then Simpler (Inl ())
                else Absurd
              | None -> Absurd))))
  
  (** val subst_equation :
      substitution -> Coq_es.equation -> (Coq_es.equation, (unit,
      (substitution, substitution*substitution) sum) sum) result **)
  
  let subst_equation sbst = function
  | p,fp3 ->
    let fp1,fp2 = p in
    simpl_equation
      (((subst substable_object sbst fp1),(subst substable_object sbst fp2)),
      (subst substable_object sbst fp3))
  
  (** val substable_equation :
      (Coq_es.equation, (Coq_es.equation, (unit, (substitution,
      substitution*substitution) sum) sum) result) substable **)
  
  let substable_equation =
    subst_equation
  
  (** val subst_substitution_list :
      substitution -> substitution list -> substitution list option **)
  
  let rec subst_substitution_list sbst = function
  | [] -> Some []
  | sbst1 :: sbst_list' ->
    (match subst substable_substitution sbst sbst1 with
     | Absurd -> None
     | Simpler y -> subst_substitution_list sbst sbst_list'
     | Same sbst1' ->
       (match subst_substitution_list sbst sbst_list' with
        | Some sbst_list'' -> Some (sbst1' :: sbst_list'')
        | None -> None))
  
  (** val substab_substitution_list :
      (substitution list, substitution list option) substable **)
  
  let substab_substitution_list =
    subst_substitution_list
  
  (** val simpl_equation_list :
      Coq_es.equation list -> (substitution list*Coq_es.equation list) option **)
  
  let rec simpl_equation_list = function
  | [] -> Some ([],[])
  | eqn :: eqn_list' ->
    (match simpl_equation eqn with
     | Absurd -> None
     | Simpler s0 ->
       (match s0 with
        | Inl u -> simpl_equation_list eqn_list'
        | Inr s1 ->
          (match s1 with
           | Inl eq1 ->
             (match simpl_equation_list eqn_list' with
              | Some p -> let eql,eqnl = p in Some ((eq1 :: eql),eqnl)
              | None -> None)
           | Inr p ->
             let eq1,eq2 = p in
             (match simpl_equation_list eqn_list' with
              | Some p0 ->
                let eql,eqnl = p0 in Some ((eq1 :: (eq2 :: eql)),eqnl)
              | None -> None)))
     | Same eqn' ->
       (match simpl_equation_list eqn_list' with
        | Some p -> let eql,eqnl = p in Some (eql,(eqn' :: eqnl))
        | None -> None))
  
  (** val subst_equation_list :
      substitution -> Coq_es.equation list -> (substitution
      list*Coq_es.equation list) option **)
  
  let rec subst_equation_list sbst = function
  | [] -> Some ([],[])
  | eqn :: eqn_list' ->
    (match subst substable_equation sbst eqn with
     | Absurd -> None
     | Simpler y ->
       (match y with
        | Inl y0 -> subst_equation_list sbst eqn_list'
        | Inr y0 ->
          (match y0 with
           | Inl eq1 ->
             (match subst_equation_list sbst eqn_list' with
              | Some p ->
                let eq_list,eqn_list'' = p in
                Some ((eq1 :: eq_list),eqn_list'')
              | None -> None)
           | Inr y1 ->
             let eq1,eq2 = y1 in
             (match subst_equation_list sbst eqn_list' with
              | Some p ->
                let eq_list,eqn_list'' = p in
                Some ((eq1 :: (eq2 :: eq_list)),eqn_list'')
              | None -> None)))
     | Same eqn' ->
       (match subst_equation_list sbst eqn_list' with
        | Some p ->
          let eq_list,eqn_list'' = p in Some (eq_list,(eqn' :: eqn_list''))
        | None -> None))
  
  (** val substable_eq_list :
      (Coq_es.equation list, (substitution list*Coq_es.equation list) option)
      substable **)
  
  let substable_eq_list =
    subst_equation_list
  
  (** val simpl_nequation :
      Coq_es.nequation -> (Coq_es.nequation, unit) result **)
  
  let simpl_nequation neqn = match neqn with
  | e0,u ->
    let p,fp3 = e0 in
    let o,o0 = p in
    (match o with
     | Vobject v0 -> Same neqn
     | Cobject s1 ->
       (match o0 with
        | Vobject v0 -> Same neqn
        | Cobject s2 ->
          (match fp3 with
           | Vobject v0 -> Same neqn
           | Cobject s3 ->
             (match Coq_spec.add s1 s2 with
              | Some s0 ->
                if eq_dec0 Coq_dom'.e_eq_dec s0 s3
                then Absurd
                else Simpler ()
              | None -> Simpler ()))))
  
  (** val subst_nequation :
      substitution -> Coq_es.nequation -> (Coq_es.nequation, unit) result **)
  
  let subst_nequation sbst = function
  | e0,u ->
    let p,fp3 = e0 in
    let fp1,fp2 = p in
    simpl_nequation
      ((((subst substable_object sbst fp1),(subst substable_object sbst fp2)),
      (subst substable_object sbst fp3)),u)
  
  (** val substable_nequation :
      (Coq_es.nequation, (Coq_es.nequation, unit) result) substable **)
  
  let substable_nequation =
    subst_nequation
  
  (** val subst_nequation_list :
      substitution -> Coq_es.nequation list -> Coq_es.nequation list option **)
  
  let rec subst_nequation_list sbst = function
  | [] -> Some []
  | neqn :: l'0 ->
    (match subst_nequation sbst neqn with
     | Absurd -> None
     | Simpler u -> subst_nequation_list sbst l'0
     | Same ne' ->
       (match subst_nequation_list sbst l'0 with
        | Some l'' -> Some (ne' :: l'')
        | None -> None))
  
  (** val substable_neqn_list :
      (Coq_es.nequation list, Coq_es.nequation list option) substable **)
  
  let substable_neqn_list =
    subst_nequation_list
  
  type equation_system = { eqs_substitutions : substitution list;
                           eqs_equations : Coq_es.equation list;
                           eqs_nequations : Coq_es.nequation list }
  
  (** val equation_system_rect :
      (substitution list -> Coq_es.equation list -> Coq_es.nequation list ->
      'a1) -> equation_system -> 'a1 **)
  
  let equation_system_rect f e0 =
    let { eqs_substitutions = x; eqs_equations = x0; eqs_nequations = x1 } =
      e0
    in
    f x x0 x1
  
  (** val equation_system_rec :
      (substitution list -> Coq_es.equation list -> Coq_es.nequation list ->
      'a1) -> equation_system -> 'a1 **)
  
  let equation_system_rec f e0 =
    let { eqs_substitutions = x; eqs_equations = x0; eqs_nequations = x1 } =
      e0
    in
    f x x0 x1
  
  (** val eqs_substitutions : equation_system -> substitution list **)
  
  let eqs_substitutions e0 =
    e0.eqs_substitutions
  
  (** val eqs_equations : equation_system -> Coq_es.equation list **)
  
  let eqs_equations e0 =
    e0.eqs_equations
  
  (** val eqs_nequations : equation_system -> Coq_es.nequation list **)
  
  let eqs_nequations e0 =
    e0.eqs_nequations
  
  (** val evalable_equation_system :
      (Coq_es.context, equation_system) evalable **)
  
  let evalable_equation_system =
    Evalable
  
  (** val size_equation_system : equation_system -> int **)
  
  let size_equation_system eqs =
    plus (length (eqs_substitutions eqs))
      (mult ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0)))
        (length (eqs_equations eqs)))
  
  (** val simpl_equation_system_F :
      (equation_system -> equation_system option) -> equation_system ->
      equation_system option **)
  
  let simpl_equation_system_F simpl_equation_system0 eqs =
    match eqs_substitutions eqs with
    | [] ->
      (match simpl_equation_list (eqs_equations eqs) with
       | Some p ->
         let eq_list',eqn_list' = p in
         (match eq_list' with
          | [] ->
            Some { eqs_substitutions = []; eqs_equations = eqn_list';
              eqs_nequations = (eqs_nequations eqs) }
          | s0 :: l0 ->
            simpl_equation_system0 { eqs_substitutions = eq_list';
              eqs_equations = eqn_list'; eqs_nequations =
              (eqs_nequations eqs) })
       | None -> None)
    | sbst1 :: sbst_list ->
      (match subst substab_substitution_list sbst1 sbst_list with
       | Some sbst_list' ->
         (match subst substable_eq_list sbst1 (eqs_equations eqs) with
          | Some y ->
            let sbst_list'',eqn_list' = y in
            (match subst substable_neqn_list sbst1 (eqs_nequations eqs) with
             | Some neqn_list' ->
               (match simpl_equation_system0 { eqs_substitutions =
                        (app sbst_list' sbst_list''); eqs_equations =
                        eqn_list'; eqs_nequations = neqn_list' } with
                | Some s0 ->
                  Some { eqs_substitutions =
                    (sbst1 :: (eqs_substitutions s0)); eqs_equations =
                    (eqs_equations s0); eqs_nequations =
                    (eqs_nequations s0) }
                | None -> None)
             | None -> None)
          | None -> None)
       | None -> None)
  
  (** val simpl_equation_system_terminate :
      equation_system -> equation_system option **)
  
  let rec simpl_equation_system_terminate eqs =
    match eqs_substitutions eqs with
    | [] ->
      (match simpl_equation_list (eqs_equations eqs) with
       | Some p ->
         let eq_list',eqn_list' = p in
         (match eq_list' with
          | [] ->
            Some { eqs_substitutions = []; eqs_equations = eqn_list';
              eqs_nequations = (eqs_nequations eqs) }
          | s0 :: l0 ->
            simpl_equation_system_terminate { eqs_substitutions = (s0 :: l0);
              eqs_equations = eqn_list'; eqs_nequations =
              (eqs_nequations eqs) })
       | None -> None)
    | sbst1 :: sbst_list ->
      (match subst substab_substitution_list sbst1 sbst_list with
       | Some sbst_list' ->
         (match subst substable_eq_list sbst1 (eqs_equations eqs) with
          | Some y ->
            let sbst_list'',eqn_list' = y in
            (match subst substable_neqn_list sbst1 (eqs_nequations eqs) with
             | Some neqn_list' ->
               (match simpl_equation_system_terminate { eqs_substitutions =
                        (app sbst_list' sbst_list''); eqs_equations =
                        eqn_list'; eqs_nequations = neqn_list' } with
                | Some s0 ->
                  Some { eqs_substitutions =
                    (sbst1 :: (eqs_substitutions s0)); eqs_equations =
                    (eqs_equations s0); eqs_nequations =
                    (eqs_nequations s0) }
                | None -> None)
             | None -> None)
          | None -> None)
       | None -> None)
  
  (** val simpl_equation_system :
      equation_system -> equation_system option **)
  
  let simpl_equation_system x =
    simpl_equation_system_terminate x
  
  type coq_R_simpl_equation_system =
  | R_simpl_equation_system_0 of equation_system * Coq_es.equation list
     * Coq_es.equation list
  | R_simpl_equation_system_1 of equation_system * Coq_es.equation list
     * substitution list * Coq_es.equation list * equation_system option
     * coq_R_simpl_equation_system
  | R_simpl_equation_system_2 of equation_system * Coq_es.equation list
  | R_simpl_equation_system_3 of equation_system * substitution
     * substitution list * Coq_es.equation list * substitution list
     * substitution list * Coq_es.equation list * Coq_es.nequation list
     * equation_system option * coq_R_simpl_equation_system
  | R_simpl_equation_system_4 of equation_system * substitution
     * substitution list * Coq_es.equation list * substitution list
     * substitution list * Coq_es.equation list * Coq_es.nequation list
     * equation_system option * coq_R_simpl_equation_system * equation_system
  | R_simpl_equation_system_5 of equation_system * substitution
     * substitution list * Coq_es.equation list * substitution list
     * substitution list * Coq_es.equation list
  | R_simpl_equation_system_6 of equation_system * substitution
     * substitution list * Coq_es.equation list * substitution list
  | R_simpl_equation_system_7 of equation_system * substitution
     * substitution list * Coq_es.equation list
  
  (** val coq_R_simpl_equation_system_rect :
      (equation_system -> __ -> Coq_es.equation list -> __ -> Coq_es.equation
      list -> __ -> 'a1) -> (equation_system -> __ -> Coq_es.equation list ->
      __ -> substitution list -> Coq_es.equation list -> __ -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 -> 'a1) ->
      (equation_system -> __ -> Coq_es.equation list -> __ -> __ -> 'a1) ->
      (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 ->
      equation_system -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> substitution
      list -> __ -> substitution list -> Coq_es.equation list -> __ -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> __ -> 'a1) ->
      (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> __ -> 'a1) -> equation_system ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 **)
  
  let rec coq_R_simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6 eqs o = function
  | R_simpl_equation_system_0 (eqs0, eqn_list, eqn_list') ->
    f eqs0 __ eqn_list __ eqn_list' __
  | R_simpl_equation_system_1 (eqs0, eqn_list, eq_list', eqn_list', res, r0) ->
    f0 eqs0 __ eqn_list __ eq_list' eqn_list' __ __ res r0
      (coq_R_simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = eq_list'; eqs_equations = eqn_list';
        eqs_nequations = (eqs_nequations eqs0) } res r0)
  | R_simpl_equation_system_2 (eqs0, eqn_list) -> f1 eqs0 __ eqn_list __ __
  | R_simpl_equation_system_3 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list', neqn_list', res, r0) ->
    f2 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ neqn_list' __ res r0
      (coq_R_simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = (app sbst_list' sbst_list''); eqs_equations =
        eqn_list'; eqs_nequations = neqn_list' } res r0) __
  | R_simpl_equation_system_4 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list', neqn_list', res, r0,
                               s0) ->
    f3 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ neqn_list' __ res r0
      (coq_R_simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = (app sbst_list' sbst_list''); eqs_equations =
        eqn_list'; eqs_nequations = neqn_list' } res r0) s0 __
  | R_simpl_equation_system_5 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list') ->
    f4 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ __
  | R_simpl_equation_system_6 (eqs0, sbst1, sbst_list, eqn_list, sbst_list') ->
    f5 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ __
  | R_simpl_equation_system_7 (eqs0, sbst1, sbst_list, eqn_list) ->
    f6 eqs0 sbst1 sbst_list __ eqn_list __ __
  
  (** val coq_R_simpl_equation_system_rec :
      (equation_system -> __ -> Coq_es.equation list -> __ -> Coq_es.equation
      list -> __ -> 'a1) -> (equation_system -> __ -> Coq_es.equation list ->
      __ -> substitution list -> Coq_es.equation list -> __ -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 -> 'a1) ->
      (equation_system -> __ -> Coq_es.equation list -> __ -> __ -> 'a1) ->
      (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 ->
      equation_system -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> substitution
      list -> __ -> substitution list -> Coq_es.equation list -> __ -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> __ -> 'a1) ->
      (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> __ -> 'a1) -> equation_system ->
      equation_system option -> coq_R_simpl_equation_system -> 'a1 **)
  
  let rec coq_R_simpl_equation_system_rec f f0 f1 f2 f3 f4 f5 f6 eqs o = function
  | R_simpl_equation_system_0 (eqs0, eqn_list, eqn_list') ->
    f eqs0 __ eqn_list __ eqn_list' __
  | R_simpl_equation_system_1 (eqs0, eqn_list, eq_list', eqn_list', res, r0) ->
    f0 eqs0 __ eqn_list __ eq_list' eqn_list' __ __ res r0
      (coq_R_simpl_equation_system_rec f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = eq_list'; eqs_equations = eqn_list';
        eqs_nequations = (eqs_nequations eqs0) } res r0)
  | R_simpl_equation_system_2 (eqs0, eqn_list) -> f1 eqs0 __ eqn_list __ __
  | R_simpl_equation_system_3 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list', neqn_list', res, r0) ->
    f2 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ neqn_list' __ res r0
      (coq_R_simpl_equation_system_rec f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = (app sbst_list' sbst_list''); eqs_equations =
        eqn_list'; eqs_nequations = neqn_list' } res r0) __
  | R_simpl_equation_system_4 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list', neqn_list', res, r0,
                               s0) ->
    f3 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ neqn_list' __ res r0
      (coq_R_simpl_equation_system_rec f f0 f1 f2 f3 f4 f5 f6
        { eqs_substitutions = (app sbst_list' sbst_list''); eqs_equations =
        eqn_list'; eqs_nequations = neqn_list' } res r0) s0 __
  | R_simpl_equation_system_5 (eqs0, sbst1, sbst_list, eqn_list, sbst_list',
                               sbst_list'', eqn_list') ->
    f4 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ sbst_list''
      eqn_list' __ __
  | R_simpl_equation_system_6 (eqs0, sbst1, sbst_list, eqn_list, sbst_list') ->
    f5 eqs0 sbst1 sbst_list __ eqn_list __ sbst_list' __ __
  | R_simpl_equation_system_7 (eqs0, sbst1, sbst_list, eqn_list) ->
    f6 eqs0 sbst1 sbst_list __ eqn_list __ __
  
  (** val simpl_equation_system_rect :
      (equation_system -> __ -> Coq_es.equation list -> __ -> Coq_es.equation
      list -> __ -> 'a1) -> (equation_system -> __ -> Coq_es.equation list ->
      __ -> substitution list -> Coq_es.equation list -> __ -> __ -> 'a1 ->
      'a1) -> (equation_system -> __ -> Coq_es.equation list -> __ -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      'a1 -> __ -> 'a1) -> (equation_system -> substitution -> substitution
      list -> __ -> Coq_es.equation list -> __ -> substitution list -> __ ->
      substitution list -> Coq_es.equation list -> __ -> Coq_es.nequation
      list -> __ -> 'a1 -> equation_system -> __ -> 'a1) -> (equation_system
      -> substitution -> substitution list -> __ -> Coq_es.equation list ->
      __ -> substitution list -> __ -> substitution list -> Coq_es.equation
      list -> __ -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> substitution
      list -> __ -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> __ -> 'a1) ->
      equation_system -> 'a1 **)
  
  let rec simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6 eqs =
    let f7 = f6 eqs in
    let f8 = f5 eqs in
    let f9 = f4 eqs in
    let f10 = f3 eqs in
    let f11 = f2 eqs in
    let f12 = f1 eqs in
    let f13 = f0 eqs in
    let f14 = f eqs in
    (match eqs_substitutions eqs with
     | [] ->
       let f15 = f14 __ in
       let f16 = let eqn_list = eqs_equations eqs in f15 eqn_list __ in
       let f17 = f13 __ in
       let f18 = let eqn_list = eqs_equations eqs in f17 eqn_list __ in
       let f19 = f12 __ in
       let f20 = let eqn_list = eqs_equations eqs in f19 eqn_list __ in
       (match simpl_equation_list (eqs_equations eqs) with
        | Some p ->
          let l0,l1 = p in
          let f21 = f18 l0 l1 __ in
          (match l0 with
           | [] -> f16 l1 __
           | s0 :: l2 ->
             let f22 = f21 __ in
             let hrec =
               simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
                 { eqs_substitutions = (s0 :: l2); eqs_equations = l1;
                 eqs_nequations = (eqs_nequations eqs) }
             in
             f22 hrec)
        | None -> f20 __)
     | s0 :: l0 ->
       let f15 = f11 s0 l0 __ in
       let f16 = let eqn_list = eqs_equations eqs in f15 eqn_list __ in
       let f17 = f10 s0 l0 __ in
       let f18 = let eqn_list = eqs_equations eqs in f17 eqn_list __ in
       let f19 = f9 s0 l0 __ in
       let f20 = let eqn_list = eqs_equations eqs in f19 eqn_list __ in
       let f21 = f8 s0 l0 __ in
       let f22 = let eqn_list = eqs_equations eqs in f21 eqn_list __ in
       let f23 = f7 s0 l0 __ in
       let f24 = let eqn_list = eqs_equations eqs in f23 eqn_list __ in
       (match subst substab_substitution_list s0 l0 with
        | Some l1 ->
          let f25 = f22 l1 __ in
          let f26 = f20 l1 __ in
          let f27 = f18 l1 __ in
          let f28 = f16 l1 __ in
          (match subst substable_eq_list s0 (eqs_equations eqs) with
           | Some p ->
             let l2,l3 = p in
             let f29 = f26 l2 l3 __ in
             let f30 = f27 l2 l3 __ in
             let f31 = f28 l2 l3 __ in
             (match subst substable_neqn_list s0 (eqs_nequations eqs) with
              | Some l4 ->
                let f32 = f31 l4 __ in
                let f33 = f30 l4 __ in
                (match simpl_equation_system { eqs_substitutions =
                         (app l1 l2); eqs_equations = l3; eqs_nequations =
                         l4 } with
                 | Some e0 ->
                   let f34 = fun h1 -> f33 h1 e0 __ in
                   let hrec =
                     simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
                       { eqs_substitutions = (app l1 l2); eqs_equations = l3;
                       eqs_nequations = l4 }
                   in
                   f34 hrec
                 | None ->
                   let f34 = fun h1 -> f32 h1 __ in
                   let hrec =
                     simpl_equation_system_rect f f0 f1 f2 f3 f4 f5 f6
                       { eqs_substitutions = (app l1 l2); eqs_equations = l3;
                       eqs_nequations = l4 }
                   in
                   f34 hrec)
              | None -> f29 __)
           | None -> f25 __)
        | None -> f24 __))
  
  (** val simpl_equation_system_rec :
      (equation_system -> __ -> Coq_es.equation list -> __ -> Coq_es.equation
      list -> __ -> 'a1) -> (equation_system -> __ -> Coq_es.equation list ->
      __ -> substitution list -> Coq_es.equation list -> __ -> __ -> 'a1 ->
      'a1) -> (equation_system -> __ -> Coq_es.equation list -> __ -> __ ->
      'a1) -> (equation_system -> substitution -> substitution list -> __ ->
      Coq_es.equation list -> __ -> substitution list -> __ -> substitution
      list -> Coq_es.equation list -> __ -> Coq_es.nequation list -> __ ->
      'a1 -> __ -> 'a1) -> (equation_system -> substitution -> substitution
      list -> __ -> Coq_es.equation list -> __ -> substitution list -> __ ->
      substitution list -> Coq_es.equation list -> __ -> Coq_es.nequation
      list -> __ -> 'a1 -> equation_system -> __ -> 'a1) -> (equation_system
      -> substitution -> substitution list -> __ -> Coq_es.equation list ->
      __ -> substitution list -> __ -> substitution list -> Coq_es.equation
      list -> __ -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> substitution
      list -> __ -> __ -> 'a1) -> (equation_system -> substitution ->
      substitution list -> __ -> Coq_es.equation list -> __ -> __ -> 'a1) ->
      equation_system -> 'a1 **)
  
  let simpl_equation_system_rec =
    simpl_equation_system_rect
  
  (** val coq_R_simpl_equation_system_correct :
      equation_system -> equation_system option ->
      coq_R_simpl_equation_system **)
  
  let coq_R_simpl_equation_system_correct x res =
    simpl_equation_system_rect (fun y _ y1 _ y3 _ z _ ->
      R_simpl_equation_system_0 (y, y1, y3))
      (fun y _ y1 _ y3 y4 _ _ y7 z _ -> R_simpl_equation_system_1 (y, y1, y3,
      y4,
      (simpl_equation_system { eqs_substitutions = y3; eqs_equations = y4;
        eqs_nequations = (eqs_nequations y) }),
      (y7
        (simpl_equation_system { eqs_substitutions = y3; eqs_equations = y4;
          eqs_nequations = (eqs_nequations y) }) __))) (fun y _ y1 _ _ z _ ->
      R_simpl_equation_system_2 (y, y1))
      (fun y y0 y1 _ y3 _ y5 _ y7 y8 _ y10 _ y12 _ z _ ->
      R_simpl_equation_system_3 (y, y0, y1, y3, y5, y7, y8, y10,
      (simpl_equation_system { eqs_substitutions = (app y5 y7);
        eqs_equations = y8; eqs_nequations = y10 }),
      (y12
        (simpl_equation_system { eqs_substitutions = (app y5 y7);
          eqs_equations = y8; eqs_nequations = y10 }) __)))
      (fun y y0 y1 _ y3 _ y5 _ y7 y8 _ y10 _ y12 y13 _ z _ ->
      R_simpl_equation_system_4 (y, y0, y1, y3, y5, y7, y8, y10,
      (simpl_equation_system { eqs_substitutions = (app y5 y7);
        eqs_equations = y8; eqs_nequations = y10 }),
      (y12
        (simpl_equation_system { eqs_substitutions = (app y5 y7);
          eqs_equations = y8; eqs_nequations = y10 }) __), y13))
      (fun y y0 y1 _ y3 _ y5 _ y7 y8 _ _ z _ -> R_simpl_equation_system_5 (y,
      y0, y1, y3, y5, y7, y8)) (fun y y0 y1 _ y3 _ y5 _ _ z _ ->
      R_simpl_equation_system_6 (y, y0, y1, y3, y5))
      (fun y y0 y1 _ y3 _ _ z _ -> R_simpl_equation_system_7 (y, y0, y1, y3))
      x res __
  
  (** val upd_subst_list :
      Coq_es.context -> substitution list -> Coq_es.context **)
  
  let upd_subst_list ctx subst_list0 =
    fold_right (fun vfp ctx' -> upd_subst ctx' vfp) ctx subst_list0
  
  (** val eql2subst : Coq_es.equality -> (substitution, unit) result **)
  
  let eql2subst = function
  | obj,obj0 ->
    (match obj with
     | Vobject v0 ->
       let filtered_var =
         eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Coq_dom'.e_eq_dec) obj0
           (Vobject v0)
       in
       if filtered_var then Simpler () else Same (v0,obj0)
     | Cobject c1 ->
       let obj1 = Cobject c1 in
       (match obj0 with
        | Vobject v0 ->
          let filtered_var =
            eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Coq_dom'.e_eq_dec) obj1
              (Vobject v0)
          in
          if filtered_var then Simpler () else Same (v0,obj1)
        | Cobject c2 ->
          let filtered_var = eq_dec0 Coq_dom'.e_eq_dec c1 c2 in
          if filtered_var then Simpler () else Absurd))
  
  (** val eql2subst_list :
      Coq_es.equality list -> substitution list option **)
  
  let rec eql2subst_list = function
  | [] -> Some []
  | eql :: l'0 ->
    (match eql2subst eql with
     | Absurd -> None
     | Simpler u -> eql2subst_list l'0
     | Same subst' ->
       (match eql2subst_list l'0 with
        | Some l'' -> Some (subst' :: l'')
        | None -> None))
  
  (** val subst2eql : substitution -> Coq_es.equality **)
  
  let subst2eql = function
  | v0,obj -> (Vobject v0),obj
  
  (** val subst2eql_list : substitution list -> Coq_es.equality list **)
  
  let subst2eql_list l0 =
    fold_right (fun sbst l'0 -> (subst2eql sbst) :: l'0) [] l0
  
  (** val wrapped_ses :
      Coq_es.sat_equation_system -> equation_system option **)
  
  let wrapped_ses ses =
    let l1 = Coq_es.sat_equalities ses in
    let l2 = Coq_es.sat_equations ses in
    let l3 = Coq_es.sat_nequations ses in
    (match eql2subst_list l1 with
     | Some l1' ->
       Some { eqs_substitutions = l1'; eqs_equations = l2; eqs_nequations =
         l3 }
     | None -> None)
  
  (** val unwrapped_ses : equation_system -> Coq_es.sat_equation_system **)
  
  let unwrapped_ses ses =
    let l1 = eqs_substitutions ses in
    let l2 = eqs_equations ses in
    let l3 = eqs_nequations ses in
    { Coq_es.sat_equalities = (subst2eql_list l1); Coq_es.sat_equations = l2;
    Coq_es.sat_nequations = l3 }
  
  (** val coq_SATsimplifier :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system option **)
  
  let coq_SATsimplifier ses =
    match wrapped_ses ses with
    | Some ses' ->
      (match simpl_equation_system ses' with
       | Some ses'' -> Some (unwrapped_ses ses'')
       | None -> None)
    | None -> None
  
  (** val ies_simplifier :
      Coq_es.impl_equation_system -> Coq_es.impl_equation_system option **)
  
  let ies_simplifier ies =
    match coq_SATsimplifier (Coq_es.ies2ses ies) with
    | Some ses ->
      Some { Coq_es.impl_exvars = (Coq_es.impl_exvars ies);
        Coq_es.impl_equalities = (Coq_es.sat_equalities ses);
        Coq_es.impl_equations = (Coq_es.sat_equations ses);
        Coq_es.impl_nequations = (Coq_es.sat_nequations ses) }
    | None -> None
  
  (** val subst_list :
      ('a1, 'a1 option) substable -> substitution list -> 'a1 -> 'a1 option **)
  
  let rec subst_list h l0 a0 =
    match l0 with
    | [] -> Some a0
    | sbst :: l'0 ->
      (match subst h sbst a0 with
       | Some a' -> subst_list h l'0 a'
       | None -> None)
  
  (** val subst_list_eqn :
      substitution list -> Coq_es.equation list -> (substitution
      list*Coq_es.equation list) option **)
  
  let rec subst_list_eqn l0 leqn =
    match l0 with
    | [] -> Some ([],leqn)
    | sbst :: l'0 ->
      (match subst substable_eq_list sbst leqn with
       | Some y ->
         let l1,l2 = y in
         let o = subst_list substab_substitution_list l'0 l1 in
         let o0 = subst_list_eqn l'0 l2 in
         (match o with
          | Some l1' ->
            (match o0 with
             | Some p -> let l2',l3' = p in Some ((app l1' l2'),l3')
             | None -> None)
          | None -> None)
       | None -> None)
  
  (** val subst_list_eqs :
      substitution list -> equation_system -> equation_system option **)
  
  let subst_list_eqs l0 eqs =
    let l1 = eqs_substitutions eqs in
    let l2 = eqs_equations eqs in
    let l3 = eqs_nequations eqs in
    let p =
      (subst_list substab_substitution_list l0 l1),(subst_list_eqn l0 l2)
    in
    let o = subst_list substable_neqn_list l0 l3 in
    let o0,o1 = p in
    (match o0 with
     | Some l1' ->
       (match o1 with
        | Some pl ->
          (match o with
           | Some l3' ->
             Some { eqs_substitutions = (app (fst pl) l1'); eqs_equations =
               (snd pl); eqs_nequations = l3' }
           | None -> None)
        | None -> None)
     | None -> None)
  
  (** val exclusive : 'a1 eqDec -> 'a1 list -> 'a1 list -> bool **)
  
  let exclusive h l1 l2 =
    fold_right (fun a0 b0 -> if in_dec h a0 l1 then false else b0) true l2
  
  (** val vars_filter :
      ('a1, 'a2) varsable -> 'a2 eqDec -> 'a1 list -> 'a2 list -> 'a1 list **)
  
  let vars_filter h h0 l1 l2 =
    filter (fun a0 -> exclusive h0 (vars h a0) l2) l1
  
  (** val ses2ies :
      Coq_es.var list -> Coq_es.sat_equation_system ->
      Coq_es.impl_equation_system **)
  
  let ses2ies l0 ses =
    { Coq_es.impl_exvars = l0; Coq_es.impl_equalities =
      (Coq_es.sat_equalities ses); Coq_es.impl_equations =
      (Coq_es.sat_equations ses); Coq_es.impl_nequations =
      (Coq_es.sat_nequations ses) }
  
  (** val is_empty_eqs : equation_system -> bool **)
  
  let is_empty_eqs eqs =
    let p = (eqs_substitutions eqs),(eqs_equations eqs) in
    let l0 = eqs_nequations eqs in
    let l1,l2 = p in
    (match l1 with
     | [] ->
       (match l2 with
        | [] ->
          (match l0 with
           | [] -> true
           | n0 :: l3 -> false)
        | e0 :: l3 -> false)
     | s0 :: l3 -> false)
  
  (** val coq_IMPLsimplifier :
      Coq_es.impl_system -> (Coq_es.impl_system, unit) result **)
  
  let coq_IMPLsimplifier = function
  | ies1,ies2 ->
    let ses54 = Coq_es.ies2ses ies1 in
    let ses55 = Coq_es.ies2ses ies2 in
    let o = wrapped_ses ses54 in
    let o0 = wrapped_ses ses55 in
    (match o with
     | Some eqs1 ->
       (match o0 with
        | Some eqs2 ->
          (match simpl_equation_system eqs1 with
           | Some eqs1' ->
             let l1 = Coq_es.impl_exvars ies1 in
             let l2 = Coq_es.impl_exvars ies2 in
             let lsbst = eqs_substitutions eqs1' in
             let l0 =
               vars_filter varsable_subst Coq_es.var_eq_dec lsbst (app l1 l2)
             in
             (match subst_list_eqs l0 eqs2 with
              | Some eqs2' ->
                (match simpl_equation_system eqs2' with
                 | Some eqs2'' ->
                   if is_empty_eqs eqs2''
                   then Simpler ()
                   else Same
                          ((ses2ies l1 (unwrapped_ses eqs1')),(ses2ies l2
                                                                (unwrapped_ses
                                                                  eqs2'')))
                 | None -> Absurd)
              | None -> Absurd)
           | None -> Simpler ())
        | None -> Absurd)
     | None -> Absurd)
 end

module Round_Average = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e = share
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_Share.t
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_es.sat_equation_system heightable
  
  val ies_h : Coq_es.impl_equation_system -> int
  
  val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_es.impl_equation_system heightable
  
  val is_h : Coq_es.impl_system -> int
  
  val is_h_zero : Coq_es.impl_system is_height_zero_spec
  
  val is_height : Coq_es.impl_system heightable
  
  val var_cheight : (Coq_es.context, Coq_es.var) cheightable
  
  val object_cheight : (Coq_es.context, Coq_es.coq_object) cheightable
  
  val equality_cheight : (Coq_es.context, Coq_es.equality) cheightable
  
  val equation_cheight : (Coq_es.context, Coq_es.equation) cheightable
  
  val nequation_cheight : (Coq_es.context, Coq_es.nequation) cheightable
  
  val ses_cheight : (Coq_es.context, Coq_es.sat_equation_system) cheightable
  
  val ies_cheight : (Coq_es.context, Coq_es.impl_equation_system) cheightable
  
  val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable
  
  val object_vars : (Coq_es.coq_object, Coq_es.var) varsable
  
  val equality_vars : (Coq_es.equality, Coq_es.var) varsable
  
  val equation_vars : (Coq_es.equation, Coq_es.var) varsable
  
  val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable
  
  val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable
  
  val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable
  
  val is_vars : (Coq_es.impl_system, Coq_es.var) varsable
  
  val vheight : Coq_es.var -> int
  
  val vheight_zero : Coq_es.var is_height_zero_spec
  
  val height_var : Coq_es.var heightable
  
  val varsable_var : (Coq_es.var, Coq_es.var) varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system -> Coq_es.nequation list ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system -> Coq_es.nequation list ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
    Coq_es.impl_system
 end) ->
 struct 
  (** val avg_ctx :
      Coq_es.context -> Coq_es.context -> int -> Coq_es.var list ->
      Coq_es.context **)
  
  let avg_ctx ctxL ctxR h l0 v0 =
    if in_dec (eq_dec0 Coq_es.var_eq_dec) v0 l0
    then (match avg
                  (Obj.magic (fun n0 t1 t2 ->
                    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
                      (fun _ ->
                      None)
                      (fun n' ->
                      let o = Share.mkFull n' t1 in
                      let o0 = Share.mkFull n' t2 in
                      (match o with
                       | Some t1' ->
                         (match o0 with
                          | Some t2' ->
                            (match Share.tree_avgP t1' t2' with
                             | Some t' -> Some (Share.mkCanon t')
                             | None -> None)
                          | None -> None)
                       | None -> None))
                      n0)) h (ctxL v0) (ctxR v0) with
          | Some s0 -> s0
          | None -> emptyshare)
    else Coq_Share.recompose ((ctxL v0),(ctxR v0))
  
  (** val rL_ctx :
      Coq_es.context -> int -> Coq_es.var list -> Coq_es.context **)
  
  let rL_ctx ctx h l0 v0 =
    if in_dec (eq_dec0 Coq_es.var_eq_dec) v0 l0
    then (match roundL (Obj.magic Share.roundableL_tree) h (ctx v0) with
          | Some s0 -> s0
          | None -> emptyshare)
    else let sL,sR = decompose (Obj.magic Share.decompose_tree) (ctx v0) in
         sL
  
  (** val rR_ctx :
      Coq_es.context -> int -> Coq_es.var list -> Coq_es.context **)
  
  let rR_ctx ctx h l0 v0 =
    if in_dec (eq_dec0 Coq_es.var_eq_dec) v0 l0
    then (match roundR (Obj.magic Share.roundableR_tree) h (ctx v0) with
          | Some s0 ->
            s0
          | None ->
            emptyshare)
    else let sL,sR =
           decompose
             (Obj.magic
               Share.decompose_tree)
             (ctx
               v0)
         in
         sR
 end

module SAT_Base = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height :
    Coq_es.coq_object
    heightable
  
  val equality_h :
    Coq_es.equality
    ->
    int
  
  val equality_h_zero :
    Coq_es.equality
    is_height_zero_spec
  
  val equality_height :
    Coq_es.equality
    heightable
  
  val equation_h :
    Coq_es.equation
    ->
    int
  
  val equation_h_zero :
    Coq_es.equation
    is_height_zero_spec
  
  val equation_height :
    Coq_es.equation
    heightable
  
  val nequation_h :
    Coq_es.nequation
    ->
    int
  
  val nequation_h_zero :
    Coq_es.nequation
    is_height_zero_spec
  
  val nequation_height :
    Coq_es.nequation
    heightable
  
  val ses_h :
    Coq_es.sat_equation_system
    ->
    int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  module RA = Round_Average(Coq_sv)(Coq_es)(Coq_esf)
  
  type 'a avg_ctx_SAT_prop =
  | Avg_ctx_SAT_prop
  
  (** val avg_ctx_SAT_prop_rect :
      'a1
      heightable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      cheightable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let avg_ctx_SAT_prop_rect h h0 h1 h2 f =
    f
      __
  
  (** val avg_ctx_SAT_prop_rec :
      'a1
      heightable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      cheightable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let avg_ctx_SAT_prop_rec h h0 h1 h2 f =
    f
      __
 end

module IMPL_Base = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height :
    Coq_es.coq_object
    heightable
  
  val equality_h :
    Coq_es.equality
    ->
    int
  
  val equality_h_zero :
    Coq_es.equality
    is_height_zero_spec
  
  val equality_height :
    Coq_es.equality
    heightable
  
  val equation_h :
    Coq_es.equation
    ->
    int
  
  val equation_h_zero :
    Coq_es.equation
    is_height_zero_spec
  
  val equation_height :
    Coq_es.equation
    heightable
  
  val nequation_h :
    Coq_es.nequation
    ->
    int
  
  val nequation_h_zero :
    Coq_es.nequation
    is_height_zero_spec
  
  val nequation_height :
    Coq_es.nequation
    heightable
  
  val ses_h :
    Coq_es.sat_equation_system
    ->
    int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  module SB = SAT_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  module RA = Round_Average(Coq_sv)(Coq_es)(Coq_esf)
  
  type 'a eval_equiv_prop =
  | Eval_equiv_prop
  
  (** val eval_equiv_prop_rect :
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let eval_equiv_prop_rect h h0 f =
    f
      __
  
  (** val eval_equiv_prop_rec :
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let eval_equiv_prop_rec h h0 f =
    f
      __
  
  type 'a avg_ctx_IMPL_prop =
  | Avg_ctx_IMPL_prop
  
  (** val avg_ctx_IMPL_prop_rect :
      'a1
      heightable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      cheightable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let avg_ctx_IMPL_prop_rect h h0 h1 h2 f =
    f
      __
  
  (** val avg_ctx_IMPL_prop_rec :
      'a1
      heightable
      ->
      (Coq_es.context,
      'a1)
      evalable
      ->
      ('a1,
      Coq_es.var)
      varsable
      ->
      (Coq_es.context,
      'a1)
      cheightable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let avg_ctx_IMPL_prop_rec h h0 h1 h2 f =
    f
      __
 end

module SAT_Correctness = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height :
    Coq_es.coq_object
    heightable
  
  val equality_h :
    Coq_es.equality
    ->
    int
  
  val equality_h_zero :
    Coq_es.equality
    is_height_zero_spec
  
  val equality_height :
    Coq_es.equality
    heightable
  
  val equation_h :
    Coq_es.equation
    ->
    int
  
  val equation_h_zero :
    Coq_es.equation
    is_height_zero_spec
  
  val equation_height :
    Coq_es.equation
    heightable
  
  val nequation_h :
    Coq_es.nequation
    ->
    int
  
  val nequation_h_zero :
    Coq_es.nequation
    is_height_zero_spec
  
  val nequation_height :
    Coq_es.nequation
    heightable
  
  val ses_h :
    Coq_es.sat_equation_system
    ->
    int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  module SB = SAT_Base(Coq_sv)(Coq_es)(Coq_esf)
 end

module IMPL_Correctness = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height :
    Coq_es.coq_object
    heightable
  
  val equality_h :
    Coq_es.equality
    ->
    int
  
  val equality_h_zero :
    Coq_es.equality
    is_height_zero_spec
  
  val equality_height :
    Coq_es.equality
    heightable
  
  val equation_h :
    Coq_es.equation
    ->
    int
  
  val equation_h_zero :
    Coq_es.equation
    is_height_zero_spec
  
  val equation_height :
    Coq_es.equation
    heightable
  
  val nequation_h :
    Coq_es.nequation
    ->
    int
  
  val nequation_h_zero :
    Coq_es.nequation
    is_height_zero_spec
  
  val nequation_height :
    Coq_es.nequation
    heightable
  
  val ses_h :
    Coq_es.sat_equation_system
    ->
    int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  module SB = SAT_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  module IB = IMPL_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  module RA = Round_Average(Coq_sv)(Coq_es)(Coq_esf)
 end

module Decompose_Base = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height :
    Coq_es.coq_object
    heightable
  
  val equality_h :
    Coq_es.equality
    ->
    int
  
  val equality_h_zero :
    Coq_es.equality
    is_height_zero_spec
  
  val equality_height :
    Coq_es.equality
    heightable
  
  val equation_h :
    Coq_es.equation
    ->
    int
  
  val equation_h_zero :
    Coq_es.equation
    is_height_zero_spec
  
  val equation_height :
    Coq_es.equation
    heightable
  
  val nequation_h :
    Coq_es.nequation
    ->
    int
  
  val nequation_h_zero :
    Coq_es.nequation
    is_height_zero_spec
  
  val nequation_height :
    Coq_es.nequation
    heightable
  
  val ses_h :
    Coq_es.sat_equation_system
    ->
    int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  (** val context_decompose :
      Coq_es.context
      ->
      Coq_es.context*Coq_es.context **)
  
  let context_decompose ctx =
    (fun v0 ->
      fst
        (decompose
          (Obj.magic
            Share.decompose_tree)
          (ctx
            v0))),(fun v0 ->
      snd
        (decompose
          (Obj.magic
            Share.decompose_tree)
          (ctx
            v0)))
  
  (** val decompose_context :
      Coq_es.context
      decomposible **)
  
  let decompose_context =
    context_decompose
  
  type 'a recomposible =
    ('a*'a)
    ->
    'a
    (* singleton inductive, whose constructor was Recomposible *)
  
  (** val recomposible_rect :
      ((('a1*'a1)
      ->
      'a1)
      ->
      'a2)
      ->
      'a1
      recomposible
      ->
      'a2 **)
  
  let recomposible_rect f r =
    f
      r
  
  (** val recomposible_rec :
      ((('a1*'a1)
      ->
      'a1)
      ->
      'a2)
      ->
      'a1
      recomposible
      ->
      'a2 **)
  
  let recomposible_rec f r =
    f
      r
  
  (** val recompose :
      'a1
      recomposible
      ->
      ('a1*'a1)
      ->
      'a1 **)
  
  let recompose recomposible0 =
    recomposible0
  
  (** val share_recompose :
      share
      recomposible **)
  
  let share_recompose =
    Coq_Share.recompose
  
  (** val context_recompose :
      (Coq_es.context*Coq_es.context)
      ->
      Coq_es.context **)
  
  let context_recompose p v0 =
    recompose
      share_recompose
      ((fst
         p
         v0),(snd
               p
               v0))
  
  (** val ctx_recompose :
      Coq_es.context
      recomposible **)
  
  let ctx_recompose =
    context_recompose
  
  (** val decompose_list :
      'a1
      decomposible
      ->
      'a1
      list
      ->
      'a1
      list*'a1
      list **)
  
  let decompose_list h l0 =
    fold_right
      (fun a0 pl ->
      let aL,aR =
        decompose
          h
          a0
      in
      (aL :: (fst
               pl)),(aR :: (snd
                             pl)))
      ([],[])
      l0
  
  (** val decomposible_list :
      'a1
      decomposible
      ->
      'a1
      list
      decomposible **)
  
  let decomposible_list h =
    decompose_list
      h
  
  (** val decompose_obj :
      Coq_es.coq_object
      ->
      Coq_es.coq_object*Coq_es.coq_object **)
  
  let decompose_obj obj = match obj with
  | Vobject v0 ->
    obj,obj
  | Cobject c0 ->
    let c1,c2 =
      decompose
        (Obj.magic
          Share.decompose_tree)
        c0
    in
    (Cobject
    c1),(Cobject
    c2)
  
  (** val obj_decomposible :
      Coq_es.coq_object
      decomposible **)
  
  let obj_decomposible =
    decompose_obj
  
  (** val decompose_eql :
      Coq_es.equality
      ->
      (Coq_es.coq_object*Coq_es.coq_object)*(Coq_es.coq_object*Coq_es.coq_object) **)
  
  let decompose_eql = function
  | obj1,obj2 ->
    let obj1L,obj1R =
      decompose
        obj_decomposible
        obj1
    in
    let obj2L,obj2R =
      decompose
        obj_decomposible
        obj2
    in
    (obj1L,obj2L),(obj1R,obj2R)
  
  (** val eql_decompose :
      Coq_es.equality
      decomposible **)
  
  let eql_decompose =
    decompose_eql
  
  (** val decompose_eqn :
      Coq_es.equation
      ->
      ((Coq_es.coq_object*Coq_es.coq_object)*Coq_es.coq_object)*((Coq_es.coq_object*Coq_es.coq_object)*Coq_es.coq_object) **)
  
  let decompose_eqn = function
  | p,obj3 ->
    let obj1,obj2 =
      p
    in
    let obj1L,obj1R =
      decompose
        obj_decomposible
        obj1
    in
    let obj2L,obj2R =
      decompose
        obj_decomposible
        obj2
    in
    let obj3L,obj3R =
      decompose
        obj_decomposible
        obj3
    in
    ((obj1L,obj2L),obj3L),((obj1R,obj2R),obj3R)
  
  (** val eqn_decompose :
      Coq_es.equation
      decomposible **)
  
  let eqn_decompose =
    decompose_eqn
  
  (** val decompose_neqn :
      Coq_es.nequation
      ->
      (((Coq_es.coq_object*Coq_es.coq_object)*Coq_es.coq_object)*unit)*(((Coq_es.coq_object*Coq_es.coq_object)*Coq_es.coq_object)*unit) **)
  
  let decompose_neqn = function
  | e0,u ->
    let p,obj3 =
      e0
    in
    let obj1,obj2 =
      p
    in
    let obj1L,obj1R =
      decompose
        obj_decomposible
        obj1
    in
    let obj2L,obj2R =
      decompose
        obj_decomposible
        obj2
    in
    let obj3L,obj3R =
      decompose
        obj_decomposible
        obj3
    in
    (((obj1L,obj2L),obj3L),u),(((obj1R,obj2R),obj3R),u)
  
  (** val neqn_decompose :
      Coq_es.nequation
      decomposible **)
  
  let neqn_decompose =
    decompose_neqn
  
  (** val decompose_ses :
      Coq_es.sat_equation_system
      ->
      Coq_es.sat_equation_system*Coq_es.sat_equation_system **)
  
  let decompose_ses ses =
    let leqlL,leqlR =
      decompose
        (decomposible_list
          eql_decompose)
        (Coq_es.sat_equalities
          ses)
    in
    let leqnL,leqnR =
      decompose
        (decomposible_list
          eqn_decompose)
        (Coq_es.sat_equations
          ses)
    in
    let lneqnL,lneqnR =
      decompose
        (decomposible_list
          neqn_decompose)
        (Coq_es.sat_nequations
          ses)
    in
    { Coq_es.sat_equalities =
    leqlL;
    Coq_es.sat_equations =
    leqnL;
    Coq_es.sat_nequations =
    lneqnL },{ Coq_es.sat_equalities =
    leqlR;
    Coq_es.sat_equations =
    leqnR;
    Coq_es.sat_nequations =
    lneqnR }
  
  (** val ses_decompose :
      Coq_es.sat_equation_system
      decomposible **)
  
  let ses_decompose =
    decompose_ses
  
  (** val decompose_ies :
      Coq_es.impl_equation_system
      ->
      Coq_es.impl_equation_system*Coq_es.impl_equation_system **)
  
  let decompose_ies ies =
    let lex =
      Coq_es.impl_exvars
        ies
    in
    let leqlL,leqlR =
      decompose
        (decomposible_list
          eql_decompose)
        (Coq_es.impl_equalities
          ies)
    in
    let leqnL,leqnR =
      decompose
        (decomposible_list
          eqn_decompose)
        (Coq_es.impl_equations
          ies)
    in
    let lneqnL,lneqnR =
      decompose
        (decomposible_list
          neqn_decompose)
        (Coq_es.impl_nequations
          ies)
    in
    { Coq_es.impl_exvars =
    lex;
    Coq_es.impl_equalities =
    leqlL;
    Coq_es.impl_equations =
    leqnL;
    Coq_es.impl_nequations =
    lneqnL },{ Coq_es.impl_exvars =
    lex;
    Coq_es.impl_equalities =
    leqlR;
    Coq_es.impl_equations =
    leqnR;
    Coq_es.impl_nequations =
    lneqnR }
  
  (** val ies_decompose :
      Coq_es.impl_equation_system
      decomposible **)
  
  let ies_decompose =
    decompose_ies
  
  (** val decompose_is :
      Coq_es.impl_system
      ->
      (Coq_es.impl_equation_system*Coq_es.impl_equation_system)*(Coq_es.impl_equation_system*Coq_es.impl_equation_system) **)
  
  let decompose_is = function
  | ies1,ies2 ->
    let ies1L,ies1R =
      decompose
        ies_decompose
        ies1
    in
    let ies2L,ies2R =
      decompose
        ies_decompose
        ies2
    in
    (ies1L,ies2L),(ies1R,ies2R)
  
  (** val is_decompose :
      Coq_es.impl_system
      decomposible **)
  
  let is_decompose =
    decompose_is
  
  type 'a decompose_height_prop =
  | Decompose_height_prop
  
  (** val decompose_height_prop_rect :
      'a1
      heightable
      ->
      'a1
      decomposible
      ->
      (__
      ->
      __
      ->
      'a2)
      ->
      'a2 **)
  
  let decompose_height_prop_rect h h0 f =
    f
      __
      __
  
  (** val decompose_height_prop_rec :
      'a1
      heightable
      ->
      'a1
      decomposible
      ->
      (__
      ->
      __
      ->
      'a2)
      ->
      'a2 **)
  
  let decompose_height_prop_rec h h0 f =
    f
      __
      __
  
  type ('a,
        'b) decompose_eval_prop =
  | Decompose_eval_prop
  
  (** val decompose_eval_prop_rect :
      'a1
      decomposible
      ->
      'a2
      decomposible
      ->
      ('a2,
      'a1)
      evalable
      ->
      (__
      ->
      'a3)
      ->
      'a3 **)
  
  let decompose_eval_prop_rect h h0 h1 f =
    f
      __
  
  (** val decompose_eval_prop_rec :
      'a1
      decomposible
      ->
      'a2
      decomposible
      ->
      ('a2,
      'a1)
      evalable
      ->
      (__
      ->
      'a3)
      ->
      'a3 **)
  
  let decompose_eval_prop_rec h h0 h1 f =
    f
      __
  
  type 'a decompose_eq_prop =
  | Decompose_eq_prop
  
  (** val decompose_eq_prop_rect :
      'a1
      decomposible
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let decompose_eq_prop_rect h f =
    f
      __
  
  (** val decompose_eq_prop_rec :
      'a1
      decomposible
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let decompose_eq_prop_rec h f =
    f
      __
  
  module IB = IMPL_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  module IC = IMPL_Correctness(Coq_sv)(Coq_es)(Coq_esf)
 end

module SAT_Decompose = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_es.sat_equation_system heightable
  
  val ies_h : Coq_es.impl_equation_system -> int
  
  val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_es.impl_equation_system heightable
  
  val is_h : Coq_es.impl_system -> int
  
  val is_h_zero : Coq_es.impl_system is_height_zero_spec
  
  val is_height : Coq_es.impl_system heightable
  
  val var_cheight : (Coq_es.context, Coq_es.var) cheightable
  
  val object_cheight : (Coq_es.context, Coq_es.coq_object) cheightable
  
  val equality_cheight : (Coq_es.context, Coq_es.equality) cheightable
  
  val equation_cheight : (Coq_es.context, Coq_es.equation) cheightable
  
  val nequation_cheight : (Coq_es.context, Coq_es.nequation) cheightable
  
  val ses_cheight : (Coq_es.context, Coq_es.sat_equation_system) cheightable
  
  val ies_cheight : (Coq_es.context, Coq_es.impl_equation_system) cheightable
  
  val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable
  
  val object_vars : (Coq_es.coq_object, Coq_es.var) varsable
  
  val equality_vars : (Coq_es.equality, Coq_es.var) varsable
  
  val equation_vars : (Coq_es.equation, Coq_es.var) varsable
  
  val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable
  
  val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable
  
  val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable
  
  val is_vars : (Coq_es.impl_system, Coq_es.var) varsable
  
  val vheight : Coq_es.var -> int
  
  val vheight_zero : Coq_es.var is_height_zero_spec
  
  val height_var : Coq_es.var heightable
  
  val varsable_var : (Coq_es.var, Coq_es.var) varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system -> Coq_es.nequation list ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system -> Coq_es.nequation list ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
    Coq_es.impl_system
 end) ->
 struct 
  module DB = Decompose_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  (** val coq_SAT_decompose_F :
      (Coq_es.sat_equation_system -> Coq_es.sat_equation_system list) ->
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system list **)
  
  let coq_SAT_decompose_F sAT_decompose ses =
    if Coq_esf.ses_height.is_height_zero ses
    then ses :: []
    else let sesL,sesR = decompose DB.ses_decompose ses in
         app (sAT_decompose sesL) (sAT_decompose sesR)
  
  (** val coq_SAT_decompose_terminate :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system list **)
  
  let rec coq_SAT_decompose_terminate ses =
    if Coq_esf.ses_height.is_height_zero ses
    then ses :: []
    else let sesL,sesR = decompose DB.ses_decompose ses in
         app (coq_SAT_decompose_terminate sesL)
           (coq_SAT_decompose_terminate sesR)
  
  (** val coq_SAT_decompose :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system list **)
  
  let coq_SAT_decompose x =
    coq_SAT_decompose_terminate x
  
  type coq_R_SAT_decompose =
  | R_SAT_decompose_0 of Coq_es.sat_equation_system
  | R_SAT_decompose_1 of Coq_es.sat_equation_system
     * Coq_es.sat_equation_system * Coq_es.sat_equation_system
     * Coq_es.sat_equation_system list * coq_R_SAT_decompose
     * Coq_es.sat_equation_system list * coq_R_SAT_decompose
  
  (** val coq_R_SAT_decompose_rect :
      (Coq_es.sat_equation_system -> __ -> __ -> 'a1) ->
      (Coq_es.sat_equation_system -> __ -> __ -> Coq_es.sat_equation_system
      -> Coq_es.sat_equation_system -> __ -> Coq_es.sat_equation_system list
      -> coq_R_SAT_decompose -> 'a1 -> Coq_es.sat_equation_system list ->
      coq_R_SAT_decompose -> 'a1 -> 'a1) -> Coq_es.sat_equation_system ->
      Coq_es.sat_equation_system list -> coq_R_SAT_decompose -> 'a1 **)
  
  let rec coq_R_SAT_decompose_rect f f0 ses l0 = function
  | R_SAT_decompose_0 ses0 -> f ses0 __ __
  | R_SAT_decompose_1 (ses0, sesL, sesR, res0, r0, res, r1) ->
    f0 ses0 __ __ sesL sesR __ res0 r0
      (coq_R_SAT_decompose_rect f f0 sesL res0 r0) res r1
      (coq_R_SAT_decompose_rect f f0 sesR res r1)
  
  (** val coq_R_SAT_decompose_rec :
      (Coq_es.sat_equation_system -> __ -> __ -> 'a1) ->
      (Coq_es.sat_equation_system -> __ -> __ -> Coq_es.sat_equation_system
      -> Coq_es.sat_equation_system -> __ -> Coq_es.sat_equation_system list
      -> coq_R_SAT_decompose -> 'a1 -> Coq_es.sat_equation_system list ->
      coq_R_SAT_decompose -> 'a1 -> 'a1) -> Coq_es.sat_equation_system ->
      Coq_es.sat_equation_system list -> coq_R_SAT_decompose -> 'a1 **)
  
  let rec coq_R_SAT_decompose_rec f f0 ses l0 = function
  | R_SAT_decompose_0 ses0 -> f ses0 __ __
  | R_SAT_decompose_1 (ses0, sesL, sesR, res0, r0, res, r1) ->
    f0 ses0 __ __ sesL sesR __ res0 r0
      (coq_R_SAT_decompose_rec f f0 sesL res0 r0) res r1
      (coq_R_SAT_decompose_rec f f0 sesR res r1)
  
  (** val coq_SAT_decompose_rect :
      (Coq_es.sat_equation_system -> __ -> __ -> 'a1) ->
      (Coq_es.sat_equation_system -> __ -> __ -> Coq_es.sat_equation_system
      -> Coq_es.sat_equation_system -> __ -> 'a1 -> 'a1 -> 'a1) ->
      Coq_es.sat_equation_system -> 'a1 **)
  
  let rec coq_SAT_decompose_rect f f0 ses =
    let f1 = f0 ses in
    let f2 = f ses in
    if Coq_esf.ses_height.is_height_zero ses
    then f2 __ __
    else let f3 = f1 __ __ in
         let s0,s1 = decompose DB.ses_decompose ses in
         let f4 = f3 s0 s1 __ in
         let f5 = let hrec = coq_SAT_decompose_rect f f0 s0 in f4 hrec in
         let hrec = coq_SAT_decompose_rect f f0 s1 in f5 hrec
  
  (** val coq_SAT_decompose_rec :
      (Coq_es.sat_equation_system -> __ -> __ -> 'a1) ->
      (Coq_es.sat_equation_system -> __ -> __ -> Coq_es.sat_equation_system
      -> Coq_es.sat_equation_system -> __ -> 'a1 -> 'a1 -> 'a1) ->
      Coq_es.sat_equation_system -> 'a1 **)
  
  let coq_SAT_decompose_rec =
    coq_SAT_decompose_rect
  
  (** val coq_R_SAT_decompose_correct :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system list ->
      coq_R_SAT_decompose **)
  
  let coq_R_SAT_decompose_correct x res =
    coq_SAT_decompose_rect (fun y _ _ z _ -> R_SAT_decompose_0 y)
      (fun y _ _ y2 y3 _ y5 y6 z _ -> R_SAT_decompose_1 (y, y2, y3,
      (coq_SAT_decompose y2), (y5 (coq_SAT_decompose y2) __),
      (coq_SAT_decompose y3), (y6 (coq_SAT_decompose y3) __))) x res __
 end

module IMPL_Decompose = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e = share
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_Share.t
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_es.sat_equation_system heightable
  
  val ies_h : Coq_es.impl_equation_system -> int
  
  val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_es.impl_equation_system heightable
  
  val is_h : Coq_es.impl_system -> int
  
  val is_h_zero : Coq_es.impl_system is_height_zero_spec
  
  val is_height : Coq_es.impl_system heightable
  
  val var_cheight : (Coq_es.context, Coq_es.var) cheightable
  
  val object_cheight : (Coq_es.context, Coq_es.coq_object) cheightable
  
  val equality_cheight : (Coq_es.context, Coq_es.equality) cheightable
  
  val equation_cheight : (Coq_es.context, Coq_es.equation) cheightable
  
  val nequation_cheight : (Coq_es.context, Coq_es.nequation) cheightable
  
  val ses_cheight : (Coq_es.context, Coq_es.sat_equation_system) cheightable
  
  val ies_cheight : (Coq_es.context, Coq_es.impl_equation_system) cheightable
  
  val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable
  
  val object_vars : (Coq_es.coq_object, Coq_es.var) varsable
  
  val equality_vars : (Coq_es.equality, Coq_es.var) varsable
  
  val equation_vars : (Coq_es.equation, Coq_es.var) varsable
  
  val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable
  
  val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable
  
  val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable
  
  val is_vars : (Coq_es.impl_system, Coq_es.var) varsable
  
  val vheight : Coq_es.var -> int
  
  val vheight_zero : Coq_es.var is_height_zero_spec
  
  val height_var : Coq_es.var heightable
  
  val varsable_var : (Coq_es.var, Coq_es.var) varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system -> Coq_es.nequation list ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system -> Coq_es.nequation list ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
    Coq_es.impl_system
 end) ->
 struct 
  module DB = Decompose_Base(Coq_sv)(Coq_es)(Coq_esf)
  
  (** val coq_IMPL_decompose_F :
      (Coq_es.impl_system -> Coq_es.impl_system list) -> Coq_es.impl_system
      -> Coq_es.impl_system list **)
  
  let coq_IMPL_decompose_F iMPL_decompose is =
    if Coq_esf.is_height.is_height_zero is
    then is :: []
    else let isL,isR = decompose DB.is_decompose is in
         app (iMPL_decompose isL) (iMPL_decompose isR)
  
  (** val coq_IMPL_decompose_terminate :
      Coq_es.impl_system -> Coq_es.impl_system list **)
  
  let rec coq_IMPL_decompose_terminate is =
    if Coq_esf.is_height.is_height_zero is
    then is :: []
    else let isL,isR = decompose DB.is_decompose is in
         app (coq_IMPL_decompose_terminate isL)
           (coq_IMPL_decompose_terminate isR)
  
  (** val coq_IMPL_decompose :
      Coq_es.impl_system -> Coq_es.impl_system list **)
  
  let coq_IMPL_decompose x =
    coq_IMPL_decompose_terminate x
  
  type coq_R_IMPL_decompose =
  | R_IMPL_decompose_0 of Coq_es.impl_system
  | R_IMPL_decompose_1 of Coq_es.impl_system * Coq_es.impl_system
     * Coq_es.impl_system * Coq_es.impl_system list * coq_R_IMPL_decompose
     * Coq_es.impl_system list * coq_R_IMPL_decompose
  
  (** val coq_R_IMPL_decompose_rect :
      (Coq_es.impl_system -> __ -> __ -> 'a1) -> (Coq_es.impl_system -> __ ->
      __ -> Coq_es.impl_system -> Coq_es.impl_system -> __ ->
      Coq_es.impl_system list -> coq_R_IMPL_decompose -> 'a1 ->
      Coq_es.impl_system list -> coq_R_IMPL_decompose -> 'a1 -> 'a1) ->
      Coq_es.impl_system -> Coq_es.impl_system list -> coq_R_IMPL_decompose
      -> 'a1 **)
  
  let rec coq_R_IMPL_decompose_rect f f0 is l0 = function
  | R_IMPL_decompose_0 is0 -> f is0 __ __
  | R_IMPL_decompose_1 (is0, isL, isR, res0, r0, res, r1) ->
    f0 is0 __ __ isL isR __ res0 r0
      (coq_R_IMPL_decompose_rect f f0 isL res0 r0) res r1
      (coq_R_IMPL_decompose_rect f f0 isR res r1)
  
  (** val coq_R_IMPL_decompose_rec :
      (Coq_es.impl_system -> __ -> __ -> 'a1) -> (Coq_es.impl_system -> __ ->
      __ -> Coq_es.impl_system -> Coq_es.impl_system -> __ ->
      Coq_es.impl_system list -> coq_R_IMPL_decompose -> 'a1 ->
      Coq_es.impl_system list -> coq_R_IMPL_decompose -> 'a1 -> 'a1) ->
      Coq_es.impl_system -> Coq_es.impl_system list -> coq_R_IMPL_decompose
      -> 'a1 **)
  
  let rec coq_R_IMPL_decompose_rec f f0 is l0 = function
  | R_IMPL_decompose_0 is0 -> f is0 __ __
  | R_IMPL_decompose_1 (is0, isL, isR, res0, r0, res, r1) ->
    f0 is0 __ __ isL isR __ res0 r0
      (coq_R_IMPL_decompose_rec f f0 isL res0 r0) res r1
      (coq_R_IMPL_decompose_rec f f0 isR res r1)
  
  (** val coq_IMPL_decompose_rect :
      (Coq_es.impl_system -> __ -> __ -> 'a1) -> (Coq_es.impl_system -> __ ->
      __ -> Coq_es.impl_system -> Coq_es.impl_system -> __ -> 'a1 -> 'a1 ->
      'a1) -> Coq_es.impl_system -> 'a1 **)
  
  let rec coq_IMPL_decompose_rect f f0 is =
    let f1 = f0 is in
    let f2 = f is in
    if Coq_esf.is_height.is_height_zero is
    then f2 __ __
    else let f3 = f1 __ __ in
         let i,i0 = decompose DB.is_decompose is in
         let f4 = f3 i i0 __ in
         let f5 = let hrec = coq_IMPL_decompose_rect f f0 i in f4 hrec in
         let hrec = coq_IMPL_decompose_rect f f0 i0 in f5 hrec
  
  (** val coq_IMPL_decompose_rec :
      (Coq_es.impl_system -> __ -> __ -> 'a1) -> (Coq_es.impl_system -> __ ->
      __ -> Coq_es.impl_system -> Coq_es.impl_system -> __ -> 'a1 -> 'a1 ->
      'a1) -> Coq_es.impl_system -> 'a1 **)
  
  let coq_IMPL_decompose_rec =
    coq_IMPL_decompose_rect
  
  (** val coq_R_IMPL_decompose_correct :
      Coq_es.impl_system -> Coq_es.impl_system list -> coq_R_IMPL_decompose **)
  
  let coq_R_IMPL_decompose_correct x res =
    coq_IMPL_decompose_rect (fun y _ _ z _ -> R_IMPL_decompose_0 y)
      (fun y _ _ y2 y3 _ y5 y6 z _ -> R_IMPL_decompose_1 (y, y2, y3,
      (coq_IMPL_decompose y2), (y5 (coq_IMPL_decompose y2) __),
      (coq_IMPL_decompose y3), (y6 (coq_IMPL_decompose y3) __))) x res __
 end

module Share2Bool = 
 functor (Coq_sv:SV) ->
 functor (Coq_ses:sig 
  module Coq_dom : 
   sig 
    type e = share
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_Share.t
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_sesf:sig 
  val object_height : Coq_ses.coq_object heightable
  
  val equality_h : Coq_ses.equality -> int
  
  val equality_h_zero : Coq_ses.equality is_height_zero_spec
  
  val equality_height : Coq_ses.equality heightable
  
  val equation_h : Coq_ses.equation -> int
  
  val equation_h_zero : Coq_ses.equation is_height_zero_spec
  
  val equation_height : Coq_ses.equation heightable
  
  val nequation_h : Coq_ses.nequation -> int
  
  val nequation_h_zero : Coq_ses.nequation is_height_zero_spec
  
  val nequation_height : Coq_ses.nequation heightable
  
  val ses_h : Coq_ses.sat_equation_system -> int
  
  val ses_h_zero : Coq_ses.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_ses.sat_equation_system heightable
  
  val ies_h : Coq_ses.impl_equation_system -> int
  
  val ies_h_zero : Coq_ses.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_ses.impl_equation_system heightable
  
  val is_h : Coq_ses.impl_system -> int
  
  val is_h_zero : Coq_ses.impl_system is_height_zero_spec
  
  val is_height : Coq_ses.impl_system heightable
  
  val var_cheight : (Coq_ses.context, Coq_ses.var) cheightable
  
  val object_cheight : (Coq_ses.context, Coq_ses.coq_object) cheightable
  
  val equality_cheight : (Coq_ses.context, Coq_ses.equality) cheightable
  
  val equation_cheight : (Coq_ses.context, Coq_ses.equation) cheightable
  
  val nequation_cheight : (Coq_ses.context, Coq_ses.nequation) cheightable
  
  val ses_cheight :
    (Coq_ses.context, Coq_ses.sat_equation_system) cheightable
  
  val ies_cheight :
    (Coq_ses.context, Coq_ses.impl_equation_system) cheightable
  
  val is_cheight : (Coq_ses.context, Coq_ses.impl_system) cheightable
  
  val object_vars : (Coq_ses.coq_object, Coq_ses.var) varsable
  
  val equality_vars : (Coq_ses.equality, Coq_ses.var) varsable
  
  val equation_vars : (Coq_ses.equation, Coq_ses.var) varsable
  
  val nequation_vars : (Coq_ses.nequation, Coq_ses.var) varsable
  
  val ses_vars : (Coq_ses.sat_equation_system, Coq_ses.var) varsable
  
  val ies_vars : (Coq_ses.impl_equation_system, Coq_ses.var) varsable
  
  val is_vars : (Coq_ses.impl_system, Coq_ses.var) varsable
  
  val vheight : Coq_ses.var -> int
  
  val vheight_zero : Coq_ses.var is_height_zero_spec
  
  val height_var : Coq_ses.var heightable
  
  val varsable_var : (Coq_ses.var, Coq_ses.var) varsable
  
  val replace_ses_nequations :
    Coq_ses.sat_equation_system -> Coq_ses.nequation list ->
    Coq_ses.sat_equation_system
  
  val replace_ies_nequations :
    Coq_ses.impl_equation_system -> Coq_ses.nequation list ->
    Coq_ses.impl_equation_system
  
  val replace_is_nequations :
    Coq_ses.impl_system -> Coq_ses.nequation list -> Coq_ses.nequation list
    -> Coq_ses.impl_system
 end) ->
 functor (Coq_bes:sig 
  module Coq_dom : 
   sig 
    type e = bool
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : bool
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_besf:sig 
  val object_height : Coq_bes.coq_object heightable
  
  val equality_h : Coq_bes.equality -> int
  
  val equality_h_zero : Coq_bes.equality is_height_zero_spec
  
  val equality_height : Coq_bes.equality heightable
  
  val equation_h : Coq_bes.equation -> int
  
  val equation_h_zero : Coq_bes.equation is_height_zero_spec
  
  val equation_height : Coq_bes.equation heightable
  
  val nequation_h : Coq_bes.nequation -> int
  
  val nequation_h_zero : Coq_bes.nequation is_height_zero_spec
  
  val nequation_height : Coq_bes.nequation heightable
  
  val ses_h : Coq_bes.sat_equation_system -> int
  
  val ses_h_zero : Coq_bes.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_bes.sat_equation_system heightable
  
  val ies_h : Coq_bes.impl_equation_system -> int
  
  val ies_h_zero : Coq_bes.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_bes.impl_equation_system heightable
  
  val is_h : Coq_bes.impl_system -> int
  
  val is_h_zero : Coq_bes.impl_system is_height_zero_spec
  
  val is_height : Coq_bes.impl_system heightable
  
  val var_cheight : (Coq_bes.context, Coq_bes.var) cheightable
  
  val object_cheight : (Coq_bes.context, Coq_bes.coq_object) cheightable
  
  val equality_cheight : (Coq_bes.context, Coq_bes.equality) cheightable
  
  val equation_cheight : (Coq_bes.context, Coq_bes.equation) cheightable
  
  val nequation_cheight : (Coq_bes.context, Coq_bes.nequation) cheightable
  
  val ses_cheight :
    (Coq_bes.context, Coq_bes.sat_equation_system) cheightable
  
  val ies_cheight :
    (Coq_bes.context, Coq_bes.impl_equation_system) cheightable
  
  val is_cheight : (Coq_bes.context, Coq_bes.impl_system) cheightable
  
  val object_vars : (Coq_bes.coq_object, Coq_bes.var) varsable
  
  val equality_vars : (Coq_bes.equality, Coq_bes.var) varsable
  
  val equation_vars : (Coq_bes.equation, Coq_bes.var) varsable
  
  val nequation_vars : (Coq_bes.nequation, Coq_bes.var) varsable
  
  val ses_vars : (Coq_bes.sat_equation_system, Coq_bes.var) varsable
  
  val ies_vars : (Coq_bes.impl_equation_system, Coq_bes.var) varsable
  
  val is_vars : (Coq_bes.impl_system, Coq_bes.var) varsable
  
  val vheight : Coq_bes.var -> int
  
  val vheight_zero : Coq_bes.var is_height_zero_spec
  
  val height_var : Coq_bes.var heightable
  
  val varsable_var : (Coq_bes.var, Coq_bes.var) varsable
  
  val replace_ses_nequations :
    Coq_bes.sat_equation_system -> Coq_bes.nequation list ->
    Coq_bes.sat_equation_system
  
  val replace_ies_nequations :
    Coq_bes.impl_equation_system -> Coq_bes.nequation list ->
    Coq_bes.impl_equation_system
  
  val replace_is_nequations :
    Coq_bes.impl_system -> Coq_bes.nequation list -> Coq_bes.nequation list
    -> Coq_bes.impl_system
 end) ->
 struct 
  module DB = Decompose_Base(Coq_sv)(Coq_ses)(Coq_sesf)
  
  type ('a, 'b) coq_S2B =
    'a -> 'b
    (* singleton inductive, whose constructor was Transformation *)
  
  (** val coq_S2B_rect :
      (('a1 -> 'a2) -> 'a3) -> ('a1, 'a2) coq_S2B -> 'a3 **)
  
  let coq_S2B_rect f s0 =
    f s0
  
  (** val coq_S2B_rec :
      (('a1 -> 'a2) -> 'a3) -> ('a1, 'a2) coq_S2B -> 'a3 **)
  
  let coq_S2B_rec f s0 =
    f s0
  
  (** val transform : ('a1, 'a2) coq_S2B -> 'a1 -> 'a2 **)
  
  let transform s2B =
    s2B
  
  (** val sv2bv : Coq_ses.var -> Coq_bes.var **)
  
  let sv2bv sv =
    sv
  
  (** val coq_Sv2bv : (Coq_ses.var, Coq_bes.var) coq_S2B **)
  
  let coq_Sv2bv =
    sv2bv
  
  (** val ss2bs : Coq_ses.s -> Coq_bes.s **)
  
  let ss2bs sc =
    if eq_dec0 Share_Domain.e_eq_dec sc emptyshare then false else true
  
  (** val coq_Ss2bs : (Coq_ses.s, Coq_bes.s) coq_S2B **)
  
  let coq_Ss2bs =
    ss2bs
  
  (** val sobj2bobj : Coq_ses.coq_object -> Coq_bes.coq_object **)
  
  let sobj2bobj = function
  | Vobject v0 -> Vobject (transform coq_Sv2bv v0)
  | Cobject c0 -> Cobject (transform coq_Ss2bs c0)
  
  (** val coq_Sobj2bobj :
      (Coq_ses.coq_object, Coq_bes.coq_object) coq_S2B **)
  
  let coq_Sobj2bobj =
    sobj2bobj
  
  (** val seql2beql : Coq_ses.equality -> Coq_bes.equality **)
  
  let seql2beql = function
  | obj1,obj2 ->
    (transform coq_Sobj2bobj obj1),(transform coq_Sobj2bobj obj2)
  
  (** val coq_Seql2beql : (Coq_ses.equality, Coq_bes.equality) coq_S2B **)
  
  let coq_Seql2beql =
    seql2beql
  
  (** val seqn2beqn : Coq_ses.equation -> Coq_bes.equation **)
  
  let seqn2beqn = function
  | pobj,obj -> (transform coq_Seql2beql pobj),(transform coq_Sobj2bobj obj)
  
  (** val coq_Seqn2beqn : (Coq_ses.equation, Coq_bes.equation) coq_S2B **)
  
  let coq_Seqn2beqn =
    seqn2beqn
  
  (** val sneqn2bneqn : Coq_ses.nequation -> Coq_bes.nequation **)
  
  let sneqn2bneqn = function
  | e0,u ->
    let pobj,obj = e0 in
    ((transform coq_Seql2beql pobj),(transform coq_Sobj2bobj obj)),u
  
  (** val coq_Sneqn2bneqn :
      (Coq_ses.nequation, Coq_bes.nequation) coq_S2B **)
  
  let coq_Sneqn2bneqn =
    sneqn2bneqn
  
  (** val slist2blist : ('a1, 'a2) coq_S2B -> 'a1 list -> 'a2 list **)
  
  let slist2blist h l0 =
    fold_right (fun a0 lb -> (transform h a0) :: lb) [] l0
  
  (** val coq_Slist2blist :
      ('a1, 'a2) coq_S2B -> ('a1 list, 'a2 list) coq_S2B **)
  
  let coq_Slist2blist h =
    slist2blist h
  
  (** val sses2bses :
      Coq_ses.sat_equation_system -> Coq_bes.sat_equation_system **)
  
  let sses2bses sses =
    let leql =
      transform (coq_Slist2blist coq_Seql2beql) (Coq_ses.sat_equalities sses)
    in
    let leqn =
      transform (coq_Slist2blist coq_Seqn2beqn) (Coq_ses.sat_equations sses)
    in
    let lneqn =
      transform (coq_Slist2blist coq_Sneqn2bneqn)
        (Coq_ses.sat_nequations sses)
    in
    { Coq_bes.sat_equalities = leql; Coq_bes.sat_equations = leqn;
    Coq_bes.sat_nequations = lneqn }
  
  (** val coq_Sses2bses :
      (Coq_ses.sat_equation_system, Coq_bes.sat_equation_system) coq_S2B **)
  
  let coq_Sses2bses =
    sses2bses
  
  (** val sies2bies :
      Coq_ses.impl_equation_system -> Coq_bes.impl_equation_system **)
  
  let sies2bies sies =
    let lexvars =
      transform (coq_Slist2blist coq_Sv2bv) (Coq_ses.impl_exvars sies)
    in
    let leql =
      transform (coq_Slist2blist coq_Seql2beql)
        (Coq_ses.impl_equalities sies)
    in
    let leqn =
      transform (coq_Slist2blist coq_Seqn2beqn) (Coq_ses.impl_equations sies)
    in
    let lneqn =
      transform (coq_Slist2blist coq_Sneqn2bneqn)
        (Coq_ses.impl_nequations sies)
    in
    { Coq_bes.impl_exvars = lexvars; Coq_bes.impl_equalities = leql;
    Coq_bes.impl_equations = leqn; Coq_bes.impl_nequations = lneqn }
  
  (** val coq_Sies2bies :
      (Coq_ses.impl_equation_system, Coq_bes.impl_equation_system) coq_S2B **)
  
  let coq_Sies2bies =
    sies2bies
  
  (** val sis2bis : Coq_ses.impl_system -> Coq_bes.impl_system **)
  
  let sis2bis = function
  | ies1,ies2 ->
    (transform coq_Sies2bies ies1),(transform coq_Sies2bies ies2)
  
  (** val coq_Sis2bis :
      (Coq_ses.impl_system, Coq_bes.impl_system) coq_S2B **)
  
  let coq_Sis2bis =
    sis2bis
  
  (** val sctx2bctx : Coq_ses.context -> Coq_bes.context **)
  
  let sctx2bctx ctx v0 =
    transform coq_Ss2bs (ctx v0)
  
  (** val coq_Sctx2bctx : (Coq_ses.context, Coq_bes.context) coq_S2B **)
  
  let coq_Sctx2bctx =
    sctx2bctx
  
  type ('a, 'b, ' a', ' b') transform_prop =
  | Transform_eval
  
  (** val transform_prop_rect :
      ('a1, 'a2) evalable -> ('a3, 'a4) evalable -> 'a2 heightable -> ('a2,
      Coq_ses.var) varsable -> ('a1, Coq_ses.var) cheightable -> ('a1, 'a3)
      coq_S2B -> ('a2, 'a4) coq_S2B -> (__ -> 'a5) -> 'a5 **)
  
  let transform_prop_rect h h0 h1 h2 h3 h4 h5 f =
    f __
  
  (** val transform_prop_rec :
      ('a1, 'a2) evalable -> ('a3, 'a4) evalable -> 'a2 heightable -> ('a2,
      Coq_ses.var) varsable -> ('a1, Coq_ses.var) cheightable -> ('a1, 'a3)
      coq_S2B -> ('a2, 'a4) coq_S2B -> (__ -> 'a5) -> 'a5 **)
  
  let transform_prop_rec h h0 h1 h2 h3 h4 h5 f =
    f __
  
  (** val transformB : Coq_bes.context -> Coq_ses.context **)
  
  let transformB rho v0 =
    if rho v0 then Coq_Share.top else Coq_Share.bot
 end

module Bool_formula = 
 functor (Coq_sv:SV) ->
 struct 
  type var = Coq_sv.t
  
  type context = var -> bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF * bF
  | Coq_orF of bF * bF
  | Coq_implF of bF * bF
  | Coq_negF of bF
  | Coq_exF of var * bF
  | Coq_allF of var * bF
  
  (** val bF_rect :
      (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
      -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
      -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 ->
      'a1) -> bF -> 'a1 **)
  
  let rec bF_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_valF b1 -> f b1
  | Coq_varF v0 -> f0 v0
  | Coq_andF (b1, b2) ->
    f1 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rect f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_orF (b1, b2) ->
    f2 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rect f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_implF (b1, b2) ->
    f3 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rect f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_negF b1 -> f4 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1)
  | Coq_exF (v0, b1) -> f5 v0 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1)
  | Coq_allF (v0, b1) -> f6 v0 b1 (bF_rect f f0 f1 f2 f3 f4 f5 f6 b1)
  
  (** val bF_rec :
      (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
      -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
      -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 ->
      'a1) -> bF -> 'a1 **)
  
  let rec bF_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_valF b1 -> f b1
  | Coq_varF v0 -> f0 v0
  | Coq_andF (b1, b2) ->
    f1 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rec f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_orF (b1, b2) ->
    f2 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rec f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_implF (b1, b2) ->
    f3 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1) b2
      (bF_rec f f0 f1 f2 f3 f4 f5 f6 b2)
  | Coq_negF b1 -> f4 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1)
  | Coq_exF (v0, b1) -> f5 v0 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1)
  | Coq_allF (v0, b1) -> f6 v0 b1 (bF_rec f f0 f1 f2 f3 f4 f5 f6 b1)
  
  (** val bF_vars : bF -> var list **)
  
  let rec bF_vars = function
  | Coq_valF b0 -> []
  | Coq_varF v0 -> v0 :: []
  | Coq_andF (f1, f2) -> app (bF_vars f1) (bF_vars f2)
  | Coq_orF (f1, f2) -> app (bF_vars f1) (bF_vars f2)
  | Coq_implF (f1, f2) -> app (bF_vars f1) (bF_vars f2)
  | Coq_negF f' -> bF_vars f'
  | Coq_exF (v0, f') -> v0 :: (bF_vars f')
  | Coq_allF (v0, f') -> v0 :: (bF_vars f')
  
  (** val bF_varsable : (bF, var) varsable **)
  
  let bF_varsable x =
    bF_vars x
  
  (** val beval : context -> bF -> bool **)
  
  let rec beval ctx = function
  | Coq_valF b0 -> b0
  | Coq_varF v0 -> ctx v0
  | Coq_andF (f1, f2) -> (&&) (beval ctx f1) (beval ctx f2)
  | Coq_orF (f1, f2) -> (||) (beval ctx f1) (beval ctx f2)
  | Coq_implF (f1, f2) -> if beval ctx f1 then beval ctx f2 else true
  | Coq_negF f' -> negb (beval ctx f')
  | Coq_exF (v0, f') ->
    (||)
      (beval (fun a' ->
        if eq_dec0 Coq_sv.t_eq_dec v0 a' then true else ctx a') f')
      (beval (fun a' ->
        if eq_dec0 Coq_sv.t_eq_dec v0 a' then false else ctx a') f')
  | Coq_allF (v0, f') ->
    (&&)
      (beval (fun a' ->
        if eq_dec0 Coq_sv.t_eq_dec v0 a' then true else ctx a') f')
      (beval (fun a' ->
        if eq_dec0 Coq_sv.t_eq_dec v0 a' then false else ctx a') f')
  
  (** val bF_eval : (context, bF) evalable **)
  
  let bF_eval =
    Evalable
  
  (** val bsize : bF -> int **)
  
  let rec bsize = function
  | Coq_andF (f1, f2) ->
    plus (plus ((fun x -> x + 1) 0) (bsize f1)) (bsize f2)
  | Coq_orF (f1, f2) ->
    plus (plus ((fun x -> x + 1) 0) (bsize f1)) (bsize f2)
  | Coq_implF (f1, f2) ->
    plus (plus ((fun x -> x + 1) 0) (bsize f1)) (bsize f2)
  | Coq_negF f' -> plus ((fun x -> x + 1) 0) (bsize f')
  | Coq_exF (v0, f') -> plus ((fun x -> x + 1) 0) (bsize f')
  | Coq_allF (v0, f') -> plus ((fun x -> x + 1) 0) (bsize f')
  | _ -> (fun x -> x + 1) 0
  
  (** val bsubst : bF -> var -> bool -> bF **)
  
  let rec bsubst f v0 b0 =
    match f with
    | Coq_valF b' -> Coq_valF b'
    | Coq_varF v' ->
      if eq_dec0 Coq_sv.t_eq_dec v0 v' then Coq_valF b0 else Coq_varF v'
    | Coq_andF (f1, f2) -> Coq_andF ((bsubst f1 v0 b0), (bsubst f2 v0 b0))
    | Coq_orF (f1, f2) -> Coq_orF ((bsubst f1 v0 b0), (bsubst f2 v0 b0))
    | Coq_implF (f1, f2) -> Coq_implF ((bsubst f1 v0 b0), (bsubst f2 v0 b0))
    | Coq_negF f' -> Coq_negF (bsubst f' v0 b0)
    | Coq_exF (v', f') ->
      if eq_dec0 Coq_sv.t_eq_dec v0 v'
      then Coq_exF (v', f')
      else Coq_exF (v', (bsubst f' v0 b0))
    | Coq_allF (v', f') ->
      if eq_dec0 Coq_sv.t_eq_dec v0 v'
      then Coq_allF (v', f')
      else Coq_allF (v', (bsubst f' v0 b0))
  
  (** val bF_eq_dec : bF eqDec **)
  
  let rec bF_eq_dec b0 a' =
    match b0 with
    | Coq_valF b1 ->
      (match a' with
       | Coq_valF b2 -> bool_dec b1 b2
       | _ -> false)
    | Coq_varF v0 ->
      (match a' with
       | Coq_varF v1 -> eq_dec0 Coq_sv.t_eq_dec v0 v1
       | _ -> false)
    | Coq_andF (b1, b2) ->
      (match a' with
       | Coq_andF (a'1, a'2) ->
         let iHa1 = bF_eq_dec b1 a'1 in
         let iHa2 = bF_eq_dec b2 a'2 in if iHa1 then iHa2 else false
       | _ -> false)
    | Coq_orF (b1, b2) ->
      (match a' with
       | Coq_orF (a'1, a'2) ->
         let iHa1 = bF_eq_dec b1 a'1 in
         let iHa2 = bF_eq_dec b2 a'2 in if iHa1 then iHa2 else false
       | _ -> false)
    | Coq_implF (b1, b2) ->
      (match a' with
       | Coq_implF (a'1, a'2) ->
         let iHa1 = bF_eq_dec b1 a'1 in
         let iHa2 = bF_eq_dec b2 a'2 in if iHa1 then iHa2 else false
       | _ -> false)
    | Coq_negF b1 ->
      (match a' with
       | Coq_negF a'0 -> bF_eq_dec b1 a'0
       | _ -> false)
    | Coq_exF (v0, b1) ->
      (match a' with
       | Coq_exF (v1, a'0) ->
         let iHa = bF_eq_dec b1 a'0 in
         if iHa then eq_dec0 Coq_sv.t_eq_dec v0 v1 else false
       | _ -> false)
    | Coq_allF (v0, b1) ->
      (match a' with
       | Coq_allF (v1, a'0) ->
         let iHa = bF_eq_dec b1 a'0 in
         if iHa then eq_dec0 Coq_sv.t_eq_dec v0 v1 else false
       | _ -> false)
 end

module BF_solver = 
 functor (Coq_sv:SV) ->
 functor (Coq_bf:sig 
  type var = Coq_sv.t
  
  type context = var -> bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF * bF
  | Coq_orF of bF * bF
  | Coq_implF of bF * bF
  | Coq_negF of bF
  | Coq_exF of var * bF
  | Coq_allF of var * bF
  
  val bF_rect :
    (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
    -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF ->
    'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) ->
    bF -> 'a1
  
  val bF_rec :
    (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
    -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF ->
    'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) ->
    bF -> 'a1
  
  val bF_vars : bF -> var list
  
  val bF_varsable : (bF, var) varsable
  
  val beval : context -> bF -> bool
  
  val bF_eval : (context, bF) evalable
  
  val bsize : bF -> int
  
  val bsubst : bF -> var -> bool -> bF
  
  val bF_eq_dec : bF eqDec
 end) ->
 struct 
  type fType =
  | Coq_bT of bool
  | Coq_fT of Coq_bf.bF
  
  (** val fType_rect :
      (bool -> 'a1) -> (Coq_bf.bF -> 'a1) -> fType -> 'a1 **)
  
  let fType_rect f f0 = function
  | Coq_bT x -> f x
  | Coq_fT x -> f0 x
  
  (** val fType_rec : (bool -> 'a1) -> (Coq_bf.bF -> 'a1) -> fType -> 'a1 **)
  
  let fType_rec f f0 = function
  | Coq_bT x -> f x
  | Coq_fT x -> f0 x
  
  (** val check_bval : Coq_bf.bF -> fType **)
  
  let check_bval f = match f with
  | Coq_bf.Coq_valF b0 -> Coq_bT b0
  | _ -> Coq_fT f
  
  (** val fsimpl_onepass : Coq_bf.bF -> Coq_bf.bF **)
  
  let rec fsimpl_onepass f = match f with
  | Coq_bf.Coq_andF (f1, f2) ->
    (match check_bval f1 with
     | Coq_bT b0 -> if b0 then f2 else Coq_bf.Coq_valF false
     | Coq_fT f1' ->
       (match check_bval f2 with
        | Coq_bT b0 -> if b0 then f1 else Coq_bf.Coq_valF false
        | Coq_fT f2' -> Coq_bf.Coq_andF (f1, f2)))
  | Coq_bf.Coq_orF (f1, f2) ->
    (match check_bval f1 with
     | Coq_bT b0 -> if b0 then Coq_bf.Coq_valF true else f2
     | Coq_fT f1' ->
       (match check_bval
                f2 with
        | Coq_bT b0 ->
          if b0
          then Coq_bf.Coq_valF
                 true
          else f1
        | Coq_fT f2' ->
          Coq_bf.Coq_orF
            (f1,
            f2)))
  | Coq_bf.Coq_implF (f1,
                      f2) ->
    (match check_bval
             f1 with
     | Coq_bT b0 ->
       if b0
       then f2
       else Coq_bf.Coq_valF
              true
     | Coq_fT f1' ->
       (match check_bval
                f2 with
        | Coq_bT b0 ->
          if b0
          then Coq_bf.Coq_valF
                 true
          else Coq_bf.Coq_negF
                 f1
        | Coq_fT f2' ->
          Coq_bf.Coq_implF
            (f1,
            f2)))
  | Coq_bf.Coq_negF f' ->
    (match check_bval
             f' with
     | Coq_bT b0 ->
       Coq_bf.Coq_valF
         (negb
           b0)
     | Coq_fT f'' ->
       Coq_bf.Coq_negF
         f')
  | Coq_bf.Coq_exF (v0,
                    f') ->
    (match check_bval
             f' with
     | Coq_bT b0 ->
       Coq_bf.Coq_valF
         b0
     | Coq_fT f'' ->
       Coq_bf.Coq_exF
         (v0,
         f'))
  | Coq_bf.Coq_allF (v0,
                     f') ->
    (match check_bval
             f' with
     | Coq_bT b0 ->
       Coq_bf.Coq_valF
         b0
     | Coq_fT f'' ->
       Coq_bf.Coq_allF
         (v0,
         f'))
  | _ ->
    f
  
  (** val fsimpl :
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let rec fsimpl = function
  | Coq_bf.Coq_andF (f1,
                     f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_andF
      ((fsimpl
         f1),
      (fsimpl
        f2)))
  | Coq_bf.Coq_orF (f1,
                    f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_orF
      ((fsimpl
         f1),
      (fsimpl
        f2)))
  | Coq_bf.Coq_implF (f1,
                      f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_implF
      ((fsimpl
         f1),
      (fsimpl
        f2)))
  | Coq_bf.Coq_negF f' ->
    fsimpl_onepass
      (Coq_bf.Coq_negF
      (fsimpl
        f'))
  | Coq_bf.Coq_exF (v0,
                    f') ->
    fsimpl_onepass
      (Coq_bf.Coq_exF
      (v0,
      (fsimpl
        f')))
  | Coq_bf.Coq_allF (v0,
                     f') ->
    fsimpl_onepass
      (Coq_bf.Coq_allF
      (v0,
      (fsimpl
        f')))
  | x ->
    x
  
  (** val quan_elim_exF :
      Coq_bf.var
      ->
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let quan_elim_exF v0 f =
    fsimpl_onepass
      (Coq_bf.Coq_orF
      ((fsimpl
         (Coq_bf.bsubst
           f
           v0
           true)),
      (fsimpl
        (Coq_bf.bsubst
          f
          v0
          false))))
  
  (** val quan_elim_allF :
      Coq_bf.var
      ->
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let quan_elim_allF v0 f =
    fsimpl_onepass
      (Coq_bf.Coq_andF
      ((fsimpl
         (Coq_bf.bsubst
           f
           v0
           true)),
      (fsimpl
        (Coq_bf.bsubst
          f
          v0
          false))))
  
  (** val quan_elim :
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let rec quan_elim = function
  | Coq_bf.Coq_andF (f1,
                     f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_andF
      ((quan_elim
         f1),
      (quan_elim
        f2)))
  | Coq_bf.Coq_orF (f1,
                    f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_orF
      ((quan_elim
         f1),
      (quan_elim
        f2)))
  | Coq_bf.Coq_implF (f1,
                      f2) ->
    fsimpl_onepass
      (Coq_bf.Coq_implF
      ((quan_elim
         f1),
      (quan_elim
        f2)))
  | Coq_bf.Coq_negF f' ->
    fsimpl_onepass
      (Coq_bf.Coq_negF
      (quan_elim
        f'))
  | Coq_bf.Coq_exF (v0,
                    f') ->
    quan_elim_exF
      v0
      (quan_elim
        f')
  | Coq_bf.Coq_allF (v0,
                     f') ->
    quan_elim_allF
      v0
      (quan_elim
        f')
  | x ->
    x
  
  type ('a,
        'b) var_free_prop =
  | Var_free_prop
  
  (** val var_free_prop_rect :
      ('a1,
      Coq_bf.var)
      varsable
      ->
      ('a2,
      'a1)
      evalable
      ->
      (__
      ->
      'a3)
      ->
      'a3 **)
  
  let var_free_prop_rect h h0 f =
    f
      __
  
  (** val var_free_prop_rec :
      ('a1,
      Coq_bf.var)
      varsable
      ->
      ('a2,
      'a1)
      evalable
      ->
      (__
      ->
      'a3)
      ->
      'a3 **)
  
  let var_free_prop_rec h h0 f =
    f
      __
  
  (** val bsolver :
      Coq_bf.bF
      ->
      bool
      option **)
  
  let bsolver f =
    match check_bval
            (quan_elim
              (fsimpl
                f)) with
    | Coq_bT b0 ->
      Some
        b0
    | Coq_fT b0 ->
      None
 end

module Interpreter = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      bool
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      bool
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_bf:sig 
  type var
    =
    Coq_sv.t
  
  type context
    =
    var
    ->
    bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF
     * bF
  | Coq_orF of bF
     * bF
  | Coq_implF of bF
     * bF
  | Coq_negF of bF
  | Coq_exF of var
     * bF
  | Coq_allF of var
     * bF
  
  val bF_rect :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_rec :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_vars :
    bF
    ->
    var
    list
  
  val bF_varsable :
    (bF,
    var)
    varsable
  
  val beval :
    context
    ->
    bF
    ->
    bool
  
  val bF_eval :
    (context,
    bF)
    evalable
  
  val bsize :
    bF
    ->
    int
  
  val bsubst :
    bF
    ->
    var
    ->
    bool
    ->
    bF
  
  val bF_eq_dec :
    bF
    eqDec
 end) ->
 struct 
  module Coq_sys_features = System_Features(Coq_sv)(Coq_es)
  
  type ('a,
        'b) coq_B2F =
    'a
    ->
    'b
    (* singleton inductive, whose constructor was Interpret *)
  
  (** val coq_B2F_rect :
      (('a1
      ->
      'a2)
      ->
      'a3)
      ->
      ('a1,
      'a2)
      coq_B2F
      ->
      'a3 **)
  
  let coq_B2F_rect f b0 =
    f
      b0
  
  (** val coq_B2F_rec :
      (('a1
      ->
      'a2)
      ->
      'a3)
      ->
      ('a1,
      'a2)
      coq_B2F
      ->
      'a3 **)
  
  let coq_B2F_rec f b0 =
    f
      b0
  
  (** val interpret :
      ('a1,
      'a2)
      coq_B2F
      ->
      'a1
      ->
      'a2 **)
  
  let interpret b2F =
    b2F
  
  (** val v_int :
      Coq_bf.var
      ->
      Coq_bf.bF **)
  
  let v_int v0 =
    Coq_bf.Coq_varF
      v0
  
  (** val b2f_v :
      (Coq_bf.var,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_v =
    v_int
  
  (** val b_int :
      bool
      ->
      Coq_bf.bF **)
  
  let b_int b0 =
    Coq_bf.Coq_valF
      b0
  
  (** val b2f_b :
      (bool,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_b =
    b_int
  
  (** val obj_int :
      Coq_es.coq_object
      ->
      Coq_bf.bF **)
  
  let obj_int = function
  | Vobject v0 ->
    Coq_bf.Coq_varF
      v0
  | Cobject c0 ->
    Coq_bf.Coq_valF
      c0
  
  (** val b2f_obj :
      (Coq_es.coq_object,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_obj =
    obj_int
  
  (** val eql_int :
      Coq_es.equality
      ->
      Coq_bf.bF **)
  
  let eql_int = function
  | obj1,obj2 ->
    (match obj1 with
     | Vobject v0 ->
       (match obj2 with
        | Vobject v1 ->
          Coq_bf.Coq_orF
            ((Coq_bf.Coq_andF
            ((interpret
               b2f_obj
               obj1),
            (interpret
              b2f_obj
              obj2))),
            (Coq_bf.Coq_andF
            ((Coq_bf.Coq_negF
            (interpret
              b2f_obj
              obj1)),
            (Coq_bf.Coq_negF
            (interpret
              b2f_obj
              obj2)))))
        | Cobject c0 ->
          if c0
          then Coq_bf.Coq_varF
                 v0
          else Coq_bf.Coq_negF
                 (Coq_bf.Coq_varF
                 v0))
     | Cobject c0 ->
       (match obj2 with
        | Vobject v0 ->
          if c0
          then Coq_bf.Coq_varF
                 v0
          else Coq_bf.Coq_negF
                 (Coq_bf.Coq_varF
                 v0)
        | Cobject c2 ->
          if bool_dec
               c0
               c2
          then Coq_bf.Coq_valF
                 true
          else Coq_bf.Coq_valF
                 false))
  
  (** val b2f_eql :
      (Coq_es.equality,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_eql =
    eql_int
  
  (** val eqn_int :
      Coq_es.equation
      ->
      Coq_bf.bF **)
  
  let eqn_int = function
  | p,obj3 ->
    let obj1,obj2 =
      p
    in
    let p0 =
      obj1,obj2
    in
    let o,o0 =
      p0
    in
    (match o with
     | Vobject v0 ->
       (match o0 with
        | Vobject v2 ->
          (match obj3 with
           | Vobject v1 ->
             Coq_bf.Coq_orF
               ((Coq_bf.Coq_andF
               ((Coq_bf.Coq_negF
               (interpret
                 b2f_obj
                 obj1)),
               (interpret
                 b2f_eql
                 (obj2,obj3)))),
               (Coq_bf.Coq_andF
               ((interpret
                  b2f_obj
                  obj1),
               (Coq_bf.Coq_andF
               ((Coq_bf.Coq_negF
               (interpret
                 b2f_obj
                 obj2)),
               (interpret
                 b2f_obj
                 obj3))))))
           | Cobject s0 ->
             if s0
             then Coq_bf.Coq_orF
                    ((Coq_bf.Coq_andF
                    ((Coq_bf.Coq_varF
                    v0),
                    (Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v2)))),
                    (Coq_bf.Coq_andF
                    ((Coq_bf.Coq_varF
                    v2),
                    (Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v0)))))
             else Coq_bf.Coq_andF
                    ((Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v0)),
                    (Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v2))))
        | Cobject c1 ->
          if c1
          then (match obj3 with
                | Vobject v2 ->
                  Coq_bf.Coq_andF
                    ((Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v0)),
                    (Coq_bf.Coq_varF
                    v2))
                | Cobject c2 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_negF
                              (Coq_bf.Coq_varF
                              v0)
                       else Coq_bf.Coq_valF
                              false
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2)))
          else (match obj3 with
                | Vobject v2 ->
                  interpret
                    b2f_eql
                    ((Vobject
                    v0),(Vobject
                    v2))
                | Cobject c2 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_negF
                              (Coq_bf.Coq_varF
                              v0)
                       else Coq_bf.Coq_valF
                              false
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2))))
     | Cobject c1 ->
       if c1
       then (match o0 with
             | Vobject v0 ->
               (match obj3 with
                | Vobject v2 ->
                  Coq_bf.Coq_andF
                    ((Coq_bf.Coq_negF
                    (Coq_bf.Coq_varF
                    v0)),
                    (Coq_bf.Coq_varF
                    v2))
                | Cobject c2 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_negF
                              (Coq_bf.Coq_varF
                              v0)
                       else Coq_bf.Coq_valF
                              false
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2)))
             | Cobject c2 ->
               (match obj3 with
                | Vobject v0 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_valF
                              false
                       else Coq_bf.Coq_varF
                              v0
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2))
                | Cobject c3 ->
                  if c1
                  then Coq_bf.Coq_valF
                         ((&&)
                           (negb
                             c2)
                           c3)
                  else if bool_dec
                            c2
                            c3
                       then Coq_bf.Coq_valF
                              true
                       else Coq_bf.Coq_valF
                              false))
       else (match o0 with
             | Vobject v0 ->
               (match obj3 with
                | Vobject v2 ->
                  interpret
                    b2f_eql
                    ((Vobject
                    v0),(Vobject
                    v2))
                | Cobject c2 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_negF
                              (Coq_bf.Coq_varF
                              v0)
                       else Coq_bf.Coq_valF
                              false
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2)))
             | Cobject c2 ->
               (match obj3 with
                | Vobject v0 ->
                  if c1
                  then if c2
                       then Coq_bf.Coq_valF
                              false
                       else Coq_bf.Coq_varF
                              v0
                  else interpret
                         b2f_eql
                         ((Vobject
                         v0),(Cobject
                         c2))
                | Cobject c3 ->
                  if c1
                  then Coq_bf.Coq_valF
                         ((&&)
                           (negb
                             c2)
                           c3)
                  else if bool_dec
                            c2
                            c3
                       then Coq_bf.Coq_valF
                              true
                       else Coq_bf.Coq_valF
                              false)))
  
  (** val b2f_eqn :
      (Coq_es.equation,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_eqn =
    eqn_int
  
  (** val neqn_int :
      Coq_es.nequation
      ->
      Coq_bf.bF **)
  
  let neqn_int = function
  | e0,u ->
    Coq_bf.Coq_negF
      (eqn_int
        e0)
  
  (** val b2f_neqn :
      (Coq_es.nequation,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_neqn =
    neqn_int
  
  (** val list_int :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      'a1
      list
      ->
      Coq_bf.bF **)
  
  let list_int h l0 =
    fold_right
      (fun a0 f ->
      Coq_bf.Coq_andF
      ((interpret
         h
         a0),
      f))
      (Coq_bf.Coq_valF
      true)
      l0
  
  (** val b2f_list :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      ('a1
      list,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_list h =
    list_int
      h
  
  (** val fold_right_nodup :
      ('a2
      ->
      'a1
      ->
      'a1)
      ->
      'a1
      ->
      'a2
      list
      ->
      'a2
      eqDec
      ->
      'a1 **)
  
  let rec fold_right_nodup f a0 l0 h =
    match l0 with
    | [] ->
      a0
    | b0 :: l'0 ->
      if in_dec
           (eq_dec0
             h)
           b0
           l'0
      then fold_right_nodup
             f
             a0
             l'0
             h
      else f
             b0
             (fold_right_nodup
               f
               a0
               l'0
               h)
  
  (** val exF_quan :
      Coq_bf.var
      list
      ->
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let exF_quan l0 f =
    fold_right_nodup
      (fun x x0 ->
      Coq_bf.Coq_exF
      (x,
      x0))
      f
      l0
      Coq_es.var_eq_dec
  
  (** val allF_quan :
      Coq_bf.var
      list
      ->
      Coq_bf.bF
      ->
      Coq_bf.bF **)
  
  let allF_quan l0 f =
    fold_right_nodup
      (fun x x0 ->
      Coq_bf.Coq_allF
      (x,
      x0))
      f
      l0
      Coq_es.var_eq_dec
  
  (** val ses_int :
      Coq_es.sat_equation_system
      ->
      Coq_bf.bF **)
  
  let ses_int ses =
    let f1 =
      interpret
        (b2f_list
          b2f_eql)
        (Coq_es.sat_equalities
          ses)
    in
    let f2 =
      interpret
        (b2f_list
          b2f_eqn)
        (Coq_es.sat_equations
          ses)
    in
    let f3 =
      interpret
        (b2f_list
          b2f_neqn)
        (Coq_es.sat_nequations
          ses)
    in
    Coq_bf.Coq_andF
    (f1,
    (Coq_bf.Coq_andF
    (f2,
    f3)))
  
  (** val b2f_ses :
      (Coq_es.sat_equation_system,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_ses =
    ses_int
  
  (** val ies_int :
      Coq_es.impl_equation_system
      ->
      Coq_bf.bF **)
  
  let ies_int ies =
    let f1 =
      interpret
        (b2f_list
          b2f_eql)
        (Coq_es.impl_equalities
          ies)
    in
    let f2 =
      interpret
        (b2f_list
          b2f_eqn)
        (Coq_es.impl_equations
          ies)
    in
    let f3 =
      interpret
        (b2f_list
          b2f_neqn)
        (Coq_es.impl_nequations
          ies)
    in
    exF_quan
      (Coq_es.impl_exvars
        ies)
      (Coq_bf.Coq_andF
      (f1,
      (Coq_bf.Coq_andF
      (f2,
      f3))))
  
  (** val b2f_ies :
      (Coq_es.impl_equation_system,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_ies =
    ies_int
  
  (** val is_int :
      Coq_es.impl_system
      ->
      Coq_bf.bF **)
  
  let is_int = function
  | ies1,ies2 ->
    let f1 =
      interpret
        b2f_ies
        ies1
    in
    let f2 =
      interpret
        b2f_ies
        ies2
    in
    Coq_bf.Coq_implF
    (f1,
    f2)
  
  (** val b2f_is :
      (Coq_es.impl_system,
      Coq_bf.bF)
      coq_B2F **)
  
  let b2f_is =
    is_int
  
  type 'a vars_interpret_prop =
  | Vars_interpret_prop
  
  (** val vars_interpret_prop_rect :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      ('a1,
      Coq_bf.var)
      varsable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let vars_interpret_prop_rect h h0 f =
    f
      __
  
  (** val vars_interpret_prop_rec :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      ('a1,
      Coq_bf.var)
      varsable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let vars_interpret_prop_rec h h0 f =
    f
      __
  
  (** val var_vars :
      (Coq_bf.var,
      Coq_bf.var)
      varsable **)
  
  let var_vars x =
    x :: []
  
  type 'a beval_interpret_prop =
  | Beval_interpret_prop
  
  (** val beval_interpret_prop_rect :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      (Coq_bf.context,
      'a1)
      evalable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let beval_interpret_prop_rect h h0 f =
    f
      __
  
  (** val beval_interpret_prop_rec :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      (Coq_bf.context,
      'a1)
      evalable
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let beval_interpret_prop_rec h h0 f =
    f
      __
  
  (** val is_free :
      Coq_bf.var
      ->
      Coq_es.impl_equation_system
      ->
      bool **)
  
  let is_free v0 ies =
    if in_dec
         (eq_dec0
           Coq_es.var_eq_dec)
         v0
         (Coq_es.impl_exvars
           ies)
    then false
    else true
  
  type 'a in_not_free_prop =
  | In_not_free_prop
  
  (** val in_not_free_prop_rect :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let in_not_free_prop_rect h f =
    f
      __
  
  (** val in_not_free_prop_rec :
      ('a1,
      Coq_bf.bF)
      coq_B2F
      ->
      (__
      ->
      'a2)
      ->
      'a2 **)
  
  let in_not_free_prop_rec h f =
    f
      __
 end

module Bool_solver = 
 functor (Coq_sv:SV) ->
 functor (Coq_bf:sig 
  type var
    =
    Coq_sv.t
  
  type context
    =
    var
    ->
    bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF
     * bF
  | Coq_orF of bF
     * bF
  | Coq_implF of bF
     * bF
  | Coq_negF of bF
  | Coq_exF of var
     * bF
  | Coq_allF of var
     * bF
  
  val bF_rect :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_rec :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_vars :
    bF
    ->
    var
    list
  
  val bF_varsable :
    (bF,
    var)
    varsable
  
  val beval :
    context
    ->
    bF
    ->
    bool
  
  val bF_eval :
    (context,
    bF)
    evalable
  
  val bsize :
    bF
    ->
    int
  
  val bsubst :
    bF
    ->
    var
    ->
    bool
    ->
    bF
  
  val bF_eq_dec :
    bF
    eqDec
 end) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      bool
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      bool
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_simplifier:sig 
  val coq_SATsimplifier :
    Coq_es.sat_equation_system
    ->
    Coq_es.sat_equation_system
    option
  
  val coq_IMPLsimplifier :
    Coq_es.impl_system
    ->
    (Coq_es.impl_system,
    unit)
    result
 end) ->
 functor (Coq_interpreter:sig 
  module Coq_sys_features : 
   sig 
    val object_height :
      Coq_es.coq_object
      heightable
    
    val equality_h :
      Coq_es.equality
      ->
      int
    
    val equality_h_zero :
      Coq_es.equality
      is_height_zero_spec
    
    val equality_height :
      Coq_es.equality
      heightable
    
    val equation_h :
      Coq_es.equation
      ->
      int
    
    val equation_h_zero :
      Coq_es.equation
      is_height_zero_spec
    
    val equation_height :
      Coq_es.equation
      heightable
    
    val nequation_h :
      Coq_es.nequation
      ->
      int
    
    val nequation_h_zero :
      Coq_es.nequation
      is_height_zero_spec
    
    val nequation_height :
      Coq_es.nequation
      heightable
    
    val ses_h :
      Coq_es.sat_equation_system
      ->
      int
    
    val ses_h_zero :
      Coq_es.sat_equation_system
      is_height_zero_spec
    
    val ses_height :
      Coq_es.sat_equation_system
      heightable
    
    val ies_h :
      Coq_es.impl_equation_system
      ->
      int
    
    val ies_h_zero :
      Coq_es.impl_equation_system
      is_height_zero_spec
    
    val ies_height :
      Coq_es.impl_equation_system
      heightable
    
    val is_h :
      Coq_es.impl_system
      ->
      int
    
    val is_h_zero :
      Coq_es.impl_system
      is_height_zero_spec
    
    val is_height :
      Coq_es.impl_system
      heightable
    
    val var_cheight :
      (Coq_es.context,
      Coq_es.var)
      cheightable
    
    val object_cheight :
      (Coq_es.context,
      Coq_es.coq_object)
      cheightable
    
    val equality_cheight :
      (Coq_es.context,
      Coq_es.equality)
      cheightable
    
    val equation_cheight :
      (Coq_es.context,
      Coq_es.equation)
      cheightable
    
    val nequation_cheight :
      (Coq_es.context,
      Coq_es.nequation)
      cheightable
    
    val ses_cheight :
      (Coq_es.context,
      Coq_es.sat_equation_system)
      cheightable
    
    val ies_cheight :
      (Coq_es.context,
      Coq_es.impl_equation_system)
      cheightable
    
    val is_cheight :
      (Coq_es.context,
      Coq_es.impl_system)
      cheightable
    
    val object_vars :
      (Coq_es.coq_object,
      Coq_es.var)
      varsable
    
    val equality_vars :
      (Coq_es.equality,
      Coq_es.var)
      varsable
    
    val equation_vars :
      (Coq_es.equation,
      Coq_es.var)
      varsable
    
    val nequation_vars :
      (Coq_es.nequation,
      Coq_es.var)
      varsable
    
    val ses_vars :
      (Coq_es.sat_equation_system,
      Coq_es.var)
      varsable
    
    val ies_vars :
      (Coq_es.impl_equation_system,
      Coq_es.var)
      varsable
    
    val is_vars :
      (Coq_es.impl_system,
      Coq_es.var)
      varsable
    
    val vheight :
      Coq_es.var
      ->
      int
    
    val vheight_zero :
      Coq_es.var
      is_height_zero_spec
    
    val height_var :
      Coq_es.var
      heightable
    
    val varsable_var :
      (Coq_es.var,
      Coq_es.var)
      varsable
    
    val replace_ses_nequations :
      Coq_es.sat_equation_system
      ->
      Coq_es.nequation
      list
      ->
      Coq_es.sat_equation_system
    
    val replace_ies_nequations :
      Coq_es.impl_equation_system
      ->
      Coq_es.nequation
      list
      ->
      Coq_es.impl_equation_system
    
    val replace_is_nequations :
      Coq_es.impl_system
      ->
      Coq_es.nequation
      list
      ->
      Coq_es.nequation
      list
      ->
      Coq_es.impl_system
   end
  
  type ('a,
        'b) coq_B2F =
    'a
    ->
    'b
    (* singleton inductive, whose constructor was Interpret *)
  
  val coq_B2F_rect :
    (('a1
    ->
    'a2)
    ->
    'a3)
    ->
    ('a1,
    'a2)
    coq_B2F
    ->
    'a3
  
  val coq_B2F_rec :
    (('a1
    ->
    'a2)
    ->
    'a3)
    ->
    ('a1,
    'a2)
    coq_B2F
    ->
    'a3
  
  val interpret :
    ('a1,
    'a2)
    coq_B2F
    ->
    'a1
    ->
    'a2
  
  val b2f_ses :
    (Coq_es.sat_equation_system,
    Coq_bf.bF)
    coq_B2F
  
  val b2f_ies :
    (Coq_es.impl_equation_system,
    Coq_bf.bF)
    coq_B2F
  
  val is_int :
    Coq_es.impl_system
    ->
    Coq_bf.bF
  
  val b2f_is :
    (Coq_es.impl_system,
    Coq_bf.bF)
    coq_B2F
  
  val exF_quan :
    Coq_bf.var
    list
    ->
    Coq_bf.bF
    ->
    Coq_bf.bF
  
  val allF_quan :
    Coq_bf.var
    list
    ->
    Coq_bf.bF
    ->
    Coq_bf.bF
  
  type 'a vars_interpret_prop =
  | Vars_interpret_prop
  
  val vars_interpret_prop_rect :
    ('a1,
    Coq_bf.bF)
    coq_B2F
    ->
    ('a1,
    Coq_bf.var)
    varsable
    ->
    (__
    ->
    'a2)
    ->
    'a2
  
  val vars_interpret_prop_rec :
    ('a1,
    Coq_bf.bF)
    coq_B2F
    ->
    ('a1,
    Coq_bf.var)
    varsable
    ->
    (__
    ->
    'a2)
    ->
    'a2
  
  type 'a beval_interpret_prop =
  | Beval_interpret_prop
  
  val beval_interpret_prop_rect :
    ('a1,
    Coq_bf.bF)
    coq_B2F
    ->
    (Coq_bf.context,
    'a1)
    evalable
    ->
    (__
    ->
    'a2)
    ->
    'a2
  
  val beval_interpret_prop_rec :
    ('a1,
    Coq_bf.bF)
    coq_B2F
    ->
    (Coq_bf.context,
    'a1)
    evalable
    ->
    (__
    ->
    'a2)
    ->
    'a2
 end) ->
 functor (Coq_bsf:sig 
  val bsolver :
    Coq_bf.bF
    ->
    bool
    option
 end) ->
 struct 
  module Coq_sys_features = System_Features(Coq_sv)(Coq_es)
  
  (** val fvars_is :
      Coq_es.impl_system
      ->
      Coq_es.var
      list **)
  
  let fvars_is is =
    let f1 =
      Coq_interpreter.interpret
        Coq_interpreter.b2f_ies
        (fst
          is)
    in
    let f2 =
      Coq_interpreter.interpret
        Coq_interpreter.b2f_ies
        (snd
          is)
    in
    app
      (filter
        (fun v0 ->
        if in_dec
             (eq_dec0
               Coq_es.var_eq_dec)
             v0
             (Coq_es.impl_exvars
               (fst
                 is))
        then false
        else true)
        (vars
          Coq_bf.bF_varsable
          f1))
      (filter
        (fun v0 ->
        if in_dec
             (eq_dec0
               Coq_es.var_eq_dec)
             v0
             (Coq_es.impl_exvars
               (snd
                 is))
        then false
        else true)
        (vars
          Coq_bf.bF_varsable
          f2))
  
  (** val neqn_reduce :
      Coq_es.nequation
      ->
      Coq_es.equality
      list*Coq_es.nequation
      list **)
  
  let neqn_reduce neqn = match neqn with
  | e0,u ->
    let p,obj3 =
      e0
    in
    let o,o0 =
      p
    in
    (match o with
     | Vobject v0 ->
       (match o0 with
        | Vobject v1 ->
          [],(neqn :: [])
        | Cobject c1 ->
          (match obj3 with
           | Vobject v1 ->
             [],(neqn :: [])
           | Cobject c2 ->
             if c1
             then if c2
                  then (((Vobject
                         v0),(Cobject
                         true)) :: []),[]
                  else [],[]
             else if c2
                  then (((Vobject
                         v0),(Cobject
                         false)) :: []),[]
                  else (((Vobject
                         v0),(Cobject
                         true)) :: []),[]))
     | Cobject c1 ->
       (match o0 with
        | Vobject v0 ->
          (match obj3 with
           | Vobject v1 ->
             [],(neqn :: [])
           | Cobject c2 ->
             if c1
             then if c2
                  then (((Vobject
                         v0),(Cobject
                         true)) :: []),[]
                  else [],[]
             else if c2
                  then (((Vobject
                         v0),(Cobject
                         false)) :: []),[]
                  else (((Vobject
                         v0),(Cobject
                         true)) :: []),[])
        | Cobject s0 ->
          [],(neqn :: [])))
  
  (** val neqn_list_reduce :
      Coq_es.nequation
      list
      ->
      Coq_es.equality
      list*Coq_es.nequation
      list **)
  
  let rec neqn_list_reduce = function
  | [] ->
    [],[]
  | neqn :: l'0 ->
    let l1,l2 =
      neqn_reduce
        neqn
    in
    let l1',l2' =
      neqn_list_reduce
        l'0
    in
    (app
      l1
      l1'),(app
             l2
             l2')
  
  (** val ses_reduce :
      Coq_es.sat_equation_system
      ->
      Coq_es.sat_equation_system **)
  
  let ses_reduce ses =
    let l1,l2 =
      neqn_list_reduce
        (Coq_es.sat_nequations
          ses)
    in
    { Coq_es.sat_equalities =
    (app
      l1
      (Coq_es.sat_equalities
        ses));
    Coq_es.sat_equations =
    (Coq_es.sat_equations
      ses);
    Coq_es.sat_nequations =
    l2 }
  
  (** val coq_SAT_preprocess :
      Coq_es.sat_equation_system
      ->
      Coq_es.sat_equation_system
      option **)
  
  let coq_SAT_preprocess ses =
    Coq_simplifier.coq_SATsimplifier
      (ses_reduce
        ses)
  
  (** val coq_SATbsolver :
      Coq_es.sat_equation_system
      ->
      bool **)
  
  let coq_SATbsolver ses =
    match coq_SAT_preprocess
            ses with
    | Some ses' ->
      (match Coq_bsf.bsolver
               (Coq_interpreter.exF_quan
                 (vars
                   Coq_sys_features.ses_vars
                   ses')
                 (Coq_interpreter.interpret
                   Coq_interpreter.b2f_ses
                   ses')) with
       | Some b0 ->
         b0
       | None ->
         false)
    | None ->
      false
  
  (** val ies_reduce :
      Coq_es.impl_equation_system
      ->
      Coq_es.impl_equation_system **)
  
  let ies_reduce ies =
    let l1,l2 =
      neqn_list_reduce
        (Coq_es.impl_nequations
          ies)
    in
    { Coq_es.impl_exvars =
    (Coq_es.impl_exvars
      ies);
    Coq_es.impl_equalities =
    (app
      l1
      (Coq_es.impl_equalities
        ies));
    Coq_es.impl_equations =
    (Coq_es.impl_equations
      ies);
    Coq_es.impl_nequations =
    l2 }
  
  (** val coq_IMPL_preprocess :
      Coq_es.impl_system
      ->
      (Coq_es.impl_system,
      unit)
      result **)
  
  let coq_IMPL_preprocess is =
    Coq_simplifier.coq_IMPLsimplifier
      ((ies_reduce
         (fst
           is)),(ies_reduce
                  (snd
                    is)))
  
  (** val coq_IMPLbsolver :
      Coq_es.impl_system
      ->
      bool **)
  
  let coq_IMPLbsolver is =
    match coq_IMPL_preprocess
            is with
    | Absurd ->
      if coq_SATbsolver
           (Coq_es.ies2ses
             (fst
               is))
      then false
      else true
    | Simpler u ->
      true
    | Same is' ->
      (match Coq_bsf.bsolver
               (Coq_interpreter.allF_quan
                 (fvars_is
                   is')
                 (Coq_interpreter.interpret
                   Coq_interpreter.b2f_is
                   is')) with
       | Some b0 ->
         b0
       | None ->
         false)
 end

type 'x compare0 =
| LT
| EQ
| GT

module type MiniOrderedType = 
 sig 
  type t 
  
  val compare :
    t
    ->
    t
    ->
    t
    compare0
 end

module type Coq_OrderedType = 
 sig 
  type t 
  
  val compare :
    t
    ->
    t
    ->
    t
    compare0
  
  val eq_dec :
    t
    ->
    t
    ->
    bool
 end

module MOT_to_OT = 
 functor (O:MiniOrderedType) ->
 struct 
  type t
    =
    O.t
  
  (** val compare :
      t
      ->
      t
      ->
      t
      compare0 **)
  
  let compare =
    O.compare
  
  (** val eq_dec :
      t
      ->
      t
      ->
      bool **)
  
  let eq_dec x y =
    match compare
            x
            y with
    | EQ ->
      true
    | _ ->
      false
 end

module Coq_OrderedTypeFacts = 
 functor (O:Coq_OrderedType) ->
 struct 
  module TO = 
   struct 
    type t
      =
      O.t
   end
  
  module IsTO = 
   struct 
    
   end
  
  module OrderTac = MakeOrderTac(TO)(IsTO)
  
  (** val eq_dec :
      O.t
      ->
      O.t
      ->
      bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec :
      O.t
      ->
      O.t
      ->
      bool **)
  
  let lt_dec x y =
    match O.compare
            x
            y with
    | LT ->
      true
    | _ ->
      false
  
  (** val eqb :
      O.t
      ->
      O.t
      ->
      bool **)
  
  let eqb x y =
    if eq_dec
         x
         y
    then true
    else false
 end

module KeyOrderedType = 
 functor (O:Coq_OrderedType) ->
 struct 
  module MO = Coq_OrderedTypeFacts(O)
 end

module Raw = 
 functor (X:Coq_OrderedType) ->
 struct 
  module MX = Coq_OrderedTypeFacts(X)
  
  module PX = KeyOrderedType(X)
  
  type key
    =
    X.t
  
  type 'elt t
    =
    (X.t*'elt)
    list
  
  (** val empty :
      'a1
      t **)
  
  let empty =
    []
  
  (** val is_empty :
      'a1
      t
      ->
      bool **)
  
  let is_empty = function
  | [] ->
    true
  | x :: x0 ->
    false
  
  (** val mem :
      key
      ->
      'a1
      t
      ->
      bool **)
  
  let rec mem k = function
  | [] ->
    false
  | p :: l0 ->
    let k',e0 =
      p
    in
    (match X.compare
             k
             k' with
     | LT ->
       false
     | EQ ->
       true
     | GT ->
       mem
         k
         l0)
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt
               t
  | R_mem_1 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_mem_2 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_mem_3 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
     * bool
     * 'elt
       coq_R_mem
  
  (** val coq_R_mem_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      bool
      ->
      'a1
      coq_R_mem
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      bool
      ->
      'a1
      coq_R_mem
      ->
      'a2 **)
  
  let rec coq_R_mem_rect k f f0 f1 f2 s0 b0 = function
  | R_mem_0 s1 ->
    f
      s1
      __
  | R_mem_1 (s1,
             k',
             _x,
             l0) ->
    f0
      s1
      k'
      _x
      l0
      __
      __
      __
  | R_mem_2 (s1,
             k',
             _x,
             l0) ->
    f1
      s1
      k'
      _x
      l0
      __
      __
      __
  | R_mem_3 (s1,
             k',
             _x,
             l0,
             res,
             r0) ->
    f2
      s1
      k'
      _x
      l0
      __
      __
      __
      res
      r0
      (coq_R_mem_rect
        k
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val coq_R_mem_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      bool
      ->
      'a1
      coq_R_mem
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      bool
      ->
      'a1
      coq_R_mem
      ->
      'a2 **)
  
  let rec coq_R_mem_rec k f f0 f1 f2 s0 b0 = function
  | R_mem_0 s1 ->
    f
      s1
      __
  | R_mem_1 (s1,
             k',
             _x,
             l0) ->
    f0
      s1
      k'
      _x
      l0
      __
      __
      __
  | R_mem_2 (s1,
             k',
             _x,
             l0) ->
    f1
      s1
      k'
      _x
      l0
      __
      __
      __
  | R_mem_3 (s1,
             k',
             _x,
             l0,
             res,
             r0) ->
    f2
      s1
      k'
      _x
      l0
      __
      __
      __
      res
      r0
      (coq_R_mem_rec
        k
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val mem_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let rec mem_rect k f2 f1 f0 f s0 =
    let f3 =
      f2
        s0
    in
    let f4 =
      f1
        s0
    in
    let f5 =
      f0
        s0
    in
    let f6 =
      f
        s0
    in
    (match s0 with
     | [] ->
       f3
         __
     | p :: l0 ->
       let t0,e0 =
         p
       in
       let f7 =
         f6
           t0
           e0
           l0
           __
       in
       let f8 =
         fun _ _ ->
         let hrec =
           mem_rect
             k
             f2
             f1
             f0
             f
             l0
         in
         f7
           __
           __
           hrec
       in
       let f9 =
         f5
           t0
           e0
           l0
           __
       in
       let f10 =
         f4
           t0
           e0
           l0
           __
       in
       (match X.compare
                k
                t0 with
        | LT ->
          f10
            __
            __
        | EQ ->
          f9
            __
            __
        | GT ->
          f8
            __
            __))
  
  (** val mem_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let mem_rec k =
    mem_rect
      k
  
  (** val coq_R_mem_correct :
      key
      ->
      'a1
      t
      ->
      bool
      ->
      'a1
      coq_R_mem **)
  
  let coq_R_mem_correct x x0 res =
    let princ =
      fun x1 ->
      mem_rect
        x1
    in
    Obj.magic
      princ
      x
      (fun y _ z _ ->
      R_mem_0
      y)
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_mem_1
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_mem_2
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ ->
      R_mem_3
      (y,
      y0,
      y1,
      y2,
      (mem
        x
        y2),
      (y6
        (mem
          x
          y2)
        __)))
      x0
      res
      __
  
  (** val find :
      key
      ->
      'a1
      t
      ->
      'a1
      option **)
  
  let rec find k = function
  | [] ->
    None
  | p :: s' ->
    let k',x =
      p
    in
    (match X.compare
             k
             k' with
     | LT ->
       None
     | EQ ->
       Some
         x
     | GT ->
       find
         k
         s')
  
  type 'elt coq_R_find =
  | R_find_0 of 'elt
                t
  | R_find_1 of 'elt
                t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_find_2 of 'elt
                t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_find_3 of 'elt
                t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
     * 'elt
       option
     * 'elt
       coq_R_find
  
  (** val coq_R_find_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      option
      ->
      'a1
      coq_R_find
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      option
      ->
      'a1
      coq_R_find
      ->
      'a2 **)
  
  let rec coq_R_find_rect k f f0 f1 f2 s0 o = function
  | R_find_0 s1 ->
    f
      s1
      __
  | R_find_1 (s1,
              k',
              x,
              s') ->
    f0
      s1
      k'
      x
      s'
      __
      __
      __
  | R_find_2 (s1,
              k',
              x,
              s') ->
    f1
      s1
      k'
      x
      s'
      __
      __
      __
  | R_find_3 (s1,
              k',
              x,
              s',
              res,
              r0) ->
    f2
      s1
      k'
      x
      s'
      __
      __
      __
      res
      r0
      (coq_R_find_rect
        k
        f
        f0
        f1
        f2
        s'
        res
        r0)
  
  (** val coq_R_find_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      option
      ->
      'a1
      coq_R_find
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      option
      ->
      'a1
      coq_R_find
      ->
      'a2 **)
  
  let rec coq_R_find_rec k f f0 f1 f2 s0 o = function
  | R_find_0 s1 ->
    f
      s1
      __
  | R_find_1 (s1,
              k',
              x,
              s') ->
    f0
      s1
      k'
      x
      s'
      __
      __
      __
  | R_find_2 (s1,
              k',
              x,
              s') ->
    f1
      s1
      k'
      x
      s'
      __
      __
      __
  | R_find_3 (s1,
              k',
              x,
              s',
              res,
              r0) ->
    f2
      s1
      k'
      x
      s'
      __
      __
      __
      res
      r0
      (coq_R_find_rec
        k
        f
        f0
        f1
        f2
        s'
        res
        r0)
  
  (** val find_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let rec find_rect k f2 f1 f0 f s0 =
    let f3 =
      f2
        s0
    in
    let f4 =
      f1
        s0
    in
    let f5 =
      f0
        s0
    in
    let f6 =
      f
        s0
    in
    (match s0 with
     | [] ->
       f3
         __
     | p :: l0 ->
       let t0,e0 =
         p
       in
       let f7 =
         f6
           t0
           e0
           l0
           __
       in
       let f8 =
         fun _ _ ->
         let hrec =
           find_rect
             k
             f2
             f1
             f0
             f
             l0
         in
         f7
           __
           __
           hrec
       in
       let f9 =
         f5
           t0
           e0
           l0
           __
       in
       let f10 =
         f4
           t0
           e0
           l0
           __
       in
       (match X.compare
                k
                t0 with
        | LT ->
          f10
            __
            __
        | EQ ->
          f9
            __
            __
        | GT ->
          f8
            __
            __))
  
  (** val find_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let find_rec k =
    find_rect
      k
  
  (** val coq_R_find_correct :
      key
      ->
      'a1
      t
      ->
      'a1
      option
      ->
      'a1
      coq_R_find **)
  
  let coq_R_find_correct x x0 res =
    let princ =
      fun x1 ->
      find_rect
        x1
    in
    Obj.magic
      princ
      x
      (fun y _ z _ ->
      R_find_0
      y)
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_find_1
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_find_2
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ ->
      R_find_3
      (y,
      y0,
      y1,
      y2,
      (find
        x
        y2),
      (y6
        (find
          x
          y2)
        __)))
      x0
      res
      __
  
  (** val add :
      key
      ->
      'a1
      ->
      'a1
      t
      ->
      'a1
      t **)
  
  let rec add k x s0 = match s0 with
  | [] ->
    (k,x) :: []
  | p :: l0 ->
    let k',y =
      p
    in
    (match X.compare
             k
             k' with
     | LT ->
       (k,x) :: s0
     | EQ ->
       (k,x) :: l0
     | GT ->
       (k',y) :: (add
                   k
                   x
                   l0))
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt
               t
  | R_add_1 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_add_2 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_add_3 of 'elt
               t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
     * 'elt
       t
     * 'elt
       coq_R_add
  
  (** val coq_R_add_rect :
      key
      ->
      'a1
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      t
      ->
      'a1
      coq_R_add
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_add
      ->
      'a2 **)
  
  let rec coq_R_add_rect k x f f0 f1 f2 s0 t0 = function
  | R_add_0 s1 ->
    f
      s1
      __
  | R_add_1 (s1,
             k',
             y,
             l0) ->
    f0
      s1
      k'
      y
      l0
      __
      __
      __
  | R_add_2 (s1,
             k',
             y,
             l0) ->
    f1
      s1
      k'
      y
      l0
      __
      __
      __
  | R_add_3 (s1,
             k',
             y,
             l0,
             res,
             r0) ->
    f2
      s1
      k'
      y
      l0
      __
      __
      __
      res
      r0
      (coq_R_add_rect
        k
        x
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val coq_R_add_rec :
      key
      ->
      'a1
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      t
      ->
      'a1
      coq_R_add
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_add
      ->
      'a2 **)
  
  let rec coq_R_add_rec k x f f0 f1 f2 s0 t0 = function
  | R_add_0 s1 ->
    f
      s1
      __
  | R_add_1 (s1,
             k',
             y,
             l0) ->
    f0
      s1
      k'
      y
      l0
      __
      __
      __
  | R_add_2 (s1,
             k',
             y,
             l0) ->
    f1
      s1
      k'
      y
      l0
      __
      __
      __
  | R_add_3 (s1,
             k',
             y,
             l0,
             res,
             r0) ->
    f2
      s1
      k'
      y
      l0
      __
      __
      __
      res
      r0
      (coq_R_add_rec
        k
        x
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val add_rect :
      key
      ->
      'a1
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let rec add_rect k x f2 f1 f0 f s0 =
    let f3 =
      f2
        s0
    in
    let f4 =
      f1
        s0
    in
    let f5 =
      f0
        s0
    in
    let f6 =
      f
        s0
    in
    (match s0 with
     | [] ->
       f3
         __
     | p :: l0 ->
       let t0,e0 =
         p
       in
       let f7 =
         f6
           t0
           e0
           l0
           __
       in
       let f8 =
         fun _ _ ->
         let hrec =
           add_rect
             k
             x
             f2
             f1
             f0
             f
             l0
         in
         f7
           __
           __
           hrec
       in
       let f9 =
         f5
           t0
           e0
           l0
           __
       in
       let f10 =
         f4
           t0
           e0
           l0
           __
       in
       (match X.compare
                k
                t0 with
        | LT ->
          f10
            __
            __
        | EQ ->
          f9
            __
            __
        | GT ->
          f8
            __
            __))
  
  (** val add_rec :
      key
      ->
      'a1
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let add_rec k x =
    add_rect
      k
      x
  
  (** val coq_R_add_correct :
      key
      ->
      'a1
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_add **)
  
  let coq_R_add_correct x x0 x1 res =
    add_rect
      x
      x0
      (fun y _ z _ ->
      R_add_0
      y)
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_add_1
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_add_2
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ ->
      R_add_3
      (y,
      y0,
      y1,
      y2,
      (add
        x
        x0
        y2),
      (y6
        (add
          x
          x0
          y2)
        __)))
      x1
      res
      __
  
  (** val remove :
      key
      ->
      'a1
      t
      ->
      'a1
      t **)
  
  let rec remove k s0 = match s0 with
  | [] ->
    []
  | p :: l0 ->
    let k',x =
      p
    in
    (match X.compare
             k
             k' with
     | LT ->
       s0
     | EQ ->
       l0
     | GT ->
       (k',x) :: (remove
                   k
                   l0))
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt
                  t
  | R_remove_1 of 'elt
                  t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_remove_2 of 'elt
                  t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
  | R_remove_3 of 'elt
                  t
     * X.t
     * 'elt
     * (X.t*'elt)
       list
     * 'elt
       t
     * 'elt
       coq_R_remove
  
  (** val coq_R_remove_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      t
      ->
      'a1
      coq_R_remove
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_remove
      ->
      'a2 **)
  
  let rec coq_R_remove_rect k f f0 f1 f2 s0 t0 = function
  | R_remove_0 s1 ->
    f
      s1
      __
  | R_remove_1 (s1,
                k',
                x,
                l0) ->
    f0
      s1
      k'
      x
      l0
      __
      __
      __
  | R_remove_2 (s1,
                k',
                x,
                l0) ->
    f1
      s1
      k'
      x
      l0
      __
      __
      __
  | R_remove_3 (s1,
                k',
                x,
                l0,
                res,
                r0) ->
    f2
      s1
      k'
      x
      l0
      __
      __
      __
      res
      r0
      (coq_R_remove_rect
        k
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val coq_R_remove_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a1
      t
      ->
      'a1
      coq_R_remove
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_remove
      ->
      'a2 **)
  
  let rec coq_R_remove_rec k f f0 f1 f2 s0 t0 = function
  | R_remove_0 s1 ->
    f
      s1
      __
  | R_remove_1 (s1,
                k',
                x,
                l0) ->
    f0
      s1
      k'
      x
      l0
      __
      __
      __
  | R_remove_2 (s1,
                k',
                x,
                l0) ->
    f1
      s1
      k'
      x
      l0
      __
      __
      __
  | R_remove_3 (s1,
                k',
                x,
                l0,
                res,
                r0) ->
    f2
      s1
      k'
      x
      l0
      __
      __
      __
      res
      r0
      (coq_R_remove_rec
        k
        f
        f0
        f1
        f2
        l0
        res
        r0)
  
  (** val remove_rect :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let rec remove_rect k f2 f1 f0 f s0 =
    let f3 =
      f2
        s0
    in
    let f4 =
      f1
        s0
    in
    let f5 =
      f0
        s0
    in
    let f6 =
      f
        s0
    in
    (match s0 with
     | [] ->
       f3
         __
     | p :: l0 ->
       let t0,e0 =
         p
       in
       let f7 =
         f6
           t0
           e0
           l0
           __
       in
       let f8 =
         fun _ _ ->
         let hrec =
           remove_rect
             k
             f2
             f1
             f0
             f
             l0
         in
         f7
           __
           __
           hrec
       in
       let f9 =
         f5
           t0
           e0
           l0
           __
       in
       let f10 =
         f4
           t0
           e0
           l0
           __
       in
       (match X.compare
                k
                t0 with
        | LT ->
          f10
            __
            __
        | EQ ->
          f9
            __
            __
        | GT ->
          f8
            __
            __))
  
  (** val remove_rec :
      key
      ->
      ('a1
      t
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      ('a1
      t
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2 **)
  
  let remove_rec k =
    remove_rect
      k
  
  (** val coq_R_remove_correct :
      key
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      'a1
      coq_R_remove **)
  
  let coq_R_remove_correct x x0 res =
    let princ =
      fun x1 ->
      remove_rect
        x1
    in
    Obj.magic
      princ
      x
      (fun y _ z _ ->
      R_remove_0
      y)
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_remove_1
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ z _ ->
      R_remove_2
      (y,
      y0,
      y1,
      y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ ->
      R_remove_3
      (y,
      y0,
      y1,
      y2,
      (remove
        x
        y2),
      (y6
        (remove
          x
          y2)
        __)))
      x0
      res
      __
  
  (** val elements :
      'a1
      t
      ->
      'a1
      t **)
  
  let elements m =
    m
  
  (** val fold :
      (key
      ->
      'a1
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2
      ->
      'a2 **)
  
  let rec fold f m acc =
    match m with
    | [] ->
      acc
    | p :: m' ->
      let k,e0 =
        p
      in
      fold
        f
        m'
        (f
          k
          e0
          acc)
  
  type ('elt,
        'a) coq_R_fold =
  | R_fold_0 of (key
                ->
                'elt
                ->
                'a
                ->
                'a)
     * 'elt
       t
     * 'a
  | R_fold_1 of (key
                ->
                'elt
                ->
                'a
                ->
                'a)
     * 'elt
       t
     * 'a
     * X.t
     * 'elt
     * (X.t*'elt)
       list
     * 'a
     * ('elt,
       'a)
       coq_R_fold
  
  (** val coq_R_fold_rect :
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      ('a1,
      __)
      coq_R_fold
      ->
      'a2
      ->
      'a2)
      ->
      (key
      ->
      'a1
      ->
      'a3
      ->
      'a3)
      ->
      'a1
      t
      ->
      'a3
      ->
      'a3
      ->
      ('a1,
      'a3)
      coq_R_fold
      ->
      'a2 **)
  
  let rec coq_R_fold_rect f f0 f1 m acc a0 = function
  | R_fold_0 (f2,
              m0,
              acc0) ->
    Obj.magic
      f
      __
      f2
      m0
      acc0
      __
  | R_fold_1 (f2,
              m0,
              acc0,
              k,
              e0,
              m',
              res,
              r0) ->
    Obj.magic
      f0
      __
      f2
      m0
      acc0
      k
      e0
      m'
      __
      res
      r0
      (coq_R_fold_rect
        f
        f0
        f2
        m'
        (f2
          k
          e0
          acc0)
        res
        r0)
  
  (** val coq_R_fold_rec :
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      __
      ->
      ('a1,
      __)
      coq_R_fold
      ->
      'a2
      ->
      'a2)
      ->
      (key
      ->
      'a1
      ->
      'a3
      ->
      'a3)
      ->
      'a1
      t
      ->
      'a3
      ->
      'a3
      ->
      ('a1,
      'a3)
      coq_R_fold
      ->
      'a2 **)
  
  let rec coq_R_fold_rec f f0 f1 m acc a0 = function
  | R_fold_0 (f2,
              m0,
              acc0) ->
    Obj.magic
      f
      __
      f2
      m0
      acc0
      __
  | R_fold_1 (f2,
              m0,
              acc0,
              k,
              e0,
              m',
              res,
              r0) ->
    Obj.magic
      f0
      __
      f2
      m0
      acc0
      k
      e0
      m'
      __
      res
      r0
      (coq_R_fold_rec
        f
        f0
        f2
        m'
        (f2
          k
          e0
          acc0)
        res
        r0)
  
  (** val fold_rect :
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      (key
      ->
      'a1
      ->
      'a3
      ->
      'a3)
      ->
      'a1
      t
      ->
      'a3
      ->
      'a2 **)
  
  let rec fold_rect f0 f f1 m acc =
    let f2 =
      Obj.magic
        f0
        __
        f1
        m
        acc
    in
    let f3 =
      Obj.magic
        f
        __
        f1
        m
        acc
    in
    (match m with
     | [] ->
       f2
         __
     | p :: l0 ->
       let t0,e0 =
         p
       in
       let f4 =
         f3
           t0
           e0
           l0
           __
       in
       let hrec =
         fold_rect
           f0
           f
           f1
           l0
           (f1
             t0
             e0
             acc)
       in
       f4
         hrec)
  
  (** val fold_rec :
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      __
      ->
      'a2)
      ->
      (__
      ->
      (key
      ->
      'a1
      ->
      __
      ->
      __)
      ->
      'a1
      t
      ->
      __
      ->
      X.t
      ->
      'a1
      ->
      (X.t*'a1)
      list
      ->
      __
      ->
      'a2
      ->
      'a2)
      ->
      (key
      ->
      'a1
      ->
      'a3
      ->
      'a3)
      ->
      'a1
      t
      ->
      'a3
      ->
      'a2 **)
  
  let fold_rec f f0 f1 m acc =
    fold_rect
      f
      f0
      f1
      m
      acc
  
  (** val coq_R_fold_correct :
      (key
      ->
      'a1
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t
      ->
      'a2
      ->
      'a2
      ->
      ('a1,
      'a2)
      coq_R_fold **)
  
  let coq_R_fold_correct x0 x1 x2 res =
    let princ =
      fun x x3 ->
      fold_rect
        x
        x3
    in
    Obj.magic
      princ
      (fun _ y0 y1 y2 _ z _ ->
      R_fold_0
      (y0,
      y1,
      y2))
      (fun _ y0 y1 y2 y3 y4 y5 _ y7 z _ ->
      R_fold_1
      (y0,
      y1,
      y2,
      y3,
      y4,
      y5,
      (fold
        y0
        y5
        (y0
          y3
          y4
          y2)),
      (y7
        (fold
          y0
          y5
          (y0
            y3
            y4
            y2))
        __)))
      x0
      x1
      x2
      res
      __
  
  (** val equal :
      ('a1
      ->
      'a1
      ->
      bool)
      ->
      'a1
      t
      ->
      'a1
      t
      ->
      bool **)
  
  let rec equal cmp m m' =
    match m with
    | [] ->
      (match m' with
       | [] ->
         true
       | p :: l0 ->
         false)
    | p :: l0 ->
      let x,e0 =
        p
      in
      (match m' with
       | [] ->
         false
       | p0 :: l'0 ->
         let x',e' =
           p0
         in
         (match X.compare
                  x
                  x' with
          | EQ ->
            (&&)
              (cmp
                e0
                e')
              (equal
                cmp
                l0
                l'0)
          | _ ->
            false))
  
  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
  
  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t ->
      'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
      t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1
      t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rect cmp f f0 f1 f2 m m' b0 = function
  | R_equal_0 (m0, m'0) -> f m0 m'0 __ __
  | R_equal_1 (m0, m'0, x, e0, l0, x', e', l'0, res, r0) ->
    f0 m0 m'0 x e0 l0 __ x' e' l'0 __ __ __ res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l0 l'0 res r0)
  | R_equal_2 (m0, m'0, x, e0, l0, x', e', l'0, _x) ->
    f1 m0 m'0 x e0 l0 __ x' e' l'0 __ _x __ __
  | R_equal_3 (m0, m'0, _x, _x0) -> f2 m0 m'0 _x __ _x0 __ __
  
  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t ->
      'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
      t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1
      t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rec cmp f f0 f1 f2 m m' b0 = function
  | R_equal_0 (m0, m'0) -> f m0 m'0 __ __
  | R_equal_1 (m0, m'0, x, e0, l0, x', e', l'0, res, r0) ->
    f0 m0 m'0 x e0 l0 __ x' e' l'0 __ __ __ res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l0 l'0 res r0)
  | R_equal_2 (m0, m'0, x, e0, l0, x', e', l'0, _x) ->
    f1 m0 m'0 x e0 l0 __ x' e' l'0 __ _x __ __
  | R_equal_3 (m0, m'0, _x, _x0) -> f2 m0 m'0 _x __ _x0 __ __
  
  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
      __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)
  
  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] ->
       let f9 = f3 __ in
       (match m' with
        | [] -> f9 __
        | p :: l0 -> f8 __)
     | p :: l0 ->
       let t0,e0 = p in
       let f9 = f5 t0 e0 l0 __ in
       let f10 = f4 t0 e0 l0 __ in
       (match m' with
        | [] -> f8 __
        | p0 :: l1 ->
          let t1,e1 = p0 in
          let f11 = f9 t1 e1 l1 __ in
          let f12 = let _x = X.compare t0 t1 in f11 _x __ in
          let f13 = f10 t1 e1 l1 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l0 l1 in f13 __ __ hrec
          in
          (match X.compare t0 t1 with
           | EQ -> f14 __ __
           | _ -> f12 __)))
  
  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
      __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)
  
  let equal_rec cmp =
    equal_rect cmp
  
  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)
  
  let coq_R_equal_correct x x0 x1 res =
    equal_rect x (fun y y0 _ _ z _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal x y3 y7), (y11 (equal x y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ z _ -> R_equal_3 (y, y0, y1,
      y3)) x0 x1 res __
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec map f = function
  | [] -> []
  | p :: m' -> let k,e0 = p in (k,(f e0)) :: (map f m')
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec mapi f = function
  | [] -> []
  | p :: m' -> let k,e0 = p in (k,(f k e0)) :: (mapi f m')
  
  (** val option_cons :
      key -> 'a1 option -> (key*'a1) list -> (key*'a1) list **)
  
  let option_cons k o l0 =
    match o with
    | Some e0 -> (k,e0) :: l0
    | None -> l0
  
  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)
  
  let rec map2_l f = function
  | [] -> []
  | p :: l0 -> let k,e0 = p in option_cons k (f (Some e0) None) (map2_l f l0)
  
  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)
  
  let rec map2_r f = function
  | [] -> []
  | p :: l'0 ->
    let k,e' = p in option_cons k (f None (Some e')) (map2_r f l'0)
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l0 ->
    let k,e0 = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l'0 ->
      let k',e' = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e0) None) (map2 f l0 m')
       | EQ -> option_cons k (f (Some e0) (Some e')) (map2 f l0 l'0)
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'0))
    in map2_aux
  
  (** val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t **)
  
  let rec combine m = match m with
  | [] -> map (fun e' -> None,(Some e'))
  | p :: l0 ->
    let k,e0 = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e1 -> (Some e1),None) m
    | p0 :: l'0 ->
      let k',e' = p0 in
      (match X.compare k k' with
       | LT -> (k,((Some e0),None)) :: (combine l0 m')
       | EQ -> (k,((Some e0),(Some e'))) :: (combine l0 l'0)
       | GT -> (k',(None,(Some e'))) :: (combine_aux l'0))
    in combine_aux
  
  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3 **)
  
  let fold_right_pair f l0 i =
    fold_right (fun p -> f (fst p) (snd p)) i l0
  
  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key*'a3)
      list **)
  
  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []
  
  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option*'a2 option) option **)
  
  let at_least_one o o' =
    match o with
    | Some e0 -> Some (o,o')
    | None ->
      (match o' with
       | Some e0 -> Some (o,o')
       | None -> None)
  
  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)
  
  let at_least_one_then_f f o o' =
    match o with
    | Some e0 -> f o o'
    | None ->
      (match o' with
       | Some e0 -> f o o'
       | None -> None)
 end

module Make = 
 functor (X:Coq_OrderedType) ->
 struct 
  module Raw = Raw(X)
  
  module E = X
  
  type key = E.t
  
  type 'elt slist =
    'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  (** val slist_rect : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2 **)
  
  let slist_rect f s0 =
    f s0 __
  
  (** val slist_rec : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2 **)
  
  let slist_rec f s0 =
    f s0 __
  
  (** val this : 'a1 slist -> 'a1 Raw.t **)
  
  let this s0 =
    s0
  
  type 'elt t = 'elt slist
  
  (** val empty : 'a1 t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty m =
    Raw.is_empty (this m)
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let add x e0 m =
    Raw.add x e0 (this m)
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let find x m =
    Raw.find x (this m)
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let remove x m =
    Raw.remove x (this m)
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let mem x m =
    Raw.mem x (this m)
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    Raw.map f (this m)
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let mapi f m =
    Raw.mapi f (this m)
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let map2 f m m' =
    Raw.map2 f (this m) (this m')
  
  (** val elements : 'a1 t -> (key*'a1) list **)
  
  let elements m =
    Raw.elements (this m)
  
  (** val cardinal : 'a1 t -> int **)
  
  let cardinal m =
    length (this m)
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f m i =
    Raw.fold f (this m) i
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module BoundMap = 
 functor (Coq_sv:SV) ->
 struct 
  type bound_type = share*share
  
  type bound = (share*share)
  
  (** val o_bound : bound -> share*share **)
  
  let o_bound b0 =
    b0
  
  (** val bound_eq_dec : bound eqDec **)
  
  let bound_eq_dec a0 a' =
    let l0,u = a0 in
    let l'0,u' = a' in
    if eq_dec0 (Obj.magic Share.coq_EqDec_share) l0 l'0
    then eq_dec0 (Obj.magic Share.coq_EqDec_share) u u'
    else false
  
  (** val bound_map : ((share*share) -> share*share) -> bound -> bound **)
  
  let bound_map f b0 =
    f (o_bound b0)
  
  (** val initial_bound : bound **)
  
  let initial_bound =
    share_ba.bot0,share_ba.top0
  
  module SV_MiniOrderedType = 
   struct 
    type t = Coq_sv.t
    
    (** val compare : t -> t -> t compare0 **)
    
    let compare x y =
      if eq_dec0 Coq_sv.t_eq_dec x y
      then EQ
      else if Coq_sv.t_lt_dec x y then LT else GT
   end
  
  module SV_OrderedType = MOT_to_OT(SV_MiniOrderedType)
  
  module ContextMap = Make(SV_OrderedType)
  
  type bmap = bound ContextMap.t
  
  (** val initial_bmap : bmap **)
  
  let initial_bmap =
    ContextMap.empty
  
  (** val lookup : bmap -> Coq_sv.t -> bound **)
  
  let lookup bm v0 =
    match ContextMap.find v0 bm with
    | Some b0 -> b0
    | None -> initial_bound
  
  (** val update : bmap -> Coq_sv.t -> bound -> bmap **)
  
  let update bm v0 b0 =
    ContextMap.add v0 b0 bm
  
  type mappable = (bound -> bound)
  
  (** val app_mappable : mappable -> bound -> bound **)
  
  let app_mappable f =
    f
  
  (** val map : mappable -> bmap -> bmap **)
  
  let map f bm =
    ContextMap.map (app_mappable f) bm
  
  (** val cm_map :
      ((share*share) -> share*share) -> bound ContextMap.t -> bound
      ContextMap.t **)
  
  let cm_map f m =
    ContextMap.map (bound_map f) m
 end

module Bounder = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e = share
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_Share.t
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 struct 
  module Coq_sys_features = System_Features(Coq_sv)(Coq_es)
  
  module BM = BoundMap(Coq_sv)
  
  type bcontext = BM.bmap
  
  (** val bound_object : bcontext -> Coq_es.coq_object -> BM.bound **)
  
  let bound_object bctx = function
  | Vobject v0 -> BM.lookup bctx v0
  | Cobject c0 -> c0,c0
  
  (** val evalable_bound_object :
      (bcontext, Coq_es.coq_object, BM.bound) getable **)
  
  let evalable_bound_object =
    bound_object
  
  (** val update_object :
      bcontext -> Coq_es.coq_object -> BM.bound -> bcontext **)
  
  let update_object bctx o b0 =
    match o with
    | Vobject v0 -> BM.update bctx v0 b0
    | Cobject s0 -> bctx
  
  (** val one_bound_size : int -> share -> share -> int **)
  
  let one_bound_size n0 l0 u =
    minus (Coq_Share.share_metric n0 u) (Coq_Share.share_metric n0 l0)
  
  (** val o_bounds_size : int -> bcontext -> Coq_es.coq_object -> int **)
  
  let o_bounds_size n0 bctx = function
  | Vobject v0 ->
    let l0 = BM.lookup bctx v0 in one_bound_size n0 (fst l0) (snd l0)
  | Cobject s0 -> 0
  
  (** val initial_bcontext : bcontext **)
  
  let initial_bcontext =
    BM.initial_bmap
  
  (** val lhs1_bound :
      share -> share -> share -> share -> share -> share -> BM.bound **)
  
  let lhs1_bound l1 u1 l2 u2 l3 u3 =
    (share_ba.lub0 l1 (share_ba.glb0 l3 (share_ba.comp0 u2))),(share_ba.glb0
                                                                u1
                                                                (share_ba.glb0
                                                                  u3
                                                                  (share_ba.comp0
                                                                    l2)))
  
  (** val lhs2_bound :
      share -> share -> share -> share -> share -> share -> BM.bound **)
  
  let lhs2_bound l1 u1 l2 u2 l3 u3 =
    (share_ba.lub0 l2 (share_ba.glb0 l3 (share_ba.comp0 u1))),(share_ba.glb0
                                                                u2
                                                                (share_ba.glb0
                                                                  u3
                                                                  (share_ba.comp0
                                                                    l1)))
  
  (** val rhs_bound :
      share -> share -> share -> share -> share -> share -> BM.bound **)
  
  let rhs_bound l1 u1 l2 u2 l3 u3 =
    (share_ba.lub0 l3 (share_ba.lub0 l1 l2)),(share_ba.glb0 u3
                                               (share_ba.lub0 u1 u2))
  
  type substitution = (Coq_es.var*Coq_es.coq_object)
  
  (** val sbst_var : substitution -> Coq_es.var **)
  
  let sbst_var sbst =
    fst sbst
  
  (** val sbst_object : substitution -> Coq_es.coq_object **)
  
  let sbst_object sbst =
    snd sbst
  
  (** val mkCsubstitution : Coq_es.var -> share -> substitution **)
  
  let mkCsubstitution x sh =
    x,(Cobject sh)
  
  (** val mkVsubstitution : Coq_es.var -> Coq_es.var -> substitution **)
  
  let mkVsubstitution x y =
    x,(Vobject y)
  
  (** val dec_eq_substitution : substitution eqDec **)
  
  let dec_eq_substitution a0 a' =
    let v0,o = a0 in
    let v1,o0 = a' in
    if eq_dec0 Coq_es.var_eq_dec v0 v1
    then eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Share_Domain.e_eq_dec) o
           o0
    else false
  
  (** val evalable_substitution : (Coq_es.context, substitution) evalable **)
  
  let evalable_substitution =
    Evalable
  
  (** val vars_subst : substitution -> Coq_es.var list **)
  
  let vars_subst subst0 =
    (sbst_var subst0) :: (vars Coq_sys_features.object_vars
                           (sbst_object subst0))
  
  (** val varsable_subst : (substitution, Coq_es.var) varsable **)
  
  let varsable_subst =
    vars_subst
  
  type equation_system = { eqs_substitutions : substitution list;
                           eqs_equations : Coq_es.equation list;
                           eqs_nequations : Coq_es.nequation list }
  
  (** val equation_system_rect :
      (substitution list -> Coq_es.equation list -> Coq_es.nequation list ->
      'a1) -> equation_system -> 'a1 **)
  
  let equation_system_rect f e0 =
    let { eqs_substitutions = x; eqs_equations = x0; eqs_nequations = x1 } =
      e0
    in
    f x x0 x1
  
  (** val equation_system_rec :
      (substitution list -> Coq_es.equation list -> Coq_es.nequation list ->
      'a1) -> equation_system -> 'a1 **)
  
  let equation_system_rec f e0 =
    let { eqs_substitutions = x; eqs_equations = x0; eqs_nequations = x1 } =
      e0
    in
    f x x0 x1
  
  (** val eqs_substitutions : equation_system -> substitution list **)
  
  let eqs_substitutions e0 =
    e0.eqs_substitutions
  
  (** val eqs_equations : equation_system -> Coq_es.equation list **)
  
  let eqs_equations e0 =
    e0.eqs_equations
  
  (** val eqs_nequations : equation_system -> Coq_es.nequation list **)
  
  let eqs_nequations e0 =
    e0.eqs_nequations
  
  (** val evalable_equation_system :
      (Coq_es.context, equation_system) evalable **)
  
  let evalable_equation_system =
    Evalable
  
  (** val eql2subst : Coq_es.equality -> (substitution, unit) result **)
  
  let eql2subst = function
  | obj,obj0 ->
    (match obj with
     | Vobject v0 ->
       let filtered_var =
         eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Share_Domain.e_eq_dec)
           obj0 (Vobject v0)
       in
       if filtered_var then Simpler () else Same (v0,obj0)
     | Cobject c1 ->
       let obj1 = Cobject c1 in
       (match obj0 with
        | Vobject v0 ->
          let filtered_var =
            eq_dec0 (objectT_eq_dec Coq_es.var_eq_dec Share_Domain.e_eq_dec)
              obj1 (Vobject v0)
          in
          if filtered_var then Simpler () else Same (v0,obj1)
        | Cobject c2 ->
          let filtered_var = eq_dec0 Share_Domain.e_eq_dec c1 c2 in
          if filtered_var then Simpler () else Absurd))
  
  (** val eql2subst_list :
      Coq_es.equality list -> substitution list option **)
  
  let rec eql2subst_list = function
  | [] -> Some []
  | eql :: l'0 ->
    (match eql2subst eql with
     | Absurd -> None
     | Simpler u -> eql2subst_list l'0
     | Same subst' ->
       (match eql2subst_list l'0 with
        | Some l'' -> Some (subst' :: l'')
        | None -> None))
  
  (** val subst2eql : substitution -> Coq_es.equality **)
  
  let subst2eql = function
  | v0,obj -> (Vobject v0),obj
  
  (** val subst2eql_list : substitution list -> Coq_es.equality list **)
  
  let subst2eql_list l0 =
    fold_right (fun sbst l'0 -> (subst2eql sbst) :: l'0) [] l0
  
  (** val wrapped_ses :
      Coq_es.sat_equation_system -> equation_system option **)
  
  let wrapped_ses ses =
    let l1 = Coq_es.sat_equalities ses in
    let l2 = Coq_es.sat_equations ses in
    let l3 = Coq_es.sat_nequations ses in
    (match eql2subst_list l1 with
     | Some l1' ->
       Some { eqs_substitutions = l1'; eqs_equations = l2; eqs_nequations =
         l3 }
     | None -> None)
  
  (** val unwrapped_ses : equation_system -> Coq_es.sat_equation_system **)
  
  let unwrapped_ses ses =
    let l1 = eqs_substitutions ses in
    let l2 = eqs_equations ses in
    let l3 = eqs_nequations ses in
    { Coq_es.sat_equalities = (subst2eql_list l1); Coq_es.sat_equations = l2;
    Coq_es.sat_nequations = l3 }
  
  type bound_result =
  | Coq_br_narrower of substitution list * bcontext
  | Coq_br_unchanged
  | Coq_br_absurd
  
  (** val bound_result_rect :
      (substitution list -> bcontext -> 'a1) -> 'a1 -> 'a1 -> bound_result ->
      'a1 **)
  
  let bound_result_rect f f0 f1 = function
  | Coq_br_narrower (x, x0) -> f x x0
  | Coq_br_unchanged -> f0
  | Coq_br_absurd -> f1
  
  (** val bound_result_rec :
      (substitution list -> bcontext -> 'a1) -> 'a1 -> 'a1 -> bound_result ->
      'a1 **)
  
  let bound_result_rec f f0 f1 = function
  | Coq_br_narrower (x, x0) -> f x x0
  | Coq_br_unchanged -> f0
  | Coq_br_absurd -> f1
  
  (** val bound_constant_dec : BM.bound -> bool **)
  
  let bound_constant_dec b0 =
    eq_dec0 Share_Domain.e_eq_dec (fst b0) (snd b0)
  
  type ('a, 'b, 'c) triple =
  | Triple of 'a * 'b * 'c
  
  (** val triple_rect :
      ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) triple -> 'a4 **)
  
  let triple_rect f = function
  | Triple (x, x0, x1) -> f x x0 x1
  
  (** val triple_rec :
      ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) triple -> 'a4 **)
  
  let triple_rec f = function
  | Triple (x, x0, x1) -> f x x0 x1
  
  (** val process_bound :
      bcontext -> BM.bound -> BM.bound -> Coq_es.coq_object ->
      (Coq_es.coq_object*BM.bound) list -> (bcontext, bool,
      (Coq_es.coq_object*BM.bound) list) triple **)
  
  let process_bound bctx oldB newB o oldConstL =
    if eq_dec0 BM.bound_eq_dec oldB newB
    then Triple (bctx, false, oldConstL)
    else Triple ((update_object bctx o newB), true,
           (if bound_constant_dec newB
            then (o,newB) :: oldConstL
            else oldConstL))
  
  (** val objBound2subst :
      (Coq_es.coq_object*BM.bound) list -> substitution list **)
  
  let rec objBound2subst = function
  | [] -> []
  | p :: obL' ->
    let o,b0 = p in
    let sL' = objBound2subst obL' in
    (match o with
     | Vobject x -> (mkCsubstitution x (fst b0)) :: sL'
     | Cobject s0 -> sL')
  
  (** val share_leq_dec : share -> share -> bool **)
  
  let share_leq_dec x y =
    Coq_Share.leq_dec x y
  
  (** val bound_equation : bcontext -> Coq_es.equation -> bound_result **)
  
  let bound_equation bctx = function
  | p,o3 ->
    let o1,o2 = p in
    let p0 =
      (get evalable_bound_object bctx o1),(get evalable_bound_object bctx o2)
    in
    let rhs = get evalable_bound_object bctx o3 in
    let lhs1,lhs2 = p0 in
    let l1,u1 = lhs1 in
    let l2,u2 = lhs2 in
    let l3,u3 = rhs in
    if share_leq_dec (share_ba.lub0 l1 l2) u3
    then if share_leq_dec l3 (share_ba.lub0 u1 u2)
         then if eq_dec0 Share_Domain.e_eq_dec (share_ba.glb0 l1 l2)
                   share_ba.bot0
              then let lhs1' = lhs1_bound l1 u1 l2 u2 l3 u3 in
                   let lhs2' = lhs2_bound l1 u1 l2 u2 l3 u3 in
                   let rhs' = rhs_bound l1 u1 l2 u2 l3 u3 in
                   let Triple (bctx1, c1, cL1) =
                     process_bound bctx lhs1 lhs1' o1 []
                   in
                   let Triple (bctx2, c2, cL2) =
                     process_bound bctx1 lhs2 lhs2' o2 cL1
                   in
                   let Triple (bctx3, c3, cL3) =
                     process_bound bctx2 rhs rhs' o3 cL2
                   in
                   if (||) c1 ((||) c2 c3)
                   then Coq_br_narrower ((objBound2subst cL3), bctx3)
                   else Coq_br_unchanged
              else Coq_br_absurd
         else Coq_br_absurd
    else Coq_br_absurd
  
  (** val var_bound_size : int -> BM.bmap -> Coq_sv.t -> int **)
  
  let var_bound_size n0 bctx v0 =
    let l0 = BM.lookup bctx v0 in one_bound_size n0 (fst l0) (snd l0)
  
  (** val bound_once_equation_list :
      bcontext -> Coq_es.equation list -> bound_result **)
  
  let bound_once_equation_list bctx eqs =
    fold_right (fun c0 a0 ->
      match a0 with
      | Coq_br_narrower (ls, bctx0) ->
        (match bound_equation bctx0 c0 with
         | Coq_br_narrower (ls2, bctx1) ->
           Coq_br_narrower ((app ls2 ls), bctx1)
         | Coq_br_unchanged -> a0
         | Coq_br_absurd -> Coq_br_absurd)
      | Coq_br_unchanged -> bound_equation bctx c0
      | Coq_br_absurd -> a0) Coq_br_unchanged eqs
  
  (** val eq_bounds_size : int -> bcontext -> Coq_es.equation -> int **)
  
  let eq_bounds_size n0 bctx = function
  | p,o3 ->
    let o1,o2 = p in
    plus (plus (o_bounds_size n0 bctx o1) (o_bounds_size n0 bctx o2))
      (o_bounds_size n0 bctx o3)
  
  (** val eq_bound_height_max : bcontext -> Coq_es.equation -> int **)
  
  let eq_bound_height_max bctx = function
  | p,o3 ->
    let o1,o2 = p in
    let p0 =
      (get evalable_bound_object bctx o1),(get evalable_bound_object bctx o2)
    in
    let y = get evalable_bound_object bctx o3 in
    let y0,y1 = p0 in
    let l1,u1 = y0 in
    let l2,u2 = y1 in
    let l3,u3 = y in
    let m1 =
      max (plus (Share_Domain.e_height.height l1) ((fun x -> x + 1) 0))
        (plus (Share_Domain.e_height.height u1) ((fun x -> x + 1) 0))
    in
    let m2 =
      max (plus (Share_Domain.e_height.height l2) ((fun x -> x + 1) 0))
        (plus (Share_Domain.e_height.height u2) ((fun x -> x + 1) 0))
    in
    let m3 =
      max (plus (Share_Domain.e_height.height l3) ((fun x -> x + 1) 0))
        (plus (Share_Domain.e_height.height u3) ((fun x -> x + 1) 0))
    in
    max (max m1 m2) m3
  
  (** val eq_bound_height_eql : bcontext -> Coq_es.equation list -> int **)
  
  let eq_bound_height_eql bctx eql =
    fold_right (fun c0 a0 -> max a0 (eq_bound_height_max bctx c0)) 0 eql
  
  (** val eql_bounds_size :
      int -> bcontext -> Coq_es.equation list -> int **)
  
  let eql_bounds_size h bctx l0 =
    fold_right (fun c0 a0 -> plus a0 (eq_bounds_size h bctx c0)) 0 l0
  
  (** val bounds_size :
      ((bcontext*Coq_es.equation list)*substitution list) -> int **)
  
  let bounds_size = function
  | p0,lsub ->
    let bctx,eql = p0 in
    let h = eq_bound_height_eql bctx eql in eql_bounds_size h bctx eql
  
  (** val bound_eql_fix_F :
      (((bcontext*Coq_es.equation list)*substitution list) ->
      (bcontext*substitution list) option) -> ((bcontext*Coq_es.equation
      list)*substitution list) -> (bcontext*substitution list) option **)
  
  let bound_eql_fix_F bound_eql_fix0 = function
  | p0,subsl ->
    let bctx,eql = p0 in
    (match bound_once_equation_list bctx eql with
     | Coq_br_narrower (ls, bctx') ->
       bound_eql_fix0 ((bctx',eql),(app ls subsl))
     | Coq_br_unchanged -> Some (bctx,subsl)
     | Coq_br_absurd -> None)
  
  (** val bound_eql_fix_terminate :
      ((bcontext*Coq_es.equation list)*substitution list) ->
      (bcontext*substitution list) option **)
  
  let rec bound_eql_fix_terminate = function
  | p0,subsl ->
    let bctx,eql = p0 in
    (match bound_once_equation_list bctx eql with
     | Coq_br_narrower (ls, bctx') ->
       bound_eql_fix_terminate ((bctx',eql),(app ls subsl))
     | Coq_br_unchanged -> Some (bctx,subsl)
     | Coq_br_absurd -> None)
  
  (** val bound_eql_fix :
      ((bcontext*Coq_es.equation list)*substitution list) ->
      (bcontext*substitution list) option **)
  
  let bound_eql_fix x =
    bound_eql_fix_terminate x
  
  type coq_R_bound_eql_fix =
  | R_bound_eql_fix_0 of ((bcontext*Coq_es.equation list)*substitution list)
     * bcontext * Coq_es.equation list * substitution list
  | R_bound_eql_fix_1 of ((bcontext*Coq_es.equation list)*substitution list)
     * bcontext * Coq_es.equation list * substitution list
  | R_bound_eql_fix_2 of ((bcontext*Coq_es.equation list)*substitution list)
     * bcontext * Coq_es.equation list * substitution list
     * substitution list * bcontext * (bcontext*substitution list) option
     * coq_R_bound_eql_fix
  
  (** val coq_R_bound_eql_fix_rect :
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> substitution list ->
      bcontext -> __ -> (bcontext*substitution list) option ->
      coq_R_bound_eql_fix -> 'a1 -> 'a1) -> ((bcontext*Coq_es.equation
      list)*substitution list) -> (bcontext*substitution list) option ->
      coq_R_bound_eql_fix -> 'a1 **)
  
  let rec coq_R_bound_eql_fix_rect f f0 f1 p o = function
  | R_bound_eql_fix_0 (p0, bctx, eql, subsl) -> f p0 bctx eql subsl __ __
  | R_bound_eql_fix_1 (p0, bctx, eql, subsl) -> f0 p0 bctx eql subsl __ __
  | R_bound_eql_fix_2 (p0, bctx, eql, subsl, ls, bctx', res, r0) ->
    f1 p0 bctx eql subsl __ ls bctx' __ res r0
      (coq_R_bound_eql_fix_rect f f0 f1 ((bctx',eql),(app ls subsl)) res r0)
  
  (** val coq_R_bound_eql_fix_rec :
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> substitution list ->
      bcontext -> __ -> (bcontext*substitution list) option ->
      coq_R_bound_eql_fix -> 'a1 -> 'a1) -> ((bcontext*Coq_es.equation
      list)*substitution list) -> (bcontext*substitution list) option ->
      coq_R_bound_eql_fix -> 'a1 **)
  
  let rec coq_R_bound_eql_fix_rec f f0 f1 p o = function
  | R_bound_eql_fix_0 (p0, bctx, eql, subsl) -> f p0 bctx eql subsl __ __
  | R_bound_eql_fix_1 (p0, bctx, eql, subsl) -> f0 p0 bctx eql subsl __ __
  | R_bound_eql_fix_2 (p0, bctx, eql, subsl, ls, bctx', res, r0) ->
    f1 p0 bctx eql subsl __ ls bctx' __ res r0
      (coq_R_bound_eql_fix_rec f f0 f1 ((bctx',eql),(app ls subsl)) res r0)
  
  (** val bound_eql_fix_rect :
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> substitution list ->
      bcontext -> __ -> 'a1 -> 'a1) -> ((bcontext*Coq_es.equation
      list)*substitution list) -> 'a1 **)
  
  let rec bound_eql_fix_rect f f0 f1 p =
    let f2 = f1 p in
    let f3 = f0 p in
    let f4 = f p in
    let p0,l0 = p in
    let b0,l1 = p0 in
    let f5 = f2 b0 l1 l0 __ in
    let f6 = f3 b0 l1 l0 __ in
    let f7 = f4 b0 l1 l0 __ in
    (match bound_once_equation_list b0 l1 with
     | Coq_br_narrower (l2, b1) ->
       let f8 = f5 l2 b1 __ in
       let hrec = bound_eql_fix_rect f f0 f1 ((b1,l1),(app l2 l0)) in f8 hrec
     | Coq_br_unchanged -> f6 __
     | Coq_br_absurd -> f7 __)
  
  (** val bound_eql_fix_rec :
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> __ -> 'a1) ->
      (((bcontext*Coq_es.equation list)*substitution list) -> bcontext ->
      Coq_es.equation list -> substitution list -> __ -> substitution list ->
      bcontext -> __ -> 'a1 -> 'a1) -> ((bcontext*Coq_es.equation
      list)*substitution list) -> 'a1 **)
  
  let bound_eql_fix_rec =
    bound_eql_fix_rect
  
  (** val coq_R_bound_eql_fix_correct :
      ((bcontext*Coq_es.equation list)*substitution list) ->
      (bcontext*substitution list) option -> coq_R_bound_eql_fix **)
  
  let coq_R_bound_eql_fix_correct x res =
    bound_eql_fix_rect (fun y y0 y1 y2 _ _ z _ -> R_bound_eql_fix_0 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ z _ -> R_bound_eql_fix_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ y4 y5 _ y7 z _ -> R_bound_eql_fix_2 (y, y0, y1, y2,
      y4, y5, (bound_eql_fix ((y5,y1),(app y4 y2))),
      (y7 (bound_eql_fix ((y5,y1),(app y4 y2))) __))) x res __
  
  (** val check_sat : equation_system -> substitution list option **)
  
  let check_sat eqs =
    match bound_eql_fix
            ((initial_bcontext,(eqs_equations eqs)),(eqs_substitutions eqs)) with
    | Some p -> let b0,subsl = p in Some subsl
    | None -> None
  
  (** val coq_SATbounder :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system option **)
  
  let coq_SATbounder ses =
    match wrapped_ses ses with
    | Some ses' ->
      (match check_sat ses' with
       | Some l0 ->
         Some
           (unwrapped_ses { eqs_substitutions =
             (app l0 (eqs_substitutions ses')); eqs_equations =
             (eqs_equations ses'); eqs_nequations = (eqs_nequations ses') })
       | None -> None)
    | None -> None
  
  (** val ies_bounder :
      Coq_es.impl_equation_system -> Coq_es.impl_equation_system option **)
  
  let ies_bounder ies =
    match coq_SATbounder (Coq_es.ies2ses ies) with
    | Some ses' ->
      Some { Coq_es.impl_exvars = (Coq_es.impl_exvars ies);
        Coq_es.impl_equalities = (Coq_es.sat_equalities ses');
        Coq_es.impl_equations = (Coq_es.sat_equations ses');
        Coq_es.impl_nequations = (Coq_es.sat_nequations ses') }
    | None -> None
  
  (** val coq_IMPLbounder :
      Coq_es.impl_system -> (Coq_es.impl_system, unit) result **)
  
  let coq_IMPLbounder = function
  | ies1,ies2 ->
    (match ies_bounder ies1 with
     | Some ies1' ->
       (match ies_bounder ies2 with
        | Some ies2' -> Same (ies1',ies2')
        | None -> Absurd)
     | None -> Simpler ())
 end

module Solver = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e = share
    
    val e_eq_dec : e eqDec
    
    val e_height : e heightable
    
    val bot : Coq_Share.t
   end
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_bf:sig 
  type var = Coq_sv.t
  
  type context = var -> bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF * bF
  | Coq_orF of bF * bF
  | Coq_implF of bF * bF
  | Coq_negF of bF
  | Coq_exF of var * bF
  | Coq_allF of var * bF
  
  val bF_rect :
    (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
    -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF ->
    'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) ->
    bF -> 'a1
  
  val bF_rec :
    (bool -> 'a1) -> (var -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF
    -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF -> 'a1 -> bF -> 'a1 -> 'a1) -> (bF ->
    'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) -> (var -> bF -> 'a1 -> 'a1) ->
    bF -> 'a1
  
  val bF_vars : bF -> var list
  
  val bF_varsable : (bF, var) varsable
  
  val beval : context -> bF -> bool
  
  val bF_eval : (context, bF) evalable
  
  val bsize : bF -> int
  
  val bsubst : bF -> var -> bool -> bF
  
  val bF_eq_dec : bF eqDec
 end) ->
 functor (Coq_bsf:sig 
  val bsolver : Coq_bf.bF -> bool option
 end) ->
 struct 
  module Coq_esf = System_Features(Coq_sv)(Coq_es)
  
  module Coq_bes = Equation_system(Coq_sv)(Bool_Domain)
  
  module Coq_besf = System_Features(Coq_sv)(Coq_bes)
  
  module Coq_sat_decompose = SAT_Decompose(Coq_sv)(Coq_es)(Coq_esf)
  
  module Coq_impl_decompose = IMPL_Decompose(Coq_sv)(Coq_es)(Coq_esf)
  
  module Coq_s2b = Share2Bool(Coq_sv)(Coq_es)(Coq_esf)(Coq_bes)(Coq_besf)
  
  module Coq_sat_correct = SAT_Correctness(Coq_sv)(Coq_es)(Coq_esf)
  
  module Coq_impl_correct = IMPL_Correctness(Coq_sv)(Coq_es)(Coq_esf)
  
  module Coq_sh_simplifier = Simplifier(Coq_sv)(Share_Domain)(Coq_es)(Share_Simpl_Spec)
  
  module Coq_b_simplifier = Simplifier(Coq_sv)(Bool_Domain)(Coq_bes)(Bool_Simpl_Spec)
  
  module Coq_interpreter = Interpreter(Coq_sv)(Coq_bes)(Coq_bf)
  
  module Coq_b_solver = Bool_solver(Coq_sv)(Coq_bf)(Coq_bes)(Coq_b_simplifier)(Coq_interpreter)(Coq_bsf)
  
  module Coq_bounder = Bounder(Coq_sv)(Coq_es)
  
  (** val eval_disjunct : ('a1 -> bool) -> 'a1 list -> bool **)
  
  let rec eval_disjunct f = function
  | [] -> true
  | a0 :: l'0 ->
    (match l'0 with
     | [] -> f a0
     | a22 :: l1 -> if f a0 then true else eval_disjunct f l'0)
  
  (** val eval_conjunct : ('a1 -> bool) -> 'a1 list -> bool **)
  
  let rec eval_conjunct f = function
  | [] -> true
  | a0 :: l'0 -> if f a0 then eval_conjunct f l'0 else false
  
  (** val nSATbsolver : Coq_bes.sat_equation_system -> bool **)
  
  let nSATbsolver ses =
    Coq_b_solver.coq_SATbsolver (Coq_besf.replace_ses_nequations ses [])
  
  (** val sSATbsolver :
      Coq_bes.nequation -> Coq_bes.sat_equation_system -> bool **)
  
  let sSATbsolver ne ses =
    Coq_b_solver.coq_SATbsolver
      (Coq_besf.replace_ses_nequations ses (ne :: []))
  
  (** val nIMPLbsolver : Coq_bes.impl_system -> bool **)
  
  let nIMPLbsolver is =
    Coq_b_solver.coq_IMPLbsolver (Coq_besf.replace_is_nequations is [] [])
  
  (** val zIMPLbsolver : Coq_bes.nequation -> Coq_bes.impl_system -> bool **)
  
  let zIMPLbsolver ne is =
    Coq_b_solver.coq_IMPLbsolver
      (Coq_besf.replace_is_nequations is [] (ne :: []))
  
  (** val sIMPLbsolver :
      Coq_bes.nequation -> Coq_bes.nequation -> Coq_bes.impl_system -> bool **)
  
  let sIMPLbsolver ne ne' is =
    Coq_b_solver.coq_IMPLbsolver
      (Coq_besf.replace_is_nequations is (ne :: []) (ne' :: []))
  
  (** val coq_SATpreprocess :
      Coq_es.sat_equation_system -> Coq_es.sat_equation_system option **)
  
  let coq_SATpreprocess ses =
    match Coq_sh_simplifier.coq_SATsimplifier ses with
    | Some ses54 ->
      (match Coq_bounder.coq_SATbounder ses54 with
       | Some ses55 -> Coq_sh_simplifier.coq_SATsimplifier ses55
       | None -> None)
    | None -> None
  
  (** val nSATsolver : Coq_es.sat_equation_system -> bool **)
  
  let nSATsolver ses =
    let ses_list =
      map (Coq_s2b.transform Coq_s2b.coq_Sses2bses)
        (Coq_sat_decompose.coq_SAT_decompose ses)
    in
    eval_conjunct (fun ses' ->
      Coq_b_solver.coq_SATbsolver (Coq_besf.replace_ses_nequations ses' []))
      ses_list
  
  (** val sSATsolver :
      Coq_es.sat_equation_system -> Coq_es.nequation -> bool **)
  
  let sSATsolver ses neqn =
    let ses_list =
      Coq_sat_decompose.coq_SAT_decompose
        (Coq_esf.replace_ses_nequations ses (neqn :: []))
    in
    eval_disjunct Coq_b_solver.coq_SATbsolver
      (map (Coq_s2b.transform Coq_s2b.coq_Sses2bses) ses_list)
  
  (** val coq_SATsolver : Coq_es.sat_equation_system -> bool **)
  
  let coq_SATsolver ses =
    match coq_SATpreprocess ses with
    | Some ses' ->
      if nSATsolver ses'
      then eval_conjunct (sSATsolver ses') (Coq_es.sat_nequations ses')
      else false
    | None -> false
  
  (** val coq_IMPLpreprocess :
      Coq_es.impl_system -> (Coq_es.impl_system, unit) result **)
  
  let coq_IMPLpreprocess is =
    match Coq_sh_simplifier.coq_IMPLsimplifier is with
    | Same is50 ->
      (match Coq_bounder.coq_IMPLbounder is50 with
       | Same is51 -> Coq_sh_simplifier.coq_IMPLsimplifier is51
       | x -> x)
    | x -> x
  
  (** val nIMPLsolver : Coq_es.impl_system -> bool **)
  
  let nIMPLsolver is =
    let is_list =
      map (Coq_s2b.transform Coq_s2b.coq_Sis2bis)
        (Coq_impl_decompose.coq_IMPL_decompose is)
    in
    eval_conjunct (fun is' ->
      Coq_b_solver.coq_IMPLbsolver (Coq_besf.replace_is_nequations is' [] []))
      is_list
  
  (** val zIMPLsolver : Coq_es.impl_system -> Coq_es.nequation -> bool **)
  
  let zIMPLsolver is ne =
    let is_list =
      Coq_impl_decompose.coq_IMPL_decompose
        (Coq_esf.replace_is_nequations is [] (ne :: []))
    in
    eval_disjunct Coq_b_solver.coq_IMPLbsolver
      (map (Coq_s2b.transform Coq_s2b.coq_Sis2bis) is_list)
  
  (** val sIMPLsolver :
      Coq_es.impl_system -> Coq_es.nequation -> Coq_es.nequation -> bool **)
  
  let sIMPLsolver is ne ne' =
    let is_list =
      Coq_impl_decompose.coq_IMPL_decompose
        (Coq_esf.replace_is_nequations is (ne :: []) (ne' :: []))
    in
    eval_conjunct Coq_b_solver.coq_IMPLbsolver
      (map (Coq_s2b.transform Coq_s2b.coq_Sis2bis) is_list)
  
  (** val is_empty : 'a1 list -> bool **)
  
  let is_empty = function
  | [] -> true
  | a0 :: l1 -> false
  
  (** val subroutine :
      Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation -> bool **)
  
  let subroutine is l0 ne =
    if zIMPLsolver is ne
    then true
    else eval_disjunct (fun ne' -> sIMPLsolver is ne' ne) l0
  
  (** val coq_IMPLsolver : Coq_es.impl_system -> bool **)
  
  let coq_IMPLsolver is =
    match coq_IMPLpreprocess is with
    | Absurd ->
      if coq_SATsolver (Coq_es.ies2ses (fst is)) then false else true
    | Simpler u -> true
    | Same is' ->
      let ies1,ies2 = is' in
      if coq_SATsolver (Coq_es.ies2ses ies1)
      then if nIMPLsolver is'
           then let l1 = Coq_es.impl_nequations ies1 in
                let l2 = Coq_es.impl_nequations ies2 in
                if is_empty l2
                then true
                else if is_empty l1
                     then eval_conjunct (zIMPLsolver is') l2
                     else eval_conjunct (subroutine is' l1) l2
           else false
      else true
 end

module type INPUT = 
 sig 
  type e 
  
  val e_eq_dec : e -> e -> bool
 end

module UnionFind_Lemmas = 
 functor (Coq_i:INPUT) ->
 functor (Coq_uf:sig 
  type t 
  
  val empty : t
  
  val singleton : t -> Coq_i.e -> t
  
  val union : t -> Coq_i.e -> Coq_i.e -> t
  
  val find : t -> Coq_i.e -> Coq_i.e option*t
  
  val find_e : t -> Coq_i.e -> Coq_i.e option
  
  val find_t : t -> Coq_i.e -> t
 end) ->
 struct 
  (** val coq_In_dec : Coq_uf.t -> Coq_i.e -> bool **)
  
  let coq_In_dec s0 el =
    match Coq_uf.find_e s0 el with
    | Some e0 -> true
    | None -> false
 end

type ('a, 'b) varsable0 =
  'a -> 'b list
  (* singleton inductive, whose constructor was Varsable *)

(** val vars0 : ('a1, 'a2) varsable0 -> 'a1 -> 'a2 list **)

let vars0 varsable1 =
  varsable1

type 'a eqDec0 = 'a -> 'a -> bool

(** val eq_dec1 : 'a1 eqDec0 -> 'a1 -> 'a1 -> bool **)

let eq_dec1 eqDec1 =
  eqDec1

type ('a, 'b) evalable0 =
| Evalable0

type ('a, 'b) overridable =
  'a -> 'a -> 'b list -> 'a
  (* singleton inductive, whose constructor was Overridable *)

(** val override0 :
    ('a1, 'a2) overridable -> 'a1 -> 'a1 -> 'a2 list -> 'a1 **)

let override0 overridable0 =
  overridable0

module type PARTITION_INPUT = 
 sig 
  type equation 
  
  val eqn_eq_dec : equation eqDec0
  
  type var 
  
  val var_eq_dec : var eqDec0
  
  val varsable_equation : (equation, var) varsable0
  
  type context 
  
  val a_context : context
  
  val context_override :
    (context,
    var)
    overridable
  
  val eval :
    (context,
    equation)
    evalable0
 end

(** val remove_1st :
    ('a1*'a2)
    list
    ->
    'a2
    list **)

let remove_1st l0 =
  map
    (fun e0 ->
    snd
      e0)
    l0

module MakeListOrdering = 
 functor (O:OrderedType) ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

type colour =
| Red
| Black

module Colour = 
 struct 
  type t
    =
    colour
 end

module Coq_Make = 
 functor (K:OrderedType) ->
 struct 
  module Raw = 
   struct 
    type key
      =
      K.t
    
    type 'value tree =
    | E
    | N of Colour.t
       * 'value
         tree
       * key
       * 'value
       * 'value
         tree
    
    type 'value map_of
      =
      'value
      tree
    
    (** val min_elt :
        'a1
        tree
        ->
        (key*'a1)
        option **)
    
    let rec min_elt = function
    | E ->
      None
    | N (t1,
         l0,
         k,
         v0,
         t2) ->
      (match l0 with
       | E ->
         Some
           (k,v0)
       | N (t3,
            t4,
            k0,
            y,
            t5) ->
         min_elt
           l0)
    
    (** val max_elt :
        'a1
        tree
        ->
        (key*'a1)
        option **)
    
    let rec max_elt = function
    | E ->
      None
    | N (t1,
         t2,
         k,
         v0,
         r) ->
      (match r with
       | E ->
         Some
           (k,v0)
       | N (t3,
            t4,
            k0,
            y,
            t5) ->
         max_elt
           r)
    
    (** val mem :
        K.t
        ->
        'a1
        tree
        ->
        bool **)
    
    let rec mem x = function
    | E ->
      false
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Eq ->
         true
       | Lt ->
         mem
           x
           l0
       | Gt ->
         mem
           x
           r)
    
    type 'val0 coq_R_min_elt =
    | R_min_elt_0 of 'val0
                     tree
    | R_min_elt_1 of 'val0
                     tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
    | R_min_elt_2 of 'val0
                     tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
       * (key*'val0)
         option
       * 'val0
         coq_R_min_elt
    
    type 'val0 coq_R_max_elt =
    | R_max_elt_0 of 'val0
                     tree
    | R_max_elt_1 of 'val0
                     tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
    | R_max_elt_2 of 'val0
                     tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
       * Colour.t
       * 'val0
         tree
       * key
       * 'val0
       * 'val0
         tree
       * (key*'val0)
         option
       * 'val0
         coq_R_max_elt
    
    (** val empty :
        'a1
        map_of **)
    
    let empty =
      E
    
    (** val update :
        K.t
        ->
        'a1
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let rec update x y t0 = match t0 with
    | E ->
      t0
    | N (c0,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Eq ->
         N
           (c0,
           l0,
           k,
           y,
           r)
       | Lt ->
         N
           (c0,
           (update
             x
             y
             l0),
           k,
           v0,
           r)
       | Gt ->
         N
           (c0,
           l0,
           k,
           v0,
           (update
             x
             y
             r)))
    
    (** val is_empty :
        'a1
        map_of
        ->
        bool **)
    
    let is_empty = function
    | E ->
      true
    | N (x,
         x0,
         x1,
         x2,
         x3) ->
      false
    
    (** val find :
        K.t
        ->
        'a1
        map_of
        ->
        'a1
        option **)
    
    let rec find x = function
    | E ->
      None
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Eq ->
         Some
           v0
       | Lt ->
         find
           x
           l0
       | Gt ->
         find
           x
           r)
    
    (** val subsetl :
        ('a1
        tree
        ->
        bool)
        ->
        K.t
        ->
        'a1
        map_of
        ->
        bool **)
    
    let rec subsetl subset_l1 k1 t2 = match t2 with
    | E ->
      false
    | N (t0,
         l0,
         k2,
         v0,
         r) ->
      (match K.compare
               k1
               k2 with
       | Eq ->
         subset_l1
           l0
       | Lt ->
         subsetl
           subset_l1
           k1
           l0
       | Gt ->
         if mem
              k1
              r
         then subset_l1
                t2
         else false)
    
    (** val subsetr :
        ('a1
        tree
        ->
        bool)
        ->
        K.t
        ->
        'a1
        map_of
        ->
        bool **)
    
    let rec subsetr subset_r1 k1 t2 = match t2 with
    | E ->
      false
    | N (t0,
         l0,
         k2,
         v2,
         r) ->
      (match K.compare
               k1
               k2 with
       | Eq ->
         subset_r1
           r
       | Lt ->
         if mem
              k1
              l0
         then subset_r1
                t2
         else false
       | Gt ->
         subsetr
           subset_r1
           k1
           r)
    
    (** val subset :
        'a1
        map_of
        ->
        'a2
        map_of
        ->
        bool **)
    
    let rec subset t1 t2 =
      match t1 with
      | E ->
        true
      | N (t0,
           l1,
           k1,
           v0,
           r1) ->
        (match t2 with
         | E ->
           false
         | N (t3,
              l2,
              k2,
              v1,
              r2) ->
           (match K.compare
                    k1
                    k2 with
            | Eq ->
              if subset
                   l1
                   l2
              then subset
                     r1
                     r2
              else false
            | Lt ->
              if subsetl
                   (subset
                     l1)
                   k1
                   l2
              then subset
                     r1
                     t2
              else false
            | Gt ->
              if subsetr
                   (subset
                     r1)
                   k1
                   r2
              then subset
                     l1
                     t2
              else false))
    
    type 'val' enumeration =
    | End
    | More of key
       * 'val'
         map_of
       * 'val'
         enumeration
    
    (** val econs :
        'a1
        map_of
        ->
        'a1
        enumeration
        ->
        'a1
        enumeration **)
    
    let rec econs t0 e0 =
      match t0 with
      | E ->
        e0
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        econs
          l0
          (More
          (k,
          r,
          e0))
    
    (** val compare_more :
        K.t
        ->
        ('a1
        enumeration
        ->
        comparison)
        ->
        'a1
        enumeration
        ->
        comparison **)
    
    let compare_more k1 cont = function
    | End ->
      Gt
    | More (k2,
            r2,
            e3) ->
      (match K.compare
               k1
               k2 with
       | Eq ->
         cont
           (econs
             r2
             e3)
       | x ->
         x)
    
    (** val compare_cont :
        'a1
        map_of
        ->
        ('a2
        enumeration
        ->
        comparison)
        ->
        'a2
        enumeration
        ->
        comparison **)
    
    let rec compare_cont m1 cont e2 =
      match m1 with
      | E ->
        cont
          e2
      | N (t0,
           l0,
           k,
           v0,
           r) ->
        compare_cont
          l0
          (compare_more
            k
            (compare_cont
              r
              cont))
          e2
    
    (** val compare_end :
        'a1
        enumeration
        ->
        comparison **)
    
    let compare_end = function
    | End ->
      Eq
    | More (x,
            x0,
            x1) ->
      Lt
    
    (** val compare :
        'a1
        map_of
        ->
        'a2
        map_of
        ->
        comparison **)
    
    let compare m m' =
      compare_cont
        m
        compare_end
        (econs
          m'
          End)
    
    type 'val' enum_ =
    | End_
    | More_ of key
       * 'val'
       * 'val'
         map_of
       * 'val'
         enum_
    
    (** val econs_ :
        'a1
        map_of
        ->
        'a1
        enum_
        ->
        'a1
        enum_ **)
    
    let rec econs_ t0 e0 =
      match t0 with
      | E ->
        e0
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        econs_
          l0
          (More_
          (k,
          v0,
          r,
          e0))
    
    (** val equal_more :
        K.t
        ->
        'a1
        ->
        ('a1
        ->
        'a2
        ->
        bool)
        ->
        ('a2
        enum_
        ->
        bool)
        ->
        'a2
        enum_
        ->
        bool **)
    
    let equal_more k1 v1 cmp cont = function
    | End_ ->
      false
    | More_ (k2,
             v2,
             r2,
             e3) ->
      (match K.compare
               k1
               k2 with
       | Eq ->
         if cmp
              v1
              v2
         then cont
                (econs_
                  r2
                  e3)
         else false
       | _ ->
         false)
    
    (** val equal_cont :
        'a1
        map_of
        ->
        ('a1
        ->
        'a2
        ->
        bool)
        ->
        ('a2
        enum_
        ->
        bool)
        ->
        'a2
        enum_
        ->
        bool **)
    
    let rec equal_cont m1 cmp cont e2 =
      match m1 with
      | E ->
        cont
          e2
      | N (t0,
           l0,
           k,
           v0,
           r) ->
        equal_cont
          l0
          cmp
          (equal_more
            k
            v0
            cmp
            (equal_cont
              r
              cmp
              cont))
          e2
    
    (** val equal_end :
        'a1
        enum_
        ->
        bool **)
    
    let equal_end = function
    | End_ ->
      true
    | More_ (x,
             x0,
             x1,
             x2) ->
      false
    
    (** val equal :
        ('a1
        ->
        'a2
        ->
        bool)
        ->
        'a1
        map_of
        ->
        'a2
        map_of
        ->
        bool **)
    
    let equal cmp m m' =
      equal_cont
        m
        cmp
        equal_end
        (econs_
          m'
          End_)
    
    (** val for_all :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        tree
        ->
        bool **)
    
    let rec for_all f = function
    | E ->
      true
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      if if f
              k
              v0
         then for_all
                f
                l0
         else false
      then for_all
             f
             r
      else false
    
    (** val exists_ :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        tree
        ->
        bool **)
    
    let rec exists_ f = function
    | E ->
      false
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      if if f
              k
              v0
         then true
         else exists_
                f
                l0
      then true
      else exists_
             f
             r
    
    (** val cardinal :
        'a1
        map_of
        ->
        int **)
    
    let rec cardinal = function
    | E ->
      0
    | N (t0,
         l0,
         k,
         v0,
         r) ->
      (fun x -> x + 1)
        (plus
          (cardinal
            l0)
          (cardinal
            r))
    
    (** val elements_aux :
        (key*'a1)
        list
        ->
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let rec elements_aux acc = function
    | E ->
      acc
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      elements_aux
        ((k,v0) :: (elements_aux
                     acc
                     r))
        l0
    
    (** val elements :
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let elements t0 =
      elements_aux
        []
        t0
    
    (** val rev_elements_aux :
        (key*'a1)
        list
        ->
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let rec rev_elements_aux acc = function
    | E ->
      acc
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      rev_elements_aux
        ((k,v0) :: (rev_elements_aux
                     acc
                     l0))
        r
    
    (** val rev_elements :
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let rev_elements t0 =
      rev_elements_aux
        []
        t0
    
    (** val kelements_aux :
        key
        list
        ->
        'a1
        map_of
        ->
        key
        list **)
    
    let rec kelements_aux acc = function
    | E ->
      acc
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      kelements_aux
        (k :: (kelements_aux
                acc
                r))
        l0
    
    (** val kelements :
        'a1
        map_of
        ->
        key
        list **)
    
    let kelements t0 =
      kelements_aux
        []
        t0
    
    (** val rev_kelements_aux :
        key
        list
        ->
        'a1
        map_of
        ->
        key
        list **)
    
    let rec rev_kelements_aux acc = function
    | E ->
      acc
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      rev_kelements_aux
        (k :: (rev_kelements_aux
                acc
                l0))
        r
    
    (** val rev_kelements :
        'a1
        map_of
        ->
        key
        list **)
    
    let rev_kelements t0 =
      rev_kelements_aux
        []
        t0
    
    (** val foldl :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        'a2
        ->
        'a2 **)
    
    let rec foldl f t0 sd =
      match t0 with
      | E ->
        sd
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        foldl
          f
          r
          (f
            k
            v0
            (foldl
              f
              l0
              sd))
    
    (** val foldr :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        'a2
        ->
        'a2 **)
    
    let rec foldr f t0 sd =
      match t0 with
      | E ->
        sd
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        foldr
          f
          l0
          (f
            k
            v0
            (foldr
              f
              r
              sd))
    
    (** val fone :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        key
        ->
        'a1
        ->
        ('a2
        ->
        'a2)
        ->
        'a2
        ->
        'a2 **)
    
    let fone f k v0 cont sd =
      cont
        (f
          k
          v0
          sd)
    
    (** val fleft :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        ('a2
        ->
        'a2)
        ->
        'a2
        ->
        'a2 **)
    
    let rec fleft f t0 cont sd =
      match t0 with
      | E ->
        cont
          sd
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        (match l0 with
         | E ->
           fleft
             f
             r
             cont
             (f
               k
               v0
               sd)
         | N (t2,
              t3,
              k0,
              y,
              t4) ->
           fleft
             f
             l0
             (fone
               f
               k
               v0
               (fleft
                 f
                 r
                 cont))
             sd)
    
    (** val foldl_cps :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        'a2
        ->
        'a2 **)
    
    let foldl_cps f t0 sd =
      fleft
        f
        t0
        id
        sd
    
    (** val fright :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        ('a2
        ->
        'a2)
        ->
        'a2
        ->
        'a2 **)
    
    let rec fright f t0 cont sd =
      match t0 with
      | E ->
        cont
          sd
      | N (t1,
           l0,
           k,
           v0,
           r) ->
        (match r with
         | E ->
           fright
             f
             l0
             cont
             (f
               k
               v0
               sd)
         | N (t2,
              t3,
              k0,
              y,
              t4) ->
           fright
             f
             r
             (fone
               f
               k
               v0
               (fleft
                 f
                 l0
                 cont))
             sd)
    
    (** val foldr_cps :
        (key
        ->
        'a1
        ->
        'a2
        ->
        'a2)
        ->
        'a1
        tree
        ->
        'a2
        ->
        'a2 **)
    
    let foldr_cps f t0 sd =
      fright
        f
        t0
        id
        sd
    
    (** val elements_cps :
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let elements_cps t0 =
      foldr_cps
        (fun k v0 l0 ->
        (k,v0) :: l0)
        t0
        []
    
    (** val rev_elements_cps :
        'a1
        tree
        ->
        (key*'a1)
        list **)
    
    let rev_elements_cps t0 =
      foldl_cps
        (fun k v0 l0 ->
        (k,v0) :: l0)
        t0
        []
    
    (** val kelements_cps :
        'a1
        tree
        ->
        key
        list **)
    
    let kelements_cps t0 =
      foldr_cps
        (fun k x l0 ->
        k :: l0)
        t0
        []
    
    (** val map :
        ('a1
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a2
        map_of **)
    
    let rec map f = function
    | E ->
      E
    | N (c0,
         l0,
         x,
         y,
         r) ->
      N
        (c0,
        (map
          f
          l0),
        x,
        (f
          y),
        (map
          f
          r))
    
    (** val mapi :
        (key
        ->
        'a1
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a2
        map_of **)
    
    let rec mapi f = function
    | E ->
      E
    | N (c0,
         l0,
         x,
         y,
         r) ->
      N
        (c0,
        (mapi
          f
          l0),
        x,
        (f
          x
          y),
        (mapi
          f
          r))
    
    (** val choose :
        'a1
        tree
        ->
        (key*'a1)
        option **)
    
    let choose =
      min_elt
    
    (** val singleton :
        key
        ->
        'a1
        ->
        'a1
        map_of **)
    
    let singleton k v0 =
      N
        (Red,
        E,
        k,
        v0,
        E)
    
    (** val makeBlack :
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let makeBlack t0 = match t0 with
    | E ->
      t0
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match t1 with
       | Red ->
         N
           (Black,
           l0,
           k,
           v0,
           r)
       | Black ->
         t0)
    
    (** val makeRed :
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let makeRed t0 = match t0 with
    | E ->
      t0
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match t1 with
       | Red ->
         t0
       | Black ->
         N
           (Red,
           l0,
           k,
           v0,
           r))
    
    (** val lbal :
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        tree **)
    
    let lbal l0 z z' d0 =
      match l0 with
      | E ->
        N
          (Black,
          l0,
          z,
          z',
          d0)
      | N (t0,
           a0,
           x,
           x',
           c0) ->
        (match t0 with
         | Red ->
           (match a0 with
            | E ->
              (match c0 with
               | E ->
                 N
                   (Black,
                   l0,
                   z,
                   z',
                   d0)
               | N (t1,
                    b0,
                    y,
                    y',
                    c1) ->
                 (match t1 with
                  | Red ->
                    N
                      (Red,
                      (N
                      (Black,
                      a0,
                      x,
                      x',
                      b0)),
                      y,
                      y',
                      (N
                      (Black,
                      c1,
                      z,
                      z',
                      d0)))
                  | Black ->
                    N
                      (Black,
                      l0,
                      z,
                      z',
                      d0)))
            | N (t1,
                 a22,
                 x0,
                 x'0,
                 b0) ->
              (match t1 with
               | Red ->
                 N
                   (Red,
                   (N
                   (Black,
                   a22,
                   x0,
                   x'0,
                   b0)),
                   x,
                   x',
                   (N
                   (Black,
                   c0,
                   z,
                   z',
                   d0)))
               | Black ->
                 (match c0 with
                  | E ->
                    N
                      (Black,
                      l0,
                      z,
                      z',
                      d0)
                  | N (t2,
                       b1,
                       y,
                       y',
                       c1) ->
                    (match t2 with
                     | Red ->
                       N
                         (Red,
                         (N
                         (Black,
                         a0,
                         x,
                         x',
                         b1)),
                         y,
                         y',
                         (N
                         (Black,
                         c1,
                         z,
                         z',
                         d0)))
                     | Black ->
                       N
                         (Black,
                         l0,
                         z,
                         z',
                         d0)))))
         | Black ->
           N
             (Black,
             l0,
             z,
             z',
             d0))
    
    (** val rbal :
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        tree **)
    
    let rbal a0 x x' r = match r with
    | E ->
      N
        (Black,
        a0,
        x,
        x',
        r)
    | N (t0,
         b0,
         y,
         y',
         d0) ->
      (match t0 with
       | Red ->
         (match b0 with
          | E ->
            (match d0 with
             | E ->
               N
                 (Black,
                 a0,
                 x,
                 x',
                 r)
             | N (t1,
                  c0,
                  z,
                  z',
                  d1) ->
               (match t1 with
                | Red ->
                  N
                    (Red,
                    (N
                    (Black,
                    a0,
                    x,
                    x',
                    b0)),
                    y,
                    y',
                    (N
                    (Black,
                    c0,
                    z,
                    z',
                    d1)))
                | Black ->
                  N
                    (Black,
                    a0,
                    x,
                    x',
                    r)))
          | N (t1,
               b1,
               y0,
               y'0,
               c0) ->
            (match t1 with
             | Red ->
               N
                 (Red,
                 (N
                 (Black,
                 a0,
                 x,
                 x',
                 b1)),
                 y0,
                 y'0,
                 (N
                 (Black,
                 c0,
                 y,
                 y',
                 d0)))
             | Black ->
               (match d0 with
                | E ->
                  N
                    (Black,
                    a0,
                    x,
                    x',
                    r)
                | N (t2,
                     c1,
                     z,
                     z',
                     d1) ->
                  (match t2 with
                   | Red ->
                     N
                       (Red,
                       (N
                       (Black,
                       a0,
                       x,
                       x',
                       b0)),
                       y,
                       y',
                       (N
                       (Black,
                       c1,
                       z,
                       z',
                       d1)))
                   | Black ->
                     N
                       (Black,
                       a0,
                       x,
                       x',
                       r)))))
       | Black ->
         N
           (Black,
           a0,
           x,
           x',
           r))
    
    (** val ins :
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        tree **)
    
    let rec ins x y = function
    | E ->
      N
        (Red,
        E,
        x,
        y,
        E)
    | N (c0,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Eq ->
         N
           (c0,
           l0,
           k,
           y,
           r)
       | Lt ->
         (match c0 with
          | Red ->
            N
              (Red,
              (ins
                x
                y
                l0),
              k,
              v0,
              r)
          | Black ->
            lbal
              (ins
                x
                y
                l0)
              k
              v0
              r)
       | Gt ->
         (match c0 with
          | Red ->
            N
              (Red,
              l0,
              k,
              v0,
              (ins
                x
                y
                r))
          | Black ->
            rbal
              l0
              k
              v0
              (ins
                x
                y
                r)))
    
    (** val add :
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let add x y t0 =
      makeBlack
        (ins
          x
          y
          t0)
    
    (** val lbalS :
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        tree **)
    
    let lbalS l0 k v0 r =
      match l0 with
      | E ->
        (match r with
         | E ->
           N
             (Red,
             l0,
             k,
             v0,
             r)
         | N (t0,
              a0,
              z,
              z',
              c0) ->
           (match t0 with
            | Red ->
              (match a0 with
               | E ->
                 N
                   (Red,
                   l0,
                   k,
                   v0,
                   r)
               | N (t1,
                    a22,
                    y,
                    y',
                    b0) ->
                 (match t1 with
                  | Red ->
                    N
                      (Red,
                      l0,
                      k,
                      v0,
                      r)
                  | Black ->
                    N
                      (Red,
                      (N
                      (Black,
                      l0,
                      k,
                      v0,
                      a22)),
                      y,
                      y',
                      (rbal
                        b0
                        z
                        z'
                        (makeRed
                          c0)))))
            | Black ->
              rbal
                l0
                k
                v0
                (N
                (Red,
                a0,
                z,
                z',
                c0))))
      | N (t0,
           a0,
           x,
           x',
           b0) ->
        (match t0 with
         | Red ->
           N
             (Red,
             (N
             (Black,
             a0,
             x,
             x',
             b0)),
             k,
             v0,
             r)
         | Black ->
           (match r with
            | E ->
              N
                (Red,
                l0,
                k,
                v0,
                r)
            | N (t1,
                 a22,
                 z,
                 z',
                 c0) ->
              (match t1 with
               | Red ->
                 (match a22 with
                  | E ->
                    N
                      (Red,
                      l0,
                      k,
                      v0,
                      r)
                  | N (t2,
                       a23,
                       y,
                       y',
                       b1) ->
                    (match t2 with
                     | Red ->
                       N
                         (Red,
                         l0,
                         k,
                         v0,
                         r)
                     | Black ->
                       N
                         (Red,
                         (N
                         (Black,
                         l0,
                         k,
                         v0,
                         a23)),
                         y,
                         y',
                         (rbal
                           b1
                           z
                           z'
                           (makeRed
                             c0)))))
               | Black ->
                 rbal
                   l0
                   k
                   v0
                   (N
                   (Red,
                   a22,
                   z,
                   z',
                   c0)))))
    
    (** val rbalS :
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        map_of
        ->
        'a1
        tree **)
    
    let rbalS l0 k v0 r = match r with
    | E ->
      (match l0 with
       | E ->
         N
           (Red,
           l0,
           k,
           v0,
           r)
       | N (t0,
            a0,
            x,
            x',
            b0) ->
         (match t0 with
          | Red ->
            (match b0 with
             | E ->
               N
                 (Red,
                 l0,
                 k,
                 v0,
                 r)
             | N (t1,
                  b1,
                  y,
                  y',
                  c0) ->
               (match t1 with
                | Red ->
                  N
                    (Red,
                    l0,
                    k,
                    v0,
                    r)
                | Black ->
                  N
                    (Red,
                    (lbal
                      (makeRed
                        a0)
                      x
                      x'
                      b1),
                    y,
                    y',
                    (N
                    (Black,
                    c0,
                    k,
                    v0,
                    r)))))
          | Black ->
            lbal
              (N
              (Red,
              a0,
              x,
              x',
              b0))
              k
              v0
              r))
    | N (t0,
         b0,
         y,
         y',
         c0) ->
      (match t0 with
       | Red ->
         N
           (Red,
           l0,
           k,
           v0,
           (N
           (Black,
           b0,
           y,
           y',
           c0)))
       | Black ->
         (match l0 with
          | E ->
            N
              (Red,
              l0,
              k,
              v0,
              r)
          | N (t1,
               a0,
               x,
               x',
               b1) ->
            (match t1 with
             | Red ->
               (match b1 with
                | E ->
                  N
                    (Red,
                    l0,
                    k,
                    v0,
                    r)
                | N (t2,
                     b2,
                     y0,
                     y'0,
                     c1) ->
                  (match t2 with
                   | Red ->
                     N
                       (Red,
                       l0,
                       k,
                       v0,
                       r)
                   | Black ->
                     N
                       (Red,
                       (lbal
                         (makeRed
                           a0)
                         x
                         x'
                         b2),
                       y0,
                       y'0,
                       (N
                       (Black,
                       c1,
                       k,
                       v0,
                       r)))))
             | Black ->
               lbal
                 (N
                 (Red,
                 a0,
                 x,
                 x',
                 b1))
                 k
                 v0
                 r)))
    
    (** val append :
        'a1
        map_of
        ->
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let rec append l0 = match l0 with
    | E ->
      (fun x ->
        x)
    | N (lc,
         ll,
         lx,
         ly,
         lr) ->
      let rec append_l r = match r with
      | E ->
        l0
      | N (rc,
           rl,
           rx,
           ry,
           rr) ->
        (match lc with
         | Red ->
           (match rc with
            | Red ->
              let lrl =
                append
                  lr
                  rl
              in
              (match lrl with
               | E ->
                 N
                   (Red,
                   ll,
                   lx,
                   ly,
                   (N
                   (Red,
                   lrl,
                   rx,
                   ry,
                   rr)))
               | N (t0,
                    lr',
                    x,
                    y,
                    rl') ->
                 (match t0 with
                  | Red ->
                    N
                      (Red,
                      (N
                      (Red,
                      ll,
                      lx,
                      ly,
                      lr')),
                      x,
                      y,
                      (N
                      (Red,
                      rl',
                      rx,
                      ry,
                      rr)))
                  | Black ->
                    N
                      (Red,
                      ll,
                      lx,
                      ly,
                      (N
                      (Red,
                      lrl,
                      rx,
                      ry,
                      rr)))))
            | Black ->
              N
                (Red,
                ll,
                lx,
                ly,
                (append
                  lr
                  r)))
         | Black ->
           (match rc with
            | Red ->
              N
                (Red,
                (append_l
                  rl),
                rx,
                ry,
                rr)
            | Black ->
              let lrl =
                append
                  lr
                  rl
              in
              (match lrl with
               | E ->
                 lbalS
                   ll
                   lx
                   ly
                   (N
                   (Black,
                   lrl,
                   rx,
                   ry,
                   rr))
               | N (t0,
                    lr',
                    x,
                    y,
                    rl') ->
                 (match t0 with
                  | Red ->
                    N
                      (Red,
                      (N
                      (Black,
                      ll,
                      lx,
                      ly,
                      lr')),
                      x,
                      y,
                      (N
                      (Black,
                      rl',
                      rx,
                      ry,
                      rr)))
                  | Black ->
                    lbalS
                      ll
                      lx
                      ly
                      (N
                      (Black,
                      lrl,
                      rx,
                      ry,
                      rr))))))
      in append_l
    
    (** val del :
        K.t
        ->
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let rec del x t0 = match t0 with
    | E ->
      t0
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Eq ->
         append
           l0
           r
       | Lt ->
         (match l0 with
          | E ->
            N
              (Red,
              (del
                x
                l0),
              k,
              v0,
              r)
          | N (t2,
               t3,
               k0,
               v1,
               t4) ->
            (match t2 with
             | Red ->
               N
                 (Red,
                 (del
                   x
                   l0),
                 k,
                 v0,
                 r)
             | Black ->
               lbalS
                 (del
                   x
                   l0)
                 k
                 v0
                 r))
       | Gt ->
         (match r with
          | E ->
            N
              (Red,
              l0,
              k,
              v0,
              (del
                x
                r))
          | N (t2,
               t3,
               k0,
               v1,
               t4) ->
            (match t2 with
             | Red ->
               N
                 (Red,
                 l0,
                 k,
                 v0,
                 (del
                   x
                   r))
             | Black ->
               rbalS
                 l0
                 k
                 v0
                 (del
                   x
                   r))))
    
    (** val remove :
        K.t
        ->
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let remove x t0 =
      makeBlack
        (del
          x
          t0)
    
    (** val bogus :
        'a1
        map_of*(key*'a1)
        list **)
    
    let bogus =
      E,[]
    
    (** val treeify_zero :
        (key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list **)
    
    let treeify_zero acc =
      E,acc
    
    (** val treeify_one :
        (key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list **)
    
    let treeify_one = function
    | [] ->
      bogus
    | p :: acc' ->
      let x,y =
        p
      in
      (N
      (Red,
      E,
      x,
      y,
      E)),acc'
    
    (** val treeify_cont :
        ((key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list)
        ->
        ((key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list)
        ->
        (key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list **)
    
    let treeify_cont f g lst =
      let l0,l1 =
        f
          lst
      in
      (match l1 with
       | [] ->
         bogus
       | p :: t0 ->
         let x,y =
           p
         in
         let r,t' =
           g
             t0
         in
         (N
         (Black,
         l0,
         x,
         y,
         r)),t')
    
    (** val ev :
        bool **)
    
    let ev =
      true
    
    (** val od :
        bool **)
    
    let od =
      false
    
    (** val treeify_aux :
        bool
        ->
        positive
        ->
        (key*'a1)
        list
        ->
        'a1
        map_of*(key*'a1)
        list **)
    
    let rec treeify_aux pr = function
    | XI m ->
      treeify_cont
        (treeify_aux
          od
          m)
        (treeify_aux
          pr
          m)
    | XO m ->
      treeify_cont
        (treeify_aux
          pr
          m)
        (treeify_aux
          ev
          m)
    | XH ->
      if pr
      then treeify_zero
      else treeify_one
    
    (** val plength_aux :
        (key*'a1)
        list
        ->
        positive
        ->
        positive **)
    
    let rec plength_aux l0 acc =
      match l0 with
      | [] ->
        acc
      | p :: l1 ->
        plength_aux
          l1
          (Pos.succ
            acc)
    
    (** val plength :
        (key*'a1)
        list
        ->
        positive **)
    
    let plength lst =
      plength_aux
        lst
        XH
    
    (** val treeify :
        (key*'a1)
        list
        ->
        'a1
        map_of **)
    
    let treeify l0 =
      fst
        (treeify_aux
          ev
          (plength
            l0)
          l0)
    
    (** val sl_aux :
        K.t
        ->
        (key*'a1)
        list
        ->
        (bool*positive)
        ->
        bool*positive **)
    
    let rec sl_aux x0 l0 acc =
      match l0 with
      | [] ->
        acc
      | p :: t0 ->
        let x,v0 =
          p
        in
        let b0,len =
          acc
        in
        (match K.compare
                 x0
                 x with
         | Lt ->
           sl_aux
             x
             t0
             (b0,(Pos.add
                   len
                   XH))
         | _ ->
           false,len)
    
    (** val sorted_length :
        (key*'a1)
        list
        ->
        bool*positive **)
    
    let sorted_length = function
    | [] ->
      true,XH
    | p :: t0 ->
      let x,v0 =
        p
      in
      sl_aux
        x
        t0
        (true,(XO
        XH))
    
    (** val fromList :
        (key*'a1)
        list
        ->
        'a1
        map_of **)
    
    let fromList lst =
      let b0,len =
        sorted_length
          lst
      in
      if b0
      then fst
             (treeify_aux
               ev
               len
               lst)
      else fold_left
             (fun t0 kv ->
             add
               (fst
                 kv)
               (snd
                 kv)
               t0)
             lst
             empty
    
    (** val filter_aux :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        map_of
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list **)
    
    let rec filter_aux p m acc =
      match m with
      | E ->
        acc
      | N (t0,
           l0,
           k,
           v0,
           r) ->
        let new_acc =
          filter_aux
            p
            r
            acc
        in
        if p
             k
             v0
        then filter_aux
               p
               l0
               ((k,v0) :: new_acc)
        else filter_aux
               p
               l0
               new_acc
    
    (** val filter :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        map_of
        ->
        'a1
        map_of **)
    
    let filter p t0 =
      treeify
        (filter_aux
          p
          t0
          [])
    
    (** val partition_aux :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        map_of
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list*(key*'a1)
        list **)
    
    let rec partition_aux f m ac1 ac2 =
      match m with
      | E ->
        ac1,ac2
      | N (t0,
           sl,
           k,
           v0,
           sr) ->
        let nac1,nac2 =
          partition_aux
            f
            sr
            ac1
            ac2
        in
        if f
             k
             v0
        then partition_aux
               f
               sl
               ((k,v0) :: nac1)
               nac2
        else partition_aux
               f
               sl
               nac1
               ((k,v0) :: nac2)
    
    (** val partition :
        (key
        ->
        'a1
        ->
        bool)
        ->
        'a1
        map_of
        ->
        'a1
        map_of*'a1
        map_of **)
    
    let partition f m =
      let l0,r =
        partition_aux
          f
          m
          []
          []
      in
      (treeify
        l0),(treeify
              r)
    
    (** val skp_R :
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let skp_R m = match m with
    | E ->
      m
    | N (t0,
         l0,
         k,
         y,
         t1) ->
      (match t0 with
       | Red ->
         l0
       | Black ->
         m)
    
    (** val skp_B :
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let skp_B m =
      match skp_R
              m with
      | E ->
        E
      | N (t0,
           l0,
           k,
           v0,
           t1) ->
        (match t0 with
         | Red ->
           N
             (Red,
             l0,
             k,
             v0,
             t1)
         | Black ->
           l0)
    
    (** val compare_bheight :
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        tree
        ->
        comparison **)
    
    let rec compare_bheight sx2 s0 t0 tx2 =
      match skp_R
              sx2 with
      | E ->
        (match skp_R
                 s0 with
         | E ->
           (match skp_R
                    tx2 with
            | E ->
              Eq
            | N (t1,
                 t2,
                 k,
                 v0,
                 t3) ->
              Lt)
         | N (t1,
              b0,
              k,
              v0,
              t2) ->
           (match skp_R
                    t0 with
            | E ->
              Eq
            | N (t3,
                 c0,
                 k0,
                 v1,
                 t4) ->
              (match skp_R
                       tx2 with
               | E ->
                 Eq
               | N (t5,
                    d0,
                    k1,
                    v2,
                    t6) ->
                 compare_bheight
                   E
                   b0
                   c0
                   (skp_B
                     d0))))
      | N (t1,
           a0,
           k,
           v0,
           t2) ->
        (match skp_R
                 s0 with
         | E ->
           (match skp_R
                    t0 with
            | E ->
              (match skp_R
                       tx2 with
               | E ->
                 Gt
               | N (t3,
                    t4,
                    k0,
                    v1,
                    t5) ->
                 Lt)
            | N (t3,
                 t4,
                 k0,
                 v1,
                 t5) ->
              (match skp_R
                       tx2 with
               | E ->
                 Eq
               | N (t6,
                    t7,
                    k1,
                    v2,
                    t8) ->
                 Lt))
         | N (t3,
              b0,
              k0,
              v1,
              t4) ->
           (match skp_R
                    t0 with
            | E ->
              Gt
            | N (t5,
                 c0,
                 k1,
                 v2,
                 t6) ->
              (match skp_R
                       tx2 with
               | E ->
                 compare_bheight
                   (skp_B
                     a0)
                   b0
                   c0
                   E
               | N (t7,
                    d0,
                    k2,
                    v3,
                    t8) ->
                 compare_bheight
                   (skp_B
                     a0)
                   b0
                   c0
                   (skp_B
                     d0))))
    
    (** val inter_list :
        (key
        ->
        'a1
        ->
        'a1
        ->
        'a1)
        ->
        (K.t*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list **)
    
    let rec inter_list sl = function
    | [] ->
      (fun x acc ->
        acc)
    | y0 :: t1 ->
      let x,y =
        y0
      in
      let rec inter_l1 l2 acc =
        match l2 with
        | [] ->
          acc
        | y1 :: t2 ->
          let a0,b0 =
            y1
          in
          (match K.compare
                   x
                   a0 with
           | Eq ->
             inter_list
               sl
               t1
               t2
               ((x,(sl
                     x
                     y
                     b0)) :: acc)
           | Lt ->
             inter_l1
               t2
               acc
           | Gt ->
             inter_list
               sl
               t1
               l2
               acc)
      in inter_l1
    
    (** val filter_inter_aux :
        (key
        ->
        'a1
        ->
        'a1
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a1
        map_of
        ->
        (key*'a2)
        list
        ->
        (key*'a2)
        list **)
    
    let rec filter_inter_aux sl sub0 min0 acc =
      match min0 with
      | E ->
        acc
      | N (t0,
           l0,
           x,
           y,
           r) ->
        let new_acc =
          filter_inter_aux
            sl
            sub0
            r
            acc
        in
        (match find
                 x
                 sub0 with
         | Some b0 ->
           filter_inter_aux
             sl
             sub0
             l0
             ((x,(sl
                   x
                   y
                   b0)) :: new_acc)
         | None ->
           filter_inter_aux
             sl
             sub0
             l0
             new_acc)
    
    (** val linear_inter :
        (key
        ->
        'a1
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let linear_inter sl t1 t2 =
      treeify
        (inter_list
          sl
          (rev_elements
            t1)
          (rev_elements
            t2)
          [])
    
    (** val filter_inter :
        (key
        ->
        'a1
        ->
        'a1
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a1
        map_of
        ->
        'a2
        map_of **)
    
    let filter_inter sl sub0 min0 =
      treeify
        (filter_inter_aux
          sl
          sub0
          min0
          [])
    
    (** val inter :
        (key
        ->
        'a1
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let inter sl t1 t2 =
      linear_inter
        sl
        t1
        t2
    
    (** val diff_list :
        (K.t*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list **)
    
    let rec diff_list l1 = match l1 with
    | [] ->
      (fun x acc ->
        acc)
    | y0 :: l1' ->
      let x,y =
        y0
      in
      let rec diff_l1 l2 acc =
        match l2 with
        | [] ->
          rev_append
            l1
            acc
        | y1 :: l2' ->
          let x2,y2 =
            y1
          in
          (match K.compare
                   x
                   x2 with
           | Eq ->
             diff_list
               l1'
               l2'
               acc
           | Lt ->
             diff_l1
               l2'
               acc
           | Gt ->
             diff_list
               l1'
               l2
               ((x,y) :: acc))
      in diff_l1
    
    (** val linear_diff :
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let linear_diff s1 s2 =
      treeify
        (diff_list
          (rev_elements
            s1)
          (rev_elements
            s2)
          [])
    
    (** val diff :
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let diff t1 t2 =
      match compare_bheight
              t1
              t1
              t2
              t2 with
      | Eq ->
        linear_diff
          t1
          t2
      | Lt ->
        filter
          (fun k x ->
          negb
            (mem
              k
              t2))
          t1
      | Gt ->
        foldl
          (fun k v0 ->
          remove
            k)
          t2
          t1
    
    (** val union_list :
        (K.t*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list
        ->
        (key*'a1)
        list **)
    
    let rec union_list l1 = match l1 with
    | [] ->
      rev_append
    | y0 :: t1 ->
      let x,y =
        y0
      in
      let rec union_l1 l2 acc =
        match l2 with
        | [] ->
          rev_append
            l1
            acc
        | y1 :: t2 ->
          let a0,b0 =
            y1
          in
          (match K.compare
                   x
                   a0 with
           | Eq ->
             union_list
               t1
               t2
               ((x,y) :: acc)
           | Lt ->
             union_l1
               t2
               ((a0,b0) :: acc)
           | Gt ->
             union_list
               t1
               l2
               ((x,y) :: acc))
      in union_l1
    
    (** val linear_union :
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let linear_union t1 t2 =
      treeify
        (union_list
          (rev_elements
            t1)
          (rev_elements
            t2)
          [])
    
    (** val union :
        'a1
        tree
        ->
        'a1
        tree
        ->
        'a1
        map_of **)
    
    let union t1 t2 =
      linear_union
        t1
        t2
    
    module MX = OrderedTypeFacts(K)
    
    module L = MakeListOrdering(K)
    
    (** val ltb_tree :
        K.t
        ->
        'a1
        map_of
        ->
        bool **)
    
    let rec ltb_tree x = function
    | E ->
      true
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Gt ->
         (&&)
           (ltb_tree
             x
             l0)
           (ltb_tree
             x
             r)
       | _ ->
         false)
    
    (** val gtb_tree :
        K.t
        ->
        'a1
        map_of
        ->
        bool **)
    
    let rec gtb_tree x = function
    | E ->
      true
    | N (t1,
         l0,
         k,
         v0,
         r) ->
      (match K.compare
               x
               k with
       | Lt ->
         (&&)
           (gtb_tree
             x
             l0)
           (gtb_tree
             x
             r)
       | _ ->
         false)
    
    (** val isok :
        'a1
        tree
        ->
        bool **)
    
    let rec isok = function
    | E ->
      true
    | N (t1,
         l0,
         k,
         y,
         r) ->
      (&&)
        ((&&)
          ((&&)
            (isok
              l0)
            (isok
              r))
          (ltb_tree
            k
            l0))
        (gtb_tree
          k
          r)
    
    (** val flatten_e :
        'a1
        enumeration
        ->
        key
        list **)
    
    let rec flatten_e = function
    | End ->
      []
    | More (k,
            t0,
            r) ->
      k :: (app
             (kelements
               t0)
             (flatten_e
               r))
    
    (** val rcase :
        ('a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        tree
        ->
        'a2)
        ->
        ('a1
        map_of
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a2 **)
    
    let rcase f g t0 = match t0 with
    | E ->
      g
        t0
    | N (t1,
         a0,
         k,
         v0,
         b0) ->
      (match t1 with
       | Red ->
         f
           a0
           k
           v0
           b0
       | Black ->
         g
           t0)
    
    (** val rrcase :
        ('a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        tree
        ->
        'a2)
        ->
        ('a1
        map_of
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a2 **)
    
    let rrcase f g t0 = match t0 with
    | E ->
      g
        t0
    | N (t1,
         a0,
         x,
         x',
         c0) ->
      (match t1 with
       | Red ->
         (match a0 with
          | E ->
            (match c0 with
             | E ->
               g
                 t0
             | N (t2,
                  b0,
                  y,
                  y',
                  c1) ->
               (match t2 with
                | Red ->
                  f
                    a0
                    x
                    x'
                    b0
                    y
                    y'
                    c1
                | Black ->
                  g
                    t0))
          | N (t2,
               a22,
               x0,
               x'0,
               b0) ->
            (match t2 with
             | Red ->
               f
                 a22
                 x0
                 x'0
                 b0
                 x
                 x'
                 c0
             | Black ->
               (match c0 with
                | E ->
                  g
                    t0
                | N (t3,
                     b1,
                     y,
                     y',
                     c1) ->
                  (match t3 with
                   | Red ->
                     f
                       a0
                       x
                       x'
                       b1
                       y
                       y'
                       c1
                   | Black ->
                     g
                       t0))))
       | Black ->
         g
           t0)
    
    (** val rrcase' :
        ('a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        tree
        ->
        key
        ->
        'a1
        ->
        'a1
        tree
        ->
        'a2)
        ->
        ('a1
        map_of
        ->
        'a2)
        ->
        'a1
        map_of
        ->
        'a2 **)
    
    let rrcase' f g t0 = match t0 with
    | E ->
      g
        t0
    | N (t1,
         a0,
         y,
         y',
         c0) ->
      (match t1 with
       | Red ->
         (match a0 with
          | E ->
            (match c0 with
             | E ->
               g
                 t0
             | N (t2,
                  b0,
                  y0,
                  y'0,
                  c1) ->
               (match t2 with
                | Red ->
                  f
                    a0
                    y
                    y'
                    b0
                    y0
                    y'0
                    c1
                | Black ->
                  g
                    t0))
          | N (t2,
               a22,
               x,
               x',
               b0) ->
            (match t2 with
             | Red ->
               (match c0 with
                | E ->
                  f
                    a22
                    x
                    x'
                    b0
                    y
                    y'
                    c0
                | N (t3,
                     b1,
                     y0,
                     y'0,
                     c1) ->
                  (match t3 with
                   | Red ->
                     f
                       a0
                       y
                       y'
                       b1
                       y0
                       y'0
                       c1
                   | Black ->
                     f
                       a22
                       x
                       x'
                       b0
                       y
                       y'
                       c0))
             | Black ->
               (match c0 with
                | E ->
                  g
                    t0
                | N (t3,
                     b1,
                     y0,
                     y'0,
                     c1) ->
                  (match t3 with
                   | Red ->
                     f
                       a0
                       y
                       y'
                       b1
                       y0
                       y'0
                       c1
                   | Black ->
                     g
                       t0))))
       | Black ->
         g
           t0)
    
    (** val coq_INV_rect :
        (K.t*'a1)
        list
        ->
        (K.t*'a1)
        list
        ->
        (K.t*'a1)
        list
        ->
        (__
        ->
        __
        ->
        __
        ->
        __
        ->
        __
        ->
        'a2)
        ->
        'a2 **)
    
    let coq_INV_rect l1 l2 acc f =
      f
        __
        __
        __
        __
        __
    
    (** val coq_INV_rec :
        (K.t*'a1)
        list
        ->
        (K.t*'a1)
        list
        ->
        (K.t*'a1)
        list
        ->
        (__
        ->
        __
        ->
        __
        ->
        __
        ->
        __
        ->
        'a2)
        ->
        'a2 **)
    
    let coq_INV_rec l1 l2 acc f =
      f
        __
        __
        __
        __
        __
   end
  
  type 'typ t_ =
    'typ
    Raw.map_of
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val v :
      'a1
      t_
      ->
      'a1
      Raw.map_of **)
  
  let v t0 =
    t0
  
  type 'typ map_of
    =
    'typ
    t_
  
  (** val empty :
      'a1
      map_of **)
  
  let empty =
    Raw.empty
  
  (** val singleton :
      K.t
      ->
      'a1
      ->
      'a1
      map_of **)
  
  let singleton x y =
    Raw.singleton
      x
      y
  
  (** val add :
      K.t
      ->
      'a1
      ->
      'a1
      t_
      ->
      'a1
      map_of **)
  
  let add x y m =
    Raw.add
      x
      y
      (v
        m)
  
  (** val is_empty :
      'a1
      map_of
      ->
      bool **)
  
  let is_empty m =
    Raw.is_empty
      (v
        m)
  
  (** val mem :
      K.t
      ->
      'a1
      map_of
      ->
      bool **)
  
  let mem x m =
    Raw.mem
      x
      (v
        m)
  
  (** val cardinal :
      'a1
      map_of
      ->
      int **)
  
  let cardinal m =
    Raw.cardinal
      (v
        m)
  
  (** val update :
      K.t
      ->
      'a1
      ->
      'a1
      t_
      ->
      'a1
      map_of **)
  
  let update x y m =
    Raw.update
      x
      y
      (v
        m)
  
  (** val remove :
      K.t
      ->
      'a1
      t_
      ->
      'a1
      map_of **)
  
  let remove x m =
    Raw.remove
      x
      (v
        m)
  
  (** val fromList :
      (K.t*'a1)
      list
      ->
      'a1
      map_of **)
  
  let fromList l0 =
    Raw.fromList
      l0
  
  (** val find :
      K.t
      ->
      'a1
      map_of
      ->
      'a1
      option **)
  
  let find x m =
    Raw.find
      x
      (v
        m)
  
  (** val subset :
      'a1
      map_of
      ->
      'a2
      map_of
      ->
      bool **)
  
  let subset m m' =
    Raw.subset
      (v
        m)
      (v
        m')
  
  (** val equal :
      ('a1
      ->
      'a2
      ->
      bool)
      ->
      'a1
      map_of
      ->
      'a2
      map_of
      ->
      bool **)
  
  let equal cmp m m2 =
    Raw.equal
      cmp
      (v
        m)
      (v
        m2)
  
  (** val compare :
      'a1
      map_of
      ->
      'a2
      map_of
      ->
      comparison **)
  
  let compare m m' =
    Raw.compare
      (v
        m)
      (v
        m')
  
  (** val for_all :
      (K.t
      ->
      'a1
      ->
      bool)
      ->
      'a1
      map_of
      ->
      bool **)
  
  let for_all p m =
    Raw.for_all
      p
      (v
        m)
  
  (** val exists_ :
      (K.t
      ->
      'a1
      ->
      bool)
      ->
      'a1
      map_of
      ->
      bool **)
  
  let exists_ p m =
    Raw.exists_
      p
      (v
        m)
  
  (** val union :
      'a1
      map_of
      ->
      'a1
      map_of
      ->
      'a1
      t_ **)
  
  let union m m2 =
    Raw.union
      (v
        m)
      (v
        m2)
  
  (** val inter :
      (K.t
      ->
      'a1
      ->
      'a1
      ->
      'a1)
      ->
      'a1
      map_of
      ->
      'a1
      map_of
      ->
      'a1
      t_ **)
  
  let inter sl m m2 =
    Raw.inter
      sl
      (v
        m)
      (v
        m2)
  
  (** val diff :
      'a1
      map_of
      ->
      'a1
      map_of
      ->
      'a1
      t_ **)
  
  let diff m m2 =
    Raw.diff
      (v
        m)
      (v
        m2)
  
  (** val foldl :
      (K.t
      ->
      'a1
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t_
      ->
      'a2
      ->
      'a2 **)
  
  let foldl f m sd =
    Raw.foldl
      f
      (v
        m)
      sd
  
  (** val foldr :
      (K.t
      ->
      'a1
      ->
      'a2
      ->
      'a2)
      ->
      'a1
      t_
      ->
      'a2
      ->
      'a2 **)
  
  let foldr f m sd =
    Raw.foldr
      f
      (v
        m)
      sd
  
  (** val filter :
      (K.t
      ->
      'a1
      ->
      bool)
      ->
      'a1
      map_of
      ->
      'a1
      t_ **)
  
  let filter p m =
    Raw.filter
      p
      (v
        m)
  
  (** val partition :
      (K.t
      ->
      'a1
      ->
      bool)
      ->
      'a1
      map_of
      ->
      'a1
      t_*'a1
      t_ **)
  
  let partition p m =
    let x =
      Raw.partition
        p
        (v
          m)
    in
    (fst
      x),(snd
           x)
  
  (** val map :
      ('a1
      ->
      'a2)
      ->
      'a1
      t_
      ->
      'a2
      t_ **)
  
  let map f m =
    Raw.map
      f
      (v
        m)
  
  (** val mapi :
      (K.t
      ->
      'a1
      ->
      'a2)
      ->
      'a1
      t_
      ->
      'a2
      t_ **)
  
  let mapi f m =
    Raw.mapi
      f
      (v
        m)
  
  (** val elements :
      'a1
      map_of
      ->
      (K.t*'a1)
      list **)
  
  let elements m =
    Raw.elements
      (v
        m)
  
  (** val kelements :
      'a1
      map_of
      ->
      K.t
      list **)
  
  let kelements m =
    Raw.kelements
      (v
        m)
  
  (** val choose :
      'a1
      map_of
      ->
      (K.t*'a1)
      option **)
  
  let choose m =
    Raw.choose
      (v
        m)
  
  (** val min_elt :
      'a1
      map_of
      ->
      (K.t*'a1)
      option **)
  
  let min_elt m =
    Raw.min_elt
      (v
        m)
  
  (** val max_elt :
      'a1
      map_of
      ->
      (K.t*'a1)
      option **)
  
  let max_elt m =
    Raw.max_elt
      (v
        m)
 end

module Union_Find_Base = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 struct 
  module RBT = Coq_Make(Coq_ot)
  
  type 'a coq_EqDec
    =
    'a
    ->
    'a
    ->
    bool
  
  (** val eq_dec :
      'a1
      coq_EqDec
      ->
      'a1
      ->
      'a1
      ->
      bool **)
  
  let eq_dec eqDec1 =
    eqDec1
  
  (** val nth_op :
      int
      ->
      'a1
      list
      ->
      'a1
      option **)
  
  let rec nth_op i = function
  | [] ->
    None
  | a0 :: l'0 ->
    ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
       (fun _ ->
       Some
       a0)
       (fun n0 ->
       nth_op
         n0
         l'0)
       i)
  
  type pointer =
  | Coq_null
  | Coq_addr of Coq_ot.t
  
  (** val pointer_rect :
      'a1
      ->
      (Coq_ot.t
      ->
      'a1)
      ->
      pointer
      ->
      'a1 **)
  
  let pointer_rect f f0 = function
  | Coq_null ->
    f
  | Coq_addr x ->
    f0
      x
  
  (** val pointer_rec :
      'a1
      ->
      (Coq_ot.t
      ->
      'a1)
      ->
      pointer
      ->
      'a1 **)
  
  let pointer_rec f f0 = function
  | Coq_null ->
    f
  | Coq_addr x ->
    f0
      x
  
  (** val pointer_dec :
      pointer
      coq_EqDec **)
  
  let pointer_dec a0 a' =
    match a0 with
    | Coq_null ->
      (match a' with
       | Coq_null ->
         true
       | Coq_addr t0 ->
         false)
    | Coq_addr t0 ->
      (match a' with
       | Coq_null ->
         false
       | Coq_addr t1 ->
         Input.e_eq_dec
           t0
           t1)
  
  type heap_node = { pt : pointer;
                     size : int }
  
  (** val heap_node_rect :
      (pointer
      ->
      int
      ->
      'a1)
      ->
      heap_node
      ->
      'a1 **)
  
  let heap_node_rect f h =
    let { pt =
      x;
      size =
      x0 } =
      h
    in
    f
      x
      x0
  
  (** val heap_node_rec :
      (pointer
      ->
      int
      ->
      'a1)
      ->
      heap_node
      ->
      'a1 **)
  
  let heap_node_rec f h =
    let { pt =
      x;
      size =
      x0 } =
      h
    in
    f
      x
      x0
  
  (** val pt :
      heap_node
      ->
      pointer **)
  
  let pt h =
    h.pt
  
  (** val size :
      heap_node
      ->
      int **)
  
  let size h =
    h.size
  
  (** val fresh_node : heap_node **)
  
  let fresh_node =
    { pt = Coq_null; size = 0 }
  
  type heap = heap_node RBT.map_of
  
  (** val check_root : Input.e -> heap_node RBT.map_of -> bool **)
  
  let check_root d0 hp =
    match RBT.find d0 hp with
    | Some hn ->
      (match pt hn with
       | Coq_null -> true
       | Coq_addr t0 -> false)
    | None -> false
  
  type vheap = heap
  
  (** val get_h : vheap -> heap **)
  
  let get_h hp =
    hp
  
  (** val find_parents_aux :
      heap -> Coq_ot.t -> int -> Coq_ot.t list -> (Coq_ot.t*Coq_ot.t list)
      option **)
  
  let rec find_parents_aux hp d0 n0 l0 =
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ ->
      match RBT.find d0 hp with
      | Some hn -> Some (d0,l0)
      | None -> None)
      (fun n' ->
      match RBT.find d0 hp with
      | Some hn ->
        (match pt hn with
         | Coq_null -> Some (d0,l0)
         | Coq_addr d' ->
           (match find_parents_aux hp d' n' l0 with
            | Some p -> let d'0,l'0 = p in Some (d'0,(d0 :: l'0))
            | None -> None))
      | None -> None)
      n0
  
  (** val find_parents :
      heap -> Coq_ot.t -> (Coq_ot.t*Coq_ot.t list) option **)
  
  let find_parents hp d0 =
    find_parents_aux hp d0 (length (RBT.kelements hp)) []
  
  (** val h_find : vheap -> Coq_ot.t -> Coq_ot.t option **)
  
  let h_find hp d0 =
    match find_parents (get_h hp) d0 with
    | Some p -> let d',l0 = p in Some d'
    | None -> None
  
  (** val h_empty : vheap **)
  
  let h_empty =
    RBT.empty
  
  (** val find_add : heap -> Coq_ot.t -> heap_node -> heap **)
  
  let find_add hp d0 hn =
    match RBT.find d0 hp with
    | Some h -> hp
    | None -> RBT.add d0 hn hp
  
  (** val h_singleton : vheap -> Coq_ot.t -> vheap **)
  
  let h_singleton hp d0 =
    find_add (get_h hp) d0 fresh_node
  
  (** val update_pt :
      heap_node RBT.map_of -> Input.e -> Input.e -> heap_node RBT.map_of **)
  
  let update_pt hp d0 d' =
    match RBT.find d0 hp with
    | Some hn ->
      if check_root d' hp
      then if Input.e_eq_dec d0 d'
           then hp
           else RBT.update d0 { pt = (Coq_addr d'); size = (size hn) } hp
      else hp
    | None -> hp
  
  (** val h_update_pt : vheap -> Input.e -> Input.e -> vheap **)
  
  let h_update_pt hp d0 d' =
    update_pt (get_h hp) d0 d'
  
  (** val path_compress : vheap -> Input.e -> Input.e list -> vheap **)
  
  let path_compress hp r l0 =
    fold_right (fun d' hp' -> h_update_pt hp' d' r) hp l0
  
  (** val h_cfind : vheap -> Coq_ot.t -> Coq_ot.t option*vheap **)
  
  let h_cfind hp d0 =
    match find_parents (get_h hp) d0 with
    | Some p -> let r,l0 = p in (Some r),(path_compress hp r l0)
    | None -> None,hp
  
  (** val h_cfind_r : vheap -> Coq_ot.t -> Coq_ot.t option **)
  
  let h_cfind_r hp d0 =
    fst (h_cfind hp d0)
  
  (** val h_cfind_hp : vheap -> Coq_ot.t -> vheap **)
  
  let h_cfind_hp hp d0 =
    snd (h_cfind hp d0)
  
  (** val update_size :
      heap_node RBT.map_of -> Input.e -> int -> heap_node RBT.map_of **)
  
  let update_size hp d0 s0 =
    match RBT.find d0 hp with
    | Some hn ->
      RBT.update d0 { pt = (pt hn); size = (plus s0 (size hn)) } hp
    | None -> hp
  
  (** val h_update_size : vheap -> Input.e -> int -> vheap **)
  
  let h_update_size hp d0 s0 =
    update_size (get_h hp) d0 s0
  
  (** val h_union : vheap -> Coq_ot.t -> Coq_ot.t -> vheap **)
  
  let h_union hp d1 d2 =
    let o,hp' = h_cfind hp d1 in
    (match o with
     | Some d1' ->
       let o0,hp'' = h_cfind hp' d2 in
       (match o0 with
        | Some d2' ->
          if Input.e_eq_dec d1' d2'
          then hp''
          else let o1 = RBT.find d1' (get_h hp'') in
               let o2 = RBT.find d2' (get_h hp'') in
               (match o1 with
                | Some hn1 ->
                  (match o2 with
                   | Some hn2 ->
                     if le_dec (size hn1) (size hn2)
                     then let hp1 = h_update_pt hp'' d1' d2' in
                          h_update_size hp1 d2' ((fun x -> x + 1) (size hn1))
                     else let hp2 = h_update_pt hp'' d2' d1' in
                          h_update_size hp2 d1' ((fun x -> x + 1) (size hn2))
                   | None -> hp'')
                | None -> hp'')
        | None -> hp')
     | None -> hp)
 end

module Union_Find = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 struct 
  module UFB = Union_Find_Base(Input)(Coq_ot)
  
  type t = UFB.vheap
  
  (** val empty : t **)
  
  let empty =
    UFB.h_empty
  
  (** val singleton : t -> Input.e -> t **)
  
  let singleton =
    UFB.h_singleton
  
  (** val union : t -> Input.e -> Input.e -> t **)
  
  let union =
    UFB.h_union
  
  (** val find : t -> Input.e -> Input.e option*t **)
  
  let find =
    UFB.h_cfind
  
  (** val find_e : t -> Input.e -> Input.e option **)
  
  let find_e s0 el =
    fst (find s0 el)
  
  (** val find_t : t -> Input.e -> t **)
  
  let find_t s0 el =
    snd (find s0 el)
 end

module Internal_Structures = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 struct 
  module UF = Union_Find(Input)(Coq_ot)
  
  module UFL = UnionFind_Lemmas(Input)(UF)
  
  module RBT = Coq_Make(Coq_ot)
  
  type var = Coq_ot.t
  
  (** val emptyUF : UF.t **)
  
  let emptyUF =
    UF.empty
  
  (** val add_singleton2uf : UF.t -> var -> UF.t*var **)
  
  let add_singleton2uf uf v0 =
    let o,uf' = UF.find uf v0 in
    (match o with
     | Some v' -> uf',v'
     | None -> (UF.singleton uf' v0),v0)
  
  (** val add_singleton2uf_t : UF.t -> var -> UF.t **)
  
  let add_singleton2uf_t p v0 =
    fst (add_singleton2uf p v0)
  
  (** val add_singleton2uf_v : UF.t -> var -> var **)
  
  let add_singleton2uf_v p v0 =
    snd (add_singleton2uf p v0)
  
  (** val union_singleton2uf :
      var -> (UF.t*var option) -> UF.t*var option **)
  
  let union_singleton2uf v0 = function
  | uf,ov ->
    let uf',v' = add_singleton2uf uf v0 in
    (match ov with
     | Some v'' -> let uf'' = UF.union uf' v' v'' in uf'',(UF.find_e uf'' v')
     | None -> uf',(Some v'))
  
  (** val union_singleton2uf_t : var -> (UF.t*var option) -> UF.t **)
  
  let union_singleton2uf_t v0 p =
    fst (union_singleton2uf v0 p)
  
  (** val union_singleton2uf_v : var -> (UF.t*var option) -> var option **)
  
  let union_singleton2uf_v v0 p =
    snd (union_singleton2uf v0 p)
  
  (** val add_list2uf : UF.t -> var list -> UF.t*var option **)
  
  let add_list2uf uf l0 =
    fold_right union_singleton2uf (uf,None) l0
  
  (** val add_list2uf_t : UF.t -> var list -> UF.t **)
  
  let add_list2uf_t uf l0 =
    fst (add_list2uf uf l0)
  
  (** val add_list2uf_v : UF.t -> var list -> var option **)
  
  let add_list2uf_v uf l0 =
    snd (add_list2uf uf l0)
  
  (** val eqn2uf : ('a1, var) varsable0 -> UF.t -> 'a1 -> UF.t*var option **)
  
  let eqn2uf vAB uf eqn =
    add_list2uf uf (vars0 vAB eqn)
  
  (** val eqn2uf_t : ('a1, var) varsable0 -> UF.t -> 'a1 -> UF.t **)
  
  let eqn2uf_t vAB uf eqn =
    fst (eqn2uf vAB uf eqn)
  
  (** val eqn2uf_v : ('a1, var) varsable0 -> UF.t -> 'a1 -> var option **)
  
  let eqn2uf_v vAB uf eqn =
    snd (eqn2uf vAB uf eqn)
  
  (** val eqnlist2uf : ('a1, var) varsable0 -> 'a1 list -> UF.t **)
  
  let eqnlist2uf vAB l0 =
    fold_right (fun eqn uf -> eqn2uf_t vAB uf eqn) emptyUF l0
  
  (** val get_t : (UF.t*'a1) -> UF.t **)
  
  let get_t p =
    fst p
  
  (** val get_v : (UF.t*'a1) -> 'a1 **)
  
  let get_v p =
    snd p
  
  (** val emptyRBT : 'a1 RBT.map_of **)
  
  let emptyRBT =
    RBT.empty
  
  (** val find_var :
      ('a1, var) varsable0 -> UF.t -> 'a1 -> var option*UF.t **)
  
  let find_var vAB uf eqn =
    match vars0 vAB eqn with
    | [] -> None,uf
    | v0 :: l0 -> UF.find uf v0
  
  (** val find_var_v : ('a1, var) varsable0 -> UF.t -> 'a1 -> var option **)
  
  let find_var_v vAB uf eqn =
    fst (find_var vAB uf eqn)
  
  (** val find_var_uf : ('a1, var) varsable0 -> UF.t -> 'a1 -> UF.t **)
  
  let find_var_uf vAB uf eqn =
    snd (find_var vAB uf eqn)
  
  (** val find_add :
      var -> 'a1 -> 'a1 list RBT.map_of -> 'a1 list RBT.map_of **)
  
  let find_add a0 b0 rbt =
    match RBT.find a0 rbt with
    | Some l0 -> RBT.add a0 (b0 :: l0) rbt
    | None -> RBT.add a0 (b0 :: []) rbt
  
  (** val find_list_rbt : var -> 'a1 list RBT.map_of -> 'a1 list **)
  
  let find_list_rbt a0 rbt =
    match RBT.find a0 rbt with
    | Some l0 -> l0
    | None -> []
  
  (** val add_equation2RBT :
      ('a1, var) varsable0 -> 'a1 -> UF.t -> 'a1 list RBT.map_of -> 'a1 list
      -> 'a1 list*'a1 list RBT.map_of **)
  
  let add_equation2RBT vAB eqn uf rbt l0 =
    match find_var_v vAB uf eqn with
    | Some v0 -> l0,(find_add v0 eqn rbt)
    | None ->
      (match vars0 vAB eqn with
       | [] -> (eqn :: l0),rbt
       | v' :: l'0 -> l0,rbt)
  
  (** val add_equation2RBT_l :
      ('a1, var) varsable0 -> 'a1 -> UF.t -> 'a1 list RBT.map_of -> 'a1 list
      -> 'a1 list **)
  
  let add_equation2RBT_l vAB eqn uf rbt l0 =
    fst (add_equation2RBT vAB eqn uf rbt l0)
  
  (** val add_equation2RBT_rbt :
      ('a1, var) varsable0 -> 'a1 -> UF.t -> 'a1 list RBT.map_of -> 'a1 list
      -> 'a1 list RBT.map_of **)
  
  let add_equation2RBT_rbt vAB eqn uf rbt l0 =
    snd (add_equation2RBT vAB eqn uf rbt l0)
  
  (** val get_list : ('a1 list*'a2 RBT.map_of) -> 'a1 list **)
  
  let get_list p =
    fst p
  
  (** val get_rbt : ('a1 list*'a2 RBT.map_of) -> 'a2 RBT.map_of **)
  
  let get_rbt p =
    snd p
  
  (** val eqnlist2RBT :
      ('a1, var) varsable0 -> 'a1 list -> UF.t -> 'a1 list*'a1 list
      RBT.map_of **)
  
  let eqnlist2RBT vAB l0 uf =
    fold_right (fun eqn p -> add_equation2RBT vAB eqn uf (snd p) (fst p))
      ([],emptyRBT) l0
  
  (** val eqnlist2RBT_l :
      ('a1, var) varsable0 -> 'a1 list -> UF.t -> 'a1 list **)
  
  let eqnlist2RBT_l vAB l0 uf =
    fst (eqnlist2RBT vAB l0 uf)
  
  (** val eqnlist2RBT_rbt :
      ('a1, var) varsable0 -> 'a1 list -> UF.t -> 'a1 list RBT.map_of **)
  
  let eqnlist2RBT_rbt vAB l0 uf =
    snd (eqnlist2RBT vAB l0 uf)
 end

module Partition = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 functor (Coq_pi:PARTITION_INPUT with type var = Coq_ot.t) ->
 struct 
  module IS = Internal_Structures(Input)(Coq_ot)
  
  (** val partition : Coq_pi.equation list -> Coq_pi.equation list list **)
  
  let partition l0 =
    let l1,rbt =
      IS.eqnlist2RBT Coq_pi.varsable_equation l0
        (IS.eqnlist2uf Coq_pi.varsable_equation l0)
    in
    l1 :: (remove_1st (IS.RBT.elements rbt))
 end

module Partition_Lemmas = 
 functor (Coq_pi:PARTITION_INPUT) ->
 functor (Coq_partition:sig 
  val partition : Coq_pi.equation list -> Coq_pi.equation list list
 end) ->
 struct 
  
 end

module Partition_SAT = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 functor (Coq_pi:PARTITION_INPUT with type var = Coq_ot.t) ->
 struct 
  module Part = Partition(Input)(Coq_ot)(Coq_pi)
  
  module PL = Partition_Lemmas(Coq_pi)(Part)
  
  (** val partition_SAT :
      Coq_pi.equation list -> Coq_pi.equation list list **)
  
  let partition_SAT =
    Part.partition
  
  (** val upd_lctx :
      Coq_pi.var list list -> Coq_pi.context list -> Coq_pi.context **)
  
  let rec upd_lctx l0 lctx =
    match l0 with
    | [] -> Coq_pi.a_context
    | lv :: l'0 ->
      (match lctx with
       | [] -> Coq_pi.a_context
       | ctx :: lctx' ->
         override0 Coq_pi.context_override (upd_lctx l'0 lctx') ctx lv)
 end

(** val varsable_pair : ('a1, 'a2) varsable0 -> ('a1*'a3, 'a2) varsable0 **)

let varsable_pair h = function
| a0,_tmp -> vars0 h a0

module Partition_Input_Impl = 
 functor (Coq_pi:PARTITION_INPUT) ->
 struct 
  type equation = Coq_pi.equation*bool
  
  type var = Coq_pi.var
  
  (** val eqn_eq_dec : equation eqDec0 **)
  
  let eqn_eq_dec a0 a' =
    let e0,b0 = a0 in
    let e1,b1 = a' in
    let s0 = Coq_pi.eqn_eq_dec e0 e1 in if s0 then bool_dec b0 b1 else false
  
  (** val var_eq_dec : var eqDec0 **)
  
  let var_eq_dec =
    Coq_pi.var_eq_dec
  
  (** val varsable_equation : (equation, var) varsable0 **)
  
  let varsable_equation =
    varsable_pair Coq_pi.varsable_equation
  
  type context = Coq_pi.context
  
  (** val a_context : Coq_pi.context **)
  
  let a_context =
    Coq_pi.a_context
  
  (** val context_override : (Coq_pi.context, Coq_pi.var) overridable **)
  
  let context_override =
    Coq_pi.context_override
  
  (** val eval : (context, equation) evalable0 **)
  
  let eval =
    Evalable0
 end

module Partition_IMPL = 
 functor (Input:INPUT) ->
 functor (Coq_ot:OrderedType with type t = Input.e) ->
 functor (Coq_pi:PARTITION_INPUT with type var = Coq_ot.t) ->
 struct 
  module Coq_pi' = Partition_Input_Impl(Coq_pi)
  
  module Part = Partition(Input)(Coq_ot)(Coq_pi')
  
  module PL = Partition_Lemmas(Coq_pi')(Part)
  
  (** val merge : 'a1 list -> 'a1 list -> ('a1*bool) list **)
  
  let merge l1 l2 =
    app (map (fun x -> x,false) l1) (map (fun x -> x,true) l2)
  
  (** val separate : ('a1*bool) list -> 'a1 list*'a1 list **)
  
  let separate l0 =
    (map fst (filter (fun x -> negb (snd x)) l0)),(map fst
                                                    (filter (fun x -> 
                                                      snd x) l0))
  
  (** val partition_IMPL :
      Coq_pi.equation list -> Coq_pi.equation list -> (Coq_pi.equation
      list*Coq_pi.equation list) list **)
  
  let partition_IMPL l1 l2 =
    map separate (Part.partition (merge l1 l2))
  
  (** val exclude : 'a1 eqDec0 -> 'a1 list -> 'a1 list -> 'a1 list **)
  
  let rec exclude eqd l0 lex =
    match l0 with
    | [] -> []
    | a0 :: l'0 ->
      if in_dec eqd a0 lex
      then exclude eqd l'0 lex
      else a0 :: (exclude eqd l'0 lex)
 end

module Input_of_SV = 
 functor (Coq_sv:SV) ->
 struct 
  type e = Coq_sv.t
  
  (** val e_eq_dec : e eqDec0 **)
  
  let e_eq_dec =
    Coq_sv.t_eq_dec
 end

module OrderedType_of_SV = 
 functor (Coq_sv:SV) ->
 struct 
  type t = Coq_sv.t
  
  (** val compare : t -> t -> comparison **)
  
  let compare t1 t2 =
    if Coq_sv.t_leq_dec t1 t2
    then if Coq_sv.t_lt_dec t1 t2 then Lt else Eq
    else Gt
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    Coq_sv.t_eq_dec
 end

(** val vars_transform : ('a1, 'a2) varsable -> ('a1, 'a2) varsable0 **)

let vars_transform vAB x =
  vars vAB x

(** val eqDec_transform : 'a1 eqDec -> 'a1 eqDec0 **)

let eqDec_transform eD =
  eD

type ('a, 'b, 'c) eqnS =
| EL of 'a
| EQ0 of 'b
| NEQ of 'c

(** val eqDec_eqnS :
    'a1 eqDec0 -> 'a2 eqDec0 -> 'a3 eqDec0 -> ('a1, 'a2, 'a3) eqnS eqDec0 **)

let eqDec_eqnS h h0 h1 a0 a' =
  match a0 with
  | EL a22 ->
    (match a' with
     | EL a23 -> eq_dec1 h a22 a23
     | _ -> false)
  | EQ0 b0 ->
    (match a' with
     | EQ0 b1 -> eq_dec1 h0 b0 b1
     | _ -> false)
  | NEQ c0 ->
    (match a' with
     | NEQ c1 -> eq_dec1 h1 c0 c1
     | _ -> false)

module Partition_Input_of_SV_nz = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   DOMAIN
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_es.sat_equation_system heightable
  
  val ies_h : Coq_es.impl_equation_system -> int
  
  val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_es.impl_equation_system heightable
  
  val is_h : Coq_es.impl_system -> int
  
  val is_h_zero : Coq_es.impl_system is_height_zero_spec
  
  val is_height : Coq_es.impl_system heightable
  
  val var_cheight : (Coq_es.context, Coq_es.var) cheightable
  
  val object_cheight : (Coq_es.context, Coq_es.coq_object) cheightable
  
  val equality_cheight : (Coq_es.context, Coq_es.equality) cheightable
  
  val equation_cheight : (Coq_es.context, Coq_es.equation) cheightable
  
  val nequation_cheight : (Coq_es.context, Coq_es.nequation) cheightable
  
  val ses_cheight : (Coq_es.context, Coq_es.sat_equation_system) cheightable
  
  val ies_cheight : (Coq_es.context, Coq_es.impl_equation_system) cheightable
  
  val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable
  
  val object_vars : (Coq_es.coq_object, Coq_es.var) varsable
  
  val equality_vars : (Coq_es.equality, Coq_es.var) varsable
  
  val equation_vars : (Coq_es.equation, Coq_es.var) varsable
  
  val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable
  
  val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable
  
  val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable
  
  val is_vars : (Coq_es.impl_system, Coq_es.var) varsable
  
  val vheight : Coq_es.var -> int
  
  val vheight_zero : Coq_es.var is_height_zero_spec
  
  val height_var : Coq_es.var heightable
  
  val varsable_var : (Coq_es.var, Coq_es.var) varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system -> Coq_es.nequation list ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system -> Coq_es.nequation list ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
    Coq_es.impl_system
 end) ->
 struct 
  type equation = (Coq_es.equality, Coq_es.equation, Coq_es.nequation) eqnS
  
  (** val obj_eq_dec : Coq_es.coq_object eqDec0 **)
  
  let obj_eq_dec =
    eqDec_transform
      (objectT_eq_dec Coq_es.var_eq_dec Coq_es.Coq_dom.e_eq_dec)
  
  (** val eqn_eq_dec : equation eqDec0 **)
  
  let eqn_eq_dec =
    eqDec_eqnS (eqDec_transform Coq_es.equality_eq_dec)
      (eqDec_transform Coq_es.equation_eq_dec)
      (eqDec_transform Coq_es.nequation_eq_dec)
  
  type var = Coq_es.var
  
  (** val var_eq_dec : var eqDec0 **)
  
  let var_eq_dec =
    eqDec_transform Coq_es.var_eq_dec
  
  (** val varsable_equation : (equation, var) varsable0 **)
  
  let varsable_equation = function
  | EL a0 -> vars0 (vars_transform Coq_esf.equality_vars) a0
  | EQ0 b0 -> vars0 (vars_transform Coq_esf.equation_vars) b0
  | NEQ c0 -> vars0 (vars_transform Coq_esf.nequation_vars) c0
  
  type context = Coq_es.context
  
  (** val a_context : context **)
  
  let a_context v0 =
    Coq_es.Coq_dom.bot
  
  (** val context_override : (context, var) overridable **)
  
  let context_override ctx1 ctx2 varList = override Coq_es.var_eq_dec ctx1 ctx2 varList
  
  (** val eval : (context, equation) evalable0 **)
  
  let eval =
    Evalable0
 end

type ('a, 'b) varT =
| Univ of 'a
| Ex of 'a * 'b

(** val varT_eq_dec : 'a1 eqDec0 -> 'a2 eqDec0 -> ('a1, 'a2) varT eqDec0 **)

let varT_eq_dec h h0 a0 a' =
  match a0 with
  | Univ a22 ->
    (match a' with
     | Univ a23 -> eq_dec1 h a22 a23
     | Ex (a23, b0) -> false)
  | Ex (a22, b0) ->
    (match a' with
     | Univ a23 -> false
     | Ex (a23, b1) ->
       let s0 = eq_dec1 h a22 a23 in if s0 then eq_dec1 h0 b0 b1 else false)

module Input_of_SV_neq_ex = 
 functor (Coq_sv:SV) ->
 struct 
  type e = (Coq_sv.t, bool) varT
  
  (** val e_eq_dec : e eqDec0 **)
  
  let e_eq_dec =
    varT_eq_dec (eqDec_transform Coq_sv.t_eq_dec)
      (eqDec_transform Bool_Domain.e_eq_dec)
 end

module OrderedType_of_SV_neq_ex = 
 functor (Coq_sv:SV) ->
 struct 
  type t = (Coq_sv.t, bool) varT
  
  (** val compare : t -> t -> comparison **)
  
  let compare t1 t2 =
    match t1 with
    | Univ v1 ->
      (match t2 with
       | Univ v2 ->
         if Coq_sv.t_leq_dec v1 v2
         then if Coq_sv.t_lt_dec v1 v2 then Lt else Eq
         else Gt
       | Ex (v2, b2) -> Gt)
    | Ex (v1, b1) ->
      (match t2 with
       | Univ v2 -> Lt
       | Ex (v2, b2) ->
         if b1
         then if b2
              then if Coq_sv.t_leq_dec v1 v2
                   then if Coq_sv.t_lt_dec v1 v2 then Lt else Eq
                   else Gt
              else Gt
         else if b2
              then Lt
              else if Coq_sv.t_leq_dec v1 v2
                   then if Coq_sv.t_lt_dec v1 v2 then Lt else Eq
                   else Gt)
  
  (** val eq_dec : t eqDec0 **)
  
  let eq_dec =
    varT_eq_dec (eqDec_transform Coq_sv.t_eq_dec)
      (eqDec_transform Bool_Domain.e_eq_dec)
 end

(** val varsable_eqnS' :
    ('a2, 'a1) varsable0 -> ('a3, 'a1) varsable0 -> ('a4, 'a1) varsable0 ->
    'a1 eqDec0 -> ((('a2, 'a3, 'a4) eqnS*'a1 list)*'a5, ('a1, 'a5) varT)
    varsable0 **)

let varsable_eqnS' h h0 h1 h2 = function
| p,x0 ->
  let e0,l0 = p in
  (match e0 with
   | EL e1 ->
     map (fun v0 ->
       if in_dec (eq_dec1 h2) v0 l0 then Ex (v0, x0) else Univ v0)
       (vars0 h e1)
   | EQ0 e1 ->
     map (fun v0 ->
       if in_dec (eq_dec1 h2) v0 l0 then Ex (v0, x0) else Univ v0)
       (vars0 h0 e1)
   | NEQ n0 ->
     map (fun v0 ->
       if in_dec (eq_dec1 h2) v0 l0 then Ex (v0, x0) else Univ v0)
       (vars0 h1 n0))

module Partition_Input_of_SV_neq_ex = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   DOMAIN
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero : Coq_es.sat_equation_system is_height_zero_spec
  
  val ses_height : Coq_es.sat_equation_system heightable
  
  val ies_h : Coq_es.impl_equation_system -> int
  
  val ies_h_zero : Coq_es.impl_equation_system is_height_zero_spec
  
  val ies_height : Coq_es.impl_equation_system heightable
  
  val is_h : Coq_es.impl_system -> int
  
  val is_h_zero : Coq_es.impl_system is_height_zero_spec
  
  val is_height : Coq_es.impl_system heightable
  
  val var_cheight : (Coq_es.context, Coq_es.var) cheightable
  
  val object_cheight : (Coq_es.context, Coq_es.coq_object) cheightable
  
  val equality_cheight : (Coq_es.context, Coq_es.equality) cheightable
  
  val equation_cheight : (Coq_es.context, Coq_es.equation) cheightable
  
  val nequation_cheight : (Coq_es.context, Coq_es.nequation) cheightable
  
  val ses_cheight : (Coq_es.context, Coq_es.sat_equation_system) cheightable
  
  val ies_cheight : (Coq_es.context, Coq_es.impl_equation_system) cheightable
  
  val is_cheight : (Coq_es.context, Coq_es.impl_system) cheightable
  
  val object_vars : (Coq_es.coq_object, Coq_es.var) varsable
  
  val equality_vars : (Coq_es.equality, Coq_es.var) varsable
  
  val equation_vars : (Coq_es.equation, Coq_es.var) varsable
  
  val nequation_vars : (Coq_es.nequation, Coq_es.var) varsable
  
  val ses_vars : (Coq_es.sat_equation_system, Coq_es.var) varsable
  
  val ies_vars : (Coq_es.impl_equation_system, Coq_es.var) varsable
  
  val is_vars : (Coq_es.impl_system, Coq_es.var) varsable
  
  val vheight : Coq_es.var -> int
  
  val vheight_zero : Coq_es.var is_height_zero_spec
  
  val height_var : Coq_es.var heightable
  
  val varsable_var : (Coq_es.var, Coq_es.var) varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system -> Coq_es.nequation list ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system -> Coq_es.nequation list ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system -> Coq_es.nequation list -> Coq_es.nequation list ->
    Coq_es.impl_system
 end) ->
 struct 
  type equation =
    ((Coq_es.equality, Coq_es.equation, Coq_es.nequation) eqnS*Coq_es.var
    list)*bool
  
  (** val eqn_eq_dec : equation eqDec0 **)
  
  let eqn_eq_dec a0 a' =
    let p,x = a0 in
    let eqn1,l1 = p in
    let p0,x0 = a' in
    let eqn2,l2 = p0 in
    let s0 =
      eq_dec1
        (eqDec_eqnS (eqDec_transform Coq_es.equality_eq_dec)
          (eqDec_transform Coq_es.equation_eq_dec)
          (eqDec_transform Coq_es.nequation_eq_dec)) eqn1 eqn2
    in
    if s0
    then let s1 =
           list_eq_dec (eq_dec1 (eqDec_transform Coq_es.var_eq_dec)) l1 l2
         in
         if s1 then bool_dec x x0 else false
    else false
  
  type var = (Coq_sv.t, bool) varT
  
  (** val var_eq_dec : var eqDec0 **)
  
  let var_eq_dec =
    varT_eq_dec (eqDec_transform Coq_es.var_eq_dec)
      (eqDec_transform Bool_Domain.e_eq_dec)
  
  (** val varsable_equation : (equation, var) varsable0 **)
  
  let varsable_equation =
    varsable_eqnS' (vars_transform Coq_esf.equality_vars)
      (vars_transform Coq_esf.equation_vars)
      (vars_transform Coq_esf.nequation_vars)
      (eqDec_transform Coq_es.var_eq_dec)
  
  type context = Coq_es.context
  
  (** val a_context : context **)
  
  let a_context v0 =
    Coq_es.Coq_dom.bot
  
  (** val eval : (context, equation) evalable0 **)
  
  let eval =
    Evalable0
  
  (** val ctx_override : context -> context -> var list -> context **)
  
  let ctx_override ctx ctx' l0 =
    ctx
  
  (** val context_override : (context, var) overridable **)
  
  let context_override =
    ctx_override
 end

module System_Partition = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   DOMAIN
  
  type var = Coq_sv.t
  
  type s = Coq_dom.e
  
  val var_eq_dec : var eqDec
  
  type coq_object = (var, s) objectT
  
  type equality = coq_object*coq_object
  
  val equality_eq_dec : equality eqDec
  
  type equation = (coq_object*coq_object)*coq_object
  
  val equation_eq_dec : equation eqDec
  
  type nequation = equation*unit
  
  val nequation_eq_dec : nequation eqDec
  
  type sat_equation_system = { sat_equalities : equality list;
                               sat_equations : equation list;
                               sat_nequations : nequation list }
  
  val sat_equation_system_rect :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equation_system_rec :
    (equality list -> equation list -> nequation list -> 'a1) ->
    sat_equation_system -> 'a1
  
  val sat_equalities : sat_equation_system -> equality list
  
  val sat_equations : sat_equation_system -> equation list
  
  val sat_nequations : sat_equation_system -> nequation list
  
  type impl_equation_system = { impl_exvars : var list;
                                impl_equalities : equality list;
                                impl_equations : equation list;
                                impl_nequations : nequation list }
  
  val impl_equation_system_rect :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_equation_system_rec :
    (var list -> equality list -> equation list -> nequation list -> 'a1) ->
    impl_equation_system -> 'a1
  
  val impl_exvars : impl_equation_system -> var list
  
  val impl_equalities : impl_equation_system -> equality list
  
  val impl_equations : impl_equation_system -> equation list
  
  val impl_nequations : impl_equation_system -> nequation list
  
  type impl_system = impl_equation_system*impl_equation_system
  
  type context = var -> s
  
  val object_get : (context, coq_object, s) getable
  
  val eval_equality : (context, equality) evalable
  
  val eval_equation : (context, equation) evalable
  
  val eval_nequation : (context, nequation) evalable
  
  val evalable_sat_equation_system : (context, sat_equation_system) evalable
  
  val ies2ses : impl_equation_system -> sat_equation_system
  
  val evalable_impl_equation_system :
    (context, impl_equation_system) evalable
  
  val evalable_impl_system : (context, impl_system) evalable
 end) ->
 functor (Coq_esf:sig 
  val object_height : Coq_es.coq_object heightable
  
  val equality_h : Coq_es.equality -> int
  
  val equality_h_zero : Coq_es.equality is_height_zero_spec
  
  val equality_height : Coq_es.equality heightable
  
  val equation_h : Coq_es.equation -> int
  
  val equation_h_zero : Coq_es.equation is_height_zero_spec
  
  val equation_height : Coq_es.equation heightable
  
  val nequation_h : Coq_es.nequation -> int
  
  val nequation_h_zero : Coq_es.nequation is_height_zero_spec
  
  val nequation_height : Coq_es.nequation heightable
  
  val ses_h : Coq_es.sat_equation_system -> int
  
  val ses_h_zero :
    Coq_es.sat_equation_system
    is_height_zero_spec
  
  val ses_height :
    Coq_es.sat_equation_system
    heightable
  
  val ies_h :
    Coq_es.impl_equation_system
    ->
    int
  
  val ies_h_zero :
    Coq_es.impl_equation_system
    is_height_zero_spec
  
  val ies_height :
    Coq_es.impl_equation_system
    heightable
  
  val is_h :
    Coq_es.impl_system
    ->
    int
  
  val is_h_zero :
    Coq_es.impl_system
    is_height_zero_spec
  
  val is_height :
    Coq_es.impl_system
    heightable
  
  val var_cheight :
    (Coq_es.context,
    Coq_es.var)
    cheightable
  
  val object_cheight :
    (Coq_es.context,
    Coq_es.coq_object)
    cheightable
  
  val equality_cheight :
    (Coq_es.context,
    Coq_es.equality)
    cheightable
  
  val equation_cheight :
    (Coq_es.context,
    Coq_es.equation)
    cheightable
  
  val nequation_cheight :
    (Coq_es.context,
    Coq_es.nequation)
    cheightable
  
  val ses_cheight :
    (Coq_es.context,
    Coq_es.sat_equation_system)
    cheightable
  
  val ies_cheight :
    (Coq_es.context,
    Coq_es.impl_equation_system)
    cheightable
  
  val is_cheight :
    (Coq_es.context,
    Coq_es.impl_system)
    cheightable
  
  val object_vars :
    (Coq_es.coq_object,
    Coq_es.var)
    varsable
  
  val equality_vars :
    (Coq_es.equality,
    Coq_es.var)
    varsable
  
  val equation_vars :
    (Coq_es.equation,
    Coq_es.var)
    varsable
  
  val nequation_vars :
    (Coq_es.nequation,
    Coq_es.var)
    varsable
  
  val ses_vars :
    (Coq_es.sat_equation_system,
    Coq_es.var)
    varsable
  
  val ies_vars :
    (Coq_es.impl_equation_system,
    Coq_es.var)
    varsable
  
  val is_vars :
    (Coq_es.impl_system,
    Coq_es.var)
    varsable
  
  val vheight :
    Coq_es.var
    ->
    int
  
  val vheight_zero :
    Coq_es.var
    is_height_zero_spec
  
  val height_var :
    Coq_es.var
    heightable
  
  val varsable_var :
    (Coq_es.var,
    Coq_es.var)
    varsable
  
  val replace_ses_nequations :
    Coq_es.sat_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.sat_equation_system
  
  val replace_ies_nequations :
    Coq_es.impl_equation_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_equation_system
  
  val replace_is_nequations :
    Coq_es.impl_system
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.nequation
    list
    ->
    Coq_es.impl_system
 end) ->
 struct 
  type equationS
    =
    (Coq_es.equality,
    Coq_es.equation,
    Coq_es.nequation)
    eqnS
  
  type ('a,
        'b,
        'c,
        'd) eqnS_transform
    =
    'd
    ->
    ('a,
    'b,
    'c)
    eqnS
  
  (** val transformS :
      ('a1,
      'a2,
      'a3,
      'a4)
      eqnS_transform
      ->
      'a4
      ->
      ('a1,
      'a2,
      'a3)
      eqnS **)
  
  let transformS eqnS_transform0 =
    eqnS_transform0
  
  type ('a,
        'b,
        'c) eqnS_transformB =
  | Build_eqnS_transformB
  
  (** val eqnS_transformB_rect :
      'a4
      ->
      'a4 **)
  
  let eqnS_transformB_rect f =
    f
  
  (** val eqnS_transformB_rec :
      'a4
      ->
      'a4 **)
  
  let eqnS_transformB_rec f =
    f
  
  (** val transformSB :
      ('a1,
      'a2,
      'a3)
      eqnS
      ->
      ('a1,
      ('a2,
      'a3)
      sum)
      sum **)
  
  let transformSB = function
  | EL eql ->
    Inl
      eql
  | EQ0 eqn0 ->
    Inr
      (Inl
      eqn0)
  | NEQ neqn ->
    Inr
      (Inr
      neqn)
  
  (** val eqnS_list_transformB :
      ('a1,
      'a2,
      'a3)
      eqnS
      list
      ->
      'a1
      list*('a2
      list*'a3
      list) **)
  
  let eqnS_list_transformB l0 =
    fold_right
      (fun eqn tl' ->
      match transformSB
              eqn with
      | Inl a0 ->
        (a0 :: (fst
                 tl')),(snd
                         tl')
      | Inr s0 ->
        (match s0 with
         | Inl b0 ->
           (fst
             tl'),((b0 :: (fst
                            (snd
                              tl'))),(snd
                                       (snd
                                         tl')))
         | Inr c0 ->
           (fst
             tl'),((fst
                     (snd
                       tl')),(c0 :: (snd
                                      (snd
                                        tl'))))))
      ([],([],[]))
      l0
  
  type ('a,
        'b) list_map =
  | Build_list_map
  
  (** val list_map_rect :
      ('a1
      ->
      'a2)
      ->
      'a3
      ->
      'a3 **)
  
  let list_map_rect f f0 =
    f0
  
  (** val list_map_rec :
      ('a1
      ->
      'a2)
      ->
      'a3
      ->
      'a3 **)
  
  let list_map_rec f f0 =
    f0
  
  (** val lmap :
      ('a1
      ->
      'a2)
      ->
      'a1
      list
      ->
      'a2
      list **)
  
  let lmap f =
    map
      f
  
  type ('a,
        'b,
        'c) preserved_eval
    =
    __
  
  (** val eql2eqnS :
      (Coq_es.equality,
      Coq_es.equation,
      Coq_es.nequation,
      Coq_es.equality)
      eqnS_transform **)
  
  let eql2eqnS eql =
    EL
      eql
  
  (** val eqn2eqnS :
      (Coq_es.equality,
      Coq_es.equation,
      Coq_es.nequation,
      Coq_es.equation)
      eqnS_transform **)
  
  let eqn2eqnS eqn =
    EQ0
      eqn
  
  (** val neqn2eqnS :
      (Coq_es.equality,
      Coq_es.equation,
      Coq_es.nequation,
      Coq_es.nequation)
      eqnS_transform **)
  
  let neqn2eqnS neqn =
    NEQ
      neqn
  
  (** val ses2eqnS :
      Coq_es.sat_equation_system
      ->
      equationS
      list **)
  
  let ses2eqnS ses =
    app
      (lmap
        (transformS
          eql2eqnS)
        (Coq_es.sat_equalities
          ses))
      (app
        (lmap
          (transformS
            eqn2eqnS)
          (Coq_es.sat_equations
            ses))
        (lmap
          (transformS
            neqn2eqnS)
          (Coq_es.sat_nequations
            ses)))
  
  (** val eqnS2ses :
      equationS
      list
      ->
      Coq_es.sat_equation_system **)
  
  let eqnS2ses l0 =
    let l1,p =
      eqnS_list_transformB
        l0
    in
    let l2,l3 =
      p
    in
    { Coq_es.sat_equalities =
    l1;
    Coq_es.sat_equations =
    l2;
    Coq_es.sat_nequations =
    l3 }
  
  module Coq_input1 = Input_of_SV(Coq_sv)
  
  module Coq_ot1 = OrderedType_of_SV(Coq_sv)
  
  module Coq_pi1 = Partition_Input_of_SV_nz(Coq_sv)(Coq_es)(Coq_esf)
  
  module SatP = Partition_SAT(Coq_input1)(Coq_ot1)(Coq_pi1)
  
  (** val ses_partition :
      Coq_es.sat_equation_system
      ->
      Coq_es.sat_equation_system
      list **)
  
  let ses_partition ses =
    map
      eqnS2ses
      (SatP.partition_SAT
        (ses2eqnS
          ses))
  
  type equationI
    =
    ((Coq_es.equality,
    Coq_es.equation,
    Coq_es.nequation)
    eqnS*Coq_es.var
    list)*bool
  
  (** val el_filter :
      'a1
      eqDec0
      ->
      'a1
      list
      ->
      'a1
      list
      ->
      'a1
      list **)
  
  let el_filter h l0 l'0 =
    filter
      (fun a0 ->
      if in_dec
           (eq_dec1
             h)
           a0
           l'0
      then true
      else false)
      l0
  
  (** val eql2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.equality
      ->
      equationI **)
  
  let eql2eqnI l0 b0 eql =
    ((EL
      eql),(el_filter
             Coq_pi1.var_eq_dec
             (vars0
               (vars_transform
                 Coq_esf.equality_vars)
               eql)
             l0)),b0
  
  (** val eqn2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.equation
      ->
      equationI **)
  
  let eqn2eqnI l0 b0 eqn =
    ((EQ0
      eqn),(el_filter
             Coq_pi1.var_eq_dec
             (vars0
               (vars_transform
                 Coq_esf.equation_vars)
               eqn)
             l0)),b0
  
  (** val neqn2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.nequation
      ->
      equationI **)
  
  let neqn2eqnI l0 b0 neqn =
    ((NEQ
      neqn),(el_filter
              Coq_pi1.var_eq_dec
              (vars0
                (vars_transform
                  Coq_esf.nequation_vars)
                neqn)
              l0)),b0
  
  (** val leql2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.equality
      list
      ->
      equationI
      list **)
  
  let leql2eqnI l0 b0 leql =
    map
      (eql2eqnI
        l0
        b0)
      leql
  
  (** val leqn2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.equation
      list
      ->
      equationI
      list **)
  
  let leqn2eqnI l0 b0 leqn =
    map
      (eqn2eqnI
        l0
        b0)
      leqn
  
  (** val lneqn2eqnI :
      Coq_es.var
      list
      ->
      bool
      ->
      Coq_es.nequation
      list
      ->
      equationI
      list **)
  
  let lneqn2eqnI l0 b0 lneqn =
    map
      (neqn2eqnI
        l0
        b0)
      lneqn
  
  (** val ies2eqnI :
      Coq_es.impl_equation_system
      ->
      bool
      ->
      equationI
      list **)
  
  let ies2eqnI ies b0 =
    let { Coq_es.impl_exvars =
      lex;
      Coq_es.impl_equalities =
      leql;
      Coq_es.impl_equations =
      leqn;
      Coq_es.impl_nequations =
      lneqn } =
      ies
    in
    app
      (leql2eqnI
        lex
        b0
        leql)
      (app
        (leqn2eqnI
          lex
          b0
          leqn)
        (lneqn2eqnI
          lex
          b0
          lneqn))
  
  (** val is2eqnI :
      Coq_es.impl_system
      ->
      equationI
      list **)
  
  let is2eqnI = function
  | ies1,ies2 ->
    app
      (ies2eqnI
        ies1
        false)
      (ies2eqnI
        ies2
        true)
  
  type tupleI
    =
    (((Coq_es.var
    list*bool)*Coq_es.equality
    list)*Coq_es.equation
    list)*Coq_es.nequation
    list
  
  (** val eqnI2tupleI :
      equationI
      ->
      tupleI **)
  
  let eqnI2tupleI = function
  | p,b0 ->
    let es,l0 =
      p
    in
    (match es with
     | EL eql ->
       (((l0,b0),(eql :: [])),[]),[]
     | EQ0 eqn ->
       (((l0,b0),[]),(eqn :: [])),[]
     | NEQ neqn ->
       (((l0,b0),[]),[]),(neqn :: []))
  
  (** val leqnI2tupleI :
      equationI
      list
      ->
      tupleI
      list **)
  
  let leqnI2tupleI lei =
    map
      eqnI2tupleI
      lei
  
  (** val emp_tupleI :
      bool
      ->
      tupleI **)
  
  let emp_tupleI b0 =
    ((([],b0),[]),[]),[]
  
  (** val removeDup :
      'a1
      eqDec0
      ->
      'a1
      list
      ->
      'a1
      list **)
  
  let rec removeDup h = function
  | [] ->
    []
  | a0 :: l'0 ->
    if in_dec
         (eq_dec1
           h)
         a0
         l'0
    then removeDup
           h
           l'0
    else a0 :: (removeDup
                 h
                 l'0)
  
  (** val merge_tupleI :
      tupleI
      ->
      tupleI
      ->
      tupleI **)
  
  let merge_tupleI ti ti' =
    let p,lneqn =
      ti
    in
    let p0,leqn =
      p
    in
    let p1,leql =
      p0
    in
    let lex,b0 =
      p1
    in
    let p2,lneqn' =
      ti'
    in
    let p3,leqn' =
      p2
    in
    let p4,leql' =
      p3
    in
    let lex',b' =
      p4
    in
    ((((app
         lex
         lex'),b'),(app
                     leql
                     leql')),(app
                               leqn
                               leqn')),(app
                                         lneqn
                                         lneqn')
  
  (** val merge_list_tupleI :
      tupleI
      list
      ->
      tupleI **)
  
  let merge_list_tupleI l0 =
    fold_right
      merge_tupleI
      (emp_tupleI
        false)
      l0
  
  (** val tuple_simpl :
      tupleI
      ->
      tupleI **)
  
  let tuple_simpl = function
  | p,lneqn ->
    let p0,leqn =
      p
    in
    let p1,leql =
      p0
    in
    let lex,b0 =
      p1
    in
    ((((removeDup
         Coq_pi1.var_eq_dec
         lex),b0),(removeDup
                    (eqDec_transform
                      Coq_es.equality_eq_dec)
                    leql)),(removeDup
                             (eqDec_transform
                               Coq_es.equation_eq_dec)
                             leqn)),(removeDup
                                      (eqDec_transform
                                        Coq_es.nequation_eq_dec)
                                      lneqn)
  
  (** val tupleI2ies :
      tupleI
      ->
      Coq_es.impl_equation_system **)
  
  let tupleI2ies ti =
    let p,lneqn =
      tuple_simpl
        ti
    in
    let p0,leqn =
      p
    in
    let p1,leql =
      p0
    in
    let lex,b0 =
      p1
    in
    { Coq_es.impl_exvars =
    lex;
    Coq_es.impl_equalities =
    leql;
    Coq_es.impl_equations =
    leqn;
    Coq_es.impl_nequations =
    lneqn }
  
  (** val eqnI2ies :
      equationI
      list
      ->
      Coq_es.impl_equation_system **)
  
  let eqnI2ies l0 =
    tupleI2ies
      (merge_list_tupleI
        (leqnI2tupleI
          l0))
  
  (** val eqnI2is :
      (equationI
      list*equationI
      list)
      ->
      Coq_es.impl_system **)
  
  let eqnI2is = function
  | l1,l2 ->
    (eqnI2ies
      l1),(eqnI2ies
            l2)
  
  module Coq_input2 = Input_of_SV_neq_ex(Coq_sv)
  
  module Coq_ot2 = OrderedType_of_SV_neq_ex(Coq_sv)
  
  module Coq_pi2 = Partition_Input_of_SV_neq_ex(Coq_sv)(Coq_es)(Coq_esf)
  
  module ImplP = Partition_IMPL(Coq_input2)(Coq_ot2)(Coq_pi2)
  
  (** val impl_partition :
      Coq_es.impl_system
      ->
      Coq_es.impl_system
      list **)
  
  let impl_partition = function
  | ies1,ies2 ->
    map
      eqnI2is
      (ImplP.partition_IMPL
        (ies2eqnI
          ies1
          false)
        (ies2eqnI
          ies2
          true))
  
  (** val emp_ies :
      Coq_es.impl_equation_system **)
  
  let emp_ies =
    { Coq_es.impl_exvars =
      [];
      Coq_es.impl_equalities =
      [];
      Coq_es.impl_equations =
      [];
      Coq_es.impl_nequations =
      [] }
  
  (** val ies_combine :
      Coq_es.impl_equation_system
      ->
      Coq_es.impl_equation_system
      ->
      Coq_es.impl_equation_system **)
  
  let ies_combine ies ies' =
    let { Coq_es.impl_exvars =
      lex;
      Coq_es.impl_equalities =
      leql;
      Coq_es.impl_equations =
      leqn;
      Coq_es.impl_nequations =
      lneqn } =
      ies
    in
    let { Coq_es.impl_exvars =
      lex';
      Coq_es.impl_equalities =
      leql';
      Coq_es.impl_equations =
      leqn';
      Coq_es.impl_nequations =
      lneqn' } =
      ies'
    in
    { Coq_es.impl_exvars =
    (app
      lex
      lex');
    Coq_es.impl_equalities =
    (app
      leql
      leql');
    Coq_es.impl_equations =
    (app
      leqn
      leqn');
    Coq_es.impl_nequations =
    (app
      lneqn
      lneqn') }
  
  (** val ies_aggregation :
      Coq_es.impl_equation_system
      list
      ->
      Coq_es.impl_equation_system **)
  
  let ies_aggregation l0 =
    fold_right
      ies_combine
      emp_ies
      l0
  
  (** val tupleI_varsable :
      (tupleI,
      Coq_es.var)
      varsable0 **)
  
  let tupleI_varsable = function
  | p,x0 ->
    let p0,x1 =
      p
    in
    let p1,x2 =
      p0
    in
    let l0,b0 =
      p1
    in
    app
      l0
      (app
        (vars0
          (vars_transform
            (varsable_list
              Coq_esf.equality_vars))
          x2)
        (app
          (vars0
            (vars_transform
              (varsable_list
                Coq_esf.equation_vars))
            x1)
          (vars0
            (vars_transform
              (varsable_list
                Coq_esf.nequation_vars))
            x0)))
  
  (** val tuple_vars :
      (tupleI,
      Coq_es.var)
      varsable0 **)
  
  let tuple_vars =
    tupleI_varsable
  
  (** val exclude :
      'a1
      eqDec0
      ->
      'a1
      list
      ->
      'a1
      list
      ->
      'a1
      list **)
  
  let rec exclude eqd l0 lex =
    match l0 with
    | [] ->
      []
    | a0 :: l'0 ->
      if in_dec
           eqd
           a0
           lex
      then exclude
             eqd
             l'0
             lex
      else a0 :: (exclude
                   eqd
                   l'0
                   lex)
 end

module Solver_with_partition = 
 functor (Coq_sv:SV) ->
 functor (Coq_es:sig 
  module Coq_dom : 
   sig 
    type e
      =
      share
    
    val e_eq_dec :
      e
      eqDec
    
    val e_height :
      e
      heightable
    
    val bot :
      Coq_Share.t
   end
  
  type var
    =
    Coq_sv.t
  
  type s
    =
    Coq_dom.e
  
  val var_eq_dec :
    var
    eqDec
  
  type coq_object
    =
    (var,
    s)
    objectT
  
  type equality
    =
    coq_object*coq_object
  
  val equality_eq_dec :
    equality
    eqDec
  
  type equation
    =
    (coq_object*coq_object)*coq_object
  
  val equation_eq_dec :
    equation
    eqDec
  
  type nequation
    =
    equation*unit
  
  val nequation_eq_dec :
    nequation
    eqDec
  
  type sat_equation_system = { sat_equalities : equality
                                                list;
                               sat_equations : equation
                                               list;
                               sat_nequations : nequation
                                                list }
  
  val sat_equation_system_rect :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equation_system_rec :
    (equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    sat_equation_system
    ->
    'a1
  
  val sat_equalities :
    sat_equation_system
    ->
    equality
    list
  
  val sat_equations :
    sat_equation_system
    ->
    equation
    list
  
  val sat_nequations :
    sat_equation_system
    ->
    nequation
    list
  
  type impl_equation_system = { impl_exvars : var
                                              list;
                                impl_equalities : equality
                                                  list;
                                impl_equations : equation
                                                 list;
                                impl_nequations : nequation
                                                  list }
  
  val impl_equation_system_rect :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_equation_system_rec :
    (var
    list
    ->
    equality
    list
    ->
    equation
    list
    ->
    nequation
    list
    ->
    'a1)
    ->
    impl_equation_system
    ->
    'a1
  
  val impl_exvars :
    impl_equation_system
    ->
    var
    list
  
  val impl_equalities :
    impl_equation_system
    ->
    equality
    list
  
  val impl_equations :
    impl_equation_system
    ->
    equation
    list
  
  val impl_nequations :
    impl_equation_system
    ->
    nequation
    list
  
  type impl_system
    =
    impl_equation_system*impl_equation_system
  
  type context
    =
    var
    ->
    s
  
  val object_get :
    (context,
    coq_object,
    s)
    getable
  
  val eval_equality :
    (context,
    equality)
    evalable
  
  val eval_equation :
    (context,
    equation)
    evalable
  
  val eval_nequation :
    (context,
    nequation)
    evalable
  
  val evalable_sat_equation_system :
    (context,
    sat_equation_system)
    evalable
  
  val ies2ses :
    impl_equation_system
    ->
    sat_equation_system
  
  val evalable_impl_equation_system :
    (context,
    impl_equation_system)
    evalable
  
  val evalable_impl_system :
    (context,
    impl_system)
    evalable
 end) ->
 functor (Coq_bf:sig 
  type var
    =
    Coq_sv.t
  
  type context
    =
    var
    ->
    bool
  
  type bF =
  | Coq_valF of bool
  | Coq_varF of var
  | Coq_andF of bF
     * bF
  | Coq_orF of bF
     * bF
  | Coq_implF of bF
     * bF
  | Coq_negF of bF
  | Coq_exF of var
     * bF
  | Coq_allF of var
     * bF
  
  val bF_rect :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_rec :
    (bool
    ->
    'a1)
    ->
    (var
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    (var
    ->
    bF
    ->
    'a1
    ->
    'a1)
    ->
    bF
    ->
    'a1
  
  val bF_vars :
    bF
    ->
    var
    list
  
  val bF_varsable :
    (bF,
    var)
    varsable
  
  val beval :
    context
    ->
    bF
    ->
    bool
  
  val bF_eval :
    (context,
    bF)
    evalable
  
  val bsize :
    bF
    ->
    int
  
  val bsubst :
    bF
    ->
    var
    ->
    bool
    ->
    bF
  
  val bF_eq_dec :
    bF
    eqDec
 end) ->
 functor (Coq_bsf:sig 
  val bsolver :
    Coq_bf.bF
    ->
    bool
    option
 end) ->
 struct 
  module Coq_basic_solver = Solver(Coq_sv)(Coq_es)(Coq_bf)(Coq_bsf)
  
  module Coq_esf = System_Features(Coq_sv)(Coq_es)
  
  module Coq_partition_fun = System_Partition(Coq_sv)(Coq_es)(Coq_esf)
  
  (** val coq_SATsolver :
      Coq_es.sat_equation_system
      ->
      bool **)
  
  let coq_SATsolver ses =
    Coq_basic_solver.eval_conjunct
      Coq_basic_solver.coq_SATsolver
      (Coq_partition_fun.ses_partition
        ses)
  
  (** val coq_IMPLsolver :
      Coq_es.impl_system
      ->
      bool **)
  
  let coq_IMPLsolver is =
    if coq_SATsolver
         (Coq_es.ies2ses
           (fst
             is))
    then Coq_basic_solver.eval_conjunct
           Coq_basic_solver.coq_IMPLsolver
           (Coq_partition_fun.impl_partition
             is)
    else true
 end


