type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
  | true -> false
  | false -> true

type nat =
  | O
  | S of nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

type 't sepalgfacts = { saf_assoc : ('t -> 't -> 't -> 't -> 't -> __ -> __
                                    -> 't * __);
                        saf_exist_units : ('t -> 't * __) }

(** val saf_assoc :
    'a1 sepalgfacts -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 * __ **)

let saf_assoc s a b c d e =
  s.saf_assoc a b c d e __ __

(** val saf_exist_units : 'a1 sepalgfacts -> 'a1 -> 'a1 * __ **)

let saf_exist_units x = x.saf_exist_units

type 't sepalg =
  't sepalgfacts
  (* singleton inductive, whose constructor was SepAlg *)

module type BOOLEAN_ALGEBRA = 
 sig 
  type t 
  
  val top : t
  
  val bot : t
  
  val lub : t -> t -> t
  
  val glb : t -> t -> t
  
  val comp : t -> t
 end

module type SHARE_MODEL = 
 sig 
  type t 
  
  val top : t
  
  val bot : t
  
  val lub : t -> t -> t
  
  val glb : t -> t -> t
  
  val comp : t -> t
  
  val saf : t sepalgfacts
  
  val sa : t sepalg
  
  val eq_dec : t -> t -> bool
  
  val split : t -> t * t
  
  val create_token : nat -> t -> t * t
  
  val split_token : nat -> t -> t * t
  
  val rel : t -> t -> t
 end

module BA_Facts = 
 functor (BA:BOOLEAN_ALGEBRA) ->
 struct 
  type t = BA.t
  
  (** val top : t **)
  
  let top =
    BA.top
  
  (** val bot : t **)
  
  let bot =
    BA.bot
  
  (** val lub : t -> t -> t **)
  
  let lub x x0 =
    BA.lub x x0
  
  (** val glb : t -> t -> t **)
  
  let glb x x0 =
    BA.glb x x0
  
  (** val comp : t -> t **)
  
  let comp x =
    BA.comp x
  
  (** val saf : t sepalgfacts **)
  
  let saf =
    { saf_assoc = (fun a b c d e _ _ -> (lub b c) , __); saf_exist_units =
      (fun x -> bot , __) }
  
  (** val sa : t sepalg **)
  
  let sa =
    saf
 end

module Share = 
 struct 
  type coq_ShareTree =
    | Leaf of bool
    | Node of coq_ShareTree * coq_ShareTree
  
  (** val coq_ShareTree_rect :
      (bool -> 'a1) -> (coq_ShareTree -> 'a1 -> coq_ShareTree -> 'a1 -> 'a1)
      -> coq_ShareTree -> 'a1 **)
  
  let rec coq_ShareTree_rect f f0 = function
    | Leaf b -> f b
    | Node (s0, s1) ->
        f0 s0 (coq_ShareTree_rect f f0 s0) s1 (coq_ShareTree_rect f f0 s1)
  
  (** val coq_ShareTree_rec :
      (bool -> 'a1) -> (coq_ShareTree -> 'a1 -> coq_ShareTree -> 'a1 -> 'a1)
      -> coq_ShareTree -> 'a1 **)
  
  let rec coq_ShareTree_rec f f0 = function
    | Leaf b -> f b
    | Node (s0, s1) ->
        f0 s0 (coq_ShareTree_rec f f0 s0) s1 (coq_ShareTree_rec f f0 s1)
  
  (** val union_tree : coq_ShareTree -> coq_ShareTree -> coq_ShareTree **)
  
  let rec union_tree x y =
    match x with
      | Leaf b -> if b then Leaf true else y
      | Node (l1, r1) ->
          (match y with
             | Leaf b -> if b then Leaf true else x
             | Node (l2, r2) -> Node ((union_tree l1 l2), (union_tree r1 r2)))
  
  (** val intersect_tree :
      coq_ShareTree -> coq_ShareTree -> coq_ShareTree **)
  
  let rec intersect_tree x y =
    match x with
      | Leaf b -> if b then y else Leaf false
      | Node (l1, r1) ->
          (match y with
             | Leaf b -> if b then x else Leaf false
             | Node (l2, r2) -> Node ((intersect_tree l1 l2),
                 (intersect_tree r1 r2)))
  
  (** val comp_tree : coq_ShareTree -> coq_ShareTree **)
  
  let rec comp_tree = function
    | Leaf b -> Leaf (negb b)
    | Node (l, r) -> Node ((comp_tree l), (comp_tree r))
  
  (** val mkCanon : coq_ShareTree -> coq_ShareTree **)
  
  let rec mkCanon = function
    | Leaf b -> Leaf b
    | Node (l, r) ->
        let l' = mkCanon l in
        let r' = mkCanon r in
        (match l' with
           | Leaf b1 ->
               (match r' with
                  | Leaf b2 ->
                      if bool_dec b1 b2 then Leaf b1 else Node (l', r')
                  | Node (s, s0) -> Node (l', r'))
           | Node (s, s0) -> Node (l', r'))
  
  (** val relativ_tree : coq_ShareTree -> coq_ShareTree -> coq_ShareTree **)
  
  let rec relativ_tree z a =
    match z with
      | Leaf b -> if b then a else Leaf false
      | Node (l, r) -> Node ((relativ_tree l a), (relativ_tree r a))
  
  (** val nonEmpty_dec : coq_ShareTree -> bool **)
  
  let rec nonEmpty_dec = function
    | Leaf b -> if b then true else false
    | Node (s0, s1) -> if nonEmpty_dec s0 then true else nonEmpty_dec s1
  
  (** val nonFull_dec : coq_ShareTree -> bool **)
  
  let rec nonFull_dec = function
    | Leaf b -> if b then false else true
    | Node (s0, s1) -> if nonFull_dec s0 then true else nonFull_dec s1
  
  type ctx =
    | NodeB of ctx * ctx
    | NodeR of coq_ShareTree * ctx
    | NodeL of ctx * coq_ShareTree
    | Hole
  
  (** val ctx_rect :
      (ctx -> 'a1 -> ctx -> 'a1 -> 'a1) -> (coq_ShareTree -> ctx -> 'a1 ->
      'a1) -> (ctx -> 'a1 -> coq_ShareTree -> 'a1) -> 'a1 -> ctx -> 'a1 **)
  
  let rec ctx_rect f f0 f1 f2 = function
    | NodeB (c0, c1) ->
        f c0 (ctx_rect f f0 f1 f2 c0) c1 (ctx_rect f f0 f1 f2 c1)
    | NodeR (s, c0) -> f0 s c0 (ctx_rect f f0 f1 f2 c0)
    | NodeL (c0, s) -> f1 c0 (ctx_rect f f0 f1 f2 c0) s
    | Hole -> f2
  
  (** val ctx_rec :
      (ctx -> 'a1 -> ctx -> 'a1 -> 'a1) -> (coq_ShareTree -> ctx -> 'a1 ->
      'a1) -> (ctx -> 'a1 -> coq_ShareTree -> 'a1) -> 'a1 -> ctx -> 'a1 **)
  
  let rec ctx_rec f f0 f1 f2 = function
    | NodeB (c0, c1) ->
        f c0 (ctx_rec f f0 f1 f2 c0) c1 (ctx_rec f f0 f1 f2 c1)
    | NodeR (s, c0) -> f0 s c0 (ctx_rec f f0 f1 f2 c0)
    | NodeL (c0, s) -> f1 c0 (ctx_rec f f0 f1 f2 c0) s
    | Hole -> f2
  
  (** val ctx_app : ctx -> ctx -> ctx **)
  
  let rec ctx_app c1 c2 =
    match c1 with
      | NodeB (l, r) -> NodeB ((ctx_app l c2), (ctx_app r c2))
      | NodeR (l, r) -> NodeR (l, (ctx_app r c2))
      | NodeL (l, r) -> NodeL ((ctx_app l c2), r)
      | Hole -> c2
  
  (** val fill : ctx -> coq_ShareTree -> coq_ShareTree **)
  
  let rec fill c x =
    match c with
      | NodeB (l, r) -> Node ((fill l x), (fill r x))
      | NodeR (l, r) -> Node (l, (fill r x))
      | NodeL (l, r) -> Node ((fill l x), r)
      | Hole -> x
  
  (** val to_ctx : coq_ShareTree -> ctx **)
  
  let rec to_ctx = function
    | Leaf b -> if b then Hole else assert false (* absurd case *)
    | Node (l, r) ->
        if nonEmpty_dec l
        then if nonEmpty_dec r
             then NodeB ((to_ctx l), (to_ctx r))
             else NodeL ((to_ctx l), r)
        else if nonEmpty_dec r
             then NodeR (l, (to_ctx r))
             else assert false (* absurd case *)
  
  type canonTree = coq_ShareTree
  
  (** val shareTree_dec_eq : coq_ShareTree -> coq_ShareTree -> bool **)
  
  let rec shareTree_dec_eq s y0 =
    match s with
      | Leaf b ->
          (match y0 with
             | Leaf b0 -> bool_dec b b0
             | Node (s0, s1) -> false)
      | Node (s0, s1) ->
          (match y0 with
             | Leaf b -> false
             | Node (s2, s3) ->
                 if shareTree_dec_eq s0 s2
                 then shareTree_dec_eq s1 s3
                 else false)
  
  (** val canonTree_eq_dec : canonTree -> canonTree -> bool **)
  
  let canonTree_eq_dec x y =
    shareTree_dec_eq x y
  
  module BA = 
   struct 
    type t = canonTree
    
    (** val lub : canonTree -> canonTree -> canonTree **)
    
    let lub x y =
      mkCanon (union_tree x y)
    
    (** val glb : canonTree -> canonTree -> canonTree **)
    
    let glb x y =
      mkCanon (intersect_tree x y)
    
    (** val top : canonTree **)
    
    let top =
      Leaf true
    
    (** val bot : canonTree **)
    
    let bot =
      Leaf false
    
    (** val comp : canonTree -> canonTree **)
    
    let comp x =
      comp_tree x
   end
  
  module BAF = BA_Facts(BA)
  
  type t = BA.t
  
  (** val top : t **)
  
  let top =
    BA.top
  
  (** val bot : t **)
  
  let bot =
    BA.bot
  
  (** val lub : t -> t -> t **)
  
  let lub x x0 =
    BA.lub x x0
  
  (** val glb : t -> t -> t **)
  
  let glb x x0 =
    BA.glb x x0
  
  (** val comp : t -> t **)
  
  let comp x =
    BA.comp x
  
  (** val saf : t sepalgfacts **)
  
  let saf =
    BAF.saf
  
  (** val sa : t sepalg **)
  
  let sa =
    saf
  
  (** val rel : t -> t -> t **)
  
  let rel a x = match x with
    | Leaf b -> if b then a else Leaf false
    | Node (s, s0) -> relativ_tree a x
  
  (** val rel_classification : t -> t -> bool **)
  
  let rel_classification a = function
    | Leaf b -> if b then false else true
    | Node (x1, x2) -> false
  
  (** val leftTree : canonTree **)
  
  let leftTree =
    Node ((Leaf true), (Leaf false))
  
  (** val rightTree : canonTree **)
  
  let rightTree =
    Node ((Leaf false), (Leaf true))
  
  (** val split : canonTree -> t * t **)
  
  let split x =
    (match leftTree with
       | Leaf b -> if b then x else Leaf false
       | Node (s, s0) -> relativ_tree x leftTree) ,
      (match rightTree with
         | Leaf b -> if b then x else Leaf false
         | Node (s, s0) -> relativ_tree x rightTree)
  
  (** val split_tok1 : nat -> coq_ShareTree -> coq_ShareTree **)
  
  let rec split_tok1 n = function
    | Leaf b -> Leaf false
    | Node (s, t2) ->
        (match s with
           | Leaf b ->
               if b
               then (match n with
                       | O -> Node ((Leaf true), (Leaf false))
                       | S n' -> Node ((Leaf true), (split_tok1 n' t2)))
               else Node ((Leaf false), (split_tok1 n t2))
           | Node (s0, s1) -> Leaf false)
  
  (** val split_tok2 : nat -> coq_ShareTree -> coq_ShareTree **)
  
  let rec split_tok2 n x = match x with
    | Leaf b -> x
    | Node (s, t2) ->
        (match s with
           | Leaf b ->
               if b
               then (match n with
                       | O -> Node ((Leaf false), t2)
                       | S n' -> Node ((Leaf false), (split_tok2 n' t2)))
               else Node ((Leaf false), (split_tok2 n t2))
           | Node (s0, s1) -> x)
  
  (** val split_token : nat -> t -> t * t **)
  
  let split_token n tok =
    match n with
      | O -> bot , tok
      | S n' -> (mkCanon (split_tok1 n' tok)) , (mkCanon (split_tok2 n' tok))
  
  (** val new_fac : nat -> coq_ShareTree **)
  
  let rec new_fac = function
    | O -> Node ((Leaf false), (Leaf true))
    | S n' -> Node ((Leaf false), (new_fac n'))
  
  (** val create_tok1 : nat -> coq_ShareTree -> coq_ShareTree **)
  
  let rec create_tok1 n x = match x with
    | Leaf b -> if b then new_fac n else x
    | Node (s, t2) ->
        (match s with
           | Leaf b ->
               if b
               then (match n with
                       | O -> Node ((Leaf false), t2)
                       | S n' -> Node ((Leaf false), (create_tok1 n' t2)))
               else Node ((Leaf false), (create_tok1 n t2))
           | Node (s0, s1) -> x)
  
  (** val create_tok2 : nat -> coq_ShareTree -> coq_ShareTree **)
  
  let rec create_tok2 n = function
    | Leaf b -> if b then comp_tree (new_fac n) else Leaf false
    | Node (s, t2) ->
        (match s with
           | Leaf b ->
               if b
               then (match n with
                       | O -> Node ((Leaf true), (Leaf false))
                       | S n' -> Node ((Leaf true), (create_tok2 n' t2)))
               else Node ((Leaf false), (create_tok2 n t2))
           | Node (s0, s1) -> Leaf false)
  
  (** val create_token : nat -> t -> t * t **)
  
  let create_token n fac =
    match n with
      | O -> fac , bot
      | S n' -> (mkCanon (create_tok1 n' fac)) ,
          (mkCanon (create_tok2 n' fac))
  
  (** val eq_dec : canonTree -> canonTree -> bool **)
  
  let eq_dec x y =
    canonTree_eq_dec x y
 end

