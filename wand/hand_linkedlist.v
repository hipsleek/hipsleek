Require Import ZArith.

Module Type Mlinkedlist.
  Parameter formula : Type.
  Parameter L : Type.
  Parameter node : Type.
  Parameter null : node.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter ptto : node -> Z -> node -> formula.
  Parameter eq : node -> node -> formula.
  Parameter lookup : L -> node -> Z -> node -> formula.
  Parameter update : L -> node -> Z -> node -> L -> formula.
  Parameter reverse : L -> L -> formula.
  Parameter append : L -> L -> L -> formula.
  Parameter isempty : L -> formula.
  Parameter ll : node -> L -> formula.
  Parameter valid : formula -> Prop.
  Axiom axiom1 : forall x v p l, valid (imp (and (eq x null) (lookup l x v p))  (isempty l)).
  Axiom axiom2 : forall l l1, valid (imp (isempty l1) (append l l1 l)).
  Axiom axiom3 : forall l, valid (imp (isempty l) (reverse l l)).
  Axiom axiom4 : forall l x v p l1 p1, valid (imp (and (lookup l x v p) (update l x v p1 l1)) (lookup l1 x v p1)).
End Mlinkedlist.
