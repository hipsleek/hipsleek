Require Import ZArith.

Module Type Mlinkedlist.
  Parameter node : Type.
  Parameter sep : Prop -> Prop -> Prop.
  Parameter node_ptto : node -> Z -> node.
  Parameter null : node.
  Parameter L : Type.
  Parameter lookup : L -> node -> Z -> node -> Prop.
  Parameter update : L -> node -> Z -> node -> L -> Prop.
  Parameter reverse : L -> L -> Prop.
  Parameter append : L -> L -> L -> Prop.
  Parameter isempty : L -> Prop.
  Parameter ll : node -> L -> Prop.
  Axiom axiom1 : forall x v p l, x=null -> (lookup l x v p) /\ (isempty l).
  Axiom axiom2 : forall l l1, (isempty l1) -> (append l l1 l).
  Axiom axiom3 : forall l, (isempty l) -> (reverse l l).
  Axiom axiom4 : forall l x v p l1 p1, (lookup l x v p) /\ (update l x v p1 l1) -> (lookup l1 x v p1).
End Mlinkedlist.
