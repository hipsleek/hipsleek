Require Import ZArith.

Module Type Mdagmark.
  Parameter node : Type.
  Parameter sep : Prop -> Prop -> Prop.
  Parameter union : Prop -> Prop -> Prop.
  Parameter mwand : Prop -> Prop -> Prop.
  Parameter node_ptto : node -> Z -> node -> node.
  Parameter null : node.
  Parameter D : Type.
  Parameter lookup : D -> node -> Z -> node -> node -> Prop.
  Parameter update : D -> node -> Z -> node -> node -> D -> Prop.
  Parameter subset_reach : D -> node -> D -> Prop.
  Parameter eq_notreach : D -> node -> D -> Prop.
  Parameter mark : D -> node -> D -> Prop.
  Parameter dag : node -> D -> Prop. 
  Axiom rlemma1 : forall x y d d1, (sep (dag x d1) (mwand (dag x d) (union (dag x d) (dag y d)))) /\ (subset_reach d x d1) /\ (eq_notreach d x d1) -> (union (dag x d1) (dag y d1)).
  Axiom axiom1 : forall d, True -> (mark d null d).
  Axiom axiom2 : forall d x l r, (lookup d x 1 l r) -> (mark d x d).
  Axiom axiom3 : forall d x v l r d1 d2 d3, (lookup d x v l r) /\ (update d x 1 l r d1) /\ v <> 1%Z /\ (mark d1 l d2) /\ (mark d2 r d3) -> (mark d x d3) /\ (lookup d3 x 1 l r).
End Mdagmark.
