Require Import ZArith.

Module Type Mlinkedlist.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter node : Type.
  Parameter null_node : node.
  Parameter ptto_node : node -> Z -> node -> formula.
  Parameter A : Type.
  Parameter ll : node -> A -> formula.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter isempty : A -> formula.
  Parameter append : A -> A -> A -> formula.
  Parameter reverse : A -> A -> formula.
  Parameter update : A -> node -> Z -> node -> A -> formula.
  Parameter lookup : A -> node -> Z -> node -> formula.
  Axiom axiom_1 : forall p L L1 x v p1, valid (imp (and (lookup L x v p) (update L x v p1 L1)) (lookup L1 x v p1)).
  Axiom axiom_2 : forall L, valid (imp (isempty L) (reverse L L)).
  Axiom axiom_3 : forall L L1, valid (imp (isempty L) (append L1 L L1)).
  Axiom axiom_4 : forall x v p L, valid (imp (and (eq x null_node) (lookup L x v p)) (isempty L)).
End Mlinkedlist.

