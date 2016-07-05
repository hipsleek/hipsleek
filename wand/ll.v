Require Import ZArith.

Module Type Mll.
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
  Parameter cons : A -> Z -> A -> formula.
  Axiom axiom_1 : forall Lt Tr L v, exists Le Lv Lr, valid (imp (and (cons L v Lt) (reverse Tr Lt)) (and (and (and (append Lr Tr Lv) (reverse Lr L)) (cons Lv v Le)) (isempty Le))).
  Axiom axiom_2 : forall L, valid (imp (isempty L) (reverse L L)).
  Axiom axiom_3 : forall L L1, valid (imp (isempty L) (append L1 L L1)).
  Axiom axiom_4 : forall v Lp L, valid (imp (cons L v Lp) (not (isempty L))).
End Mll.

