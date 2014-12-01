Require Import ZArith.

Module Type Mhip.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter node : Type.
  Parameter null_node : node.
  Parameter ptto_node : node -> Z -> node -> node -> formula.
  Parameter A : Type.
  Parameter dag : node -> A -> formula.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neq : Z -> Z -> formula.
  Parameter mark : A -> node -> A -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Parameter lookup : A -> node -> Z -> node -> node -> formula.
  Parameter update : A -> node -> Z -> node -> node -> A -> formula.

End Mhip.
