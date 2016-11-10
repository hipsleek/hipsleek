Module Type Mspanningtree.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter node : Type.
  Parameter null_node : node.
  Parameter ptto_node : node -> nat -> node -> node -> formula.
  Parameter A : Type.
  Parameter graph : node -> A -> formula.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter or : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter ext : (nat -> formula) -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neq : nat -> nat -> formula.
  Parameter cut : A -> node -> nat -> A -> formula.
  Parameter span : A -> node -> A -> formula.
  Parameter lookup : A -> node -> nat -> node -> node -> formula.
  Parameter update : A -> node -> nat -> A -> formula.
  Axiom axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 G1) (and (neq v 1) (and (or (span G1 l G2) (cut G1 x 0 G2)) (or (span G2 r G3) (cut G2 x 1 G3)))))) (and (span G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_2 : forall G, valid (span G null_node G).
  Axiom axiom_3 : forall G x, valid (imp (ext (fun Anon_13 =>  (ext (fun Anon_14 => (lookup G x 0 Anon_13 Anon_14))))) (neq x null_node)).
  Axiom lem_graph_gen_left_null : forall r l l2 r2 G1 x G2, valid (imp (and (star (ptto_node x flted_17_1346 flted_17_1345 r) (mwand (ptto_node x flted_17_1342 l r) (union (ptto_node x flted_17_1344 l r) (union (graph r G1) (union (ptto_node l flted_18_1343 l2 r2) (union (graph l2 G1) (graph r2 G1))))))) (and (and (and (and (and (eq flted_17_1346 1) (eq flted_17_1345 null_node)) (eq flted_17_1344 1)) (eq flted_18_1343 1)) (eq flted_17_1342 1)) (lookup G1 l 1 l2 r2))) (union (ptto_node x flted_20_1355 flted_20_1354 r) (graph r G2))).
  Axiom lem_graph_gen_right_null : forall l r l2 r2 G1 x G2, valid (imp (and (star (ptto_node x flted_22_1240 l flted_22_1239) (mwand (ptto_node x flted_22_1236 l r) (union (ptto_node x flted_22_1238 l r) (union (graph l G1) (union (ptto_node r flted_23_1237 l2 r2) (union (graph l2 G1) (graph r2 G1))))))) (and (and (and (and (and (eq flted_22_1240 1) (eq flted_22_1239 null_node)) (eq flted_22_1238 1)) (eq flted_23_1237 1)) (eq flted_22_1236 1)) (lookup G1 r 1 l2 r2))) (union (ptto_node x flted_25_1249 l flted_25_1248) (graph l G2))).
  Axiom lem_pttoupdate : forall v l r G x v1 G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_l : forall x r l2 r2 G1 l G2, valid (imp (and (star (graph l G2) (mwand (graph l G1) (union (ptto_node x flted_31_1092 l r) (union (graph l G1) (graph r G1))))) (and (eq flted_31_1092 1) (lookup G1 l 0 l2 r2))) (union (ptto_node x flted_32_1096 l r) (union (graph l G2) (graph r G2)))).
  Axiom lem_subgraphupdate_r : forall x l l2 r2 G1 r G2, valid (imp (and (star (graph r G2) (mwand (graph r G1) (union (ptto_node x flted_35_1030 l r) (union (graph l G1) (graph r G1))))) (and (eq flted_35_1030 1) (lookup G1 r 0 l2 r2))) (union (ptto_node x flted_36_1034 l r) (union (graph l G2) (graph r G2)))).
End Mspanningtree.

