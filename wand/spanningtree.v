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
  Parameter imp : formula -> formula -> formula.
  Parameter ext : (nat -> formula) -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neq : nat -> nat -> formula.
  Parameter cut : A -> node -> nat -> A -> formula.
  Parameter span : A -> node -> A -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Parameter lookup : A -> node -> nat -> node -> node -> formula.
  Parameter update : A -> node -> nat -> A -> formula.
  Axiom axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 G1) (and (neq v 1) (and  )))) (and (span G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_2 : forall v G x G1 y l r, valid (imp (and (span G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (ext (fun Anon_20 => (lookup G1 y Anon_20 l r)))))).
  Axiom axiom_3 : forall x G, valid (imp (ext (fun Anon_17 =>  (ext (fun Anon_18 => (lookup G x 1 Anon_17 Anon_18))))) (span G x G)).
  Axiom axiom_4 : forall G, valid (span G null_node G).
  Axiom axiom_5 : forall G x, valid (imp (ext (fun Anon_13 =>  (ext (fun Anon_14 => (lookup G x 0 Anon_13 Anon_14))))) (neq x null_node)).
  Axiom lem_graph_gen_left_null : forall r l l2 r2 G1 x G2, valid (imp (and (star (ptto_node x flted_20_1361 flted_20_1360 r) (mwand (ptto_node x flted_20_1357 l r) (union (ptto_node x flted_20_1359 l r) (union (graph r G1) (union (ptto_node l flted_21_1358 l2 r2) (union (graph l2 G1) (graph r2 G1))))))) (and (and (and (and (and (eq flted_20_1361 1) (eq flted_20_1360 null_node)) (eq flted_20_1359 1)) (eq flted_21_1358 1)) (eq flted_20_1357 1)) (lookup G1 l 1 l2 r2))) (union (ptto_node x flted_23_1370 flted_23_1369 r) (graph r G2))).
  Axiom lem_graph_gen_right_null : forall l r l2 r2 G1 x G2, valid (imp (and (star (ptto_node x flted_25_1255 l flted_25_1254) (mwand (ptto_node x flted_25_1251 l r) (union (ptto_node x flted_25_1253 l r) (union (graph l G1) (union (ptto_node r flted_26_1252 l2 r2) (union (graph l2 G1) (graph r2 G1))))))) (and (and (and (and (and (eq flted_25_1255 1) (eq flted_25_1254 null_node)) (eq flted_25_1253 1)) (eq flted_26_1252 1)) (eq flted_25_1251 1)) (lookup G1 r 1 l2 r2))) (union (ptto_node x flted_28_1264 l flted_28_1263) (graph l G2))).
  Axiom lem_pttoupdate : forall v l r G x v1 G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
End Mspanningtree.

