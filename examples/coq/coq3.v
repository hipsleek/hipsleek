Require Import Classical.

(* Useful tactics include:
  destruct
  exists
  intro / intros
  spec
  split
  apply
  left
  right
  assert
  contradiction
  inversion
  induction
  congruence
  subst
  rewrite
  trivial
  auto
  all of the tactics from hw1
  (and many others)
  
  Most of these are explained in the Coq documentation located at
  http://coq.inria.fr/
  
  You should also feel free to ask your Prof when you get stuck.
*)

Module PredicateLogic.
Parameter term : Type.

Parameter S : Prop.
Parameter P : term -> Prop.
Parameter Q : term -> Prop.

Lemma lem1 :
  (exists t, (S -> Q t)) -> (S -> exists t, Q t).
Proof.
intros.
destruct H.
exists x.
apply H.
trivial.
Qed.

Lemma lem2 :
  (exists x, (P x) /\ (Q x)) -> (exists x, P x) /\ (exists x, Q x).
Proof.
intro H.
destruct H.
destruct H.
split;exists x; assumption.
Qed.

(* The deMorgan rules are standard rules of first-order logic. *)
Lemma deMorgan_a :
  (forall t, P t) -> (~ exists t, ~P t).
Proof.
intro H.
intro.
destruct H0.
contradict H0.
apply H.
Qed.

Lemma deMorgan_b :
  (~ exists t, ~P t) -> (forall t, P t).
Proof.
intro.
intro.
apply NNPP.
contradict H.
exists t.
assumption.
Qed.

Lemma deMorgan2_a : 
  (exists t, P t) -> (~forall t, ~ P t).
Proof.
intro H.
destruct H.
intro.
contradict H.
apply H0.
Qed.


Lemma deMorgan2_b : 
  (~forall t, ~ P t) -> (exists t, P t).
Proof.
intro H.
apply NNPP.
contradict H.
intro.
contradict H.
exists t;assumption.
Qed.


Lemma lem5:
  (forall t, P t = ~ Q t) ->
  (forall t, P t) \/ (exists t, Q t).
Proof.
admit
Qed.

End PredicateLogic.