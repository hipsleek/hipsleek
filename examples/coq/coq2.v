
Require Import Classical.

Parameter A B C P Q R : Prop.

(* examples in propositional logic *)

Lemma lem1:
  A /\ B -> A \/ B.
Proof.
intro H.
destruct H.
left.
assumption.
Qed.

Lemma lem2:
  (P -> R) -> 
  (Q -> R) -> 
  (P \/ Q) -> R.
Proof.
intros H H0 H1.
destruct H1;[apply H;assumption | apply H0;assumption].
(*apply H.
assumption.
apply H0.
assumption.*)
Qed.

Lemma lem3:
  (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
intro H.
destruct H.
destruct H.
left.
assumption.
right.
left.
assumption.
right.
right.
assumption.
Qed.

Lemma lem4:
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
intro H.
destruct H.
destruct H.
split.
assumption.
split;assumption.
Qed.


Lemma lem4_5:
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
intro H.
destruct H.
destruct H0.
left.
split;assumption.
right.
split;assumption.
Qed.


Lemma lem5a:
  (~P /\ ~Q) -> (~ (P \/ Q)).
Proof.
intro H.
destruct H.
contradict H.
destruct H.
assumption.
contradict H0.
assumption.
Qed.

Lemma lem5b:
  (~ (P \/ Q)) -> (~P /\ ~Q).
Proof.
intro H.
split.
contradict H.
left; assumption.
contradict H.
right; assumption.
Qed.

Lemma lem6:
  ~B /\ (A -> B) -> ~A.
Proof.
intro H.
destruct H.
contradict H.
apply H0.
assumption.
Qed.

Lemma lem7a:
  (P -> Q) -> (~Q -> ~P).
Proof.
intros H H0.
contradict H0.
apply H.
assumption.
Qed.

Lemma lem7b:
  (~Q -> ~P) -> (P -> Q).
Proof.
intros H H0.
apply NNPP.
contradict H0.
apply H; assumption.
Qed.

Lemma lem8:
~ ((~P -> P) /\ (P -> ~P)).
Proof.
intro H.
destruct H.
apply H0;apply H;intro;apply H0; assumption.
Qed.
