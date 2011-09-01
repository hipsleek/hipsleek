(* Introduction to Coq: Sample Proof Script *)

Require Import Classical.

Parameter A B : Prop.

Lemma lemma1a: A -> A.
Proof.
intro H.
assumption.
Qed.

Check lemma1a.
Print lemma1a.

Lemma lemma1b: A -> A.
Proof.
trivial.
Qed.

Lemma lemma2: A /\ B -> B /\ A.
Proof.
intro H.
(*split; destruct H; assumption.*)
split.
destruct H.
assumption.
destruct H.
(*assumption.*)
apply H.
Qed.

Lemma lemma3: A -> A \/ B.
Proof.
intro.
left.
apply H.
Qed.

Lemma lemma4: A \/ B -> B \/ A.
Proof.
intro H.
destruct H.
right.
apply H.
left.
apply H.
Qed.

Lemma lemma5a: A /\ (A -> B) -> B.
Proof.
intro H.
destruct H.
apply H0.
assumption.
Qed.

Lemma lemma5b: A -> (A -> B) -> B.
Proof.
intros H0 H1.
apply H1.
assumption.
Qed.

Lemma lemma6 : ~ (A /\ ~A).
Proof.
intro H.
destruct H.
apply H0.
assumption.
Qed.

Lemma lemma7: (A /\ B) \/ (~A \/ ~B).
Proof.
apply NNPP.
intro.
assert (~(A /\ B)).
contradict H.
left.
assumption.
assert (~(~A \/ ~B)).
contradict H.
right.
assumption.
contradict H1.
apply not_and_or.
assumption.
Qed.
Check lemma7.
Print lemma7.
