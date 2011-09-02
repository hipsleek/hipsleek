Require Import Classical.
Axiom dep_extensionality:
 forall (A: Type) (B: A -> Type) (f g : forall x: A, B x),  (forall x, f x = g x) -> f = g.
Implicit Arguments dep_extensionality.
Lemma extensionality:
 forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply dep_extensionality; auto. Qed.
Implicit Arguments extensionality.
Tactic Notation "extensionality" := 
  (match goal with | |- ?f = ?g => apply (extensionality f g); intro end).
Tactic Notation "extensionality" ident(x) := 
  (match goal with | |- ?f = ?g => apply (extensionality f g); intro x end).
Require Import Omega.
Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
 Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).
Tactic Notation "LEM" constr(phi) :=
  (destruct (classic (phi))).

(* end #include section *)

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

Lemma deMorgan :
  (forall t, P t) = (~ exists t, ~P t).
Proof.
 apply prop_ext.
 split.
 apply deMorgan_a.
 apply deMorgan_b.
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

Lemma deMorgan2 : 
  (exists t, P t) = (~forall t, ~ P t).
Proof.
 apply prop_ext.
 split.
 apply deMorgan2_a.
 apply deMorgan2_b.
Qed.


Lemma lem5:
  (forall t, P t = ~ Q t) ->
  (forall t, P t) \/ (exists t, Q t).
Proof.
 intros.
 LEM (forall t : term, P t).
 left.
 assumption.
 right.
 rewrite deMorgan in H0.
apply NNPP in H0.
destruct H0.
spec H x.
exists x.
LEM (Q x).
assumption.
rewrite <- H in H1.
destruct H0.
trivial.
Qed.

End PredicateLogic.