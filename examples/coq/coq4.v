
Require Import Classical.
Module Induction.

(* Naturals *)
Inductive Nat : Type :=
  | Zero : Nat
  | Succ : forall n : Nat, Nat. (* Succ is short for successor *)

(* A recursive definition for addition. *)
Fixpoint Add (n1 n2 : Nat) : Nat :=
  match (n1, n2) with
   | (Zero, n2') => n2' (* 0 + n2 = n2 *)
   | (Succ n1', n2') => Succ (Add n1' n2') (* (Succ n1) + n2 = Succ (n1 + n2) *)
  end.

(* The next three lemmas are given for your study *)
Lemma Add_n1_Zero: forall n1,
  Add n1 Zero = n1.
Proof.
  induction n1.
trivial.
  simpl.
 rewrite IHn1.
  trivial.
Qed.

Lemma Add_n1_Succ_n2: forall n1 n2,
  Add n1 (Succ n2) = Succ(Add n1 n2).
Proof.
  intros.
 induction n1.
 auto.
  simpl.
 rewrite IHn1.
  trivial.
Qed.

Lemma Add_Comm: forall n1 n2,
  Add n1 n2 = Add n2 n1.
Proof.
  intros; induction n1; simpl.
  rewrite Add_n1_Zero.
 trivial.
 
 rewrite Add_n1_Succ_n2.
  congruence.
Qed.

Lemma Add_Assoc: forall n1 n2 n3,
  Add n1 (Add n2 n3) = Add (Add n1 n2) n3.
Proof.
  intros.
induction n1.
simpl.
trivial.
simpl.
congruence. 
Qed.

(* Multiplication is just repeated addition. *)
Fixpoint Mult (n1 n2 : Nat) : Nat :=
  match (n1, n2) with
   | (Zero, n2') => Zero
   | (Succ n1', n2') => Add (Mult n1' n2') n2'
  end.

Lemma Mult_Succ: forall n1 n2,
  Mult n1 (Succ n2) = Add n1 (Mult n1 n2).
Proof.
  intros.
induction n1.
simpl.
trivial.
simpl.
rewrite Add_n1_Succ_n2.
rewrite Add_Assoc.
congruence. 
Qed.

Lemma Mult_n1_Zero: forall n1,
  Mult n1 Zero = Zero.
Proof.
  induction n1.
  trivial.
  simpl.
  rewrite IHn1.
  trivial.
Qed.

Lemma Mult_Comm: forall n1 n2,
  Mult n1 n2 = Mult n2 n1.
Proof.
 intros.
  induction n1.
  rewrite Mult_n1_Zero.
  simpl.
  trivial.
  simpl.
  rewrite Mult_Succ.
  rewrite IHn1.
  rewrite Add_Comm.
  trivial. 
Qed.

(* Here is a reasonable way to define subtraction on the naturals.  Note
    that if n2 >= n1, n1 - n2 = Zero (since there are no negatives, you 
    can't get any smaller than Zero). *)
Fixpoint Sub (n1 n2 : Nat) : Nat :=
  match (n1, n2) with
   | (Zero, n2') => Zero
   | (n1', Zero) => n1'
   | (Succ n1', Succ n2') => Sub n1' n2'
  end.

Lemma Sub_Prop1: forall n1, 
  Sub n1 Zero = n1.
Proof.
  intros.
  induction n1.
  trivial.
  simpl.
trivial.
Qed.

Lemma Sub_Prop2: forall n2,
  Sub Zero n2 = Zero.
Proof.
  induction n2.
simpl.
trivial.
simpl.
trivial.
Qed.


(* Hint: You will have to make sure that you have the right induction
    hypothesis or this will be very painful.  One way that you can use 
    to do this is the "revert" tactic.  There are also other ways.  *)
Lemma Sub_Prop3: forall n3 n2 n1,
  Sub n1 n2 = n3 ->
  (n3 = Zero) \/ (Add n2 n3 = n1).
Proof.
intros.
revert H.
revert n2.
induction n1.
left.
inversion H.
trivial.
induction n2.
right.
simpl.
inversion H.
auto.
simpl.
intros.
elim IHn1 with n2.
apply IHn1 in H.
destruct H.
left.
trivial.
right.
congruence.
intro.
right.
congruence.
assumption.
Qed.

Lemma Sub_Prop4a: forall n1, Sub n1 n1 = Zero.
Proof.
  induction n1.
  trivial.
  trivial.
Qed.

Lemma Sub_Prop4b: forall n1 n2, Sub (Add n1 n2) n1 = n2.
Proof.
  induction n1.
  simpl.
  apply Sub_Prop1.
  trivial.
Qed.


Lemma Sub_Prop4: forall n1 n2 n3,
  Add n1 n2 = n3 ->
  Sub n3 n1 = n2.
Proof.
  intros.
  induction n1.
  replace n3.
  simpl.
  apply Sub_Prop1.
  induction n2.
  replace n3.
  simpl.
  rewrite Add_n1_Zero.
  apply Sub_Prop4a.
  replace n3.
  rewrite Sub_Prop4b.
  trivial.
Qed.

End Induction.