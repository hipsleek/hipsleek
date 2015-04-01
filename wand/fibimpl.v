Require fib.
Require Import ZArith.
Require Import ZArith.Znat.
Require Import Recdef.
Require Import Coq.Bool.Bool.

Module Mfibimpl <: fib.Mfib.

Inductive PF : Type :=
  | F_and : PF -> PF -> PF
  | F_imp : PF -> PF -> PF
  | F_not : PF -> PF
  | F_leq : Z -> Z -> PF
  | F_fib : Z -> Z ->  PF.

Definition formula := PF.
Definition and := F_and.
Definition imp := F_imp.
Definition not := F_not.
Definition leq := F_leq.

Definition fib := F_fib.

(*
Fixpoint FIB (n:Z) : Z :=
match n with
  | Zpos i => match i with
                       | xH => 1%Z
                       | _ => 1%Z 
                     end
  | _ => 0%Z
end.
*)

Fixpoint FIB_nat n : nat :=
match n with
   0 => 0
 | (S p) => 
       match p with
           0 => 1
         | (S m) => plus (FIB_nat p) (FIB_nat m)
       end
end.

Definition FIB (n:Z) : Z := Z.of_nat  (FIB_nat (Z.to_nat n)).

Lemma plus_1_Sn :
 forall n:nat, n + 1 = S n.
Proof.
 intro n.
 rewrite plus_n_O.
 rewrite plus_Snm_nSm.
 reflexivity.
Qed.

Lemma plus_2_SSn :
 forall n:nat, n + 2 = S (S n).
Proof.
 intro n.
 rewrite plus_n_O.
 rewrite plus_Snm_nSm.
 rewrite plus_Snm_nSm.
 reflexivity.
Qed.

Lemma FIB_nat_2 : forall n, (FIB_nat (n+2)) = (FIB_nat (n))  +  (FIB_nat (n+1)) .
Proof.
intro n.

 rewrite plus_1_Sn.
 rewrite plus_2_SSn.
 simpl FIB_nat.
 destruct n.
  reflexivity.
  omega.
Qed.


(*
Proof.
intros.
unfold Z.sub.
simpl.
induction n.
exfalso.
unfold Z.leb in teq.
simpl in teq.
apply eqb_false_iff in teq.
tauto.
unfold eqb. trivial.
apply orb_false_iff in teq0.
destruct teq0.

admit.
assert (Z.pos p > 2)%Z.
apply orb_false_iff in teq0.

apply eqb_false_iff in teq.
tauto.
unfold eqb.
rewrite teq.
unfold Z.leb in teq0. simpl in teq0.
unfold Z.leb in H.
simpl in H.
unfold Z.add.
simpl.
unfold Z.leb in teq0.
simpl in teq0.
omega.
Qed.
*)

Fixpoint satis (f:formula) : Prop := 
match f with
  | F_and f1 f2 => satis f1  /\ satis f2 
  | F_imp f1 f2 => satis f1 -> satis f2  
  | F_not f => ~(satis f)
  | F_leq n1 n2 => (Z.le n1 n2)
  | F_fib n f =>  f = (FIB n)
end.

Definition valid (f:formula) := satis f.

Lemma axiom_1 : forall n, valid (imp (leq n 0) (fib n 0)).
unfold valid.
intros.
simpl.
intros.
unfold FIB; intros.
induction n.
unfold Z.to_nat.
unfold FIB_nat.
unfold Z.of_nat.
trivial.
unfold Z.le in H.
simpl in H.
tauto.
simpl.
trivial.
Qed.

Lemma axiom_2 : forall n, valid (imp (and (leq 1 n) (leq n 2)) (fib n 1)).
unfold valid.
intros.
simpl. intros.
unfold FIB. induction n.
simpl.
unfold Z.le in H.
simpl in H. destruct H.
tauto.

destruct H.

apply Z2Nat.inj_le in H.
apply Z2Nat.inj_le in H0.
destruct (Z.to_nat (Z.pos p)).
simpl in H,H0.

unfold Pos.to_nat in H.
unfold Pos.iter_op in H.
omega.
simpl in H, H0.
unfold Pos.to_nat in H,H0.
unfold Pos.iter_op in H,H0.
assert (S n = 1 \/ S n = 2).
omega.
destruct H1.
rewrite H1.
simpl. trivial.
rewrite H1.
simpl. trivial.
unfold Z.le.
simpl.
discriminate.
omega.
omega.
unfold Z.le;simpl.
discriminate.
simpl.
destruct H.
unfold Z.le in H. simpl in H.
tauto.
Qed.

Lemma axiom_3 : forall n f1 f2, valid (imp (and (not (leq n 0)) (and (fib n f1) (fib (n+1) f2))) (fib (n+2) (f1+f2))).
intros.
unfold valid.
simpl.
intros.
destruct H.
induction n.
simpl.
unfold FIB in H0,H.
simpl in H0,H.
unfold FIB.
simpl.
omega.

(*
assert (Z.pos p > 2)%Z.
apply Znot_le_gt. trivial.
clear H.
*)

unfold FIB in H0.
destruct H0.
unfold FIB.
subst.
simpl.
admit.

(*
unfold FIB.
destruct p.
simpl.
unfold Pos.to_nat.
destruct p.
simpl.
unfold Pos.iter_op.
simpl.
unfold FIB_nat. simpl.
*)

unfold Z.le in H.
simpl in H.
intuition.
exfalso.
apply H.
discriminate.
Qed.

Lemma entail_1 :  forall n m, valid (imp (and (fib 1 n) (fib 2 m)) (and (leq n m) (leq m n))).
Proof.
intros.
unfold valid.
simpl.
intros.
unfold FIB in H.
simpl in H.
destruct H.
subst.
omega.
Qed.

Lemma entail_2 : forall n m p, valid (imp (and (and (leq n 1) (leq 1 n)) (and (fib n p) (fib (n+1) m))) (and (leq m p) (leq p m))).
Proof.
intros.
unfold valid.
simpl.
intros.
assert (n =1)%Z.
omega.
subst.
unfold FIB in H.
simpl in H.
destruct H.
destruct H0.
subst.
trivial.
Qed.

End Mfibimpl.
