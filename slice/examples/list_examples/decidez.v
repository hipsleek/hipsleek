(* Simple tactic that tried to decide (in)equalities on Z *)
Require Export ZArith List FSets.
Module ZSets := Make(Z_as_OT).

(* ------------------------------------------------------------------------------------------------------------ *)

Lemma cons_eq_nil : forall (A : Type) (x : A) (L : list A), x :: L = (@nil A) <-> False.
Proof.
  intros A x L; split.
    intro H; symmetry in H; contradict H; apply nil_cons.
    intro H; contradict H.
Qed.

Lemma nil_eq_cons : forall (A : Type) (x : A) (L : list A), (@nil A) = x :: L <-> False.
Proof.
  intros A x L; split.
    intro H; contradict H; apply nil_cons.
    intro H; contradict H.
Qed.

Lemma cons_eq_cons : forall (A : Type) (x : A) (L1 L2 : list A), x :: L1 = x :: L2 <-> L1 = L2.
Proof.
  intros A x L1 L2; split.
    intro H; injection H; intro H0; exact H0.
    intro H; f_equal; exact H.
Qed.

Lemma simpl_x_cons_app : forall (A : Type) (L1 L2 : list A) (x : A), (x :: L1) ++ L2 = x :: L1 ++ L2.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_app_nil : forall (A : Type) (L : list A), L ++ (@nil A) = L.
Proof.
  symmetry; simple apply app_nil_end.
Qed.

Lemma simpl_nil_app : forall (A : Type) (L : list A), (@nil A) ++ L = L.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma list_app_eq_nil : forall (A : Type) (L1 L2 : list A), L1 ++ L2 = (@nil A) <-> L1 = (@nil A) /\ L2 = (@nil A).
Proof.
  intros A L1 L2; split.
    intro H; simple apply app_eq_nil; exact H.
    intro H; destruct H; subst; simple apply refl_equal.
Qed.

Lemma nil_eq_list_app : forall (A : Type) (L1 L2 : list A), (@nil A) = L1 ++ L2 <-> L1 = (@nil A) /\ L2 = (@nil A).
Proof.
  intros A L1 L2; split.
    intro H; symmetry in H; simple apply app_eq_nil; exact H.
    intro H; destruct H; subst; simple apply refl_equal.
Qed.

Lemma simpl_head_cons : forall (A : Type) (L : list A) (x d : A), hd d (x :: L) = x.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_tail_nil : forall (A : Type), tail (@nil A) = (@nil A).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_tail_cons : forall (A : Type) (L : list A) (x : A), tail (x :: L) = L.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_length_nil : forall (A : Type), length (@nil A) = 0.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_length_not_nil : forall (A : Type) (L : list A), L <> (@nil A) <-> length (L) > 0.
Proof.
  admit.
Qed.
  
Lemma simpl_length_cons : forall (A : Type) (L : list A) (x : A), length (x :: L) = 1 + length L.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_rev_nil : forall (A : Type), rev (@nil A) = (@nil A).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_rev_cons : forall (A : Type) (L : list A) (x : A), rev(x :: L) = rev L ++ x :: (@nil A).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma in_x_cons : forall (A : Type) (x y : A) (L : list A), In x (y :: L) <-> y = x \/ In x L. 
Proof.
  intros A x y L; split; intro H; exact H.
Qed.

Hint Constructors Permutation : datatypes.

Hint Resolve
  Permutation_nil
  Permutation_nil_cons 
  Permutation_refl
  Permutation_sym
  Permutation_trans
  Permutation_in
  Permutation_app
  Permutation_app_swap
  Permutation_cons_app
  Permutation_length
  Permutation_rev
  Permutation_app_inv
  Permutation_cons_inv
  Permutation_cons_app_inv
  Permutation_app_inv_l
  Permutation_app_inv_r
    : datatypes.

(* ------------------------------------------------------------------------------------------------------------ *)

Lemma count_occ_le_len : forall (L : list Z) (n : Z), count_occ Z_eq_dec L n <= length L.
Proof.
  intros L n; induction L as [| a L].
    simple apply le_n.
    simpl (length (a :: L)); generalize (Z_eq_dec a n); intro H; destruct H as [H | H0].
      rewrite count_occ_cons_eq.
        omega.
        exact H.
      rewrite count_occ_cons_neq.
        omega.
        exact H0.
Qed.

Lemma count_occ_cons_eq_len : forall (x : Z) (L : list Z) (n : Z), count_occ Z_eq_dec (x :: L) n = length (x :: L) -> x = n /\ count_occ Z_eq_dec L n = length L.
Proof.
  intros x L n H; simpl (length (x :: L)) in H; generalize (Z_eq_dec x n); intro H0; destruct H0 as [H0 | H1].
    split.
      exact H0.
      rewrite count_occ_cons_eq in H.
        simple apply eq_add_S; exact H.
        exact H0.
    rewrite count_occ_cons_neq in H.
      generalize (count_occ_le_len L n); intro H2; omega.
      exact H1.
Qed.

Definition alln (l : list Z) (n : Z) := count_occ Z_eq_dec l n = length l.

Theorem alln_nil : forall (n : Z), alln (@nil Z) n.
Proof.
  intro n; unfold alln; simple apply refl_equal.
Qed.

Theorem alln_cons : forall (x : Z) (L : list Z) (n : Z), alln (x :: L) n <-> x = n /\ alln L n.
Proof.
  intros x L n; split.
    intro H; unfold alln in H; apply count_occ_cons_eq_len in H; destruct H as [H0]; split.
      exact H0.
      exact H.
    intro H; destruct H as [H0]; unfold alln; rewrite count_occ_cons_eq.
      simpl (length (x :: L)); f_equal; exact H.
      exact H0.
Qed.

Theorem alln_app : forall (L1 : list Z) (L2 : list Z) (n : Z), alln (L1 ++ L2) n <-> alln L1 n /\ alln L2 n.
Proof.
  intros L1 L2 n; split.
    intro H; induction L1 as [| a L1 IHL1].
      split.
        simple apply alln_nil.
        exact H.
      simpl in H; rewrite alln_cons in H; destruct H as [H0]; apply IHL1 in H; destruct H as [H1]; split.
        rewrite alln_cons; split.
          exact H0.
          exact H1.
        exact H.
    intro H; destruct H as [H0]; induction L1 as [| a L1 IHL1].
      exact H.
      simpl; rewrite alln_cons; rewrite alln_cons in H0; destruct H0 as [H1]; split.
        exact H1.
        apply IHL1 in H0; exact H0.
Qed.

Theorem alln_rev : forall (L : list Z) (n : Z), alln (rev L) n <-> alln L n.
Proof.
  intros L n; split.
    intro H; induction L as [| a L IHL].
      apply alln_nil.
      change (rev (a :: L)) with (rev L ++ a :: nil) in H; rewrite alln_app in H; destruct H as [H0]; rewrite alln_cons; split.
        rewrite alln_cons in H; destruct H as [H1]; exact H1.
        apply IHL in H0; exact H0.
    intro H; induction L as [| a L IHL].
      exact H.
      rewrite alln_cons in H; destruct H as [H0]; change (rev (a :: L)) with (rev L ++ a :: nil); rewrite alln_app; split.
        apply IHL; exact H.
        rewrite alln_cons; split.
          exact H0.
          apply alln_nil.
Qed.

Hint Resolve alln_nil (* alln_cons alln_app alln_rev *) : datatypes.

(* ------------------------------------------------------------------------------------------------------------ *)

Hint Rewrite
  cons_eq_nil
  nil_eq_cons
  cons_eq_cons
  rev_unit
  app_ass
  simpl_x_cons_app
  simpl_app_nil
  simpl_nil_app
  list_app_eq_nil
  nil_eq_list_app
  simpl_head_cons
  simpl_tail_nil
  simpl_tail_cons
  simpl_length_nil
  simpl_length_cons
  app_length
  rev_length
  simpl_rev_nil
  simpl_rev_cons
  distr_rev
  rev_involutive
  inj_0
  inj_S
  inj_plus
  in_x_cons
  alln_cons
  alln_app
  alln_rev
    : simpl_lists_db.

(* ------------------------------------------------------------------------------------------------------------ *)

Ltac sim :=
  match goal with
 
    | |- context [_ :: _ = (@nil Z)] => rewrite cons_eq_nil in |- *
    | |- context [(@nil Z) = _ :: _] => rewrite nil_eq_cons in |- *
    | |- context [?x :: _ = ?x :: _] => rewrite cons_eq_cons in |- *
    | |- context [rev (?L ++ ?x :: (@nil Z))] => rewrite rev_unit in |- *
    | |- context [(?L1 ++ ?L2) ++ ?L3] => rewrite app_ass in |- *
    | |- context [(?x :: ?L1) ++ ?L2] => rewrite simpl_x_cons_app in |- *
    | |- context [?L ++ (@nil Z)] => rewrite simpl_app_nil in |- *
    | |- context [(@nil Z) ++ ?L] => rewrite simpl_nil_app in |- *
    | |- context [?L1 ++ ?L2 = (@nil Z)] => rewrite list_app_eq_nil in |- *
    | |- context [(@nil Z) = ?L1 ++ ?L2] => rewrite nil_eq_list_app in |- *
    | |- context [hd 0%Z (?x :: ?L)] => rewrite simpl_head_cons in |- *
    | |- context [tail (@nil Z)] => rewrite simpl_tail_nil in |- *
    | |- context [tail (?x :: ?L)] => rewrite simpl_tail_cons in |- *
    | |- context [length (@nil Z)] => rewrite simpl_length_nil in |- *
    | |- context [length (?x :: ?L)] => rewrite simpl_length_cons in |- *
    | |- context [length (?L1 ++ ?L2)] => rewrite app_length in |- *
    | |- context [length (rev ?L)] => rewrite rev_length in |- *
    | |- context [rev (@nil Z)] => rewrite simpl_rev_nil in |- *
    | |- context [rev (?x :: ?L)] => rewrite simpl_rev_cons in |- *
    | |- context [rev (?L1 ++ ?L2)] => rewrite distr_rev in |- *
    | |- context [rev (rev ?L)] => rewrite rev_involutive in |- *
    | |- context [Z_of_nat 0] => simpl (Z_of_nat 0) in |- * (* rewrite inj_0 in |- * *)
    | |- context [Z_of_nat (S ?n)] => simpl (Z_of_nat (S n)) in |- * (* rewrite inj_S in |- * *)
    | |- context [Z_of_nat (?x1 + ?x2)] => rewrite inj_plus in |- *
    | |- context [In ?x (?y :: ?L)] => rewrite in_x_cons in |- *
    | |- context [alln (?x :: ?L) ?n] => rewrite alln_cons in |- *
    | |- context [alln (?L1 ++ ?L2) ?n] => rewrite alln_app in |- *
    | |- context [alln (rev ?L) ?n] => rewrite alln_rev in |- *
    | H: (* context [ *)_ :: _ = (@nil Z) (*]*) |- _ => rewrite cons_eq_nil in H; contradict H (* Qed *)
    | H: (* context [*)(@nil Z) = _ :: _ (*]*) |- _ => rewrite nil_eq_cons in H; contradict H (* Qed *)
    | H: context [?x :: _ = ?x :: _] |- _ => rewrite cons_eq_cons in H
    | H: context [rev (?L ++ ?x :: (@nil Z))] |- _ => rewrite rev_unit in H
    | H: context [(?L1 ++ ?L2) ++ ?L3] |- _ => rewrite app_ass in H
    | H: context [(?x :: ?L1) ++ ?L2] |- _ => rewrite simpl_x_cons_app in H
    | H: context [?L ++ (@nil Z)] |- _ => rewrite simpl_app_nil in H
    | H: context [(@nil Z) ++ ?L] |- _ => rewrite simpl_nil_app in H
    | H: context [?L1 ++ ?L2 = (@nil Z)] |- _ => rewrite list_app_eq_nil in H
    | H: context [(@nil Z) = ?L1 ++ ?L2] |- _ => rewrite nil_eq_list_app in H
    | H: context [hd 0%Z (?x :: ?L)] |- _ => rewrite simpl_head_cons in H
    | H: context [tail (@nil Z)] |- _ => rewrite simpl_tail_nil in H
    | H: context [tail (?x :: ?L)] |- _ => rewrite simpl_tail_cons in H
    | H: context [length (@nil Z)] |- _ => rewrite simpl_length_nil in H
    | H: context [length (?x :: ?L)] |- _ => rewrite simpl_length_cons in H
    | H: context [length (?L1 ++ ?L2)] |- _ => rewrite app_length in H
    | H: context [length (rev ?L)] |- _ => rewrite rev_length in H
    | H: context [rev (@nil Z)] |- _ => rewrite simpl_rev_nil in H
    | H: context [rev (?x :: ?L)] |- _ => rewrite simpl_rev_cons in H
    | H: context [rev (?L1 ++ ?L2)] |- _ => rewrite distr_rev in H
    | H: context [rev (rev ?L)] |- _ => rewrite rev_involutive in H
    | H: context [Z_of_nat 0] |- _ => simpl (Z_of_nat 0) in H (* rewrite inj_0 in H *)
    | H: context [Z_of_nat (S ?n)] |- _ => simpl (Z_of_nat (S n)) in H (* rewrite inj_S in H *)
    | H: context [Z_of_nat (?x1 + ?x2)] |- _ => rewrite inj_plus in H
    | H: context [In ?x (?y :: ?L)] |- _ => rewrite in_x_cons in H
    | H: context [alln (?x :: ?L) ?n] |- _ => rewrite alln_cons in H
    | H: context [alln (?L1 ++ ?L2) ?n] |- _ => rewrite alln_app in H
    | H: context [alln (rev ?L) ?n] |- _ => rewrite alln_rev in H
    
end.

(* ------------------------------------------------------------------------------------------------------------ *)

Ltac hyp :=
  match goal with
(*
  | H: context [hd 0%Z (@nil Z)] |- _ => admit
*)
  | |- ~ ?X => intro
  | |- forall A : _, _=> intro
  | H : exists A : _, _ |- _ => destruct H
  
  | H : ?A /\ ?B |- _ => destruct H
  | H : ?A \/ ?B |- _ => destruct H

  | |- ?A /\ ?B => split
  | |- ?A \/ ?B => try solve [ left; solve_all | right; solve_all ]; elimtype False

end

with solve_exists :=
  match goal with
    | |- context [ ex _ ] => repeat eexists; solve_all; instantiate
    | _ => idtac
end

with solve_all := repeat (repeat hyp; repeat sim; subst); auto with *
(* with solve_all := repeat (repeat hyp; autorewrite with simpl_lists_db in *; subst); auto with * *)

with decidez := intros; solve_exists; solve_all; elimtype False; auto.

(* ------------------------------------------------------------------------------------------------------------ *)
