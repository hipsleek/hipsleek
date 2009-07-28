(* Simple tactic that tried to decide (in)equalities on Z *)
Require Export ZArith List.

(* ------------------------------------------------------------------------------------------------------------ *)

Ltac sim :=
  let apply_rev_unit x L :=
    replace (rev (L ++ x :: (@nil Z))) with (x :: rev L) in * by ( symmetry; apply rev_unit ) in
  let apply_app_ass L1 L2 L3 :=
    replace ((L1 ++ L2) ++ L3) with (L1 ++ L2 ++ L3) in * by ( apply ass_app ) in
  let simpl_x_nil_app x L :=
    replace ((x :: (@nil Z)) ++ L) with (x :: L) in * by ( auto ) in
  let apply_app_nil L :=
    replace (L ++ (@nil Z)) with (L) in * by ( apply app_nil_end ) in
  let apply_nil_app L :=
    replace ((@nil Z) ++ L) with (L) in * by ( auto ) in
  let simpl_head_cons x L :=
    replace (hd 0%Z (x :: L)) with (x) in * by ( auto ) in
  let simpl_tail_nil :=
    replace (tail (@nil Z)) with (@nil Z) in * by ( auto ) in
  let simpl_tail_cons x L :=
    replace (tail (x :: L)) with (L) in * by ( auto ) in
  let simpl_length_nil :=
    replace (length (@nil Z)) with (0) in * by ( auto ) in
  let simpl_length_cons x L :=
    replace (length (x :: L)) with (1 + length L) in * by ( auto ) in
  let apply_app_length L1 L2 :=
    replace (length (L1 ++ L2)) with (length L1 + length L2) in * by ( symmetry; apply app_length ) in
  let apply_rev_length L :=
    replace (length (rev L)) with (length L) in * by ( symmetry; apply rev_length ) in
  let simpl_rev_nil :=
    replace (rev (@nil Z)) with (@nil Z) in * by ( auto ) in
  let simpl_rev_cons x L :=
    replace (rev(x :: L)) with (rev L ++ x :: (@nil Z)) in * by ( auto ) in
  let apply_distr_rev L1 L2 :=
    replace (rev (L1 ++ L2)) with (rev L2 ++ rev L1) in * by ( symmetry; apply distr_rev ) in
  let apply_rev_involutive L :=
    replace (rev (rev L)) with (L) in * by ( symmetry; apply rev_involutive ) in
  let simpl_Z_of_nat_const x :=
    simpl (Z_of_nat x) in * in
  let apply_inj_plus x1 x2 :=
    replace (Z_of_nat (x1 + x2)) with (Z_of_nat x1 + Z_of_nat x2)%Z in * by ( symmetry; apply inj_plus ) in
  match goal with
    | H : context [rev (?L ++ ?x :: (@nil Z))] |- _ => apply_rev_unit x L
    | |- context [rev (?L ++ ?x :: (@nil Z))] => apply_rev_unit x L
    | H : context [(?L1 ++ ?L2) ++ ?L3] |- _ => apply_app_ass L1 L2 L3
    | |- context [(?L1 ++ ?L2) ++ ?L3] => apply_app_ass L1 L2 L3
    | H : context [(?x :: (@nil Z)) ++ ?L] |- _ => simpl_x_nil_app x L
    | |- context [(?x :: (@nil Z)) ++ ?L] => simpl_x_nil_app x L
    | H : context [?L ++ (@nil Z)] |- _ => apply_app_nil L
    | |- context [?L ++ (@nil Z)] => apply_app_nil L
    | H : context [(@nil Z) ++ ?L] |- _ => apply_nil_app L
    | |- context [(@nil Z) ++ ?L] => apply_nil_app L
    | H : context [hd 0%Z (?x :: ?L)] |- _ => simpl_head_cons x L
    | |- context [hd 0%Z (?x :: ?L)] => simpl_head_cons x L
    | H : context [tail (@nil Z)] |- _ => simpl_tail_nil
    | |- context [tail (@nil Z)] => simpl_tail_nil
    | H : context [tail (?x :: ?L)] |- _ => simpl_tail_cons x L
    | |- context [tail (?x :: ?L)] => simpl_tail_cons x L
    | H : context [length (@nil Z)] |- _ => simpl_length_nil
    | |- context [length (@nil Z)] => simpl_length_nil
    | H : context [length (?x :: ?L)] |- _ => simpl_length_cons x L
    | |- context [length (?x :: ?L)] => simpl_length_cons x L
    | H : context [length (?L1 ++ ?L2)] |- _ => apply_app_length L1 L2
    | |- context [length (?L1 ++ ?L2)] => apply_app_length L1 L2
    | H : context [length (rev ?L)] |- _ => apply_rev_length L
    | |- context [length (rev ?L)] => apply_rev_length L
    | H : context [rev (@nil Z)] |- _ => simpl_rev_nil
    | |- context [rev (@nil Z)] => simpl_rev_nil
    | H : context [rev (?x :: ?L)] |- _ => simpl_rev_cons x L
    | |- context [rev (?x :: ?L)] => simpl_rev_cons x L
    | H : context [rev (?L1 ++ ?L2)] |- _ => apply_distr_rev L1 L2
    | |- context [rev (?L1 ++ ?L2)] => apply_distr_rev L1 L2
    | H : context [rev (rev ?L)] |- _ => apply_rev_involutive L
    | |- context [rev (rev ?L)] => apply_rev_involutive L
    | H : context [Z_of_nat 0] |- _ => simpl_Z_of_nat_const 0
    | |- context [Z_of_nat 0] => simpl_Z_of_nat_const 0
    | H : context [Z_of_nat 1] |- _ => simpl_Z_of_nat_const 1
    | |- context [Z_of_nat 1] => simpl_Z_of_nat_const 1
    | H : context [Z_of_nat (?x1 + ?x2)] |- _ => apply_inj_plus x1 x2
    | |- context [Z_of_nat (?x1 + ?x2)] => apply_inj_plus x1 x2
end.

(* ------------------------------------------------------------------------------------------------------------ *)

Lemma simpl_x_nil_app : forall (A : Type) (L : list A) (x : A), x :: (@nil A) ++ L = x :: L.
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

Hint Rewrite
  rev_unit
  app_ass
  simpl_x_nil_app
  simpl_app_nil
  simpl_nil_app
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
  inj_0 inj_S
  inj_plus
    : simpl_lists.

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

(*
Hint Resolve alln_nil alln_cons alln_app alln_rev : datatypes.
*)

(* ------------------------------------------------------------------------------------------------------------ *)

Ltac hyp :=
  match goal with

(*  | |- exists A : Z, _ =>
       try (exists 0%Z; repeat hyp; auto with *; reflexivity );
       try (exists 1%Z; repeat hyp; auto with *; reflexivity );
       try (exists 2%Z; repeat hyp; auto with *; reflexivity );
       try (exists 3%Z; repeat hyp; auto with *; reflexivity );
       match goal with
       | X : Z |- _ =>
         exists X%Z; repeat hyp; auto with *; reflexivity
       end
*)

(*
  | |- exists L : list Z, _ /\ L = ?V1 => exists V1
  | |- exists L : list Z, _ /\ _ /\ L = ?V1 => exists V1
  | |- exists L1: list Z, (exists L2: list Z, (L1 = _ :: L2 /\ L2 = ?L)) => eexists; exists L; auto
  | |- exists L1: list Z, _ /\ (exists L2: list Z, ((_ /\ L1 = _ :: L2) /\ L2 = ?L)) => eexists; split; [ simple apply refl_equal | exists L; auto ]
*)

(*  
  | |- exists L1 : list Z, _ =>
       eexists
  | |- exists L : list Z, _ =>
       try (exists (@nil Z); repeat hyp; repeat sim; auto with * );
       match goal with
       | X : list Z |- _ =>
         try (exists X; repeat hyp; repeat sim; auto with * )
       end
*)
  
  | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H
  | H : nil = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H; destruct H

  | H : In ?x (?y :: ?L) |- _ => apply in_inv in H; destruct H

  
  | H : alln (?x :: ?L) ?n |- _ => rewrite alln_cons in H; destruct H
  | |- alln (?x :: ?L) ?n => rewrite alln_cons; split
  | H : alln (?L1 ++ ?L2) ?n |- _ => rewrite alln_app in H; destruct H
  | |- alln (?L1 ++ ?L2) ?n => rewrite alln_app; split
  | H : alln (rev ?L) ?n |- _ => rewrite alln_rev in H
  | |- alln (rev ?L) ?n => rewrite alln_rev
  | |- alln (@nil Z) ?n => apply alln_nil (* Qed *)

(*
  | H : count_occ Z_eq_dec (?x :: ?L) 0%Z = length (?x :: ?L) |- _ => apply count_occ_cons_eq_len in H; destruct H
*)
  
  | H : _ :: _ = nil |- _ => symmetry in H; contradict H; simple apply nil_cons (* Qed *)
  | H : nil = _ :: _ |- _ => contradict H; simple apply nil_cons (* Qed *)
  
  | |- ?x :: _ = ?x :: _ => f_equal
  
  
  | H : exists A : _, _ |- _ => destruct H
  | |- forall A : _, _=> intro
  | |- ~ ?X => intro
 
  | H : ?A = _ |- _ => try rewrite -> H in *; clear H A
 
  | H : ?A /\ ?B |- _ => destruct H
  | H : ?A \/ ?B |- _ => destruct H
 
  | |- ?A /\ ?B => split
  | |- ?A \/ ?B => try solve [ left; solve_with_ltac | right; solve_with_ltac ]; elimtype False

end

with solve_exists :=
  match goal with
    | |- context [ ex _ ] => repeat eexists; solve_all; instantiate
    | _ => idtac
end

with solve_all := repeat (repeat hyp; repeat sim); auto with *

with solve_with_ltac :=
intros;
solve_exists;
solve_all;
simpl in *; try omega; try discriminate; try congruence; elimtype False; auto.

(* ------------------------------------------------------------------------------------------------------------ *)

(*
Ltac solve_with_ltac := intros; try do 10 hyp; repeat sim; auto with *; try do 10 hyp; repeat sim; auto with *; try do 10 hyp; repeat sim; auto with *; repeat hyp; repeat sim; auto with *; simpl in *; eauto; try omega; try discriminate; try congruence; elimtype False; auto.

Ltac solve_with_autorewrite := intros; try do 10 hyp; autorewrite with simpl_lists in *; auto with *; try do 10 hyp; autorewrite with simpl_lists in *; auto with *; try do 10 hyp; autorewrite with simpl_lists in *; auto with *; repeat hyp; autorewrite with simpl_lists in *; auto with *; simpl in *; eauto; try omega; try discriminate; try congruence; elimtype False; auto.
*)