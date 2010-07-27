(* Simple tactic that tried to decide (in)equalities on Z *)
Require Export ZArith List FSets.
Require Export stsort.
Import StsortZZ.
Module ZSets := Make(Z_as_OT).

Fixpoint keyIn (k : Z) (l : list (prod Z Z)) {struct l} :=
  match l with
    | nil => False
    | (a, b) :: t => k = a \/ keyIn k t
  end.

(* ------------------------------------------------------------------------------------------------------------ *)

Lemma cons_eq_nil : forall (x : Obj) (L : list Obj), x :: L = (@nil Obj) <-> False.
Proof.
  intros x L; split.
    intro H; symmetry in H; contradict H; apply nil_cons.
    intro H; contradict H.
Qed.

Lemma nil_eq_cons : forall (x : Obj) (L : list Obj), (@nil Obj) = x :: L <-> False.
Proof.
  intros x L; split.
    intro H; contradict H; apply nil_cons.
    intro H; contradict H.
Qed.

Lemma cons_eq_cons : forall (x : Obj) (L1 L2 : list Obj), x :: L1 = x :: L2 <-> L1 = L2.
Proof.
  intros x L1 L2; split.
    intro H; injection H. intro H0; exact H0.
    intro H; f_equal; exact H.
Qed.

Lemma simpl_x_cons_app : forall (L1 L2 : list Obj) (x : Obj), (x :: L1) ++ L2 = x :: L1 ++ L2.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_app_nil : forall (L : list Obj), L ++ (@nil Obj) = L.
Proof.
  symmetry; simple apply app_nil_end.
Qed.

Lemma simpl_nil_app : forall (L : list Obj), (@nil Obj) ++ L = L.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma list_app_eq_nil : forall (L1 L2 : list Obj), L1 ++ L2 = (@nil Obj) <-> L1 = (@nil Obj) /\ L2 = (@nil Obj).
Proof.
  intros L1 L2; split.
    intro H; simple apply app_eq_nil; exact H.
    intro H; destruct H; subst; simple apply refl_equal.
Qed.

Lemma nil_eq_list_app : forall (L1 L2 : list Obj), (@nil Obj) = L1 ++ L2 <-> L1 = (@nil Obj) /\ L2 = (@nil Obj).
Proof.
  intros L1 L2; split.
    intro H; symmetry in H; simple apply app_eq_nil; exact H.
    intro H; destruct H; subst; simple apply refl_equal.
Qed.

Lemma simpl_head_cons : forall (L : list Obj) (x d : Obj), hd d (x :: L) = x.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_tail_nil : forall (Obj : Type), tail (@nil Obj) = (@nil Obj).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_tail_cons : forall (L : list Obj) (x : Obj), tail (x :: L) = L.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_length_nil : forall (Obj : Type), length (@nil Obj) = 0%nat.
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_length_cons : forall (L : list Obj) (x : Obj), length (x :: L) = (1 + length L).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_rev_nil : forall (Obj : Type), rev (@nil Obj) = (@nil Obj).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma simpl_rev_cons : forall (L : list Obj) (x : Obj), rev(x :: L) = rev L ++ x :: (@nil Obj).
Proof.
  intros; simple apply refl_equal.
Qed.

Lemma in_x_cons : forall (x y : Obj) (L : list Obj), In x (y :: L) <-> y = x \/ In x L. 
Proof.
  intros x y L; split; intro H; exact H.
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

(* ------------------trivial-lemmas-------------------------------------------------------------------------- *)

Lemma triv0 : forall n, (S n <= n)%nat -> False.
Proof.
  intros. omega.
Qed.

Lemma triv1 : (forall m n, m >= n -> n < m \/ n = m)%Z.
Proof.
  intros. omega.
Qed.

Lemma triv2 : (forall m n, m <= n -> m < n \/ m = n)%Z.
Proof.
  intros. omega.
Qed.

Lemma triv3 : (forall m n, m > n -> n < m)%Z.
Proof.
  intros. omega.
Qed.

Lemma l1 : (0 = 1)%Z -> False.
Proof.
  omega.
Qed.

Lemma l01 : (1 = 0)%Z -> False.
Proof.
  omega.
Qed.

Lemma l0 : (0 >= 1)%Z -> False.
Proof.
  omega.
Qed.

Lemma l5: forall l : list Obj, (length l >= 0)%nat.
Proof.
intros. induction l. simpl. auto. simpl. auto.
Qed.

Lemma l6: forall n: nat, (S n >= 1)%nat.
Proof.
intros. induction n. auto. auto.
Qed.

Lemma l7: forall n : nat, (n < n -> False)%nat.
Proof. 
intros. omega.
Qed.

Lemma l8: forall n : nat, (0 > 1 + n -> False)%nat.
Proof. 
intros. omega.
Qed.

Lemma l9 : forall (m n : nat), (1 + m = S n)%nat -> (m = n)%nat.
Proof.
  intros. omega.
Qed.

Lemma l10 : forall (m n : nat), (S m = S n)%nat -> (m = n)%nat.
Proof.
  intros. omega.
Qed.

Lemma l11 : forall (m : nat), (1 + m = 0)%nat -> False.
Proof.
  intros. omega.
Qed.

Lemma l12 : forall (m : nat), (S m = 0)%nat ->  False.
Proof.
  intros. omega.
Qed.

Lemma l13 : forall (m : nat), (0 < S m)%nat.
Proof.
  intros. omega.
Qed.

Lemma p0 : forall (A B : Type) (p1 p2 : prod A B),
    p1 = p2 -> fst p1 = fst p2 /\ snd p1 = snd p2.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma plus_eq_inj_right : forall a b c : Z, (a + c = b + c -> a = b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_inj_left : forall a b c : Z, (c + a = c + b -> a = b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_inj_com_in : forall a b c : Z, (a + c = c + b -> a = b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_inj_com_out : forall a b c : Z, (c + a = b + c -> a = b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_inj_right : forall a b c : Z, (a + c < b + c -> a < b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_inj_left : forall a b c : Z, (c + a < c + b -> a < b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_inj_com_in : forall a b c : Z, (a + c < c + b -> a < b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_inj_com_out : forall a b c : Z, (c + a < b + c -> a < b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_surj_right : forall a b c : Z, (a = b -> a + c = b + c)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_surj_left : forall a b c : Z, (a = b -> c + a = c + b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_surj_com_in : forall a b c : Z, (a = b -> a + c = c + b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_eq_surj_com_out : forall a b c : Z, (a = b -> c + a = b + c )%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_surj_right : forall a b c : Z, (a < b -> a + c < b + c)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_surj_left : forall a b c : Z, (a < b -> c + a < c + b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_surj_com_in : forall a b c : Z, (a < b -> a + c < c + b)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_lt_surj_com_out : forall a b c : Z, (a < b -> c + a < b + c)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_zero_left : forall m : Z, (0 + m = m)%Z.
Proof. auto. Qed.

Lemma plus_zero_right : forall m : Z, (m + 0 = m)%Z.
Proof. intros. omega. Qed.

Lemma plus_right_assoc : forall a b c : Z, (a + (b + c) = a + b + c)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_left_assoc : forall a b c : Z, ((a + b) + c = a + b + c)%Z.
Proof.
  intros. omega.
Qed.

Lemma plus_int_comm : forall a b : Z, (a + b = b + a)%Z.
Proof.
  intros. omega.
Qed.

Lemma triple_comm_right : forall a b c : Z, (a + b + c)%Z = (a + c + b)%Z.
Proof. intros. omega. Qed.

Lemma triple_comm_left : forall a b c : Z, (a + b + c)%Z = (b + a + c)%Z.
Proof. intros. omega. Qed.

Lemma triple_comm_center : forall a b c : Z, (a + b + c)%Z = (c + b + a)%Z.
Proof. intros. omega. Qed.

Lemma p1 : forall (p1 p2 : prod Z Z),
    p1 <> p2 -> fst p1 <> fst p2 \/ snd p1 <> snd p2.
Proof.
  intros. 
rewrite (surjective_pairing p1) in H. 
rewrite (surjective_pairing p2) in H.
destruct (Z_eq_dec (fst p1) (fst p2)).
destruct (Z_eq_dec (snd p1) (snd p2)).
elimtype False.
apply H.
rewrite e. rewrite e0. reflexivity.
right. apply n.
left. apply n.
Qed.

Lemma z_of_nat_inc : forall a, (0 < Z_of_nat (1 + a))%Z.
Proof.
  intros. induction a. simpl. omega.
  auto.
Qed.

Lemma z_of_nat_le_inj : forall x y : nat, x <= y -> (Z_of_nat x <= Z_of_nat y)%Z.
Proof. intros. omega. Qed.

Lemma z_of_nat_lt_inj : forall x y : nat, x < y -> (Z_of_nat x < Z_of_nat y)%Z.
Proof. intros. omega. Qed.

Lemma z_of_nat_eq_inj : forall x y : nat, x = y -> (Z_of_nat x = Z_of_nat y)%Z.
Proof. intros. omega. Qed.

Lemma z_of_nat_le_surj : forall x y : nat, (Z_of_nat x <= Z_of_nat y)%Z -> x <= y.
Proof. intros. omega. Qed.

Lemma z_of_nat_lt_surj : forall x y : nat, (Z_of_nat x < Z_of_nat y)%Z -> x < y .
Proof. intros. omega. Qed.

Lemma z_of_nat_eq_surj : forall x y : nat, (Z_of_nat x = Z_of_nat y)%Z -> x = y.
Proof. intros. omega. Qed.

Lemma kmin_trans : forall (l m : prod Z Z), (fst l < fst m -> fst l = fst (kmin m l))%Z.
Proof.
  intros. unfold kmin. case_eq (kle_klt_dec m l).
    intros. unfold kle, klt, keq in k. omega.
    intros. reflexivity.
Qed.

Lemma kmin_trans_2 : forall (l m : prod Z Z), (fst l <= fst m -> fst l = fst (kmin l m))%Z.
Proof.
  intros. unfold kmin. case_eq (kle_klt_dec l m).
    intros. reflexivity.
    intros. unfold kle, klt, keq in k. omega.
Qed.


Lemma fold_keq : forall a b, a &= b -> fst a = fst b.
Proof.
  intros. unfold keq in H. apply H.
Qed.

(* ------------------triv-lists-------------------------------------------------------------------------- *)

Lemma l3: forall L : list Obj, Z_of_nat(length L) = 0%Z -> L = @nil Obj.
Proof.
  intros. destruct L. reflexivity.
  inversion H.
Qed.

Lemma l2: forall (x : Obj) L, length (x :: L) = 1%nat -> length L = 0%nat.
Proof.
  intros. rewrite simpl_length_cons in H.
  destruct L. reflexivity.
  simpl in H. auto.
Qed.

Lemma head_eq : forall (x x' : Obj) (l : list Obj),
  x :: l = x' :: l -> x = x'.
Proof.
  intros. injection H. intros. apply H0.
Qed.

Lemma cons_subst : forall (x x' : Obj) (l l' : list Obj),
  x :: l = x' :: l' -> x = x' /\ l = l'.
Proof.
  intros. injection H. intros. split. apply H1. apply H0.
Qed.

Lemma length_null_contr : forall l : list Obj, ((1 + Z_of_nat (length l)) = 0 -> False)%Z.
Proof.
  intros. contradict H. omega.
Qed.

(* ------------------lists-------------------------------------------------------------------------- *)

Lemma count_occ_le_len : forall (L : list Obj) (n : Obj), (count_occ obj_eq_dec L n <= length L)%nat.
Proof.
  intros L n; induction L as [| a L].
    simple apply le_n.
    simpl (length (a :: L)); generalize (obj_eq_dec a n); intro H; destruct H as [H | H0].
      rewrite count_occ_cons_eq.
        omega.
        exact H.
      rewrite count_occ_cons_neq.
        omega.
        exact H0.
Qed.

Lemma count_occ_cons_eq_len : forall (x : Obj) (L : list Obj) (n : Obj),
  count_occ obj_eq_dec (x :: L) n = length (x :: L) ->
  x = n /\ count_occ obj_eq_dec L n = length L.
Proof.
  intros x L n H; simpl (length (x :: L)) in H; generalize (obj_eq_dec x n); intro H0; destruct H0 as [H0 | H1].
    split.
      exact H0.
      rewrite count_occ_cons_eq in H.
        simple apply eq_add_S; exact H.
        exact H0.
    rewrite count_occ_cons_neq in H.
      generalize (count_occ_le_len L n). intro H2. rewrite H in H2. split.
        contradict H2. intro h. apply triv0 in h. apply h.
        apply triv0 in H2. contradict H2.
      exact H1.
Qed.

Definition alln (l : list Obj) (n : Obj) := count_occ obj_eq_dec l n = length l.

Theorem alln_nil : forall (n : Obj), alln (@nil Obj) n.
Proof.
  intro n; unfold alln; simple apply refl_equal.
Qed.

Theorem alln_cons : forall (x : Obj) (L : list Obj) (n : Obj), alln (x :: L) n <-> x = n /\ alln L n.
Proof.
  intros x L n; split.
    intro H; unfold alln in H. apply count_occ_cons_eq_len in H; destruct H as [H0]; split.
      exact H0.
      exact H.
    intro H; destruct H as [H0]; unfold alln; rewrite count_occ_cons_eq.
      simpl (length (x :: L)); f_equal; exact H.
      exact H0.
Qed.

Theorem alln_app : forall (L1 : list Obj) (L2 : list Obj) (n : Obj), alln (L1 ++ L2) n <-> alln L1 n /\ alln L2 n.
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

Theorem alln_rev : forall (L : list Obj) (n : Obj), alln (rev L) n <-> alln L n.
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

(*----------------------sorting-------------------------------------------------------------------------------------- *)
(*
Module smth := STSORT ZZ.
Import StsortZZ. //smth *)

Lemma kminl2_null : forall x, x &= kminl2 x nil.
Proof.
  intros. simpl. apply keq_refl.
Qed.

Lemma klt_contradict0 : forall o1 o2, o1 &< o2 -> o2 &< o1 -> False.
Proof.
  unfold klt. intros. omega.
Qed.

Lemma klt_contradict1 : forall o1 o2, o1 &<= o2 -> o2 &< o1 -> False.
Proof.
  unfold kle, klt, keq. intros. omega.
Qed.

Lemma klt_contradict2 : forall o1 o2, o1 &< o2 -> o2 &<= o1 -> False.
Proof.
  unfold kle, klt, keq. intros. omega.
Qed.

Lemma klt_contradict3 : forall o1 o2, o1 &< o2 -> o1 &= o2 -> False.
Proof.
  unfold klt, keq. intros. omega.
Qed.

Lemma kle_single : forall o1 o2, o1 &<= o2 -> o2 &<= o1 -> o1 &= o2.
Proof.
  unfold kle. intros. destruct H.
    destruct H0.
      generalize (klt_contradict0 o1 o2 H H0). intro h. contradict h.
      apply keq_sym. apply H0.
    apply H.
Qed.

Lemma obj_klt_dec : forall o1 o2, o2 &< o1 -> o2 &= kmin o1 o2.
Proof. unfold klt, kle, kmin.
  intros. case_eq (kle_klt_dec o1 o2).
    intros. generalize (klt_contradict1 o1 o2 k H).
      intro h. contradict h.
    intros. reflexivity.
Qed.

Lemma obj_kle_dec : forall o1 o2, o1 &<= o2 -> o1 &= kmin o1 o2.
Proof. unfold klt, kmin.
  intros. case_eq (kle_klt_dec o1 o2).
    intros. reflexivity.
    intros. unfold kle in H. destruct H.
      generalize (klt_contradict0 o1 o2 H k).
        intro h. contradict h.
      apply keq_sym in H.
        generalize (keq_klt_left o2 o1 o1 H k).
          intro h. contradict h. apply klt_antirefl.
Qed.

Lemma obj_keq_fst_kmin : forall a b, a &= kmin a b -> a &<= b.
Proof.
  intros. unfold kmin in H. case_eq(kle_klt_dec a b).
    intros. apply k.
    intros. rewrite H0 in H. unfold kle. right. apply H.
Qed.

Lemma prod_le : forall a b : prod Z Z, (fst a <= fst b)%Z -> kle a b.
Proof.
  intros. apply triv2 in H. destruct H.
  unfold kle. left. unfold klt. apply H.
  unfold kle. right. unfold keq. apply H.
Qed.

Lemma prod_eq : forall a b : prod Z Z, (fst a = fst b)%Z -> keq a b.
Proof.
  intros. unfold keq. apply H.
Qed.

Lemma prod_lt : forall a b : prod Z Z, (fst a < fst b)%Z -> klt a b.
Proof.
  intros. unfold klt. apply H.
Qed.

Lemma false_surjective_pairing : forall a, (forall x y : Z, a <> (x, y)) -> False.
Proof.
  intros.
  generalize (H (fst a) (snd a)). intros. contradict H0.
  apply surjective_pairing.
Qed.

Lemma kminl2_first : forall l a, a &= kminl2 a l -> a = kminl2 a l.
Proof.
  intro. induction l.
    intros. simpl. reflexivity.
    intros. simpl. (* simpl in H.*)
    unfold kmin. case_eq (kle_klt_dec a0 (kminl2 a l)).
      intros. reflexivity.
      intros. simpl in H.
      generalize (obj_keq_fst_kmin a0 (kminl2 a l) H). intros.
      generalize (klt_contradict1 a0 (kminl2 a l) H1 k). intros.
      contradict H2. 
Qed.

Lemma kminl2_second : forall (h a : Obj) (l : list Obj),
  nil <> l -> kminl2 a l <> a -> kminl2 (hd h l) (tail l) = kminl2 a l.
Proof.
  intros. destruct l. contradict H. reflexivity.
  simpl. simpl in H0. unfold kmin.
  case_eq (kle_klt_dec a (kminl2 o l)).
    intros. unfold kmin in H0. rewrite H1 in H0. contradict H0. reflexivity.
    intros. reflexivity.
Qed.

Lemma obj_eq_kminl2 : forall (z x : prod Z Z) L, z &= kminl2 (hd x L) (tail L)
-> z &= kminl2 z L.
Proof.
  intros. unfold keq in H. destruct L.
    simpl. reflexivity.
    simpl. unfold keq. simpl in H.
      unfold kmin. case_eq (kle_klt_dec z (kminl2 p L)).
      intros. reflexivity.
      intros. apply H.
Qed.

Lemma obj_lt_kminl2 : forall (z x : prod Z Z) L, z &< kminl2 (hd x L) (tail L)
-> z &= kminl2 z L.
Proof.
  intros. (* unfold klt in H.*) destruct L.
    simpl. reflexivity.
    simpl. unfold keq. simpl in H.
      unfold kmin. case_eq (kle_klt_dec z (kminl2 p L)).
      intros. reflexivity.
      intros. generalize (klt_trans z (kminl2 p L) z H k).
        intros. generalize (klt_antirefl z H1). intros. contradict H2.
Qed.

Lemma obj_le_kminl2 : forall (z x : prod Z Z) L, z &<= kminl2 (hd x L) (tail L)
-> z &= kminl2 z L.
Proof.
  intros. unfold kle in H. destruct H.
    apply obj_lt_kminl2 with (x := x). apply H.
    apply obj_eq_kminl2 with (x := x). apply H.
Qed.

Lemma obj_le_kminl2_unfold : forall (z x : prod Z Z) L, (fst z <= fst (kminl2 (hd x L) (tail L))
-> fst z = fst (kminl2 z L))%Z.
Proof.
  intros. apply prod_le in H.
  generalize (obj_le_kminl2 z x L H). intros. apply H0.
Qed.

Lemma obj_gt_kminl2 : forall (z x : prod Z Z) L,
  nil <> L ->
  kminl2 (hd x L) (tail L) &< z ->
  kminl2 (hd x L) (tail L) &= kminl2 z L.
Proof.
  intros. destruct L. contradict H. reflexivity. 
    simpl. unfold keq, kmin. case_eq (kle_klt_dec z (kminl2 p L)).
      intros. simpl in H0. generalize (klt_contradict1 z (kminl2 p L) k H0). intros. contradict H2.
      intros. reflexivity.
Qed.

Lemma obj_gt_kminl2_unfold : (forall (z x : prod Z Z) L,
  nil <> L ->
  fst (kminl2 (hd x L) (tail L)) < fst z ->
  fst (kminl2 (hd x L) (tail L)) = fst (kminl2 z L))%Z.
Proof.
  intros.
  generalize (obj_gt_kminl2 z x L H H0). intro. apply H1.
Qed.

Lemma rewrite_fst_kminl2 : forall (a b : Z) L, fst (a, b) = fst (kminl2 (a, b) L) ->
  a = fst (kminl2 (a, b) L).
Proof. intros. auto.
Qed.

Lemma rewrite_fst_kmin : forall (a b : Z) (z : prod Z Z), fst (a, b) = fst (kmin (a, b) z) ->
  a = fst (kmin (a, b) z).
Proof. intros. auto.
Qed.

Lemma remove_single : forall x y z l, l = remove (x, y) ((x, z) :: l).
Proof.
  intros. simpl. case_eq (keq_dec (x,z) (x,y)).
    intros. reflexivity.
    intros. contradiction n. unfold keq. simpl. reflexivity.
Qed.

Lemma remove_single_obj : forall x l, l = remove x (x :: l).
Proof.
  intros. simpl. case_eq (keq_dec x x).
    intros. reflexivity.
    intros. contradiction n. unfold keq. reflexivity.
Qed.

Lemma remove_cons: forall x y l0 l1, ~y&=x -> l0 = remove x l1 -> remove x (y::l1) = y::l0.
Proof.
  intros. simpl. case_eq (keq_dec y x).
    intros. contradict H. apply k.
    intros. rewrite H0. reflexivity.
Qed.

Lemma first_occ_cons_lt : forall (x y : prod Z Z) (l : list (prod Z Z)),
  (fst x < fst y)%Z -> first_occurrence x l x -> first_occurrence x (y::l) x.
Proof.
  intros. apply first_occurrence_tail. unfold keq. omega.
  apply H0.
Qed.

Lemma first_occ_cons_gt : forall (x y : prod Z Z) (l : list (prod Z Z)),
  (fst x > fst y)%Z -> first_occurrence x l x -> first_occurrence x (y::l) x.
Proof.
  intros. apply first_occurrence_tail. unfold keq. omega.
  apply H0.
Qed.

Lemma cons_remove_perm : forall x l, first_occurrence x l x -> Permutation (x :: remove x l) l.
Proof.
  intros. induction l. inversion H.
  simpl. case_eq(keq_dec a x).
    intros. inversion H. subst. apply Permutation_refl.
      subst. contradict H4. apply keq_sym. apply k.
    intros. inversion H. subst. contradict H5. apply n.
      subst. apply IHl in H6.
      generalize (perm_skip a H6). intros.
      generalize (perm_swap a x (remove x l)). intros.
      generalize (perm_trans H2 H1). intros. apply H3. 
Qed.

Lemma remove_cons_perm : forall (x : Obj) (l0 l1 : list Obj),
  first_occurrence x l0 x ->
  Permutation (remove x l0) l1 -> Permutation l0 (x::l1).
Proof.
  intros.
  generalize (perm_skip x H0 ). intros.
  generalize (cons_remove_perm x l4 H). intros. apply Permutation_sym in H2.
      generalize (perm_trans H2 H1). intros. apply H3. 
Qed.

Lemma first_occ_min : forall (x h : Obj) (l : list Obj),
  first_occurrence x l x ->
  x &= kminl2 (hd h l) (tail l) ->
  x = kminl2 (hd h l) (tail l).
Proof.
  intros.
    induction l. inversion H.
    simpl. simpl in H0.
    case_eq (obj_eq_dec x a).
      intros. rewrite e. rewrite e in H0. apply kminl2_first. apply H0.
      intros. inversion H. contradiction n. symmetry; apply H4.
        subst.
        assert (nil <> l).
          destruct l. inversion H. contradiction n. symmetry; apply H4.
          inversion H9. apply nil_cons.

        assert (kminl2 a l <> a).
          destruct l. contradiction H2. reflexivity.
          simpl; simpl in H0. unfold kmin in H0; unfold kmin.
          case_eq (kle_klt_dec a (kminl2 o l)).
            intros. rewrite H3 in H0. contradict H0. apply H5.
            intros. intro. generalize k; intros. rewrite H4 in k0.
            apply klt_antirefl in k0. contradict k0.

        assert (kminl2 (hd h l) (tail l) = kminl2 a l).
          apply kminl2_second. apply H2. apply H3.

        apply IHl in H7. rewrite H7. apply H4.

        assert (kminl2 (hd h l) (tail l) &= kminl2 a l).
          unfold keq. apply p0 in H4. destruct H4. apply H4.

        apply keq_trans with (b := kminl2 a l).
          apply H0. apply keq_sym. apply H6.
Qed.

Lemma first_occ_min_simpl : forall (h : Z * Z) (v : Z) (l : list (Z * Z)),
  first_occurrence (fst(kminl2 (hd h l) (tail l)),v) l (fst(kminl2 (hd h l) (tail l)),v) ->
  (fst(kminl2 (hd h l) (tail l)),v) = kminl2 (hd h l) (tail l).
Proof.
  intros. apply first_occ_min. apply H. unfold keq. simpl. reflexivity.
Qed.

Lemma list_min_remove_cons : forall (l : list Obj) (x h : Obj),
  x = kminl2 h l ->
  x :: selsort (remove x (h::l)) = selsort (h::l).
Proof.
  intros. unfold selsort. simpl. rewrite <- H.
  case_eq (keq_dec h x).
    intros. reflexivity.
    intros. destruct l.
      simpl in H. contradiction n. rewrite H. apply keq_refl.

  generalize (remove_length2 o l). intros.
  assert (nil <> o::l).
    apply nil_cons.
  assert (kminl2 h (o::l) <> h).
    intro. contradiction n. unfold keq. rewrite H. rewrite H3. reflexivity.
  generalize(kminl2_second h h (o::l) H2 H3). intros.
  simpl in H4. simpl in H. rewrite <- H in H4. rewrite H4 in H1.
  rewrite H1. reflexivity.
Qed.

Lemma list_min_remove_cons_simpl : forall (l : list Obj) (h : Obj),
  (kminl2 h l) :: selsort (remove (kminl2 h l) (h::l)) = selsort (h::l).
Proof.
  intros. apply list_min_remove_cons. reflexivity.
Qed.

Lemma equal_lengths : forall L0 L1 : list (prod Z Z), L0 = L1 -> length L0 = length L1.
Proof. intros. rewrite H. auto. Qed.

Lemma singleton_list_occurrence : forall (L0 L1 : list (prod Z Z)) (a b : (prod Z Z)),
 a :: nil = L0 ++ b :: L1 ->
 L0 = nil /\ L1 = nil /\ a = b.
Proof.
  intros.
  assert (L0 = nil /\ L1 = nil).
    apply equal_lengths in H. rewrite app_length in H. simpl in H.
    split.
      destruct L0. auto.
        simpl in H. contradict H. omega.
      destruct L1. auto.
        simpl in H. contradict H. omega.

  destruct H0. subst. simpl in H. inversion H.
  split. auto. split. auto. split.
Qed.


(***************************)
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
Lemma lkl : forall l : list Obj, nil = l \/ nil <> l.
Proof.
  intros. destruct l. left. reflexivity.
  right. auto. apply nil_cons.
Qed.

Lemma lkl2 : forall l : list Obj,
  nil = l \/
  exists o, o :: nil = l \/
  exists m, o::m = l /\ nil <> m.
Proof.
  intros. destruct l. left. reflexivity.
  right. exists o. destruct l. 
    left. reflexivity.
    right. exists (o0 :: l). split.
      reflexivity.
      apply nil_cons.
Qed.

Ltac destruct_once :=
  match goal with
    | H: (list (Z*Z)) |- context[hd ?h ?L] =>
(*          let A := L in
            destruct A *)
           generalize (lkl2 L); intros
    | _ => intros
  end.

Ltac sim :=
  match goal with
    | |- context [?x &= ?x] => apply keq_refl
    | |- context [fst ?a = fst ?b] => apply fold_keq

    | |- context [(?a + ?b = ?b + ?a)%Z] => apply plus_int_comm


(*    | |- context [kminl2 ?x ?L] => simpl in |- * *)
    | |- context [?o2 &= kmin ?o1 ?o2] => apply obj_klt_dec
    | |- context [?o1 &= kmin ?o1 ?o2] => apply obj_kle_dec

    | |- context [stable ?l (selsort ?l)] => apply selsort_stable
(*    | H: (?x &< ?y) |- (?x &= kmin ?y ?x) => apply kmin_trans
    | H: ((fst ?x < fst ?y)%Z) |- (fst ?x = fst (kmin ?y ?x)) => apply kmin_trans*)
    | H: ((fst ?x < ?y1)%Z) |- (fst ?x = fst (kmin (?y1, ?y2) ?x)) => apply kmin_trans
    | H: ((fst ?x <= fst ?y)%Z) |- (fst ?x = fst (kmin ?x ?y)) => apply kmin_trans_2
    | H: ((?x1 <= fst ?y)%Z) |- (fst (?x1, ?x2) = fst (kmin (?x1, ?x2) ?y)) => apply kmin_trans_2

    | |- context [fst ?x = fst ?y] => try (apply obj_gt_kminl2) (*hotfix ToDo: think how to generalize this case*)

    | |- (sorted nil) => apply sorted_nil
    | |- (sorted (?x::nil)) => apply sorted_singleton
    | H0: (?x &<= ?y), H1: (sorted (?y::?l)) |- (sorted (?x::?y::?l)) => apply sorted_cons
    | H0: (?x &< ?y), H1: (sorted (?y::?l)) |- (sorted (?x::?y::?l)) => apply sorted_cons
    | H0: (?x &= ?y), H1: (sorted (?y::?l)) |- (sorted (?x::?y::?l)) => apply sorted_cons
    | H0: (?x1 <= ?y1), H1: (sorted ((?y1,?y2)::?l)) |- (sorted ((?x1,?x2)::(?y1,?y2)::?l)) => apply sorted_cons
    | H0: (?x1 < ?y1), H1: (sorted ((?y1,?y2)::?l)) |- (sorted ((?x1,?x2)::(?y1,?y2)::?l)) => apply sorted_cons
    | H0: (?x1 = ?y1), H1: (sorted ((?y1,?y2)::?l)) |- (sorted ((?x1,?x2)::(?y1,?y2)::?l)) => apply sorted_cons

    | H: (?x = kminl2 ?h ?l) |- (?x :: selsort (remove ?x (?h::?l)) = selsort (?h::?l)) => apply list_min_remove_cons

    | |- context [?a%Z = fst (kmin (?a%Z, ?b%Z) ?z)] => apply rewrite_fst_kmin
    | |- context [?a%Z = fst (kminl2 (?a%Z, ?b%Z) ?L)] => apply rewrite_fst_kminl2

    | |- context [?a &<= ?b] => apply prod_le

    | |- context [0 < S ?m] => apply l13
    | |- context [0 < 1 + ?m] => simpl; apply l13

    | |- context [?l = remove (?x, ?y) ((?x, ?z) :: ?l)] => apply remove_single

    | H0: (~?y&=?x), H1: (?l0 = remove ?x ?l1)
      |- (remove ?x (?y::?l1) = ?y::?l0) => apply remove_cons
    | H0: (?y1<>?x1), H1: (?l0 = remove (?x1,?x2) ?l1)
      |- (remove (?x1,?x2) ((?y1,?y2)::?l1) = (?y1,?y2)::?l0) => apply remove_cons

    | |- context [first_occurrence ?x (?x::?l) ?x] => apply first_occurrence_head

    | H0: ((?x1 < ?y1)%Z) , H1: (first_occurrence (?x1,?x2) ?l (?x1,?x2))
      |- context [first_occurrence (?x1,?x2) ((?y1,?y2)::?l) (?x1,?x2)] => apply first_occ_cons_lt

    | H0: ((?x1 > ?y1)%Z) , H1: (first_occurrence (?x1,?x2) ?l (?x1,?x2))
      |- context [first_occurrence (?x1,?x2) ((?y1,?y2)::?l) (?x1,?x2)] => apply first_occ_cons_gt

    | H0: (first_occurrence ?x ?l0 ?x) , H1: (Permutation (remove ?x ?l0) ?l1)
      |- (Permutation ?l0 (?x::?l1)) => apply remove_cons_perm

    | |- context [length (?x :: ?L)] => try (rewrite simpl_length_cons in |- *);auto
    | |- context [(0 < Z_of_nat (1 + ?n))%Z] => apply z_of_nat_inc

    | |- context [_ :: _ = nil] => rewrite cons_eq_nil in |- *
    | |- context [nil = _ :: _] => rewrite nil_eq_cons in |- *
    | |- context [?x :: _ = ?x :: _] => rewrite cons_eq_cons in |- *
    | |- context [rev (?L ++ ?x :: (@nil Obj))] => rewrite rev_unit in |- *
    | |- context [(?L1 ++ ?L2) ++ ?L3] => rewrite app_ass in |- *
    | |- context [(?x :: ?L1) ++ ?L2] => rewrite simpl_x_cons_app in |- *
    | |- context [?L ++ nil] => rewrite simpl_app_nil in |- *
    | |- context [nil ++ ?L] => rewrite simpl_nil_app in |- *
    | |- context [?L1 ++ ?L2 = (@nil Obj)] => rewrite list_app_eq_nil in |- *
    | |- context [nil = ?L1 ++ ?L2] => rewrite nil_eq_list_app in |- *
(*    | |- context [hd obj1 (?x :: ?L)] => rewrite simpl_head_cons in |- **)
    | |- context [tail (@nil Obj)] => rewrite simpl_tail_nil in |- *
    | |- context [tail (?x :: ?L)] => rewrite simpl_tail_cons in |- *
    | |- context [length nil] => rewrite simpl_length_nil in |- *
(*    | |- context [length (?x :: ?L)] => rewrite simpl_length_cons in |- * *)
    | |- context [length (?L1 ++ ?L2)] => rewrite app_length in |- *
    | |- context [length (rev ?L)] => rewrite rev_length in |- *
    | |- context [rev nil] => rewrite simpl_rev_nil in |- *
    | |- context [rev (?x :: ?L)] => rewrite simpl_rev_cons in |- *
    | |- context [rev (?L1 ++ ?L2)] => rewrite distr_rev in |- *
    | |- context [rev (rev ?L)] => rewrite rev_involutive in |- *
    | |- context [Z_of_nat 0] => simpl (Z_of_nat 0) in |- * (* rewrite inj_0 in |- * *)
    | |- context [Z_of_nat (S ?n)] => simpl (Z_of_nat (S n)) in |- * (* rewrite inj_S in |- * *)
(*    | |- context [0 < Z_of_nat (1 + ?n)] => apply z_of_nat_inc *)

    | |- ((Z_of_nat ?x <= Z_of_nat ?y)%Z) => apply z_of_nat_le_inj
    | |- ((Z_of_nat ?x < Z_of_nat ?y)%Z) => apply z_of_nat_lt_inj
    | |- ((Z_of_nat ?x = Z_of_nat ?y)%Z) => apply z_of_nat_eq_inj

    | |- context [Z_of_nat (?x1 + ?x2)] => rewrite inj_plus in |- *
    | |- context [In ?x (?y :: ?L)] => rewrite in_x_cons in |- *
    | |- context [alln (?x :: ?L) ?n] => rewrite alln_cons in |- *
    | |- context [alln (?L1 ++ ?L2) ?n] => rewrite alln_app in |- *
    | |- context [alln (rev ?L) ?n] => rewrite alln_rev in |- *

(*    | H: context [fst ?a <= fst ?b] |- _ => apply prod_le in H
    | H: context [fst ?a < fst ?b] |- _ => apply prod_lt in H
    | H: context [fst ?a = fst ?b] |- _ => apply prod_eq in H
*)

    | |- context[(?a + (?b + ?c))%Z] => rewrite plus_right_assoc
    | |- context[((?a + ?b) + ?c)%Z] => rewrite plus_left_assoc

    | H: context[(?a + ?b + ?c)%Z] |- context[(?a + ?c + ?b)%Z] => try(rewrite triple_comm_right; auto)
    | H: context[(?a + ?b + ?c)%Z] |- context[(?b + ?a + ?c)%Z] => try(rewrite triple_comm_left; auto)
    | H: context[(?a + ?b + ?c)%Z] |- context[(?c + ?b + ?a)%Z] => try(rewrite triple_comm_center; auto)

    | |- ((?a + ?c = ?b + ?c)%Z) => apply plus_eq_surj_right
    | |- ((?c + ?a = ?c + ?b)%Z) => apply plus_eq_surj_left
    | |- ((?a + ?c = ?c + ?b)%Z) => apply plus_eq_surj_com_in
    | |- ((?c + ?a = ?b + ?c)%Z) => apply plus_eq_surj_com_out
    | |- ((?a + ?c < ?b + ?c)%Z) => apply plus_lt_surj_right
    | |- ((?c + ?a < ?c + ?b)%Z) => apply plus_lt_surj_left
    | |- ((?a + ?c < ?c + ?b)%Z) => apply plus_lt_surj_com_in
    | |- ((?c + ?a < ?b + ?c)%Z) => apply plus_lt_surj_com_out

    | |- context [(0 + ?m)%Z] => rewrite plus_zero_left
    | |- context [(?m + 0)%Z] => rewrite plus_zero_right

    | H: context [?P -> ?Q] |- context [?Q] => apply H
    | H: context [Z*Z -> Z*Z -> _] |- _ => generalize (H (0%Z, 0%Z)); intros; clear H
    | H: (forall x y : Z, ?a <> (x, y)) |- _ => apply false_surjective_pairing in H

    | H: ((?a + ?c = ?b + ?c)%Z) |- _ => apply plus_eq_inj_right in H
    | H: ((?c + ?a = ?c + ?b)%Z) |- _ => apply plus_eq_inj_left in H
    | H: ((?a + ?c = ?c + ?b)%Z) |- _ => apply plus_eq_inj_com_in in H
    | H: ((?c + ?a = ?b + ?c)%Z) |- _ => apply plus_eq_inj_com_out in H
    | H: ((?a + ?c < ?b + ?c)%Z) |- _ => apply plus_lt_inj_right in H
    | H: ((?c + ?a < ?c + ?b)%Z) |- _ => apply plus_lt_inj_left in H
    | H: ((?a + ?c < ?c + ?b)%Z) |- _ => apply plus_lt_inj_com_in in H
    | H: ((?c + ?a < ?b + ?c)%Z) |- _ => apply plus_lt_inj_com_out in H

    | H: ((Z_of_nat ?x <= Z_of_nat ?y)%Z) |- _ => apply z_of_nat_le_surj in H
    | H: ((Z_of_nat ?x < Z_of_nat ?y)%Z) |- _ => apply z_of_nat_lt_surj in H
    | H: ((Z_of_nat ?x = Z_of_nat ?y)%Z) |- _ => apply z_of_nat_eq_surj in H

    | H: context [(0 + ?m)%Z] |- _ => rewrite plus_zero_left in H
    | H: context [(?m + 0)%Z] |- _ => rewrite plus_zero_right in H

    | H: context [(1 + Z_of_nat (length ?l))%Z = 0%Z] |- _ => apply length_null_contr in H
    | H: context [Z_of_nat (?x1 + ?x2)] |- _ => rewrite inj_plus in H
    | H: context [Z_of_nat 0] |- _ => simpl (Z_of_nat 0) in H (* rewrite inj_0 in H *)
    | H: context [Z_of_nat (S ?n)] |- _ => simpl (Z_of_nat (S n)) in H (* rewrite inj_S in H *)

    | H: (_ :: _ = nil) |- _ => rewrite cons_eq_nil in H; contradict H (* Qed *)
    | H: (nil = _ :: _) |- _ => rewrite nil_eq_cons in H; contradict H (* Qed *)

    | H: context [?L ++ nil] |- _ => rewrite simpl_app_nil in H
    | H: context [nil ++ ?L] |- _ => rewrite simpl_nil_app in H

    | H0: (?a :: ?L0 = ?L1 ++ ?b :: ?L2), H1: (~In ?b ?L1)
      |- _ => (*let L := L1 in*) destruct L1; simpl in H0
    | H0: (?L1 ++ ?b :: ?L2 = ?a :: ?L0), H1: (~In ?b ?L1)
      |- _ => (*let L := L1 in*) destruct L1; simpl in H0

    | H: context [?x :: _ = ?x :: _] |- _ => rewrite cons_eq_cons in H
    | H: context [_ :: ?l = _ :: ?l] |- _ => apply head_eq in H
    | H: context [_ :: _ = _ :: _] |- _ => apply cons_subst in H; destruct H; subst

    | H: context [?a :: nil = ?L0 ++ ?b :: ?L1] |- _ => apply singleton_list_occurrence in H
    | H: context [?L0 ++ ?b :: ?L1 = ?a :: nil] |- _ => symmetry in H; apply singleton_list_occurrence in H
    | H: context [rev (?L ++ ?x :: nil)] |- _ => rewrite rev_unit in H
    | H: context [(?L1 ++ ?L2) ++ ?L3] |- _ => rewrite app_ass in H
    | H: context [(?x :: ?L1) ++ ?L2] |- _ => rewrite simpl_x_cons_app in H
    | H: context [?L1 ++ ?L2 = nil] |- _ => rewrite list_app_eq_nil in H
    | H: context [nil = ?L1 ++ ?L2] |- _ => rewrite nil_eq_list_app in H
 (*   | H: context [hd obj1 (?x :: ?L)] |- _ => rewrite simpl_head_cons in H*)
    | H: context [tail (@nil Obj)] |- _ => rewrite simpl_tail_nil in H
    | H: context [tail (?x :: ?L)] |- _ => rewrite simpl_tail_cons in H
    | H: context [length nil] |- _ => rewrite simpl_length_nil in H 
    | H: context [length (?x :: ?L)] |- _ => rewrite simpl_length_cons in H
    | H: context [length (?L1 ++ ?L2)] |- _ => rewrite app_length in H
    | H: context [length (rev ?L)] |- _ => rewrite rev_length in H
    | H: context [rev nil] |- _ => rewrite simpl_rev_nil in H
    | H: context [rev (?x :: ?L)] |- _ => rewrite simpl_rev_cons in H
    | H: context [rev (?L1 ++ ?L2)] |- _ => rewrite distr_rev in H
    | H: context [rev (rev ?L)] |- _ => rewrite rev_involutive in H
    | H: context [In ?x (?y :: ?L)] |- _ => rewrite in_x_cons in H
    | H: context [alln (?x :: ?L) ?n] |- _ => rewrite alln_cons in H
    | H: context [alln (?L1 ++ ?L2) ?n] |- _ => rewrite alln_app in H
    | H: context [alln (rev ?L) ?n] |- _ => rewrite alln_rev in H

    | H: context [(1 + ?m = 0)%Z] |- _ => apply l11 in H
    | H: context [(S ?m = 0)%nat] |- _ => apply l12 in H
    | H: context [(1 + ?m = S ?n)%nat] |- _ => apply l9 in H
    | H: context [(S ?m = S ?n)%nat] |- _ => apply l10 in H

    | H: context [(?i, ?j) = (?k, ?l)] |- _ => apply p0 in H; simpl in H
    | H: context [(?i%Z, ?j%Z) <> (?k%Z, ?l%Z)] |- _ => apply p1 in H; simpl in H
    | H: context [?n < ?n] |- _ => apply l7 in H
    | H: context [0 > 1 + ?n] |- _ => apply l8 in H
    | H: context [?L = ?x :: ?L1] |- _ => subst
    | H: context [length (?x :: ?L) = 1] |- _ => apply l2 in H
    | H: context [Z_of_nat(length ?L) = 0%Z] |- _ => apply l3 in H

    | H: context [?P] |- context [?P] => apply H
    | H: context [?x <> ?x] |- _ => contradict H

    | H: context [first_occurrence ?x nil ?x] |- _ => inversion H
(*    | H: context [first_occurrence (?x1,?x2) ((?x1,?x3)::nil) (?x1,?x2)] |- _ => inversion H; subst *)
    | H: context [first_occurrence (?x1,?x2) ((?y1,?y2)::nil) (?x1,?x2)],
      H1: context[?x1<>?y1] |-_ => inversion H; subst
    | H: context [first_occurrence (?x1,?x2) ((?y1,?y2)::nil) (?x1,?x2)],
      H1: context[?y1<>?x1] |-_ => inversion H; subst

    | H: context [first_occurrence (?x1,?x2) ((?y1,?y2)::?l) (?x1,?x2)]
        |- context [first_occurrence (?x1,?x2) ?l (?x1,?x2)] => inversion H; subst
end.

(* ------------------------------------------------------------------------------------------------------------ *)

Ltac hyp :=
  match goal with
(*
  | H: context [hd 0%Z (@nil Z)] |- _ => admit
*)
  | |- ~ ?X => intro
  | |- forall Obj : _, _=> intro
  | H : exists Obj : _, _ |- _ => destruct H
  
  | H : ?Obj /\ ?B |- _ => destruct H
  | H : ?Obj \/ ?B |- _ => destruct H

  | |- ?Obj /\ ?B => split
  | |- ?Obj \/ ?B => try solve [ left; solve_all | right; solve_all ]; elimtype False

end

with solve_exists :=
  match goal with
    | |- context [ ex _ ] => repeat eexists; solve_all; instantiate
    | _ => idtac
end

with solve_existx :=
  match goal with
    | |- context [ ex _ ] => eexists; solve_existx
    | _ => solve_all; try(instantiate)
end

with hd_cases :=
  match goal with
    | H: context [Z*Z -> _] |- False =>
          generalize (H (0%Z, 0%Z)); intros; clear H
    | H: context [Z*Z -> _] |- context[hd ?y ?L] =>
       let ex := y in
          generalize (H ex); intros; clear H
    | H: context [Z*Z -> _] |- (?x = fst ?y) =>
       let ex := y in
          generalize (H ex); intros; clear H
    | H: context [Z*Z -> _] |- context[?x%Z = fst ?p] => try (generalize (H (0%Z, 0%Z)); intros; clear H)

    | |- context [kminl2 (hd ?x ?L) (tail ?L) &= kminl2 ?z ?L2] => apply obj_gt_kminl2                 
    | |- context [fst(kminl2 (hd ?x ?L) (tail ?L)) = fst(kminl2 ?z ?L2)] => apply obj_gt_kminl2


 (*   | H: context [hd ?x ?L](* H1 : context [_ &<= _]*)|- context[?z &= _] =>
       let ex := x 
       with ez := z
       with eL := L in
       generalize (obj_le_kminl2 ez ex eL); intros

    | H: context [hd ?x ?L](*, H1 : context [_ <= _]*)|- context[fst ?z = fst ?km] =>
       let ex := x 
       with ez := z
       with eL := L in
       generalize (obj_le_kminl2 ez ex eL);(* unfold kle, keq, klt; simpl;*) intros
*)
    | H: context [Z*Z -> _] |- _ =>
          generalize (H (0%Z, 0%Z)); intros; clear H (*possibly will lead to infinite loops*)
    | _ => intros
  end

with selsort_cases :=
 match goal with
    | |- (stable ?l (selsort ?l)) => apply selsort_stable
    | |- (stable (?p::?l) (selsort (?p::?l))) => apply selsort_stable

    | H0: (first_occurrence (fst(kminl2 (hd ?h (?o::?l)) (tail (?o::?l))),?v) (?o::?l) 
                            (fst(kminl2 (hd ?h (?o::?l)) (tail (?o::?l))),?v))
      |- _ => apply first_occ_min_simpl in H0; rewrite H0 

    | H0: (first_occurrence (fst (kminl2 ?h ?l1),?x2) nil (fst (kminl2 ?h ?l1),?x2))
      |- _ => inversion H0

    | |- context[(kminl2 (hd ?h (?o::?l)) (tail (?o::?l))) :: selsort (remove (kminl2 (hd ?h (?o::?l)) (tail (?o::?l)) ) (?o::?l))] (* = selsort (?o::?l))*) =>
       rewrite list_min_remove_cons_simpl

    | H0: (first_occurrence (fst (kminl2 ?h ?l1),?x2) ?l (fst (kminl2 ?h ?l1),?x2))
      |- context[?x :: selsort (remove (fst (kminl2 ?h ?l1),?x2) ?l)] =>
              let eL := l in
        destruct eL

    | H0: (first_occurrence ?x ?l ?x), H1: (?x &= kminl2 (hd ?h ?l) (tail ?l))
      |- _ => let  eX := x
              with eH := h
              with eL := l in
        generalize (first_occ_min eX eH eL H0 H1);simpl;intros

    | H0: (first_occurrence (?x1, ?x2) ?l (?x1, ?x2)), H1: (?x1 = fst (kminl2 (hd ?h ?l) (tail ?l)))
      |- _ => let  eX1 := x1
              with eX2 := x2
              with eH  := h
              with eL  := l in
        generalize (first_occ_min (eX1, eX2) eH eL H0 H1);simpl;intros
    | _ => auto
end

with solve_all := repeat
  (repeat hyp; repeat sim;
     repeat (hd_cases; repeat hyp; subst);
     repeat selsort_cases; repeat sim; try(omega); subst; simpl);
  simpl; auto with *

with decidez := intros; destruct_once; solve_exists; solve_all; elimtype False; auto with *

with decidex := intros; destruct_once; solve_all; solve_existx; solve_all; elimtype False; auto.

(*Module smth := STSORT ZZ.
Import smth.
Print False.

Ltac d1 :=
 match goal with
    | H0: (?a :: ?L0 = ?L1 ++ ?b :: ?L2), H1: (~In ?b ?L1)
      |- _ => (*let L := L1 in*) destruct L1 
    | _ => auto
end.

Lemma test35 : (forall r_214: Z, forall L_218: list (prod Z Z), forall L1_216: list (prod Z Z), forall L2_217: list (prod Z Z), forall v_213: Z, forall L2_215: list (prod Z Z), forall a: Z, (((((((r_214=0) /\ (L2_215=(@nil (prod Z Z)))) \/  (exists L2_246:list (prod Z Z), (exists v_247:Z,((r_214<>0) /\ (L2_215=((v_247, v_247) :: L2_246)))) ) ) /\ (L_218=((v_213, v_213) :: L2_215))) /\ ( (not (In (a, a) L1_216)))) /\ (L_218=(L1_216 ++ ((a, a) :: L2_217)))) /\ (v_213<>a)) ->  (exists L1_244:list (prod Z Z), (exists L2_245:list (prod Z Z),(( (not (In (a, a) L1_244))) /\ (L2_215=(L1_244 ++ ((a, a) :: L2_245))))) ) )%Z.
Proof. intros. decidex. intros. destruct_once. solve_all. solve_existx. solve_all. eexists;eexists. decidez.
repeat hyp.
  (*eexists; eexists.*) elimtype False. decidez.
  repeat sim. (*
    eexists; eexists.*) elimtype False. decidez.
      eexists; eexists. decidez.
(* elimtype False. decidez. decidez. *)
  repeat sim. eexists. eexists.  decidez.
eexists. eexists. 
 decidez. d1; simpl in H1. d1.
    elimtype False. decidez.
    decidez.


destruct L1_216. elimtype False. decidez. (* decidez.*)
 simpl in H1. inversion H1. rewrite in_x_cons in H2.
eexists. eexists.
split.
intro.
apply H2.
right.
revert H3.
instantiate (1:=L1_216).
auto.
instantiate (1:=L2_217).
assumption.

Goal exists x:Z, exists y:Z, y = y.
eexists.
exact (0%Z).
eexists.
instantiate (1:=0%Z).
reflexivity.

 decidez.

eexists. eexists. (* L1_216. eexists L2_217.
*)
Lemma de_morgan_01: forall P Q, ~ (P \/ Q) -> ~P /\ ~Q.
Proof. auto. Qed.

apply de_morgan_01 in H2; destruct H2.
split. apply H3.
exact H5.

exists L1_216. exists L2_217.



apply equal_lengths in H1. rewrite app_length in H1. simpl in H1. 
assert (length ())


unfold app in H1.
 inversion H1.
exists L1_216.
 decidez. repeat sim. sim. sim. sim. decidez.
contradict H0.  d1. decidez. d1. generalize (H0 (fst r_238) (snd r_238)). intros.
contradict H0.
 repeat sim. subst.
 decidez. decidez.



apply false_surjective_pairing in H. decidez.

rewrite inj_plus. rewrite inj_plus. rewrite inj_plus.
simpl in H4. rewrite <- inj_plus in H4.

 sim. repeat sim. decidez.
 simpl (Z_of_nat 1) in H4. rewrite H4.
auto. decidez.



Lemma test40 : 
(forall L1: list (prod Z Z), 
  forall a: Z, forall L2_215: list (prod Z Z), 
     forall r_214: (prod Z Z), ((( (keyIn a L1)) /\ 
       (L1=((a, a) (*3*) :: L2_215))) /\ (((forall x y, r_214=(x, y)) /\ 
         (L2_215=(@nil (prod Z Z)))) \/  
         (exists L2_239:list (prod Z Z), (exists v_240:Z,(((forall x y, r_214<>(x, y))) /\ (L2_215=((v_240, v_240) (*3*) :: L2_239)))) ) )) -> ((r_214=(0, 0))))%Z.

Proof. intros.
repeat hyp. auto.
elimtype False.
apply (H0 (fst r_214) (snd r_214)).
rewrite <- surjective_pairing.
SearchAbout (fst _ , snd _).

Check in_x_cons.
decidez. auto.

Proof.
repeat hyp. auto. rewrite H. d1.

*)
