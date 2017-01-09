Require Import Omega.
Require Import Bool.
Require Import FunctionalExtensionality.

(* Abstract Variable Type *)
Module Type VARIABLE.
  Parameter var        : Type.
  Parameter var_eq_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
End VARIABLE.

(* Semantic Value Type *)
Module Type SEM_VAL.
  Parameter Val : Set.
  Parameter val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
  Parameter truth_and : Val -> Val -> Val.
  Parameter truth_or : Val -> Val -> Val.
  Parameter truth_not : Val -> Val.
  Parameter Top : Val.
  Parameter Btm : Val.
  Axiom top_neq_btm : Top <> Btm.
  Axiom truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Axiom truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Axiom truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Axiom truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Axiom truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top -> v1 = Top \/ v2 = Top.
  Axiom truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top -> v1 = Top /\ v2 = Top.
  Axiom truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm -> v1 = Btm /\ v2 = Btm.
  Axiom truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm -> v1 = Btm \/ v2 = Btm.
  Axiom tautology_1 : truth_not Btm = Top.
  Axiom tautology_2 : truth_not Top = Btm.
  Axiom tautology_3 : forall v, truth_and v v = v.
  Axiom tautology_4 : truth_and Top Btm = Btm.
  Axiom tautology_5 : forall v, truth_or v v = v.
  Axiom tautology_6 : truth_or Top Btm = Top.
End SEM_VAL.

Module Three_Val <: SEM_VAL.

  Inductive Val_Impl := VTrue | VFalse | VUnknown.
  Definition Val := Val_Impl.

  Definition val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
    intros; destruct v1, v2; intuition; right; intro; inversion H.
  Defined.

  Definition Top := VTrue.
  Definition Btm := VFalse.

  Lemma top_neq_btm: Top <> Btm.
  Proof. intro; inversion H. Qed.

  Definition truth_and (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue    , VTrue    => VTrue
      | VTrue    , VUnknown => VUnknown
      | VTrue    , VFalse   => VFalse
      | VUnknown , VTrue    => VUnknown
      | VUnknown , VUnknown => VUnknown
      | VUnknown , VFalse   => VFalse
      | VFalse   , _        => VFalse
    end.

  Definition truth_or (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue    , _        => VTrue
      | VUnknown , VTrue    => VTrue
      | VUnknown , VUnknown => VUnknown
      | VUnknown , VFalse   => VUnknown
      | VFalse   , VTrue    => VTrue
      | VFalse   , VUnknown => VUnknown
      | VFalse   , VFalse   => VFalse
    end.

  Definition truth_not v :=
    match v with
      | VTrue    => VFalse
      | VUnknown => VUnknown
      | VFalse   => VTrue
    end.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top -> v1 = Top \/ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top -> v1 = Top /\ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm -> v1 = Btm /\ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm -> v1 = Btm \/ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma tautology_1 : truth_not Btm = Top. Proof. intuition. Qed.
  Lemma tautology_2 : truth_not Top = Btm. Proof. intuition. Qed.
  Lemma tautology_3 : forall v, truth_and v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_4 : truth_and Top Btm = Btm. Proof. intuition. Qed.
  Lemma tautology_5 : forall v, truth_or v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_6 : truth_or Top Btm = Top. Proof. intuition. Qed.

End Three_Val.

Module Three_Val_NoneError <: SEM_VAL.

  Inductive Val_Impl := VTrue | VFalse | VError.
  Definition Val := Val_Impl.

  Definition val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
    intros; destruct v1, v2; intuition; right; intro; inversion H.
  Defined.

  Definition Top := VTrue.
  Definition Btm := VFalse.

  Lemma top_neq_btm: Top <> Btm.
  Proof. intro; inversion H. Qed.

  Definition truth_not v :=
    match v with
      | VTrue  => VFalse
      | VError => VError
      | VFalse => VTrue
    end.

  Definition truth_and (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue  , VTrue  => VTrue
      | VTrue  , VError => VError
      | VTrue  , VFalse => VFalse
      | VError , _      => VError
      | VFalse , VError => VError
      | VFalse , VFalse => VFalse
      | VFalse , VTrue  => VFalse
    end.

  Definition truth_or (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue  , VFalse => VTrue
      | VTrue  , VTrue  => VTrue
      | VTrue  , VError => VError
      | VError , _      => VError
      | VFalse , VTrue  => VTrue
      | VFalse , VError => VError
      | VFalse , VFalse => VFalse
    end.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top -> v1 = Top \/ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top -> v1 = Top /\ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm -> v1 = Btm /\ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm -> v1 = Btm \/ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma tautology_1 : truth_not Btm = Top. Proof. intuition. Qed.
  Lemma tautology_2 : truth_not Top = Btm. Proof. intuition. Qed.
  Lemma tautology_3 : forall v, truth_and v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_4 : truth_and Top Btm = Btm. Proof. intuition. Qed.
  Lemma tautology_5 : forall v, truth_or v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_6 : truth_or Top Btm = Top. Proof. intuition. Qed.
End Three_Val_NoneError.

Module Bool_Val <: SEM_VAL.
  Definition Val := bool.
  Definition truth_and := andb.
  Definition truth_or := orb.
  Definition truth_not := negb.
  Definition Top := true.
  Definition Btm := false.
  Definition val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
    intros; destruct v1, v2; intuition; right; intro; inversion H.
  Defined.

  Lemma top_neq_btm: Top <> Btm. Proof. intro; inversion H. Qed.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top -> v1 = Top \/ v2 = Top.
  Proof. intros; simpl; apply orb_true_iff in H; intuition. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top -> v1 = Top /\ v2 = Top.
  Proof. intros; simpl; apply andb_true_iff in H; intuition. Qed.

  Lemma truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm -> v1 = Btm /\ v2 = Btm.
  Proof. intros; simpl; apply orb_false_iff in H; intuition. Qed.

  Lemma truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm -> v1 = Btm \/ v2 = Btm.
  Proof. intros; simpl; apply andb_false_iff in H; intuition. Qed.

  Lemma tautology_1 : truth_not Btm = Top. Proof. intuition. Qed.
  Lemma tautology_2 : truth_not Top = Btm. Proof. intuition. Qed.
  Lemma tautology_3 : forall v, truth_and v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_4 : truth_and Top Btm = Btm. Proof. intuition. Qed.
  Lemma tautology_5 : forall v, truth_or v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_6 : truth_or Top Btm = Top. Proof. intuition. Qed.

End Bool_Val.

Module Type NUMBER.
  Parameter A          : Type.
  Parameter Const0     : A.
  Parameter num_eq_dec : forall n1 n2 : A, {n1 = n2} + {n1 <> n2}.
  Parameter num_neg    : A -> A.
  Parameter num_plus   : A -> A -> A.
End NUMBER.

(* Pure Integer including Infinity *)
Module ZInfinity <: NUMBER.

  Inductive ZE : Type :=
  | ZE_Fin     : Z -> ZE
  | ZE_Inf     : ZE
  | ZE_NegInf  : ZE.

  Definition ZE_eq_dec : forall ze1 ze2 : ZE, {ze1 = ze2} + {ze1 <> ze2}.
  Proof.
    destruct ze1; destruct ze2; auto; try (right; intro; discriminate).
    destruct (Z_eq_dec z z0). left; congruence.
    right; congruence.
  Defined.

  (* Negation with Infinity *)
  Definition ZEneg (ze : ZE) : ZE :=
    match ze with
        ZE_Fin z  => ZE_Fin (- z)
      | ZE_Inf    => ZE_NegInf
      | ZE_NegInf => ZE_Inf
    end.

  Definition A := option ZE.
  Definition Const0 := Some (ZE_Fin 0).

  Definition num_eq_dec : forall n1 n2 : A, {n1 = n2} + {n1 <> n2}.
  Proof.
    intros. destruct n1, n2; auto.
    destruct (ZE_eq_dec z z0).
    left; f_equal; auto.
    right; congruence.
    right; congruence.
    right; congruence.
  Defined.

  Definition num_neg := option_map ZEneg.

  (* Addition with Infinity *)
  Definition num_plus (ze1 ze2 : option ZE) : option ZE :=
    match ze1, ze2 with
      | None, _
      | _, None
      | Some ZE_Inf, Some ZE_NegInf
      | Some ZE_NegInf, Some ZE_Inf        => None
      | Some ZE_Inf, _
      | _, Some ZE_Inf                     => Some ZE_Inf
      | Some ZE_NegInf, _
      | _, Some ZE_NegInf                  => Some ZE_NegInf
      | Some (ZE_Fin z1), Some (ZE_Fin z2) => Some (ZE_Fin (z1 + z2))
    end.

  (* If sum is finite, then both addend and augend are finite. *)
  Lemma numplus_finite : forall v1 v2 z, num_plus v1 v2 = Some (ZE_Fin z)
                                         -> exists z1 z2, (v1 = Some (ZE_Fin z1)) /\
                                                          (v2 = Some (ZE_Fin z2)) /\
                                                          (z1 + z2 = z)%Z.
  Proof.
    intros until z.
    destruct v1, v2; intros; try discriminate H.
    destruct z0, z1; try discriminate H.
    exists z0, z1; simpl in *.
    split; auto.
    split; auto.
    injection H; auto.
    destruct z0; discriminate H.
  Qed.

  (* If negation is finite, then the original is finite. *)
  Lemma numneg_finite : forall v z, num_neg v = Some (ZE_Fin z)
                                    -> exists x, v = Some (ZE_Fin x) /\ (- x = z)%Z.
  Proof.
    intros until z.
    destruct v; intros; try discriminate H.
    destruct z0; try discriminate H.
    exists z0.
    split; auto.
    simpl in H.
    injection H.
    auto.
  Qed.

  (* If sum is positive infinity, then at least one addend is positive
  infinity and neither of them is negative infinity. *)
  Lemma numplus_inf : forall v1 v2, num_plus v1 v2 = Some ZE_Inf
                                    -> ((exists z, v1 = Some (ZE_Fin z)) /\ v2 = Some ZE_Inf) \/
                                       (v1 = Some ZE_Inf /\ (exists z, v2 = Some (ZE_Fin z))) \/
                                       (v1 = Some ZE_Inf /\ v2 = Some ZE_Inf).
  Proof.
    intros.
    destruct v1, v2.
    destruct z, z0; simpl in *; auto;
    try (discriminate H).
    left; split; auto; exists z; auto.
    right; left; split; auto; exists z; auto.
    simpl in H; destruct z; discriminate H.
    simpl in H; destruct z; discriminate H.
    simpl in H; discriminate H.
  Qed.

  (* If sum is negative infinity, then at least one addend is negative
  infinity and neither of them is positive infinity. *)
  Lemma numplus_neginf : forall v1 v2, num_plus v1 v2 = Some ZE_NegInf
                                       -> ((exists z, v1 = Some (ZE_Fin z)) /\ v2 = Some ZE_NegInf) \/
                                          (v1 = Some ZE_NegInf /\ (exists z, v2 = Some (ZE_Fin z))) \/
                                          (v1 = Some ZE_NegInf /\ v2 = Some ZE_NegInf).
  Proof.
    intros.
    destruct v1, v2.
    destruct z, z0; simpl in *; auto;
    try (discriminate H).
    left; split; auto; exists z; auto.
    right; left; split; auto; exists z; auto.
    simpl in H; destruct z; discriminate H.
    simpl in H; destruct z; discriminate H.
    simpl in H; discriminate H.
  Qed.

  (* If negation is positive infinity, then the original is negative infinity. *)
  Lemma numneg_inf : forall v, num_neg v = Some ZE_Inf
                               -> v = Some (ZE_NegInf).
  Proof.
    destruct v; intros; try discriminate H.
    destruct z; try discriminate H.
    auto.
  Qed.

  (* If negation is negative infinity, then the original is positive infinity. *)
  Lemma numneg_neginf : forall v, num_neg v = Some ZE_NegInf
                                  -> v = Some (ZE_Inf).
  Proof.
    destruct v; intros; try discriminate H.
    destruct z; try discriminate H.
    auto.
  Qed.

  (* If sum has no definition, then either of addends has no
  definition or it's the sum of positive infinity and negative
  infinity. *)
  Lemma numplus_none : forall v1 v2, num_plus v1 v2 = None -> v1 = None \/ v2 = None \/
                                                              (v1 = Some ZE_Inf /\ v2 = Some ZE_NegInf) \/
                                                              (v1 = Some ZE_NegInf /\ v2 = Some ZE_Inf).
  Proof.
    intros.
    destruct v1, v2.
    right; right.
    destruct z, z0; try discriminate H.
    left; auto.
    right; auto.
    right; left; auto.
    left; auto.
    left; auto.
  Qed.

  (* If the negation has no definition, then the original has no definition *)
  Lemma numneg_none: forall v, num_neg v = None -> v = None.
  Proof.
    intros.
    destruct v.
    destruct z; simpl in H; discriminate H.
    auto.
  Qed.

End ZInfinity.

(* Normal Integer Number Field *)
Module ZNumLattice <: NUMBER.
  Definition A := Z.
  Definition Const0 := 0%Z.
  Definition num_eq_dec := Z_eq_dec.
  Definition num_neg (x : A) := (0 - x)%Z.
  Definition num_plus (x y : A) := (x + y)%Z.
End ZNumLattice.

Module Type LEQ_RELATION (NUM : NUMBER) (VAL : SEM_VAL).
  Import NUM.
  Import VAL.
  Parameter num_leq : A -> A -> Val.
  Axiom num_leq_top: forall x y, num_leq x y = Top -> x = y \/ num_leq y x = Btm.
  Axiom num_leq_btm:
    forall x y, num_leq x y = Btm -> num_leq y x = Top \/ (((forall z, num_leq z x = Btm /\ num_leq x z = Btm) \/
                                                            (forall z, num_leq z y = Btm /\ num_leq y z = Btm)) /\
                                                           (forall m n, num_leq m n = Top \/ num_leq m n = Btm)).
  Axiom num_leq_trans: forall x y z, num_leq x y = Top -> num_leq y z = Top -> num_leq x z = Top.
  Axiom num_leq_both_leq: forall x y z, num_leq x z = Top -> num_leq y z = Top -> num_leq x y = Top \/ num_leq x y = Btm.
  Axiom num_leq_leq_both: forall x y z, num_leq z x = Top -> num_leq z y = Top -> num_leq x y = Top \/ num_leq x y = Btm.
End LEQ_RELATION.

Module FinLeqRelation (VAL : SEM_VAL) <: LEQ_RELATION ZNumLattice VAL.
  Import ZNumLattice.
  Import VAL.

  Definition num_leq (x y : A) := if Z_le_dec x y then Top else Btm.

  Lemma num_leq_top: forall x y, num_leq x y = Top -> x = y \/ num_leq y x = Btm.
  Proof.
    intros; unfold num_leq in H; destruct (Z_le_dec x y).
    apply Zle_lt_or_eq in l; destruct l. right. unfold num_leq. destruct (Z_le_dec y x). omega. trivial.
    left; trivial.
    generalize top_neq_btm; intro; rewrite H in H0; exfalso; apply H0; trivial.
  Qed.

  Lemma num_leq_btm:
    forall x y, num_leq x y = Btm -> num_leq y x = Top \/ (((forall z, num_leq z x = Btm /\ num_leq x z = Btm) \/
                                                            (forall z, num_leq z y = Btm /\ num_leq y z = Btm)) /\
                                                           (forall m n, num_leq m n = Top \/ num_leq m n = Btm)).
  Proof. left;
    intros; unfold num_leq in H; destruct (Z_le_dec x y).
         generalize top_neq_btm; intro; rewrite H in H0; exfalso; intuition.
         unfold num_leq. destruct (Z_le_dec y x). trivial. omega.
  Qed.

  Ltac solve_num_leq_trans_fin :=
    repeat match goal with
             | [|- forall _, _] => intros
             | [|- context[num_leq _ _]] => unfold num_leq
             | [H: context[num_leq _ _] |- _] => unfold num_leq in H
             | [|- context[Z_le_dec ?z1 ?z0]] => destruct (Z_le_dec z1 z0)
             | [H: context[Z_le_dec ?z1 ?z0] |- _] => destruct (Z_le_dec z1 z0)
             | [|- ?A = ?A] => trivial
             | [H: ?A |- ?A] => apply H
             | [|- ?A = ?A \/ _] => left; trivial
             | [|- _ \/ ?A = ?A ] => right; trivial
           end.

  Lemma num_leq_trans: forall x y z, num_leq x y = Top -> num_leq y z = Top -> num_leq x z = Top.
  Proof. solve_num_leq_trans_fin. exfalso; intuition. Qed.

  Lemma num_leq_both_leq: forall x y z, num_leq x z = Top -> num_leq y z = Top -> num_leq x y = Top \/ num_leq x y = Btm.
  Proof. solve_num_leq_trans_fin. Qed.

  Lemma num_leq_leq_both: forall x y z, num_leq z x = Top -> num_leq z y = Top -> num_leq x y = Top \/ num_leq x y = Btm.
  Proof. solve_num_leq_trans_fin. Qed.

End FinLeqRelation.

Module Type NONE_RELATION (VAL : SEM_VAL).
  Import VAL.
  Parameter noneVal : Val.
  Axiom none_neq_top : noneVal <> Top.
  Axiom none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal.
  Axiom none_tautology_2 : truth_and noneVal Top = noneVal.
  Axiom none_tautology_3 : truth_or (truth_and noneVal Btm) noneVal = noneVal.
  Axiom none_tautology_4 : truth_or noneVal Btm = noneVal.
End NONE_RELATION.

Module NoneError3ValRel <: NONE_RELATION Three_Val_NoneError.
  Import Three_Val_NoneError.
  Definition noneVal := VError.
  Lemma none_neq_top: noneVal <> Top. Proof. intro; discriminate H. Qed.
  Lemma none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_2 : truth_and noneVal Top = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_3 : truth_or (truth_and noneVal Btm) noneVal = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_4 : truth_or noneVal Btm = noneVal. Proof. intuition. Qed.
End NoneError3ValRel.

Module None3ValRel <: NONE_RELATION Three_Val.
  Import Three_Val.
  Definition noneVal := VUnknown.
  Lemma none_neq_top: noneVal <> Top. Proof. intro; discriminate H. Qed.
  Lemma none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_2 : truth_and noneVal Top = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_3 : truth_or (truth_and noneVal Btm) noneVal = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_4 : truth_or noneVal Btm = noneVal. Proof. intuition. Qed.
End None3ValRel.

Module NoneAlwaysFalse (VAL : SEM_VAL) <: NONE_RELATION VAL.
  Import VAL.
  Definition noneVal := Btm.
  Lemma none_neq_top: noneVal <> Top.
  Proof. intro; compute in H; generalize top_neq_btm; intro; rewrite H in H0; apply H0; trivial. Qed.
  Lemma none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_1, truth_and_comm, tautology_4; trivial. Qed.

  Lemma none_tautology_2 : truth_and noneVal Top = noneVal.
  Proof. unfold noneVal; simpl; rewrite truth_and_comm, tautology_4; trivial. Qed.

  Lemma none_tautology_3 : truth_or (truth_and noneVal Btm) noneVal = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_3, tautology_5; trivial. Qed.

  Lemma none_tautology_4 : truth_or noneVal Btm = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_5; trivial. Qed.

End NoneAlwaysFalse.

Module InfLeqRelation (VAL : SEM_VAL) (S: NONE_RELATION VAL) <: LEQ_RELATION ZInfinity VAL.
  Import ZInfinity.
  Import VAL.
  Import S.
  (* Definition of relation "less than or equal to" *)
  Definition num_leq (ze1 ze2 : A) : Val :=
    match ze1, ze2 with
      | None, _
      | _, None                            => noneVal
      | _, Some ZE_Inf                     => Top
      | Some ZE_NegInf, _                  => Top
      | Some ZE_Inf, Some x                => if ZE_eq_dec x ZE_Inf then Top else Btm
      | Some x, Some ZE_NegInf             => if ZE_eq_dec x ZE_NegInf then Top else Btm
      | Some (ZE_Fin z1), Some (ZE_Fin z2) => if Z_le_dec z1 z2 then Top else Btm
    end.

  Ltac solve_num_leq_top :=
    repeat match goal with
             | [|- forall _, _] => intros
             | [x : A |- _] => destruct x
             | [x : ZE |- _] => destruct x
             | [H : context[num_leq (Some _) (Some _)] |- _] => simpl in H
             | [H : context[num_leq (Some _) None] |- _] => simpl in H
             | [H : context[num_leq None (Some _)] |- _] => simpl in H
             | [H : context[num_leq None None] |- _] => simpl in H
             | [|- context[num_leq (Some _) (Some _)]] => simpl
             | [|- context[num_leq (Some _) None]] => simpl
             | [|- context[num_leq None (Some _)]] => simpl
             | [|- context[num_leq None None]] => simpl
             | [H : noneVal = Top |- _] =>
               let H0 := fresh "H0" in generalize none_neq_top; intro H0; rewrite H in H0; exfalso; intuition
             | [H : context[Z_le_dec ?z0 ?z] |- _] => destruct (Z_le_dec z0 z)
             | [H : Btm = Top |- _] =>
               let H0 := fresh "H0" in generalize top_neq_btm; intro H0; rewrite H in H0; exfalso; intuition
             | [|- _ \/ ?A = ?A] => right; trivial
             | [|- ?A = ?A \/ _] => left; trivial
           end.

  Lemma num_leq_top: forall x y, num_leq x y = Top -> x = y \/ num_leq y x = Btm.
  Proof.
    solve_num_leq_top.
    apply Zle_lt_or_eq in l; destruct l; [right; destruct (Z_le_dec z z0); [omega | trivial] | left; rewrite H0; trivial].
  Qed.

  Ltac solve_num_leq_val:=
    repeat match goal with
             | [|- forall _, _] => intros
             | [x : A |- _] => destruct x
             | [x : ZE |-_] => destruct x
             | [|- context[num_leq _ _]] => simpl
             | [H: context[num_leq _ _] |- _] => simpl in H
             | [|- ?A = ?A \/ _] => left; trivial
             | [|- _ \/ ?A = ?A \/ _] => right; left; trivial
             | [|- _ \/ _ \/ ?A = ?A] => right; right; trivial
           end.

  Lemma num_leq_val: forall x y, num_leq x y = Top \/ num_leq x y = Btm \/ num_leq x y = noneVal.
  Proof. solve_num_leq_val; destruct (Z_le_dec z0 z); [left | right; left]; trivial. Qed.

  Ltac solve_num_leq_btm :=
    repeat match goal with
             | [|- forall _, _] => intros
             | [x : A |- _] => destruct x
             | [x : ZE |-_] => destruct x
             | [H: Top = Btm |- _] => exfalso; apply top_neq_btm; apply H
             | [|- ?A = ?A \/ _] => left; trivial
             | [|- num_leq _ _ = _ \/ _ ] => simpl
             | [H: num_leq _ _ = _ |- _] => simpl in H
             | [H : noneVal = Btm |- noneVal = Top \/ _] => right
             | [H: noneVal = Btm |- (forall _, num_leq _ None = Btm /\ noneVal = Btm) \/ _] => left; split; auto
             | [H: noneVal = Btm |- _ \/ (forall _, num_leq _ None = Btm /\ noneVal = Btm)] => right; split; auto
             | [|- num_leq _ _ = _] => simpl
             | [H: ?A |- ?A] => apply H
             | [H: context[Z_le_dec ?x ?y] |- _] => destruct (Z_le_dec x y)
             | [|- context[Z_le_dec ?x ?y]] => destruct (Z_le_dec x y)
             | [|- _ /\ _] => split
             | [|- _ \/ ?A = ?A] => right; trivial
           end.

  Lemma num_leq_btm:
    forall x y, num_leq x y = Btm -> num_leq y x = Top \/ (((forall z, num_leq z x = Btm /\ num_leq x z = Btm) \/
                                                            (forall z, num_leq z y = Btm /\ num_leq y z = Btm)) /\
                                                           (forall m n, num_leq m n = Top \/ num_leq m n = Btm)).
  Proof. solve_num_leq_btm. exfalso; intuition. Qed.

  Ltac solve_num_leq_trans :=
    repeat match goal with
             | [|- forall _, _] => intros
             | [x : A |- _] => destruct x
             | [x : ZE |- _] => destruct x
             | [|- context[num_leq _ _]] => simpl
             | [H: context[num_leq _ _] |- _] => simpl in H
             | [H: ?A |- ?A] => apply H
             | [H: ?A = ?B |- ?B = ?A] => rewrite H; trivial
             | [|- ?A = ?A] => trivial
             | [H: noneVal = Top |- _] =>
               let S := fresh "S" in generalize none_neq_top; intro S; exfalso; rewrite H in S; apply S; trivial
             | [H: Btm = Top |- _] => exfalso; apply top_neq_btm
             | [|- context[Z_le_dec ?z1 ?z0]] => destruct (Z_le_dec z1 z0)
             | [H: context[Z_le_dec ?z1 ?z0] |- _] => destruct (Z_le_dec z1 z0)
             | [|- ?A = ?A \/ _] => left; trivial
             | [|- _ \/ ?A = ?A ] => right; trivial
           end.

  Lemma num_leq_trans: forall x y z, num_leq x y = Top -> num_leq y z = Top -> num_leq x z = Top.
  Proof. solve_num_leq_trans. exfalso; intuition. Qed.

  Lemma num_leq_both_leq: forall x y z, num_leq x z = Top -> num_leq y z = Top -> num_leq x y = Top \/ num_leq x y = Btm.
  Proof. solve_num_leq_trans. Qed.

  Lemma num_leq_leq_both: forall x y z, num_leq z x = Top -> num_leq z y = Top -> num_leq x y = Top \/ num_leq x y = Btm.
  Proof. solve_num_leq_trans. Qed.

End InfLeqRelation.

(* Intermediate Modules *)
(* Abstract type which separates variable domain and constant domain *)
Module Type SEMANTICS_INPUT.
  Declare Module N : NUMBER.
  Import N.
  Parameter Q      : Type.
  Parameter QT     : Q -> Type.
  Parameter conv   : forall q, (QT q) -> A.
End SEMANTICS_INPUT.

(* Variable domain can be integer with infinity or just
integer. Constant domain is integer with infinity. *)
Module PureInfinity <: SEMANTICS_INPUT.
  Module N := ZInfinity.
  Import N.
  Inductive AQ : Type :=
    Q_Z | Q_ZE.
  Definition Q : Type := AQ.
  Definition QT (q : Q) : Type := match q with Q_Z => Z | Q_ZE => ZE end.
  Definition conv {q : Q} (x : QT q) : A :=
    match q return (QT q -> A) with
      | Q_Z => fun x : Z => Some (ZE_Fin x)
      | Q_ZE => fun x : ZE => Some x
    end x.
End PureInfinity.

(* Both domains are integer. *)
Module PureInt <: SEMANTICS_INPUT.
  Module N := ZNumLattice.
  Definition Q := unit.
  Definition QT (q : Q) : Type := Z.
  Definition conv {q : Q} (x : QT q) := x.
End PureInt.

(* Variable domain is integer and constant domain is integer with infinity. *)
Module IntToInfinity <: SEMANTICS_INPUT.
  Module N := ZInfinity.
  Import N.
  Definition Q := unit.
  Definition QT (q : Q) : Type := Z.
  Definition conv {q : Q} (x : QT q) := Some (ZE_Fin x).
End IntToInfinity.

Module Type ZERO_PRODUCT (NUM : NUMBER).
  Import NUM.
  Parameter zero_times: A -> A.
End ZERO_PRODUCT.

Module Type ZERO_FIN <: ZERO_PRODUCT ZNumLattice.
  Import ZNumLattice.
  Parameter zero_times: A -> A.
  Axiom all_is_zero: forall x, zero_times x = 0%Z.
End ZERO_FIN.

Module FinZero <: ZERO_FIN.
  Import ZNumLattice.
  Definition zero_times (_ : A) := 0%Z.
  Lemma all_is_zero: forall x, zero_times x = 0%Z.
  Proof. unfold zero_times; intuition. Qed.
End FinZero.

Module Type ZERO_INF <: ZERO_PRODUCT ZInfinity.
  Import ZInfinity.
  Parameter zero_times: A -> A.
  Axiom zero_times_spec: (forall x, zero_times x = Some (ZE_Fin 0)) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end).
End ZERO_INF.

Module InfZeroAll <: ZERO_INF.
  Import ZInfinity.
  Definition zero_times (_ : A) := Some (ZE_Fin 0).
  Lemma zero_times_spec: (forall x, zero_times x = Some (ZE_Fin 0)) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end).
  Proof. left; unfold zero_times; intuition. Qed.

End InfZeroAll.

Module InfZeroFinOnly <: ZERO_INF.
  Import ZInfinity.
  Definition zero_times (x : A) :=
    match x with
      | Some (ZE_Fin _) => Some (ZE_Fin 0)
      | _ => None
    end.
  Lemma zero_times_spec: (forall x, zero_times x = Some (ZE_Fin 0)) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end).
  Proof. right; left; unfold zero_times; intuition. Qed.

End InfZeroFinOnly.

Module InfZeroInf <: ZERO_INF.
  Import ZInfinity.
  Definition zero_times (x : A) :=
    match x with
      | Some (ZE_Fin _) => Some (ZE_Fin 0)
      | _ => x
    end.
  Lemma zero_times_spec: (forall x, zero_times x = Some (ZE_Fin 0)) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end) \/
                         (forall x, zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end).
  Proof. right; right; unfold zero_times; intuition. Qed.

End InfZeroInf.

Module ArithSemantics (I : SEMANTICS_INPUT) (V : VARIABLE) (VAL : SEM_VAL) (L : LEQ_RELATION I.N VAL) (ZT : ZERO_PRODUCT I.N).
  Import I N V VAL L ZT.

  (* Syntax *)
  Section OriginalForm.

    (* Arithmetic Expression *)
    Inductive ZExp : Type :=
    | ZExp_Var     : var  -> ZExp
    | ZExp_Const   : A    -> ZExp
    | ZExp_Add     : ZExp -> ZExp -> ZExp (* + *)
    | ZExp_Inv     : ZExp -> ZExp (* unary - *)
    | ZExp_Sub     : ZExp -> ZExp -> ZExp (* - *)
    | ZExp_Mult    : Z    -> ZExp -> ZExp. (* Constant Multiplication *)

    (* Boolean Forms *)
    Inductive ZBF : Type :=
    | ZBF_Const   : Val -> ZBF
    | ZBF_Lt      : ZExp -> ZExp -> ZBF (* < *)
    | ZBF_Lte     : ZExp -> ZExp -> ZBF (* <= *)
    | ZBF_Gt      : ZExp -> ZExp -> ZBF (* > *)
    | ZBF_Gte     : ZExp -> ZExp -> ZBF (* >= *)
    | ZBF_Eq      : ZExp -> ZExp -> ZBF (* = *)
    | ZBF_Eq_Max  : ZExp -> ZExp -> ZExp -> ZBF (* a = min(b, c) *)
    | ZBF_Eq_Min  : ZExp -> ZExp -> ZExp -> ZBF (* a = max(b, c) *)
    | ZBF_Neq     : ZExp -> ZExp -> ZBF. (* <> *)

    (* Logic Forms *)
    Inductive ZF : Type :=
    | ZF_BF      : ZBF -> ZF
    | ZF_And     : ZF  -> ZF -> ZF (* /\ *)
    | ZF_Or      : ZF  -> ZF -> ZF (* \/ *)
    | ZF_Imp     : ZF  -> ZF -> ZF (* -> *)
    | ZF_Not     : ZF  -> ZF       (* ~ *)
    | ZF_Forall  : var -> Q -> ZF -> ZF  (* forall *)
    | ZF_Exists  : var -> Q -> ZF -> ZF. (* exists *)

  End OriginalForm.

  (* Semantics *)
  Section DirectSemantics.

    (* Definition of constant multiplication of natural numbers *)
    Fixpoint num_mult_nat (n : nat) (x : A) : A :=
      match n with
        | O   => zero_times x
        | S O => x
        | S n => num_plus x (num_mult_nat n x)
      end.

    Lemma num_mult_nat_2_unfold: forall n x, num_mult_nat (S (S n)) x = num_plus x (num_mult_nat (S n) x).
    Proof. induction n; intros; [simpl; auto | remember (S (S n)); simpl; destruct n0;[ discriminate Heqn0 | auto]]. Qed.

    (* Definition of constant multiplication of integers *)
    Definition num_mult (z : Z) (exp : A) : A :=
      match z with
        | Z0     => zero_times exp
        | Zpos x => num_mult_nat (nat_of_P x) exp
        | Zneg x => num_neg (num_mult_nat (nat_of_P x) exp)
      end.

    (* Substitution on Expressions *)
    Fixpoint subst_exp (p : var * A) (exp : ZExp) : ZExp :=
      match exp with
          ZExp_Var v     => if var_eq_dec (fst p) v then ZExp_Const (snd p) else exp
        | ZExp_Const _   => exp
        | ZExp_Add e1 e2 => ZExp_Add (subst_exp p e1) (subst_exp p e2)
        | ZExp_Inv e     => ZExp_Inv (subst_exp p e)
        | ZExp_Sub e1 e2 => ZExp_Sub (subst_exp p e1) (subst_exp p e2)
        | ZExp_Mult n e  => ZExp_Mult n (subst_exp p e)
      end.

    (* Substitution on Boolean Forms *)
    Fixpoint subst_bf (p : var * A) (bf : ZBF) : ZBF :=
      match bf with
          ZBF_Const _   => bf
        | ZBF_Lt e1 e2  => ZBF_Lt (subst_exp p e1) (subst_exp p e2)
        | ZBF_Lte e1 e2 => ZBF_Lte (subst_exp p e1) (subst_exp p e2)
        | ZBF_Gt e1 e2  => ZBF_Gt (subst_exp p e1) (subst_exp p e2)
        | ZBF_Gte e1 e2 => ZBF_Gte (subst_exp p e1) (subst_exp p e2)
        | ZBF_Eq e1 e2  => ZBF_Eq (subst_exp p e1) (subst_exp p e2)
        | ZBF_Eq_Max e1 e2 e3  => ZBF_Eq_Max (subst_exp p e1) (subst_exp p e2) (subst_exp p e3)
        | ZBF_Eq_Min e1 e2 e3  => ZBF_Eq_Min (subst_exp p e1) (subst_exp p e2) (subst_exp p e3)
        | ZBF_Neq e1 e2 => ZBF_Neq (subst_exp p e1) (subst_exp p e2)
      end.

    (* Substitution on Logic Forms *)
    Fixpoint substitute (p : var * A) (form : ZF) : ZF :=
      match form with
          ZF_BF bf      => ZF_BF (subst_bf p bf)
        | ZF_And f1 f2  => ZF_And (substitute p f1) (substitute p f2)
        | ZF_Or f1 f2   => ZF_Or (substitute p f1) (substitute p f2)
        | ZF_Imp f1 f2  => ZF_Imp (substitute p f1) (substitute p f2)
        | ZF_Not f      => ZF_Not (substitute p f)
        | ZF_Forall v q f => if var_eq_dec (fst p) v then form else ZF_Forall v q (substitute p f)
        | ZF_Exists v q f => if var_eq_dec (fst p) v then form else ZF_Exists v q (substitute p f)
      end.

    (* For the same variable, second substitution on expressions has no effect. *)
    Lemma same_var_subst_exp: forall exp v a1 a2, subst_exp (v, a1) (subst_exp (v, a2) exp) = subst_exp (v, a2) exp.
    Proof.
      induction exp; simpl; intros.
      destruct (var_eq_dec v0 v); simpl; auto.
      destruct (var_eq_dec v0 v); simpl; tauto.
      auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
    Qed.

    (* For the same variable, second substitution on boolean forms has no effect. *)
    Lemma same_var_subst_bf: forall bf v a1 a2, subst_bf (v, a1) (subst_bf (v, a2) bf) = subst_bf (v, a2) bf.
    Proof.
      destruct bf; simpl; intros; auto;
      try (rewrite same_var_subst_exp, same_var_subst_exp, same_var_subst_exp; auto);
      try (rewrite same_var_subst_exp, same_var_subst_exp; auto).
    Qed.

    (* For the same variable, second substitution on logic forms has no effect. *)
    Lemma same_var_subst: forall f v a1 a2, substitute (v, a1) (substitute (v, a2) f) = substitute (v, a2) f.
    Proof.
      induction f; intros;
      try (unfold substitute; rewrite same_var_subst_bf; auto);
      try (unfold substitute; fold substitute; rewrite IHf1, IHf2; auto);
      try (unfold substitute; fold substitute; rewrite IHf; auto);
      try (unfold substitute; fold substitute; unfold fst;
           destruct (var_eq_dec v0 v);
           unfold substitute; fold substitute; unfold fst;
           destruct (var_eq_dec v0 v); auto; try tauto;
           rewrite IHf; auto).
    Qed.

    (* Commutative law for substitution on expressions with different variables *)
    Lemma diff_var_subst_exp: forall exp v1 v2 a1 a2, v1 <> v2 -> subst_exp (v1, a1) (subst_exp (v2, a2) exp) =
                                                                  subst_exp (v2, a2) (subst_exp (v1, a1) exp).
    Proof.
      induction exp; simpl; intros.
      destruct (var_eq_dec v2 v), (var_eq_dec v1 v).
      rewrite <- e in e0; tauto.
      simpl; destruct (var_eq_dec v2 v); tauto.
      simpl; destruct (var_eq_dec v1 v); tauto.
      simpl. destruct (var_eq_dec v2 v), (var_eq_dec v1 v); tauto.
      auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
    Qed.

    (* Commutative law for substitution on boolean forms with different variables *)
    Lemma diff_var_subst_bf: forall bf v1 v2 a1 a2, v1 <> v2 -> subst_bf (v1, a1) (subst_bf (v2, a2) bf) =
                                                                subst_bf (v2, a2) (subst_bf (v1, a1) bf).
    Proof.
      destruct bf; simpl; intros; auto;
      (rewrite diff_var_subst_exp  with (exp := z);
       try rewrite diff_var_subst_exp with (exp := z0);
       try rewrite diff_var_subst_exp with (exp := z1);
       auto).
    Qed.

    (* Commutative law for substitution on logic forms with different variables *)
    Lemma diff_var_subst: forall f v1 v2 a1 a2, v1 <> v2 -> substitute (v1, a1) (substitute (v2, a2) f) =
                                                            substitute (v2, a2) (substitute (v1, a1) f).
    Proof.
      induction f; intros;
      try (unfold substitute; rewrite diff_var_subst_bf; auto);
      try (unfold substitute; fold substitute; rewrite IHf1, IHf2; auto);
      try (unfold substitute; fold substitute; rewrite IHf; auto);
      (unfold substitute; fold substitute; unfold fst;
       destruct (var_eq_dec v2 v), (var_eq_dec v1 v); auto;
       try (rewrite <- e in e0; tauto);
       try (simpl; destruct (var_eq_dec v2 v), (var_eq_dec v1 v); try tauto);
       rewrite IHf; auto).
    Qed.

    (* Evaluation of Expressions *)
    Fixpoint dexp2ZE (exp : ZExp) : A :=
      match exp with
          ZExp_Var _     => Const0
        | ZExp_Const z   => z
        | ZExp_Add e1 e2 => num_plus (dexp2ZE e1) (dexp2ZE e2)
        | ZExp_Inv e     => num_neg (dexp2ZE e)
        | ZExp_Sub e1 e2 => num_plus (dexp2ZE e1) (num_neg (dexp2ZE e2))
        | ZExp_Mult z e  => num_mult z (dexp2ZE e)
      end.

    (* Evaluation of Boolean Forms *)
    Fixpoint dzbf2bool (bf : ZBF) : Val :=
      match bf with
          ZBF_Const b   => b
        | ZBF_Lt e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v1 v2) (truth_not (num_leq v2 v1))
        | ZBF_Lte e1 e2 => num_leq (dexp2ZE e1) (dexp2ZE e2)
        | ZBF_Gt e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v2 v1) (truth_not (num_leq v1 v2))
        | ZBF_Gte e1 e2 => num_leq (dexp2ZE e2) (dexp2ZE e1)
        | ZBF_Eq e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v1 v2) (num_leq v2 v1)
        | ZBF_Eq_Max e1 e2 e3 =>
          let v1 := dexp2ZE e1 in
          let v2 := dexp2ZE e2 in
          let v3 := dexp2ZE e3 in
          truth_or (truth_and (num_leq v3 v2) (truth_and (num_leq v1 v2) (num_leq v2 v1)))
                   (truth_and (num_leq v2 v3) (truth_and (num_leq v1 v3) (num_leq v3 v1)))
        | ZBF_Eq_Min e1 e2 e3 =>
          let v1 := dexp2ZE e1 in
          let v2 := dexp2ZE e2 in
          let v3 := dexp2ZE e3 in
          truth_or (truth_and (num_leq v3 v2) (truth_and (num_leq v1 v3) (num_leq v3 v1)))
                   (truth_and (num_leq v2 v3) (truth_and (num_leq v1 v2) (num_leq v2 v1)))
        | ZBF_Neq e1 e2 => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_not (truth_and (num_leq v1 v2) (num_leq v2 v1))
      end.

    (* Length of Logic Form *)
    Fixpoint length_zform (form : ZF) : nat :=
      match form with
          ZF_BF _       => 1
        | ZF_And f1 f2  => S (length_zform f1 + length_zform f2)
        | ZF_Or f1 f2   => S (length_zform f1 + length_zform f2)
        | ZF_Imp f1 f2  => S (length_zform f1 + length_zform f2)
        | ZF_Not f      => S (length_zform f)
        | ZF_Forall _ _ f => S (length_zform f)
        | ZF_Exists _ _ f => S (length_zform f)
      end.

    (* Substitution doesn't change the length *)
    Lemma substitute_length_inv : forall f x v, length_zform f = length_zform (substitute (v, x) f).
    Proof.
      induction f; simpl; try tauto; intros;
      try (rewrite <- IHf1; rewrite <- IHf2);
      try rewrite <- IHf;
      try (case (var_eq_dec v0 v); intros; simpl); auto.
    Defined.

    (* Definition of Validity of Logic Forms *)
    Inductive Input := Sat: ZF -> Input | DisSat: ZF -> Input | Udtmd: ZF -> Input.

    Definition length_input (inp : Input) :=
      match inp with
        | Sat f => length_zform f
        | DisSat f => length_zform f
        | Udtmd f => length_zform f
      end.

    Definition inputOrder (f1 f2 : Input) := length_input f1 < length_input f2.

    Lemma inputOrder_wf': forall len f, length_input f <= len -> Acc inputOrder f.
    Proof.
      unfold inputOrder; induction len; intros;
      [destruct f; destruct z; simpl in H; exfalso; intuition | constructor; intros; apply IHlen; omega].
    Defined.

    Theorem inputOrder_wf: well_founded inputOrder.
    Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

    Ltac smash := intros; unfold inputOrder; simpl; omega || rewrite <- substitute_length_inv; omega.

    Lemma sat_and_1: forall f1 f2, inputOrder (Sat f1) (Sat (ZF_And f1 f2)). smash. Defined.
    Lemma sat_and_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_And f1 f2)). smash. Defined.
    Lemma sat_or_1: forall f1 f2, inputOrder (Sat f1) (Sat (ZF_Or f1 f2)). smash. Defined.
    Lemma sat_or_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_Or f1 f2)). smash. Defined.
    Lemma sat_imp_1: forall f1 f2, inputOrder (DisSat f1) (Sat (ZF_Imp f1 f2)). smash. Defined.
    Lemma sat_imp_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_Imp f1 f2)). smash. Defined.
    Lemma sat_not : forall f, inputOrder (DisSat f) (Sat (ZF_Not f)). smash. Defined.
    Lemma sat_forall:forall f v q(x:QT q),inputOrder(Sat (substitute (v, @conv q x) f))(Sat (ZF_Forall v q f)). smash. Defined.
    Lemma sat_exists:forall f v q(x:QT q),inputOrder(Sat (substitute (v, @conv q x) f))(Sat (ZF_Exists v q f)). smash. Defined.
    Lemma dst_and_1: forall f1 f2, inputOrder (DisSat f1) (DisSat (ZF_And f1 f2)). smash. Defined.
    Lemma dst_and_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_And f1 f2)). smash. Defined.
    Lemma dst_or_1: forall f1 f2, inputOrder (DisSat f1) (DisSat (ZF_Or f1 f2)). smash. Defined.
    Lemma dst_or_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_Or f1 f2)). smash. Defined.
    Lemma dst_imp_1: forall f1 f2, inputOrder (Sat f1) (DisSat (ZF_Imp f1 f2)). smash. Defined.
    Lemma dst_imp_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_Imp f1 f2)). smash. Defined.
    Lemma dst_not : forall f, inputOrder (Sat f) (DisSat (ZF_Not f)). smash. Defined.
    Lemma dst_forall:forall f v q(x:QT q),inputOrder(DisSat(substitute (v,@conv q x) f))(Sat (ZF_Forall v q f)). smash. Defined.
    Lemma dst_exists:forall f v q(x:QT q),inputOrder(DisSat(substitute (v,@conv q x) f))(Sat (ZF_Exists v q f)). smash. Defined.
    Lemma udd_and_1 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_3 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_or_1 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_3 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_imp_1 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_3 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_not_1 : forall f, inputOrder (DisSat f) (Udtmd (ZF_Not f)). smash. Defined.
    Lemma udd_not_2 : forall f, inputOrder (Sat f) (Udtmd (ZF_Not f)). smash. Defined.
    Lemma udd_forall_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Udtmd(ZF_Forall v q f)). smash. Defined.
    Lemma udd_forall_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Udtmd(ZF_Forall v q f)). smash. Defined.
    Lemma udd_exists_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Udtmd(ZF_Exists v q f)). smash. Defined.
    Lemma udd_exists_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Udtmd(ZF_Exists v q f)). smash. Defined.

    Definition three_pred : Input -> Prop :=
      Fix inputOrder_wf (fun _ => Prop)
          (fun (inp : Input) =>
             match inp return ((forall ff : Input, inputOrder ff inp -> Prop) -> Prop) with
               | Sat g =>
                 match g with
                   | ZF_BF bf      => fun _ => dzbf2bool bf = Top
                   | ZF_And f1 f2  => fun tpF => (tpF (Sat f1) (sat_and_1 f1 f2)) /\ (tpF (Sat f2) (sat_and_2 f1 f2))
                   | ZF_Or f1 f2   => fun tpF => (tpF (Sat f1) (sat_or_1 f1 f2)) \/ (tpF (Sat f2) (sat_or_2 f1 f2))
                   | ZF_Imp f1 f2  => fun tpF => (tpF (DisSat f1) (sat_imp_1 f1 f2)) \/ (tpF (Sat f2) (sat_imp_2 f1 f2))
                   | ZF_Not f      => fun tpF => (tpF (DisSat f) (sat_not f))
                   | ZF_Forall v q f => fun tpF => forall x: QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_forall f v q x))
                   | ZF_Exists v q f => fun tpF => exists x: QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_exists f v q x))
                 end
               | DisSat g =>
                 match g with
                   | ZF_BF bf => fun _ => dzbf2bool bf = Btm
                   | ZF_And f1 f2 => fun tpF => (tpF (DisSat f1) (dst_and_1 f1 f2)) \/ (tpF (DisSat f2) (dst_and_2 f1 f2))
                   | ZF_Or f1 f2 => fun tpF => (tpF (DisSat f1) (dst_or_1 f1 f2)) /\ (tpF (DisSat f2) (dst_or_2 f1 f2))
                   | ZF_Imp f1 f2 => fun tpF => (tpF (Sat f1) (dst_imp_1 f1 f2)) /\ (tpF (DisSat f2) (dst_imp_2 f1 f2))
                   | ZF_Not f => fun tpF => (tpF (Sat f) (dst_not f))
                   | ZF_Forall v q f => fun tpF => exists x : QT q,
                                                     (tpF (DisSat (substitute (v, @conv q x) f)) (dst_forall f v q x))
                   | ZF_Exists v q f => fun tpF => forall x : QT q,
                                                     (tpF (DisSat (substitute (v, @conv q x) f)) (dst_exists f v q x))
                 end
               | Udtmd g =>
                 match g with
                   | ZF_BF bf => fun _ => (dzbf2bool bf <> Top) /\ (dzbf2bool bf <> Btm)
                   | ZF_And f1 f2 => fun tpF => (~ ((tpF (Sat f1) (udd_and_1 f1 f2)) /\ (tpF (Sat f2) (udd_and_2 f1 f2)))) /\
                                                (~ ((tpF (DisSat f1) (udd_and_3 f1 f2)) \/ (tpF (DisSat f2) (udd_and_4 f1 f2))))
                   | ZF_Or f1 f2 => fun tpF => (~ ((tpF (Sat f1) (udd_or_1 f1 f2)) \/ (tpF (Sat f2) (udd_or_2 f1 f2)))) /\
                                               (~ ((tpF (DisSat f1) (udd_or_3 f1 f2)) /\ (tpF (DisSat f2) (udd_or_4 f1 f2))))
                   | ZF_Imp f1 f2 => fun tpF => (~ ((tpF (DisSat f1) (udd_imp_1 f1 f2)) \/ (tpF (Sat f2) (udd_imp_2 f1 f2)))) /\
                                                (~ ((tpF (Sat f1) (udd_imp_3 f1 f2)) /\ (tpF (DisSat f2) (udd_imp_4 f1 f2))))
                   | ZF_Not f => fun tpF => (~ ((tpF (DisSat f) (udd_not_1 f)))) /\ (~ ((tpF (Sat f) (udd_not_2 f))))
                   | ZF_Forall v q f =>
                     fun tpF => (~ (forall x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (udd_forall_1 f v q x)))) /\
                                (~ (exists x : QT q, (tpF (DisSat (substitute (v, @conv q x) f)) (udd_forall_2 f v q x))))
                   | ZF_Exists v q f =>
                     fun tpF => (~ (exists x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (udd_exists_1 f v q x)))) /\
                                (~ (forall x : QT q, (tpF (DisSat (substitute (v, @conv q x) f)) (udd_exists_2 f v q x))))
                 end
             end).
    Definition satisfied form := three_pred (Sat form).
    Definition dissatisfied form := three_pred (DisSat form).
    Definition undetermined form := three_pred (Udtmd form).

    Lemma satisfied_unfold :
      forall zf, satisfied zf = match zf with
                                  | ZF_BF bf      => (dzbf2bool bf = Top)
                                  | ZF_And f1 f2  => (satisfied f1) /\ (satisfied f2)
                                  | ZF_Or f1 f2   => (satisfied f1) \/ (satisfied f2)
                                  | ZF_Imp f1 f2  => (dissatisfied f1) \/ (satisfied f2)
                                  | ZF_Not f      =>  dissatisfied f
                                  | ZF_Forall v q f => forall x : QT q, (satisfied (substitute (v , @conv q x) f))
                                  | ZF_Exists v q f => exists x : QT q, (satisfied (substitute (v , @conv q x) f))
                                end.
    Proof.
      intro; unfold satisfied at 1; unfold three_pred; rewrite Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto); subst; destruct x]; auto.
    Qed.

    Lemma dissatisfied_unfold :
      forall zf, dissatisfied zf = match zf with
                                     | ZF_BF bf      => (dzbf2bool bf = Btm)
                                     | ZF_And f1 f2  => (dissatisfied f1) \/ (dissatisfied f2)
                                     | ZF_Or f1 f2   => (dissatisfied f1) /\ (dissatisfied f2)
                                     | ZF_Imp f1 f2  => (satisfied f1) /\ (dissatisfied f2)
                                     | ZF_Not f      => satisfied f
                                     | ZF_Forall v q f => exists x : QT q, (dissatisfied (substitute (v , @conv q x) f))
                                     | ZF_Exists v q f => forall x : QT q, (dissatisfied (substitute (v , @conv q x) f))
                                   end.
    Proof.
      intro; unfold dissatisfied at 1; unfold three_pred; rewrite Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto); subst; destruct x]; auto.
    Qed.

    Lemma undetermined_unfold : forall zf, undetermined zf <-> (~ satisfied zf) /\ (~ dissatisfied zf).
    Proof.
      intro; unfold undetermined at 1; unfold three_pred; rewrite satisfied_unfold, dissatisfied_unfold, Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality a; extensionality b; auto); subst; destruct x]; intuition.
    Qed.

    Lemma sat_dissat_disj: forall zf, ~ (satisfied zf /\ dissatisfied zf).
    Proof.
      intro zf; remember (length_zform zf); assert (length_zform zf <= n) by omega; clear Heqn; revert zf H.
      induction n; intros.
      exfalso; destruct zf; simpl in H; intuition.
      destruct zf; rewrite satisfied_unfold, dissatisfied_unfold; intro SS; destruct SS; simpl in H.
      generalize top_neq_btm; intro S; rewrite <- H0, <- H1 in S; apply S; trivial.
      destruct H0; destruct H1; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      destruct H1; destruct H0; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      rewrite <- dissatisfied_unfold in H0; rewrite dissatisfied_unfold in H1.
      destruct H1; destruct H0; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      rewrite <- dissatisfied_unfold in H0; rewrite dissatisfied_unfold in H1; apply (IHn zf); intuition.
      destruct H1; specialize (H0 x); apply (IHn (substitute (v, conv q x) zf)); [rewrite <- substitute_length_inv|]; intuition.
      destruct H0; specialize (H1 x); apply (IHn (substitute (v, conv q x) zf)); [rewrite <- substitute_length_inv|]; intuition.
    Qed.

    Lemma sat_undtmd_disj : forall zf, ~ (satisfied zf /\ undetermined zf).
    Proof. repeat intro; destruct H; rewrite undetermined_unfold in H0; destruct H0; apply H0; trivial. Qed.

    Lemma dissat_undtmd_disj : forall zf, ~ (dissatisfied zf /\ undetermined zf).
    Proof. repeat intro; destruct H; rewrite undetermined_unfold in H0; destruct H0; apply H1; trivial. Qed.

    Eval compute in satisfied (ZF_BF (ZBF_Const Btm)).

    Eval compute in satisfied (ZF_Or (ZF_BF (ZBF_Const Top)) (ZF_BF (ZBF_Const Btm))).

  End DirectSemantics.

  Section ZFWellFounded.

    Definition lengthOrder (f1 f2 : ZF) := length_zform f1 < length_zform f2.

    Lemma lengthOrder_wf': forall len f, length_zform f <= len -> Acc lengthOrder f.
    Proof.
      induction len; intros; destruct f;
      simpl in * |-; try omega;
      constructor; intros; unfold lengthOrder in * |-; simpl in * |-;
                                                                    apply IHlen with (f := y); omega.
    Defined.

    Theorem lengthOrder_wf: well_founded lengthOrder.
    Proof.
      red; intro; eapply lengthOrder_wf'; eauto.
    Defined.

    Ltac smash := intros; unfold lengthOrder; simpl; omega || rewrite <- substitute_length_inv; omega.

    Lemma lengthOrder_forall:forall f v q (x: QT q), lengthOrder (substitute (v, @conv q x) f) (ZF_Forall v q f). smash. Defined.
    Lemma lengthOrder_forall_trivial: forall f v q, lengthOrder f (ZF_Forall v q f). smash. Defined.
    Lemma lengthOrder_exists:forall f v q (x: QT q), lengthOrder (substitute (v, @conv q x) f) (ZF_Exists v q f). smash. Defined.
    Lemma lengthOrder_exists_trivial: forall f v q, lengthOrder f (ZF_Exists v q f). smash. Defined.
    Lemma lengthOrder_and_1: forall f1 f2, lengthOrder f1 (ZF_And f1 f2). smash. Defined.
    Lemma lengthOrder_and_2: forall f1 f2, lengthOrder f2 (ZF_And f1 f2). smash. Defined.
    Lemma lengthOrder_or_1: forall f1 f2, lengthOrder f1 (ZF_Or f1 f2). smash. Defined.
    Lemma lengthOrder_or_2: forall f1 f2, lengthOrder f2 (ZF_Or f1 f2). smash. Defined.
    Lemma lengthOrder_imp_1: forall f1 f2, lengthOrder f1 (ZF_Imp f1 f2). smash. Defined.
    Lemma lengthOrder_imp_2: forall f1 f2, lengthOrder f2 (ZF_Imp f1 f2). smash. Defined.
    Lemma lengthOrder_not: forall f, lengthOrder f (ZF_Not f). smash. Defined.

  End ZFWellFounded.

  Section Simplification.

    (* Elimination of Min and Max *)
    Definition eliminateMinMax (bf : ZBF) : ZF :=
      match bf with
          ZBF_Eq_Max e1 e2 e3 => ZF_Or (ZF_And (ZF_BF (ZBF_Eq e1 e2)) (ZF_BF (ZBF_Lte e3 e2)))
                                       (ZF_And (ZF_BF (ZBF_Eq e1 e3)) (ZF_BF (ZBF_Lte e2 e3)))
        | ZBF_Eq_Min e1 e2 e3 => ZF_Or (ZF_And (ZF_BF (ZBF_Eq e1 e2)) (ZF_BF (ZBF_Lte e2 e3)))
                                       (ZF_And (ZF_BF (ZBF_Eq e1 e3)) (ZF_BF (ZBF_Lte e3 e2)))
        | _ => ZF_BF bf
      end.

    Lemma num_leq_refl: forall x y, num_leq x y = Top -> num_leq y x = Top -> x = y.
    Proof.
      intros; generalize (num_leq_top _ _ H); intro; generalize (num_leq_top _ _ H0); intro;
      destruct H1, H2; trivial; rewrite H0 in H1; apply top_neq_btm in H1; intuition.
    Qed.

    Lemma num_leq_btm_trans: forall x y z, num_leq x y = Btm -> num_leq y z = Btm -> num_leq x z = Btm \/ num_leq x z = Top.
    Proof.
      intros; destruct (num_leq_btm _ _ H), (num_leq_btm _ _ H0).
      generalize (num_leq_trans _ _ _ H2 H1); intro.
      destruct (num_leq_top _ _ H3). rewrite H4 in *. rewrite H1 in H0. exfalso; apply top_neq_btm; apply H0. left; auto.
      destruct H2 as [[? | ?] ?]. destruct (H2 x). rewrite H1 in H5; exfalso; apply top_neq_btm; apply H5.
      destruct (H2 x); left; auto.
      destruct H1 as [[? | ?] ?]. destruct (H1 z); left; auto.
      destruct (H1 z). rewrite H2 in H4; exfalso; apply top_neq_btm; apply H4.
      destruct H1 as [? ?].
      destruct (H3 x z); auto.
    Qed.

    Ltac solve_eliminate :=
      repeat match goal with
               | [|- forall _, _] => intros
               | [z: ZBF |- _] => destruct z
               | [|- context[satisfied _]] => rewrite satisfied_unfold; simpl
               | [|- context[dissatisfied _]] => rewrite dissatisfied_unfold; simpl
               | [|- _ /\ _] => split
               | [|- _ <-> _] => split
               | [|- _ -> _] => intros
               | [|- context [eliminateMinMax _]] => simpl
               | [H: ?A |- ?A] => apply H
               | [H: truth_or _ _ = Top |- _] => apply truth_or_true_iff in H
               | [H: truth_or _ _ = Btm |- _] => apply truth_or_false_iff in H
               | [H: _ \/ _ |- _] => destruct H
               | [H: truth_and _ _ = Top |- _] => apply truth_and_true_iff in H
               | [H: truth_and _ _ = Btm |- _] => apply truth_and_false_iff in H
               | [H: _ /\ _ |- _] => destruct H
               | [H: ?A = _ |- context[?A]] => rewrite H
               | [|- context[truth_and ?A ?A]] => rewrite tautology_3
               | [|- ?A = ?A /\ ?B = ?B \/ _] => left; intuition
               | [|- _ \/ ?A = ?A /\ ?B = ?B] => right; intuition
               | [H1 : num_leq ?A ?A = Top, H2 : num_leq ?A ?A = Top |- _] => clear H1
               | [H1 : num_leq ?A ?B = Top, H2 : num_leq ?B ?A = Top |- _] =>
                 let H := fresh "H" in
                 generalize (num_leq_refl _ _ H1 H2); intro H; rewrite H in *; clear H H1
               | [|- context[truth_and ?v (truth_and ?v _)]] => rewrite truth_and_assoc, tautology_3
               | [H : num_leq ?A ?B = Top |- context[num_leq ?B ?A]] => destruct (num_leq_top _ _ H)
               | [|- context[truth_or ?A ?A]] => rewrite tautology_5
               | [|- ?A = ?A] => trivial
               | [|- context[truth_and Btm Top]] => rewrite (truth_and_comm Btm Top), tautology_4
               | [|- context[truth_and Top Btm]] => rewrite tautology_4
               | [|- context[truth_or Top Btm]] => rewrite tautology_6
               | [|- context[truth_or Btm Top]] => rewrite (truth_or_comm Btm Top), tautology_6
               | [|- _ \/ ?A = ?A] => right; trivial
               | [H : num_leq ?A ?B = Btm |- context[num_leq ?B ?A]] => destruct (num_leq_btm _ _ H); clear H
               | [|- ?A = ?A \/ _] => left; trivial
               | [H : forall _, num_leq _ ?A = Btm /\ num_leq ?A _ = Btm |- context[num_leq ?B ?A]] =>
                 let H1 := fresh "H1" in let H2 := fresh "H2" in destruct (H B) as [H1 H2]; rewrite H1
               | [H : forall _, num_leq _ ?A = Btm /\ num_leq ?A _ = Btm |- context[num_leq ?A ?B]] =>
                 let H1 := fresh "H1" in let H2 := fresh "H2" in destruct (H B) as [H1 H2]; rewrite H2
               | [H : forall _, num_leq _ ?A = Btm /\ num_leq ?A _ = Btm, T: num_leq ?B ?A = Top |- _] =>
                 let H1 := fresh "H1" in let H2 := fresh "H2" in destruct (H B) as [H1 H2]; rewrite T in H1;
                                                                 exfalso; apply top_neq_btm; apply H1
               | [H : forall _, num_leq _ ?A = Btm /\ num_leq ?A _ = Btm, T: num_leq ?A ?B = Top |- _] =>
                 let H1 := fresh "H1" in let H2 := fresh "H2" in destruct (H B) as [H1 H2]; rewrite T in H2;
                                                                 exfalso; apply top_neq_btm; apply H2
               | [H1 : num_leq ?x ?z = Top, H2: num_leq ?y ?z = Top |- context[num_leq ?x ?y]] =>
                 destruct (num_leq_both_leq x y z H1 H2)
               | [H1 : ?A = ?B, H2: context[?A] |- _] => rewrite H1 in H2
               | [H : forall m n : A, num_leq m n = Top \/ num_leq m n = Btm |- context[num_leq ?A ?B]] => destruct (H A B)
               | [H1 : num_leq ?x ?y = Top, H2: num_leq ?y ?z = Top |- context[num_leq ?x ?z]] =>
                 let H := fresh "H" in generalize (num_leq_trans _ _ _ H1 H2); intro H; rewrite H
               | [H1 : num_leq ?z ?x = Top, H2: num_leq ?z ?y = Top |- context[num_leq ?x ?y]] =>
                 destruct (num_leq_leq_both x y z H1 H2)
               | [H1 : num_leq ?x ?y = Btm, H2: num_leq ?y ?z = Btm |- context[num_leq ?x ?z]] =>
                 let H := fresh "H" in destruct (num_leq_btm_trans _ _ _ H1 H2) as [H | H]; rewrite H
               | [H1: num_leq ?x ?y = Btm, H2: num_leq ?y ?x = Btm |- _] => destruct (num_leq_btm _ _ H1)
               | [H: Btm = Top |- _] => exfalso; apply top_neq_btm
             end.

    (* Elimination of min and max doesn't change the validity of boolean forms *)
    Lemma eliminate_ok: forall z, (satisfied (ZF_BF z) <-> satisfied (eliminateMinMax z)) /\
                                  (dissatisfied (ZF_BF z) <-> dissatisfied (eliminateMinMax z)).
    Proof. solve_eliminate. Qed.

    Inductive SimpResult (f : ZF) :=
    | EQ_Top : f = ZF_BF (ZBF_Const Top) -> SimpResult f
    | EQ_Btm : f = ZF_BF (ZBF_Const Btm) -> SimpResult f
    | OTHER : f <> ZF_BF (ZBF_Const Top) /\ f <> ZF_BF (ZBF_Const Btm) -> SimpResult f.

    Definition judge (f : ZF) : SimpResult f.
      destruct f eqn : ?;
                         try (destruct z;
                              try (destruct (val_eq_dec v Top);
                                   [apply EQ_Top; rewrite e; trivial |
                                    destruct (val_eq_dec v Btm); [apply EQ_Btm; rewrite e; trivial |
                                                                  apply OTHER; split; intro; inversion H; contradiction]]);
                              apply OTHER; intuition; inversion H);
      apply OTHER; intuition; inversion H.
    Defined.

    (* Further Simplification: Elimination of boolean constants and min/max *)
    Fixpoint simplifyZF (form : ZF) : ZF :=
      match form with
          ZF_BF bf => eliminateMinMax bf
        | ZF_And f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                              e1, e2 =>
                              match (judge e1), (judge e2) with
                                | EQ_Top _, _ => e2
                                | _, EQ_Top _ => e1
                                | EQ_Btm _, _
                                | _, EQ_Btm _ => ZF_BF (ZBF_Const Btm)
                                | _, _ => ZF_And e1 e2
                              end
                          end
        | ZF_Or f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                             e1, e2 =>
                             match (judge e1), (judge e2) with
                               | EQ_Top _, _
                               | _, EQ_Top _ => ZF_BF (ZBF_Const Top)
                               | EQ_Btm _, _ => e2
                               | _, EQ_Btm _ => e1
                               | _, _ => ZF_Or e1 e2
                             end
                         end
        | ZF_Imp f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                              e1, e2 =>
                              match (judge e1), (judge e2) with
                                | EQ_Btm _, _
                                | _, EQ_Top _ => ZF_BF (ZBF_Const Top)
                                | EQ_Top _, EQ_Btm _ => ZF_BF (ZBF_Const Btm)
                                | EQ_Top _, _ => e2
                                | OTHER _, EQ_Btm _ => ZF_Not e1
                                | _, _ => ZF_Imp e1 e2
                              end
                          end
        | ZF_Not f => match (simplifyZF f) with
                          e => match (judge e) with
                                 | EQ_Top _ => ZF_BF (ZBF_Const Btm)
                                 | EQ_Btm _ => ZF_BF (ZBF_Const Top)
                                 | OTHER _ => ZF_Not e
                               end
                      end
        | ZF_Forall v q f => ZF_Forall v q (simplifyZF f)
        | ZF_Exists v q f => ZF_Exists v q (simplifyZF f)
      end.

  End Simplification.

End ArithSemantics.
