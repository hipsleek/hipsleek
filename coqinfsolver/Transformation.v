Require Import Theory.
Require Import ZArith.
Require Import FunctionalExtensionality.

Import ZInfinity.

Module InfSolver (sv:VARIABLE) (VAL : SEM_VAL) (S: NONE_RELATION VAL) (FZT : ZERO_FIN) (IZT : ZERO_INF).
  Import sv.
  Import VAL.
  Import S.

  Module InfRel := InfLeqRelation VAL S.
  Module FinRel := FinLeqRelation VAL.

  (* Both variable and constant domain can be integers with infinity. *)
  Module IA := ArithSemantics PureInfinity sv VAL InfRel IZT.

  (* Both variable and constant domain are integers. *)
  Module FA := ArithSemantics PureInt sv VAL FinRel FZT.

  (* Variable domain is integers and constant domain is integers with infinity. *)
  Module I2F := ArithSemantics IntToInfinity sv VAL InfRel IZT.

  Section RealExtension.

    Lemma exists_extension_sat: forall x P, IA.satisfied (IA.ZF_Exists x PureInfinity.Q_Z P) ->
                                            IA.satisfied (IA.ZF_Exists x PureInfinity.Q_ZE P).
    Proof. intros; rewrite IA.satisfied_unfold in *; destruct H as [x0 H]; simpl in *; exists (ZE_Fin x0); trivial. Qed.

    Lemma forall_extension_sat: forall x P, IA.satisfied (IA.ZF_Forall x PureInfinity.Q_ZE P) ->
                                            IA.satisfied (IA.ZF_Forall x PureInfinity.Q_Z P).
    Proof. intros; rewrite IA.satisfied_unfold in *; intros; simpl in *; apply H. Qed.

    Lemma exists_extension_dissat: forall x P, IA.dissatisfied (IA.ZF_Exists x PureInfinity.Q_ZE P) ->
                                               IA.dissatisfied (IA.ZF_Exists x PureInfinity.Q_Z P).
    Proof. intros; rewrite IA.dissatisfied_unfold in *; intros; simpl in *; apply H. Qed.

    Lemma forall_extension_dissat: forall x P, IA.dissatisfied (IA.ZF_Forall x PureInfinity.Q_Z P) ->
                                               IA.dissatisfied (IA.ZF_Forall x PureInfinity.Q_ZE P).
    Proof. intros; rewrite IA.dissatisfied_unfold in *; destruct H as [x0 H]; simpl in *; exists (ZE_Fin x0); trivial. Qed.

  End RealExtension.

  Section InfinityTransformation.

    (* Transform expressions in IA to I2F *)
    Fixpoint inf_trans_exp (exp : IA.ZExp) : I2F.ZExp :=
      match exp with
          IA.ZExp_Var v => I2F.ZExp_Var v
        | IA.ZExp_Const a => I2F.ZExp_Const a
        | IA.ZExp_Add e1 e2 => I2F.ZExp_Add (inf_trans_exp e1) (inf_trans_exp e2)
        | IA.ZExp_Inv e => I2F.ZExp_Inv (inf_trans_exp e)
        | IA.ZExp_Sub e1 e2 => I2F.ZExp_Sub (inf_trans_exp e1) (inf_trans_exp e2)
        | IA.ZExp_Mult z e => I2F.ZExp_Mult z (inf_trans_exp e)
      end.

    (* Expression transformation keeps the evaluation. *)
    Lemma inf_trans_exp_ok : forall exp, IA.dexp2ZE exp = I2F.dexp2ZE (inf_trans_exp exp).
    Proof.
      induction exp; simpl; auto;
      try (rewrite IHexp1, IHexp2; auto);
      try (rewrite IHexp; auto).
    Qed.

    (* Transform boolean forms in IA to I2F *)
    Definition inf_trans_bf (bf : IA.ZBF) : I2F.ZBF :=
      match bf with
          IA.ZBF_Const b => I2F.ZBF_Const b
        | IA.ZBF_Lt f1 f2 => I2F.ZBF_Lt (inf_trans_exp f1) (inf_trans_exp f2)
        | IA.ZBF_Lte f1 f2 => I2F.ZBF_Lte (inf_trans_exp f1) (inf_trans_exp f2)
        | IA.ZBF_Gt f1 f2 => I2F.ZBF_Gt (inf_trans_exp f1) (inf_trans_exp f2)
        | IA.ZBF_Gte f1 f2 => I2F.ZBF_Gte (inf_trans_exp f1) (inf_trans_exp f2)
        | IA.ZBF_Eq f1 f2 => I2F.ZBF_Eq (inf_trans_exp f1) (inf_trans_exp f2)
        | IA.ZBF_Eq_Max f1 f2 f3 => I2F.ZBF_Eq_Max (inf_trans_exp f1) (inf_trans_exp f2) (inf_trans_exp f3)
        | IA.ZBF_Eq_Min f1 f2 f3 => I2F.ZBF_Eq_Min (inf_trans_exp f1) (inf_trans_exp f2) (inf_trans_exp f3)
        | IA.ZBF_Neq f1 f2 => I2F.ZBF_Neq (inf_trans_exp f1) (inf_trans_exp f2)
      end.

    (* Boolean form transformation keeps the validity. *)
    Lemma inf_trans_bf_ok : forall z, IA.satisfied (IA.ZF_BF z) <-> I2F.satisfied (I2F.ZF_BF (inf_trans_bf z)).
    Proof.
      destruct z; simpl;
      rewrite IA.satisfied_unfold, I2F.satisfied_unfold;
      simpl; repeat rewrite inf_trans_exp_ok; tauto.
    Qed.

    Lemma inf_trans_bf_dst : forall z, IA.dissatisfied (IA.ZF_BF z) <-> I2F.dissatisfied (I2F.ZF_BF (inf_trans_bf z)).
    Proof.
      destruct z; simpl;
      rewrite IA.dissatisfied_unfold, I2F.dissatisfied_unfold;
      simpl; repeat rewrite inf_trans_exp_ok; tauto.
    Qed.

    (* Transform logic forms in IA to I2F *)
    Definition inf_trans : IA.ZF -> I2F.ZF :=
      Fix IA.lengthOrder_wf (fun _ => I2F.ZF)
          (fun (form : IA.ZF) =>
             match form return ((forall f : IA.ZF, IA.lengthOrder f form -> I2F.ZF) -> I2F.ZF) with
                 IA.ZF_BF bf => fun _ => I2F.ZF_BF (inf_trans_bf bf)
               | IA.ZF_And f1 f2 => fun infTrans => I2F.ZF_And (infTrans f1 (IA.lengthOrder_and_1 f1 f2))
                                                               (infTrans f2 (IA.lengthOrder_and_2 f1 f2))
               | IA.ZF_Or f1 f2 => fun infTrans => I2F.ZF_Or (infTrans f1 (IA.lengthOrder_or_1 f1 f2))
                                                             (infTrans f2 (IA.lengthOrder_or_2 f1 f2))
               | IA.ZF_Imp f1 f2 => fun infTrans => I2F.ZF_Imp (infTrans f1 (IA.lengthOrder_imp_1 f1 f2))
                                                               (infTrans f2 (IA.lengthOrder_imp_2 f1 f2))
               | IA.ZF_Not f' => fun infTrans => I2F.ZF_Not (infTrans f' (IA.lengthOrder_not f'))
               | IA.ZF_Forall v q f' =>
                 match q with
                     PureInfinity.Q_Z =>
                     fun infTrans => I2F.ZF_Forall v tt (infTrans f' (IA.lengthOrder_forall_trivial f' v PureInfinity.Q_Z))
                   | PureInfinity.Q_ZE =>
                     fun infTrans =>
                       I2F.ZF_And (I2F.ZF_Forall v tt (infTrans f' (IA.lengthOrder_forall_trivial f' v PureInfinity.Q_ZE)))
                                  (I2F.ZF_And (infTrans (IA.substitute (v, Some ZE_Inf) f')
                                                        (IA.lengthOrder_forall f' v PureInfinity.Q_ZE ZE_Inf))
                                              (infTrans (IA.substitute (v, Some ZE_NegInf) f')
                                                        (IA.lengthOrder_forall f' v PureInfinity.Q_ZE ZE_NegInf)))
                 end
               | IA.ZF_Exists v q f' =>
                 match q with
                     PureInfinity.Q_Z =>
                     fun infTrans => I2F.ZF_Exists v tt (infTrans f' (IA.lengthOrder_exists_trivial f' v PureInfinity.Q_Z))
                   | PureInfinity.Q_ZE =>
                     fun infTrans =>
                       I2F.ZF_Or (I2F.ZF_Exists v tt (infTrans f' (IA.lengthOrder_exists_trivial f' v PureInfinity.Q_ZE)))
                                 (I2F.ZF_Or (infTrans (IA.substitute (v, Some ZE_Inf) f')
                                                      (IA.lengthOrder_exists f' v PureInfinity.Q_ZE ZE_Inf))
                                            (infTrans (IA.substitute (v, Some ZE_NegInf) f')
                                                      (IA.lengthOrder_exists f' v PureInfinity.Q_ZE ZE_NegInf)))
                 end
             end).

    Lemma inf_trans_unfold:
      forall form,
        inf_trans form =
        match form with
            IA.ZF_BF bf => I2F.ZF_BF (inf_trans_bf bf)
          | IA.ZF_And f1 f2 => I2F.ZF_And (inf_trans f1) (inf_trans f2)
          | IA.ZF_Or f1 f2 => I2F.ZF_Or (inf_trans f1) (inf_trans f2)
          | IA.ZF_Imp f1 f2 => I2F.ZF_Imp (inf_trans f1) (inf_trans f2)
          | IA.ZF_Not f => I2F.ZF_Not (inf_trans f)
          | IA.ZF_Forall v q f =>
            match q with
                PureInfinity.Q_Z => I2F.ZF_Forall v tt (inf_trans f)
              | PureInfinity.Q_ZE => I2F.ZF_And (I2F.ZF_Forall v tt (inf_trans f))
                                                (I2F.ZF_And (inf_trans (IA.substitute (v, Some ZE_Inf) f))
                                                            (inf_trans (IA.substitute (v, Some ZE_NegInf) f)))
            end
          | IA.ZF_Exists v q f =>
            match q with
                PureInfinity.Q_Z => I2F.ZF_Exists v tt (inf_trans f)
              | PureInfinity.Q_ZE => I2F.ZF_Or (I2F.ZF_Exists v tt (inf_trans f))
                                               (I2F.ZF_Or (inf_trans (IA.substitute (v, Some ZE_Inf) f))
                                                          (inf_trans (IA.substitute (v, Some ZE_NegInf) f)))
            end
        end.
    Proof.
      intro; unfold inf_trans at 1; rewrite Fix_eq.
      destruct form; auto;
      destruct q; auto.
      intros; match goal with
                | [H : forall (y : IA.ZF) (p : IA.lengthOrder y ?x), ?f y p = ?g y p |- _ ] =>
                  assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto);
                    destruct x; auto; repeat (f_equal; auto); rewrite HFunEq; reflexivity
              end.
    Qed.

    (* Substitution and expression transformation from IA to I2F are commutative. *)
    Lemma subst_inf_trans_exp_eq : forall z v (x : option ZE),
                                     I2F.subst_exp (v, x) (inf_trans_exp z) = inf_trans_exp (IA.subst_exp (v, x) z).
    Proof.
      induction z; simpl; intros;
      try (destruct (var_eq_dec v0 v); simpl);
      try (rewrite IHz1, IHz2);
      try (rewrite IHz);
      auto.
    Qed.

    (* Substitution and boolean form transformation from IA to I2F are commutative. *)
    Lemma subst_inf_trans_bf_eq : forall z v (x : option ZE),
                                    I2F.substitute (v, x) (inf_trans (IA.ZF_BF z)) =
                                    inf_trans (IA.substitute (v, x) (IA.ZF_BF z)).
    Proof.
      destruct z; simpl; intros;
      unfold inf_trans;
      unfold IA.length_zform;
      simpl; auto;
      repeat rewrite subst_inf_trans_exp_eq; auto.
    Qed.

    Ltac unfold_right_inf_trans :=
      match goal with
        | [|- _ = inf_trans ?X] => rewrite inf_trans_unfold with X; auto
      end.

    (* Substitution and logic form transformation from IA to I2F are commutative. *)
    Lemma subst_inf_trans_eq: forall f v (x: option ZE), I2F.substitute (v, x) (inf_trans f) =
                                                         inf_trans (IA.substitute (v, x) f).
    Proof.
      intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H;
      induction n; intros;
      [ destruct f; exfalso; simpl in H; intuition |
        destruct f; simpl in H; apply le_S_n in H;
        let solve_cnt := (rewrite inf_trans_unfold; simpl; rewrite (IHn f1), (IHn f2);
                          [unfold_right_inf_trans | omega | omega ]) in
        let solve_quant :=
            rewrite inf_trans_unfold; destruct q; simpl;
            [destruct (var_eq_dec v v0); unfold_right_inf_trans; rewrite IHn; auto |
             destruct (var_eq_dec v v0); repeat rewrite <- IHn; auto;
             [rewrite e; repeat rewrite I2F.same_var_subst |
              repeat rewrite I2F.diff_var_subst with (v1 := v) (v2 := v0); auto];
             unfold_right_inf_trans; repeat rewrite IHn; auto; rewrite <- IA.substitute_length_inv; auto] in
        solve [rewrite subst_inf_trans_bf_eq; auto | solve_cnt | solve_cnt | solve_cnt |
               rewrite inf_trans_unfold; simpl; rewrite IHn; [unfold_right_inf_trans | omega ] |
               solve_quant | solve_quant]].
    Qed.

    Ltac solve_le_inv :=
      match goal with
        | [|- IA.length_zform (IA.substitute _ _) <= _] => rewrite <- IA.substitute_length_inv; auto
      end.

    (* Logic form transformation from IA to I2F keeps the validity. *)
    Lemma inf_trans_ok : forall f, (IA.satisfied f <-> I2F.satisfied (inf_trans f)) /\
                                   (IA.dissatisfied f <-> I2F.dissatisfied (inf_trans f)).
    Proof.
      intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H.
      induction n; intros.
      exfalso; destruct f; simpl in H; intuition.
      split.
      (* ok part *)
      destruct f; simpl in H; apply le_S_n in H; rewrite inf_trans_unfold; try (rewrite inf_trans_bf_ok; intuition);
      rewrite IA.satisfied_unfold, I2F.satisfied_unfold.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S: IA.length_zform f <= n) by omega; destruct (IHn _ S); intuition.

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
      destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
      split; intros; assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST];
      [rewrite subst_inf_trans_eq; rewrite <- SAT | rewrite SAT; rewrite <- subst_inf_trans_eq]; apply H0.
      do 2 rewrite I2F.satisfied_unfold; split; intros.
      split; intros.
      assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite subst_inf_trans_eq; rewrite <- SAT; apply H0.
      split; [rewrite <- SAT1 | rewrite <- SAT2].
      apply H0. apply H0. destruct H0 as [? [? ?]].
      destruct x.
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite SAT; rewrite <- subst_inf_trans_eq; apply H0.
      rewrite SAT1; apply H1. rewrite SAT2; apply H2.

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
      destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
      split; intros; destruct H0 as [x H0]; exists x;
      assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST];
      [rewrite subst_inf_trans_eq; rewrite <- SAT | rewrite SAT; rewrite <- subst_inf_trans_eq]; apply H0.
      do 2 rewrite I2F.satisfied_unfold; split; intros.
      destruct H0 as [x H0]; destruct x.
      left; exists z; rewrite subst_inf_trans_eq.
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite <- SAT; apply H0.
      right; left; rewrite <- SAT1; apply H0.
      right; right; rewrite <- SAT2; apply H0.
      destruct H0; destruct H0.
      exists (ZE_Fin x).
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_ZE (ZE_Fin x)) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite SAT; rewrite <- subst_inf_trans_eq; apply H0.
      exists ZE_Inf; rewrite SAT1; apply H0.
      exists ZE_NegInf; rewrite SAT2; apply H0.

      (* dst part *)
      (* intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H; *)
      destruct f; simpl in H; apply le_S_n in H; rewrite inf_trans_unfold; try (rewrite inf_trans_bf_dst; intuition);
      rewrite IA.dissatisfied_unfold, I2F.dissatisfied_unfold.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
      destruct (IHn _ S1); destruct (IHn _ S2); intuition.
      assert (S: IA.length_zform f <= n) by omega; destruct (IHn _ S); intuition.

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
      destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
      split; intros; destruct H0 as [x H0]; exists x;
      assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST];
      [rewrite subst_inf_trans_eq; rewrite <- DST | rewrite DST; rewrite <- subst_inf_trans_eq]; apply H0.
      do 2 rewrite I2F.dissatisfied_unfold; split; intros.
      destruct H0 as [x H0]; destruct x.
      left; exists z; rewrite subst_inf_trans_eq.
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite <- DST; apply H0.
      right; left; rewrite <- DST1; apply H0.
      right; right; rewrite <- DST2; apply H0.
      destruct H0; destruct H0.
      exists (ZE_Fin x).
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_ZE (ZE_Fin x)) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite DST; rewrite <- subst_inf_trans_eq; apply H0.
      exists ZE_Inf; rewrite DST1; apply H0.
      exists ZE_NegInf; rewrite DST2; apply H0.

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
      destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
      split; intros; assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST];
      [rewrite subst_inf_trans_eq; rewrite <- DST | rewrite DST; rewrite <- subst_inf_trans_eq]; apply H0.
      do 2 rewrite I2F.dissatisfied_unfold; split; intros.
      split; intros.
      assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite subst_inf_trans_eq; rewrite <- DST; apply H0.
      split; [rewrite <- DST1 | rewrite <- DST2].
      apply H0. apply H0. destruct H0 as [? [? ?]].
      destruct x.
      assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
        destruct (IHn _ INV) as [SAT DST].
      rewrite DST; rewrite <- subst_inf_trans_eq; apply H0.
      rewrite DST1; apply H1. rewrite DST2; apply H2.
    Qed.

  End InfinityTransformation.

  Section IntegerTransformation.

    (* Shortened Forms of Boolean Constants *)
    Definition embed (v : Val) := FA.ZF_BF (FA.ZBF_Const v).
    Definition FATrue := embed Top.
    Definition FAFalse := embed Btm.
    Definition FANone := embed noneVal.

    (* Projection from integers with infinity to integers *)
    Definition proj (z : IntToInfinity.N.A) : Z :=
      match z with
          Some (ZE_Fin x) => x
        | _ => 0%Z (* This case doesn't happen actually. *)
      end.

    (* Transform expressions in I2F to FA *)
    Fixpoint int_trans_exp (exp : I2F.ZExp) : FA.ZExp :=
      match exp with
          I2F.ZExp_Var v => FA.ZExp_Var v
        | I2F.ZExp_Const a => FA.ZExp_Const (proj a)
        | I2F.ZExp_Add e1 e2 => FA.ZExp_Add (int_trans_exp e1) (int_trans_exp e2)
        | I2F.ZExp_Inv e => FA.ZExp_Inv (int_trans_exp e)
        | I2F.ZExp_Sub e1 e2 => FA.ZExp_Sub (int_trans_exp e1) (int_trans_exp e2)
        | I2F.ZExp_Mult z e => FA.ZExp_Mult z (int_trans_exp e)
      end.

    (* Transform boolean forms in I2F to FA *)
    Definition int_trans_bf (bf : I2F.ZBF) : FA.ZF :=
      match bf with
          I2F.ZBF_Const f => FA.ZF_BF (FA.ZBF_Const f)
        | I2F.ZBF_Lt e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_NegInf, Some x => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some _, Some ZE_NegInf => FAFalse
            | Some ZE_Inf, Some _ => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Lt (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Lte e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some _, Some ZE_Inf => FATrue
            | Some ZE_NegInf, Some _ => FATrue
            | Some ZE_Inf, Some x => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Lte (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Gt e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_Inf, Some x => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some _, Some ZE_Inf => FAFalse
            | Some ZE_NegInf, Some _ => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Gt (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Gte e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some _, Some ZE_NegInf => FATrue
            | Some ZE_Inf, Some _ => FATrue
            | Some ZE_NegInf, Some x => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Gte (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Eq e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_NegInf, Some x
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some ZE_Inf, Some x
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Eq_Max e1 e2 e3 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2), (I2F.dexp2ZE e3) with
              None, _, _
            | _, None, _
            | _, _, None => FANone
            | Some ZE_NegInf, Some x, Some y =>
              if (ZE_eq_dec x ZE_NegInf)
              then if (ZE_eq_dec y ZE_NegInf)
                   then FATrue
                   else FAFalse
              else FAFalse
            | Some ZE_Inf, Some x, Some y =>
              if ZE_eq_dec x ZE_Inf
              then FATrue
              else if ZE_eq_dec y ZE_Inf
                   then FATrue
                   else FAFalse
            | Some (ZE_Fin _), Some ZE_NegInf, Some y =>
              match y with
                  ZE_NegInf
                | ZE_Inf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e3))
              end
            | Some (ZE_Fin _), Some y, Some ZE_NegInf =>
              match y with
                  ZE_NegInf
                | ZE_Inf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
              end
            | Some (ZE_Fin _), Some ZE_Inf, Some y
            | Some (ZE_Fin _), Some y, Some ZE_Inf => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _), Some(ZE_Fin _) =>
              FA.ZF_BF (FA.ZBF_Eq_Max (int_trans_exp e1) (int_trans_exp e2) (int_trans_exp e3))
          end
        | I2F.ZBF_Eq_Min e1 e2 e3 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2), (I2F.dexp2ZE e3) with
              None, _, _
            | _, None, _
            | _, _, None => FANone
            | Some ZE_NegInf, Some x, Some y =>
              if ZE_eq_dec x ZE_NegInf
              then FATrue
              else if ZE_eq_dec y ZE_NegInf
                   then FATrue
                   else FAFalse
            | Some ZE_Inf, Some x, Some y =>
              if (ZE_eq_dec x ZE_Inf)
              then if (ZE_eq_dec y ZE_Inf)
                   then FATrue
                   else FAFalse
              else FAFalse
            | Some (ZE_Fin _), Some ZE_NegInf, Some y
            | Some (ZE_Fin _), Some y, Some ZE_NegInf => FAFalse
            | Some (ZE_Fin _), Some ZE_Inf, Some y =>
              match y with
                  ZE_Inf
                | ZE_NegInf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e3))
              end
            | Some (ZE_Fin _), Some y, Some ZE_Inf =>
              match y with
                  ZE_Inf
                | ZE_NegInf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
              end
            | Some (ZE_Fin _), Some (ZE_Fin _), Some(ZE_Fin _) =>
              FA.ZF_BF (FA.ZBF_Eq_Min (int_trans_exp e1) (int_trans_exp e2) (int_trans_exp e3))
          end
        | I2F.ZBF_Neq e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => embed (truth_not noneVal)
            | Some ZE_NegInf, Some x
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some ZE_Inf, Some x
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Neq (int_trans_exp e1) (int_trans_exp e2))
          end
      end.

    Ltac solve_b :=
      repeat match goal with
               |[H: Some (ZE_Fin _) = Some (ZE_Fin _) |- _] => injection H; intro; clear H
               |[H: ?X = ?Y |- ?Y = ?X] => rewrite H; trivial
               |[H: context[match ?v with _ => _ end] |- _] => destruct v
               |[H: None = Some _ |- _] => discriminate H
               |[H: Some _ = None |- _] => discriminate H
               |[H: Some ZE_Inf = Some (ZE_Fin _) |- _] => discriminate H
               |[H: Some ZE_NegInf = Some (ZE_Fin _) |- _] => discriminate H
               |[H: Some (ZE_Fin _) = Some ZE_Inf  |- _] => discriminate H
               |[H: Some (ZE_Fin _) = Some ZE_NegInf |- _] => discriminate H
               |[H: Some ZE_NegInf = Some ZE_Inf |- _] => discriminate H
               |[H: Some ZE_Inf = Some ZE_NegInf |- _] => discriminate H
             end.

    (* If natural number product is finite, then either the constant is zero or the variable is finite. *)
    Lemma nat_nummult_finite: forall c v x,
                                I2F.num_mult_nat c v = Some (IntToInfinity.N.ZE_Fin x)
                                -> ((c = 0 /\ x = 0%Z) \/ (exists n, v = Some (ZE_Fin n) /\ FA.num_mult_nat c n = x)).
    Proof.
      induction c; intros.
      left; split; auto; destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; clear H0; solve_b.
      right; simpl in H.

      destruct c. exists x; intuition. apply numplus_finite in H.
      destruct H as [z1 [z2 [? [? ?]]]].
      exists z1; split; auto.
      apply IHc in H0.
      destruct H0 as [[? ?] | [n [? ?]]].
      discriminate H0.
      rewrite H in H0; injection H0; intro; rewrite H3 in *; clear H3 z1.
      rewrite FA.num_mult_nat_2_unfold, H2; unfold PureInt.N.num_plus; auto.
    Qed.

    (* If product is finite, then either the constant is zero or the variable is finite. *)
    Lemma nummult_finite: forall c v x, I2F.num_mult c v = Some (IntToInfinity.N.ZE_Fin x)
                                        -> (c = 0%Z /\ x = 0%Z) \/
                                           (exists n, v = Some (ZE_Fin n) /\ FA.num_mult c n = x).
    Proof.
      destruct c; simpl; intros.
      left; split; auto; destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; clear H0; solve_b.
      apply nat_nummult_finite in H.
      destruct H.
      destruct H.
      left.
      assert (0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
      omega.
      destruct H, H.
      right; exists x0.
      split; auto.
      apply numneg_finite in H.
      destruct H, H.
      apply nat_nummult_finite in H.
      destruct H.
      assert (0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
      omega.
      destruct H, H.
      right; exists x1.
      split; auto.
      rewrite H1; auto.
    Qed.

    (* Expression transform from I2F to FA keeps the finiteness. *)
    Lemma dexp2ZE_int_trans_eq: forall z x, I2F.dexp2ZE z = Some (IntToInfinity.N.ZE_Fin x) -> FA.dexp2ZE (int_trans_exp z) = x.
    Proof.
      induction z; simpl; intros.
      injection H; auto.
      rewrite H; auto.
      apply numplus_finite in H;
        destruct H, H, H; destruct H0;
        apply IHz1 in H;
        apply IHz2 in H0;
        rewrite H, H0; auto.

      apply numneg_finite in H;
        destruct H, H;
        apply IHz in H;
        rewrite H; auto.

      apply numplus_finite in H;
        destruct H, H, H; destruct H0;
        apply numneg_finite in H0;
        destruct H0, H0;
        apply IHz1 in H;
        apply IHz2 in H0;
        rewrite H, H0;
        rewrite <- H2 in H1;
        auto.

      apply nummult_finite in H.
      destruct H as [[? ?] | [? [? ?]]].
      rewrite H, H0 in *; clear H H0; simpl.
      rewrite FZT.all_is_zero; trivial.
      apply IHz in H.
      rewrite H; auto.
    Qed.

    Ltac smash_int_trans_bf :=
      repeat match goal with
               | [|- context[FinRel.num_leq _ _]] => unfold FinRel.num_leq
               | [ H: FANone = _ |- _] => unfold FANone in H; unfold embed in H; inversion H; simpl
               | [|- context[truth_not Btm]] => rewrite tautology_1
               | [|- context[truth_not Top]] => rewrite tautology_2
               | [|- context[truth_and ?X ?X]] => rewrite tautology_3
               | [|- context[truth_and Top Btm]] => rewrite tautology_4
               | [|- context[truth_and Btm Top]] => rewrite (truth_and_comm Btm Top), tautology_4
               | [|- context[truth_or ?X ?X]] => rewrite tautology_5
               | [|- context[truth_or Top Btm]] => rewrite tautology_6
               | [|- context[truth_or Btm Top]] => rewrite (truth_or_comm Btm Top), tautology_6
               | [|- context[truth_and noneVal (truth_not noneVal)]] => rewrite none_tautology_1
               | [|- context[truth_and noneVal Top]] => rewrite none_tautology_2
               | [|- context[truth_and Top noneVal]] => rewrite (truth_and_comm Top noneVal), none_tautology_2
               | [|- context[truth_or (truth_and noneVal Btm) noneVal]] => rewrite none_tautology_3
               | [|- context[truth_or noneVal Btm]] => rewrite none_tautology_4
               | [|- context[truth_or Btm noneVal]] => rewrite truth_or_comm, none_tautology_4
               | [H: I2F.dexp2ZE ?z = Some (IntToInfinity.N.ZE_Fin ?x) |- context[FA.dexp2ZE (int_trans_exp ?z)]]
                 => rewrite (dexp2ZE_int_trans_eq z x)
               | [|- ?X <-> ?X] => tauto
               | [H: ?X |- ?X] => apply H
               | [|- context[match (I2F.dexp2ZE ?X) with _ => _ end]] => destruct (I2F.dexp2ZE X) eqn: ?; simpl
               | [|- context[match ?X with _ => _ end]] => destruct X eqn: ?; simpl
               | [H: context[match ?X with _ => _ end] |- _] => destruct X eqn: ?; simpl
               | [|- context[InfRel.num_leq _ _]] => unfold InfRel.num_leq
               | [_: (?a <= ?b)%Z, _: ~ (?a <= ?b)%Z |- _] => contradiction
               | [_: ~ (?a <= ?b)%Z, _: ~ (?b <= ?a)%Z |- _] => exfalso; intuition
               | [|- context[truth_and Top noneVal]] => rewrite truth_and_comm, none_tautology_2
               | [|- context[truth_or noneVal (truth_and noneVal Btm)]] => rewrite truth_or_comm, none_tautology_3
               | [|- context[truth_or noneVal (truth_and Btm noneVal)]] =>
                 rewrite truth_or_comm, truth_and_comm, none_tautology_3
               | [|- context[truth_or (truth_and Btm noneVal) noneVal]] => rewrite truth_and_comm, none_tautology_3
             end.

    (* Boolean transformation from I2F to FA keeps the validity. *)
    Lemma int_trans_bf_sat: forall bf, I2F.satisfied (I2F.ZF_BF bf) <-> FA.satisfied (int_trans_bf bf).
    Proof. destruct bf; simpl; rewrite I2F.satisfied_unfold, FA.satisfied_unfold; simpl; smash_int_trans_bf. Qed.

    Lemma int_trans_bf_dst: forall bf, I2F.dissatisfied (I2F.ZF_BF bf) <-> FA.dissatisfied (int_trans_bf bf).
    Proof. destruct bf; simpl; rewrite I2F.dissatisfied_unfold, FA.dissatisfied_unfold; simpl; smash_int_trans_bf. Qed.

    (* Transform logic forms from I2F to FA *)
    Fixpoint int_trans (form : I2F.ZF) : FA.ZF :=
      match form with
          I2F.ZF_BF bf => int_trans_bf bf
        | I2F.ZF_And f1 f2 => FA.ZF_And (int_trans f1) (int_trans f2)
        | I2F.ZF_Or f1 f2 => FA.ZF_Or (int_trans f1) (int_trans f2)
        | I2F.ZF_Imp f1 f2 => FA.ZF_Imp (int_trans f1) (int_trans f2)
        | I2F.ZF_Not f => FA.ZF_Not (int_trans f)
        | I2F.ZF_Forall v q f => FA.ZF_Forall v q (int_trans f)
        | I2F.ZF_Exists v q f => FA.ZF_Exists v q (int_trans f)
      end.

    (* The products in I2F and FA are equal for finite natural number *)
    Lemma nat_nummult_eq: forall z x, I2F.num_mult_nat z (Some (ZE_Fin x)) = Some (ZE_Fin (FA.num_mult_nat z x)).
    Proof.
      induction z; intros.
      simpl; destruct IZT.zero_times_spec as [? | [? | ?]];
      rewrite FZT.all_is_zero, H; trivial.

      unfold I2F.num_mult_nat; fold I2F.num_mult_nat;
      unfold FA.num_mult_nat; fold FA.num_mult_nat;
      destruct z; [auto | rewrite IHz; auto].
    Qed.

    (* The products in I2F and FA are equal for finite integer number *)
    Lemma nummult_eq: forall z x, I2F.num_mult z (Some (ZE_Fin x)) = Some (ZE_Fin (FA.num_mult z x)).
    Proof.
      destruct z; intros.
      simpl; destruct IZT.zero_times_spec as [? | [? | ?]];
      rewrite FZT.all_is_zero, H; trivial.
      unfold I2F.num_mult, FA.num_mult.
      apply nat_nummult_eq.
      unfold I2F.num_mult, FA.num_mult.
      rewrite nat_nummult_eq; auto.
    Qed.

    (* Substitution keeps the finiteness of expressions. *)
    Lemma finite_subst2finite: forall z v x c1, I2F.dexp2ZE z = Some (ZE_Fin c1) ->
                                                (exists c2, I2F.dexp2ZE (I2F.subst_exp (v, @IntToInfinity.conv tt x) z) =
                                                            Some (ZE_Fin c2)).
    Proof.
      induction z; simpl; intros.
      destruct (var_eq_dec v0 v); [exists x | exists 0%Z]; simpl; auto.
      exists c1; auto.
      apply numplus_finite in H; destruct H, H, H; destruct H0;
      apply (IHz1 v x) in H; apply (IHz2 v x) in H0; destruct H, H0; rewrite H, H0; exists (x2 + x3)%Z; auto.
      apply numneg_finite in H; destruct H, H; apply (IHz v x) in H; destruct H; rewrite H; exists (- x1)%Z; auto.
      apply numplus_finite in H; destruct H, H, H; destruct H0; apply numneg_finite in H0; destruct H0, H0;
      apply (IHz1 v x) in H; apply (IHz2 v x) in H0; destruct H, H0;
      rewrite H, H0; rewrite <- H2 in H1; exists (x3 - x4)%Z; auto.

      destruct (nummult_finite _ _ _ H) as [[? ?] | [? [? ?]]].
      rewrite H0, H1 in *; clear H0 H1 z c1; simpl in *.
      destruct IZT.zero_times_spec as [? | [? | ?]]; exists 0%Z.
      rewrite H0; trivial.

      destruct (I2F.dexp2ZE z0) eqn : ?; rewrite H0 in H; solve_b;
      assert (S : Some (IntToInfinity.N.ZE_Fin z) = Some (ZE_Fin z)) by trivial; specialize (IHz v x z S);
      destruct IHz as [c2 IHz]; rewrite IHz, H0; trivial.

      destruct (I2F.dexp2ZE z0) eqn : ?; rewrite H0 in H; solve_b;
      assert (S : Some (IntToInfinity.N.ZE_Fin z) = Some (ZE_Fin z)) by trivial; specialize (IHz v x z S);
      destruct IHz as [c2 IHz]; rewrite IHz, H0; trivial.

      apply (IHz v x) in H0; destruct H0; rewrite H0; exists (FA.num_mult z x1); simpl; apply nummult_eq.
    Qed.

    (* If the product of natural number multiplication is positive infinity, then the variable is positive infinity. *)
    Lemma nat_nummult_inf:
      forall z v, I2F.num_mult_nat z v = Some ZE_Inf ->
                  (z > 0 /\ v = Some ZE_Inf) \/
                  (z = 0 /\ v = Some ZE_Inf /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end)).
    Proof.
      induction z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; solve_b; right; intuition.
      left; split; intuition.
      destruct z; trivial.

      apply numplus_inf in H.
      destruct H as [[[? ?] ?] | [[? [? ?]] | [? ?]]]; auto.
      apply IHz in H0; destruct H0 as [[? ?] | [? [? ?]]]; auto.
    Qed.

    (* If the product of natural number multiplication is negative infinity, then the variable is negative infinity. *)
    Lemma nat_nummult_neginf:
      forall z v, I2F.num_mult_nat z v = Some ZE_NegInf ->
                  (z > 0 /\ v = Some ZE_NegInf) \/
                  (z = 0 /\ v = Some ZE_NegInf /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end)).
    Proof.
      induction z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; solve_b; right; intuition.
      left; split; intuition.
      destruct z; trivial.

      apply numplus_neginf in H.
      destruct H as [[[? ?] ?] | [[? [? ?]] | [? ?]]]; auto.
      apply IHz in H0; destruct H0 as [[? ?] | [? [? ?]]]; auto.
    Qed.

    (* If the product of integer multiplication is positive infinity, *)
    (* then either variable is positive infinity and constant is positive *)
    (* or variable is negative infinity and constant is negative. *)
    Lemma nummult_inf:
      forall z v, I2F.num_mult z v = Some ZE_Inf ->
                  (((z > 0)%Z /\ v = Some ZE_Inf) \/
                   ((z < 0)%Z /\ v = Some ZE_NegInf) \/
                   ((z = 0)%Z /\ v = Some ZE_Inf /\
                    (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end))).
    Proof.
      destruct z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; solve_b; right; right; intuition.
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos.
      apply nat_nummult_inf in H; destruct H as [[? ?] | [? ?]]; left; split; intuition.
      apply numneg_inf in H; apply nat_nummult_neginf in H; destruct H as [[? ?] | [? [? ?]]];
      right; left; split; auto; apply Pos2Z.neg_is_neg.
    Qed.

    (* If the product of integer multiplication is negative infinity, *)
    (* then either variable is negative infinity and constant is positive *)
    (* or variable is positive infinity and constant is negative. *)
    Lemma nummult_neginf:
      forall z v, I2F.num_mult z v = Some ZE_NegInf ->
                  (((z > 0)%Z /\ v = Some ZE_NegInf) \/
                   ((z < 0)%Z /\ v = Some ZE_Inf) \/
                   ((z = 0)%Z /\ v = Some ZE_NegInf /\
                    (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end))).
    Proof.
      destruct z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H; solve_b; right; right; intuition.
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos.
      apply nat_nummult_neginf in H; destruct H as [[? ?] | [? ?]]; left; split; intuition.
      apply numneg_neginf in H; apply nat_nummult_inf in H; destruct H as [[? ?] | [? [? ?]]];
      right; left; split; auto; apply Pos2Z.neg_is_neg.
    Qed.

    Ltac solve_mul2inf p IHp:= induction p; auto; rewrite I2F.num_mult_nat_2_unfold in *; rewrite IHp; auto.

    (* positive c * infinity = infinity *)
    Lemma num_mult_nat_inf: forall p, I2F.num_mult_nat (S p) (Some ZE_Inf) = Some ZE_Inf.
    Proof. solve_mul2inf p IHp. Qed.

    (* positive c * negative infinity = negative infinity *)
    Lemma num_mult_nat_neginf: forall p, I2F.num_mult_nat (S p) (Some ZE_NegInf) = Some ZE_NegInf.
    Proof. solve_mul2inf p IHp. Qed.

    Ltac solve_tonat_infnone p l:= simpl; assert (exists pp, Pos.to_nat p = S pp) as SSS by
                                         (exists (pred (Pos.to_nat p)); apply (S_pred (Pos.to_nat p) 0); apply Pos2Nat.is_pos);
                                   destruct SSS as [pr S1]; rewrite S1; rewrite l; auto.

    (* Substitution keeps the infiniteness of expressions *)
    Lemma inf_subst2inf:
      forall z v x,
        I2F.dexp2ZE z = Some ZE_Inf -> I2F.dexp2ZE (I2F.subst_exp (v, @IntToInfinity.conv tt x) z) = Some ZE_Inf
        with neginf_subst2neginf: forall z v x, I2F.dexp2ZE z = Some ZE_NegInf ->
                                                I2F.dexp2ZE (I2F.subst_exp (v, @IntToInfinity.conv tt x) z) = Some ZE_NegInf.
    Proof.
      induction z; simpl; intros; auto.
      discriminate H.
      apply numplus_inf in H.
      destruct H, H, H.
      apply (finite_subst2finite z1 v x x0) in H; destruct H; apply (IHz2 v x) in H0; rewrite H, H0; auto.
      destruct H0; apply (IHz1 v x) in H; apply (finite_subst2finite z2 v x x0) in H0; destruct H0; rewrite H, H0; auto.
      apply (IHz1 v x) in H; apply (IHz2 v x) in H0; rewrite H, H0; auto.
      apply numneg_inf in H; apply (neginf_subst2neginf z v x) in H; rewrite H; auto.
      apply numplus_inf in H; destruct H, H, H.
      apply numneg_inf in H0; apply (finite_subst2finite z1 v x x0) in H; destruct H;
      apply (neginf_subst2neginf z2 v x) in H0; rewrite H, H0; auto.
      destruct H0. apply (IHz1 v x) in H. apply numneg_finite in H0. destruct H0, H0.
      apply (finite_subst2finite z2 v x x1) in H0; destruct H0.
      rewrite H, H0; auto.
      apply (IHz1 v x) in H. apply numneg_inf in H0. apply (neginf_subst2neginf z2 v x) in H0.
      rewrite H, H0; auto.
      apply nummult_inf in H.
      destruct H; destruct H.
      apply (IHz v x) in H0; rewrite H0.
      destruct z. discriminate H.
      solve_tonat_infnone p num_mult_nat_inf.
      assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg; omega.
      destruct H.
      apply (neginf_subst2neginf z0 v x) in H0.
      rewrite H0.
      destruct z. discriminate H.
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos; omega.
      solve_tonat_infnone p num_mult_nat_neginf.
      destruct H as [? [? ?]].
      specialize (IHz v x H0). rewrite IHz.
      rewrite H; apply H1.

      induction z; simpl; intros; auto.
      discriminate H.
      apply numplus_neginf in H.
      destruct H, H, H.
      apply (finite_subst2finite z1 v x x0) in H; destruct H; apply (IHz2 v x) in H0; rewrite H, H0; auto.
      destruct H0; apply (IHz1 v x) in H; apply (finite_subst2finite z2 v x x0) in H0; destruct H0; rewrite H, H0; auto.
      apply (IHz1 v x) in H; apply (IHz2 v x) in H0; rewrite H, H0; auto.
      apply numneg_neginf in H; apply (inf_subst2inf z v x) in H; rewrite H; auto.
      apply numplus_neginf in H; destruct H, H, H.
      apply numneg_neginf in H0; apply (finite_subst2finite z1 v x x0) in H; destruct H;
      apply (inf_subst2inf z2 v x) in H0; rewrite H, H0; auto.
      destruct H0. apply (IHz1 v x) in H. apply numneg_finite in H0. destruct H0, H0.
      apply (finite_subst2finite z2 v x x1) in H0; destruct H0.
      rewrite H, H0; auto.
      apply (IHz1 v x) in H. apply numneg_neginf in H0. apply (inf_subst2inf z2 v x) in H0.
      rewrite H, H0; auto.
      apply nummult_neginf in H.
      destruct H; destruct H.
      apply (IHz v x) in H0; rewrite H0.
      destruct z. discriminate H.
      solve_tonat_infnone p num_mult_nat_neginf.
      assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg; omega.
      destruct H.
      apply (inf_subst2inf z0 v x) in H0.
      rewrite H0.
      destruct z. discriminate H.
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos; omega.
      solve_tonat_infnone p num_mult_nat_inf.
      destruct H as [? [? ?]].
      specialize (IHz v x H0). rewrite IHz.
      rewrite H; apply H1.
    Qed.

    (* If the product of natural number multiplication is undefined, then the variable is undefined. *)
    Lemma nat_nummult_none:
      forall z v, I2F.num_mult_nat z v = None ->
                  (z <> 0 /\ v = None) \/
                  (z = 0 /\ (v = Some ZE_Inf \/ v = Some ZE_NegInf \/ v = None) /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end)) \/
                  (z = 0 /\ v = None /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end)).
    Proof.
      induction z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H;
      [discriminate H | right; left; solve_b; intuition | right; right; solve_b; intuition].

      left; split. omega.
      destruct z. apply H.
      apply numplus_none in H.
      destruct H as [? | [? | [[? ?] | [? ?]]]].
      auto.
      apply (IHz v) in H; destruct H as [[? ?] | [[? ?] | [? ?]]]; auto; discriminate H.
      apply nat_nummult_neginf in H0. destruct H0. rewrite H in H0. destruct H0. discriminate H1.
      destruct H0 as [? [? ?]]. rewrite H in H1. discriminate H1.
      apply nat_nummult_inf in H0.
      destruct H0 as [[? ?] | [? [? ?]]]; rewrite H in H1; discriminate H1.
    Qed.

    (* If the product of integer multiplication is undefined, then the variable is undefined. *)
    Lemma nummult_none:
      forall z v, I2F.num_mult z v = None ->
                  ((z <> 0)%Z /\ v = None) \/
                  (z = 0%Z /\ (v = Some ZE_Inf \/ v = Some ZE_NegInf \/ v = None) /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => None end)) \/
                  (z = 0%Z /\ v = None /\
                   (forall x, IZT.zero_times x = match x with | Some (ZE_Fin _) => Some (ZE_Fin 0) | _ => x end)).
    Proof.
      destruct z; simpl; intros.
      destruct IZT.zero_times_spec as [? | [? | ?]]; rewrite H0 in H;
      [discriminate H | right; left; solve_b; intuition | right; right; solve_b; intuition].
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos; assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg.
      generalize (Pos2Nat.is_pos p); intro.
      left; split. omega.
      apply nat_nummult_none in H. destruct H as [[? ?] | [[? [? ?]] | [? [? ?]]]]; auto. rewrite H in H2; exfalso; intuition.
      assert (0 < Z.pos p)%Z by apply Pos2Z.is_pos; assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg.
      left; split. omega.
      apply numneg_none in H.
      apply nat_nummult_none in H.
      destruct H as [[? ?] | [[? [? ?]] | [? [? ?]]]]; auto.
      generalize (Pos2Nat.is_pos p); intro.
      rewrite H in H4; exfalso; intuition.
    Qed.

    (* positive c * undefined = undefined *)
    Lemma num_mult_nat_none: forall p, I2F.num_mult_nat (S p) None = None.
    Proof.
      induction p; simpl; auto.
    Qed.

    (* Substitution keeps the undefinedness of evaluation. *)
    Lemma none_subst2none: forall z v x, I2F.dexp2ZE z = None ->
                                         I2F.dexp2ZE (I2F.subst_exp (v, @IntToInfinity.conv tt x) z) = None.
    Proof.
      induction z; simpl; intros.
      discriminate H.
      auto.
      apply numplus_none in H.
      destruct H.
      apply (IHz1 v x) in H; rewrite H; simpl; auto.
      destruct H.
      apply (IHz2 v x) in H; rewrite H.
      unfold IntToInfinity.N.num_plus; destruct (I2F.dexp2ZE (I2F.subst_exp (v, IntToInfinity.conv x) z1));
      auto; destruct z; auto.
      destruct H, H.
      apply (inf_subst2inf z1 v x) in H;
        apply (neginf_subst2neginf z2 v x) in H0;
        rewrite H, H0; auto.
      apply (neginf_subst2neginf z1 v x) in H;
        apply (inf_subst2inf z2 v x) in H0;
        rewrite H, H0; auto.
      apply numneg_none in H. apply (IHz v x) in H. rewrite H. auto.
      apply numplus_none in H.
      destruct H. apply (IHz1 v x) in H. rewrite H; auto.
      destruct H. apply numneg_none in H. apply (IHz2 v x) in H. rewrite H.
      unfold IntToInfinity.N.num_neg.
      unfold option_map.
      unfold IntToInfinity.N.num_plus.
      destruct (I2F.dexp2ZE (I2F.subst_exp (v, IntToInfinity.conv x) z1)); auto.
      destruct z; auto.
      destruct H, H.
      apply (inf_subst2inf z1 v x) in H.
      apply numneg_neginf in H0. apply (inf_subst2inf z2 v x) in H0.
      rewrite H, H0. auto.
      apply (neginf_subst2neginf z1 v x) in H.
      apply numneg_inf in H0. apply (neginf_subst2neginf z2 v x) in H0.
      rewrite H, H0. auto.
      apply nummult_none in H. destruct H as [[? ?] | [[? [? ?]] | [? [? ?]]]]. apply (IHz v x) in H0. rewrite H0.
      destruct z; simpl. omega.
      solve_tonat_infnone p num_mult_nat_none.
      solve_tonat_infnone p num_mult_nat_none.

      rewrite H; simpl; destruct H0 as [? | [? | ?]];
      [apply (inf_subst2inf _ v x) in H0 | apply (neginf_subst2neginf _ v x) in H0 |
       apply (IHz v x) in H0]; rewrite H0; apply H1.
      rewrite H; simpl; apply (IHz v x) in H0; rewrite H0; apply H1.
    Qed.

    (* Substitution and expression transformation from I2F to IA are commutative. *)
    Lemma subst_int_trans_exp_eq: forall z v x, FA.subst_exp (v, @PureInt.conv tt x) (int_trans_exp z) =
                                                int_trans_exp (I2F.subst_exp (v, @IntToInfinity.conv tt x) z).
    Proof.
      induction z; simpl; intros.
      destruct (var_eq_dec v0 v); auto.
      auto.
      rewrite IHz1, IHz2; auto.
      rewrite IHz; auto.
      rewrite IHz1, IHz2; auto.
      rewrite IHz; auto.
    Qed.

    Ltac smash_subst_int_trans_bf_eq :=
      repeat match goal with
               | [|- ?X = ?X] => apply eq_refl
               | [H1 : I2F.dexp2ZE ?z = None, H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some _ |- _] =>
                 apply (none_subst2none z v x) in H1; rewrite H1 in H2; discriminate H2
               | [H1 : I2F.dexp2ZE ?zExp = Some ?zSome,
                       H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?zExp) = None |- _] =>
                 destruct zSome; [apply (finite_subst2finite zExp v x) in H1; destruct H1 as [? H1] |
                                  apply (inf_subst2inf zExp v x) in H1 | apply (neginf_subst2neginf zExp v x) in H1];
                 rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some (IntToInfinity.N.ZE_Fin _),
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some IntToInfinity.N.ZE_Inf |- _] =>
                apply (finite_subst2finite z v x) in H1; destruct H1 as [? H1]; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some (IntToInfinity.N.ZE_Fin _),
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some IntToInfinity.N.ZE_NegInf |- _] =>
                apply (finite_subst2finite z v x) in H1; destruct H1 as [? H1]; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some IntToInfinity.N.ZE_Inf,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some (IntToInfinity.N.ZE_Fin _) |- _] =>
                apply (inf_subst2inf z v x) in H1; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some IntToInfinity.N.ZE_Inf,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some IntToInfinity.N.ZE_NegInf |- _] =>
                apply (inf_subst2inf z v x) in H1; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some IntToInfinity.N.ZE_NegInf,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some (IntToInfinity.N.ZE_Fin _) |- _] =>
                apply (neginf_subst2neginf z v x) in H1; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z = Some IntToInfinity.N.ZE_NegInf,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z) = Some IntToInfinity.N.ZE_Inf |- _] =>
                apply (neginf_subst2neginf z v x) in H1; rewrite H1 in H2; discriminate H2
               |[H1 : I2F.dexp2ZE ?z1 = Some ?z2,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z1) = Some ?z3,
                           H3 : ?z2 = ZE_NegInf, H4 : ?z3 <> ZE_NegInf |- _] =>
                let H := fresh "H" in
                rewrite H3 in H1; apply (neginf_subst2neginf z1 v x) in H1; rewrite H1 in H2;
                injection H2; intro H; rewrite H in H4; exfalso; apply H4, eq_refl
               |[H1 : I2F.dexp2ZE ?z1 = Some ?z2,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z1) = Some ?z3,
                           H3 : ?z2 = ZE_Inf, H4 : ?z3 <> ZE_Inf |- _] =>
                let H := fresh "H" in
                rewrite H3 in H1; apply (inf_subst2inf z1 v x) in H1; rewrite H1 in H2;
                injection H2; intro H; rewrite H in H4; exfalso; apply H4, eq_refl
               |[H1 : I2F.dexp2ZE ?z1 = Some ?z2,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z1) = Some ?z3,
                           H3 : ?z2 <> ZE_NegInf, H4 : ?z3 = ZE_NegInf|- _] =>
                rewrite H4 in H2; destruct z2;
                [apply (finite_subst2finite z1 v x) in H1; destruct H1 as [? H1]; rewrite H1 in H2; discriminate H2 |
                 apply (inf_subst2inf z1 v x) in H1; rewrite H1 in H2; discriminate H2 | exfalso; apply H3, eq_refl]
               |[H1 : I2F.dexp2ZE ?z1 = Some ?z2,
                      H2 : I2F.dexp2ZE (I2F.subst_exp (?v, IntToInfinity.conv ?x) ?z1) = Some ?z3,
                           H3 : ?z2 <> ZE_Inf, H4 : ?z3 = ZE_Inf|- _] =>
                rewrite H4 in H2; destruct z2;
                [apply (finite_subst2finite z1 v x) in H1; destruct H1 as [? H1]; rewrite H1 in H2; discriminate H2 |
                 exfalso; apply H3, eq_refl | apply (neginf_subst2neginf z1 v x) in H1; rewrite H1 in H2; discriminate H2 ]
               | [H: context[ZE_eq_dec _ _] |- _] => clear H
               | [|- context[FAFalse]] => unfold FAFalse
               | [|- context[FATrue]] => unfold FATrue
               | [|- context[match I2F.dexp2ZE ?X with _ => _ end]] => destruct (I2F.dexp2ZE X) eqn: ?; simpl
               | [|- context[match ?X with _ => _ end]] => destruct X eqn: ?; simpl
               | [|- context[FA.subst_exp (_, PureInt.conv _) (int_trans_exp _)]] => rewrite subst_int_trans_exp_eq
               | [|- context[embed _]] => unfold embed
               | [|- context[FANone]] => unfold FANone
             end.

    (* Substitution and boolean form transformation from I2F to IA are commutative. *)
    Lemma subst_int_trans_bf_eq: forall z v x, FA.substitute (v, @PureInt.conv tt x) (int_trans (I2F.ZF_BF z)) =
                                               int_trans (I2F.substitute (v, @IntToInfinity.conv tt x) (I2F.ZF_BF z)).
    Proof. destruct z; simpl; intros; smash_subst_int_trans_bf_eq. Qed.

    (* Substitution and logic form transformation from I2F to IA are commutative. *)
    Lemma subst_int_trans_eq: forall f v x, FA.substitute (v, @PureInt.conv tt x) (int_trans f) =
                                            int_trans (I2F.substitute (v, @IntToInfinity.conv tt x) f).
    Proof.
      intros f. remember (I2F.length_zform f). assert (I2F.length_zform f <= n) by omega. clear Heqn. revert f H.
      induction n; intros.
      exfalso; destruct f; simpl in H; omega.
      destruct f; simpl in H; apply le_S_n in H; simpl.
      apply subst_int_trans_bf_eq.
      rewrite (IHn f1), (IHn f2); auto; try omega.
      rewrite (IHn f1), (IHn f2); auto; try omega.
      rewrite (IHn f1), (IHn f2); auto; try omega.
      rewrite (IHn f); auto.
      destruct (var_eq_dec v v0); simpl; auto; rewrite (IHn f); auto.
      destruct (var_eq_dec v v0); simpl; auto; rewrite (IHn f); auto.
    Qed.

    Lemma int_trans_ok: forall f, (I2F.satisfied f <-> FA.satisfied (int_trans f)) /\
                                  (I2F.dissatisfied f <-> FA.dissatisfied (int_trans f)).
    Proof.
      intros f; remember (I2F.length_zform f); assert (I2F.length_zform f <= n) by omega; clear Heqn; revert f H;
      induction n; intros.
      exfalso; destruct f; simpl in H; exfalso; intuition.
      destruct f; simpl in H; apply le_S_n in H; simpl; try (rewrite int_trans_bf_sat, int_trans_bf_dst; tauto);
      rewrite I2F.satisfied_unfold, FA.satisfied_unfold; rewrite I2F.dissatisfied_unfold, FA.dissatisfied_unfold.
      assert (S1 : I2F.length_zform f1 <= n) by omega; assert (S2 : I2F.length_zform f2 <= n) by omega;
      destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2]; rewrite SAT1, DST1, SAT2, DST2; tauto.
      assert (S1 : I2F.length_zform f1 <= n) by omega; assert (S2 : I2F.length_zform f2 <= n) by omega;
      destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2]; rewrite SAT1, DST1, SAT2, DST2; tauto.
      rewrite <- I2F.dissatisfied_unfold, <- FA.dissatisfied_unfold;
        assert (S1 : I2F.length_zform f1 <= n) by omega; assert (S2 : I2F.length_zform f2 <= n) by omega;
        destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
        split; [rewrite DST1, SAT2 | rewrite I2F.dissatisfied_unfold, FA.dissatisfied_unfold; rewrite SAT1, DST2]; tauto.
      rewrite <- I2F.dissatisfied_unfold, <- FA.dissatisfied_unfold;
        assert (S : I2F.length_zform f <= n) by omega; destruct (IHn _ S) as [SAT DST];
        split; [rewrite DST | rewrite I2F.dissatisfied_unfold, FA.dissatisfied_unfold; rewrite SAT]; tauto.

      split; split; intros; simpl; [ | | destruct H0 as [x H0] | destruct H0 as [x H0]];
      assert (S : I2F.length_zform (I2F.substitute (v, @IntToInfinity.conv tt x) f) <= n) by
          (rewrite <- I2F.substitute_length_inv; trivial);
      destruct (IHn _ S) as [SAT DST];
      assert (FA.substitute (v, @PureInt.conv tt x) (int_trans f) =
              int_trans (I2F.substitute (v, @IntToInfinity.conv tt x) f)) by apply (subst_int_trans_eq f v x);
      unfold PureInt.QT in H1; unfold PureInt.N.A; unfold PureInt.conv in *;
      [rewrite H1; rewrite <- SAT | rewrite SAT; rewrite <- H1 |
       exists x; rewrite H1; rewrite <- DST | exists x; rewrite DST; rewrite <- H1]; apply H0.

      split; split; intros; simpl; [destruct H0 as [x H0] | destruct H0 as [x H0] | | ];
      assert (S : I2F.length_zform (I2F.substitute (v, @IntToInfinity.conv tt x) f) <= n) by
          (rewrite <- I2F.substitute_length_inv; trivial);
      destruct (IHn _ S) as [SAT DST];
      assert (FA.substitute (v, @PureInt.conv tt x) (int_trans f) =
              int_trans (I2F.substitute (v, @IntToInfinity.conv tt x) f)) by apply (subst_int_trans_eq f v x);
      unfold PureInt.QT in H1; unfold PureInt.N.A; unfold PureInt.conv in *;
      [exists x; rewrite H1; rewrite <- SAT | exists x; rewrite SAT; rewrite <- H1 | rewrite H1; rewrite <- DST |
              rewrite DST; rewrite <- H1]; apply H0.
    Qed.

  End IntegerTransformation.

  (* Transformation from IA to FA *)
  Definition T (f : IA.ZF) : FA.ZF := int_trans (inf_trans f).

  (* The transformation from IA to FA keeps the validity *)
  Theorem valid_eq: forall f, (IA.satisfied f <-> FA.satisfied (T f)) /\
                              (IA.dissatisfied f <-> FA.dissatisfied (T f)).
  Proof.
    intros; unfold T; split;
    destruct (inf_trans_ok f);
    destruct (int_trans_ok (inf_trans f));
    intuition.
  Qed.

End InfSolver.
