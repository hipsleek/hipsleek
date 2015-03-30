Require Import Theory.

Module SimplifyArith (I : SEMANTICS_INPUT) (V : VARIABLE) (VAL : SEM_VAL) (L : LEQ_RELATION I.N VAL) (ZT : ZERO_PRODUCT I.N).

  Module AR := ArithSemantics I V VAL L ZT.

  Import I N V VAL L ZT AR.

  Ltac solve_bf_simp :=
    repeat match goal with
             | [|- _ /\ _ ] => split
             | [|- _ -> _ ] => intros
             | [z: ZBF, H : simplifyZF (ZF_BF ?z) = _ |- _] => destruct z; simpl in *
             | [H : ?X |- ?X] => apply H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _) |- _] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _) |- _] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _) |- _] => discriminate H
             | [|- exists e3 e4 : ZExp, ZF_BF (?X ?A ?B) = ZF_BF (?X e3 e4)] => exists A, B
             | [|- ?A = ?A] => auto
             | [H : forall (v : var) (q : Q) (x : QT q), _ , v : var, q : Q, x : QT _ |- _ ] =>
               specialize (H v q x); destruct H as [? [? [? [? [? [? ?]]]]]]
             | [H : simplifyZF (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?X with _ => _ end] |- _] => destruct (judge X)
             | [H1 : forall c : Val, simplifyZF ?f1 = ZF_BF (ZBF_Const c) -> _ ,
                  H2 : simplifyZF ?f1 = ZF_BF (ZBF_Const _) |- _] => specialize (H1 _ H2)
             | [|- simplifyZF (substitute _ (ZF_And _ _)) = _] => simpl
             | [|- context[match judge ?X with _ => _ end]] => destruct (judge X)
             | [H1: simplifyZF (substitute ?A ?f) = _, H2: simplifyZF (substitute ?A ?f) = _ |- _] =>
               rewrite H1 in *; clear H1
             | [H : ?A = ?B |- ?B = ?A ] => rewrite <- H; auto
             | [H : ZF_BF (ZBF_Const Top) = ZF_BF (ZBF_Const Btm) |- _] => inversion H; clear H
             | [H : ZF_BF (ZBF_Const Btm) = ZF_BF (ZBF_Const Top) |- _] => inversion H; clear H
             | [H : Top = Btm |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [H : Btm = Top |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [H : ?A = _ |- context[?A]] => rewrite H in *; clear H
             | [H : _ /\ _ |- _] => destruct H
             | [H : ?A <> ?A |- _] => exfalso; apply H; auto
             | [H1 : forall e1 e2 : ZExp, simplifyZF ?f = ZF_BF (?X e1 e2) -> exists e3 e4 : _ , _ ,
                  H2 : simplifyZF ?f = ZF_BF (?X _ _) |- exists e3 e4 : ZExp, _] =>
               let ee3 := fresh "ee3" in
               let ee4 := fresh "ee4" in
               specialize (H1 _ _ H2); destruct H1 as [ee3 [ee4 ?]]; exists ee3, ee4
             | [H : simplifyZF (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Or _ _)) = _] => simpl
             | [H : simplifyZF (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Imp _ _)) = _] => simpl
             | [H : ZF_Not _ = ZF_BF _ |- _] => discriminate H
             | [H : simplifyZF (ZF_Not _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Not _)) = _] => simpl
             | [H : simplifyZF (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Forall _ _ _)) = _] => simpl
             | [H : _ _ _ _ = ZF_BF _ |- _] => discriminate H
             | [H : simplifyZF (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Exists _ _ _)) = _] => simpl
           end.

  (* Substitution doesn't change the form of simplified result on boolean forms *)
  Lemma simp_subst_bf_same:
    forall f v q x,
      (forall c, simplifyZF f = ZF_BF (ZBF_Const c) -> simplifyZF (substitute (v, conv q x) f) = ZF_BF (ZBF_Const c)) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Lt e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Lt e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Lte e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Lte e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Gt e1 e2) ->
                     (exists e3 e4, simplifyZF (substitute (v,conv q x) f) = ZF_BF(ZBF_Gt e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Gte e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Gte e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Eq e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v, conv q x) f) = ZF_BF (ZBF_Eq e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Neq e1 e2) ->
                     (exists e3 e4, simplifyZF (substitute (v, conv q x) f) = ZF_BF (ZBF_Neq e3 e4))).
  Proof. induction f; intros; solve_bf_simp. Qed.

  Ltac solve_eqminmax :=
    repeat match goal with
             | [|- eliminateMinMax ?z <> ZF_BF _] => destruct z; simpl; intuition
             | [|- context[match judge (simplifyZF ?f) with _ => _ end]] => destruct (judge (simplifyZF f))
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : forall e1 e2 e3 : ZExp, simplifyZF ?f <> ZF_BF (?X e1 e2 e3) |-
                                            simplifyZF ?f <> ZF_BF (?X _ _ _)] => apply H
             | [|- ZF_BF (_ _) <> ZF_BF (_ _ _ _)] => discriminate
             | [|- _ _ _ <> ZF_BF _] => discriminate
             | [|- _ _ _ _ <> ZF_BF _] => discriminate
             | [|- ZF_Not _ <> ZF_BF _] => discriminate
           end.

  (* Simplification really eliminates max. *)
  Lemma simp_no_eq_max : forall f e1 e2 e3, simplifyZF f <> ZF_BF (ZBF_Eq_Max e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  (* Simplification really eliminates min. *)
  Lemma simp_no_eq_min : forall f e1 e2 e3, simplifyZF f <> ZF_BF (ZBF_Eq_Min e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  Ltac solve_other_same :=
    repeat match goal with
             | [|- _ /\ _] => split
             | [|- _ -> _] => intros
             | [z : ZBF, H : simplifyZF (ZF_BF ?z) = _ |- _] => destruct z; simpl in H
             | [H : _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ |- _] => discriminate H
             | [H : ZF_BF _ = ZF_Not _ |- _] => discriminate H
             | [H : _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ _ |- _] => discriminate H
             | [|- context[simplifyZF (substitute _ (ZF_BF (ZBF_Eq_Max _ _ _)))]] => simpl
             | [|- context[simplifyZF (substitute _ (ZF_BF (ZBF_Eq_Min _ _ _)))]] => simpl
             | [|- exists f3 f4 : ZF, ?X ?A ?B = ?X f3 f4] => exists A, B; auto
             | [|- context[simplifyZF (substitute _ (ZF_And _ _))]] => simpl
             | [H : simplifyZF (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?A with _ => _ end] |- _] => destruct (judge A)
             | [|- context[match judge ?A with _ => _ end]] => destruct (judge A)
             | [H : _ /\ _ |- _ ] => destruct H
             | [H : simplifyZF ?f = ?X _ _,
                    H0 : forall f1 f3 : ZF,
                           simplifyZF ?f = ?X f1 f3 ->
                           exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5 |-
                                              exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5] =>
               let ff1 := fresh "ff1" in
               let ff2 := fresh "ff2" in
               specialize (H0 _ _ H); destruct H0 as [ff1 [ff2 ?]]; exists ff1, ff2; auto
             | [H : simplifyZF ?f = ?X _ _,
                    e1 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = _ _,
                         H0 : forall f1 f3 : ZF, simplifyZF ?f = ?X f1 f3 ->
                                                 exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5
                                                                    |- _] =>
               specialize (H0 _ _ H); destruct H0 as [? [? H0]]; rewrite H0 in e1; discriminate e1
             | [e : simplifyZF ?f = ZF_BF (ZBF_Const Top),
                    e0 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Btm) |- _] =>
               let H := fresh "H" in
               let S := fresh "S" in
               let M := fresh "M" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in e0; inversion e0 as [S];
               generalize top_neq_btm; intro M; rewrite S in M; exfalso; apply M; auto
             | [e : simplifyZF ?f = ZF_BF (ZBF_Const Btm),
                    e0 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Top) |- _] =>
               let H := fresh "H" in
               let S := fresh "S" in
               let M := fresh "M" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in e0; inversion e0 as [S];
               generalize top_neq_btm; intro M; rewrite S in M; exfalso; apply M; auto
             | [H : simplifyZF ?f = ZF_Not _,
                    e1 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF _,
                         H0 : forall f1 : ZF,
                                simplifyZF ?f = ZF_Not f1 ->
                                exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3
                                                |- _] =>
               specialize (H0 _ H); destruct H0 as [? H0]; rewrite H0 in e1; discriminate e1
             |[e : simplifyZF ?f = ZF_BF _, H : simplifyZF ?f = ZF_Not _ |- _] => rewrite H in e; discriminate e
             | [H : simplifyZF ?f = ZF_Not _,
                    H1 :
                  forall f2 : ZF,
                    simplifyZF ?f = ZF_Not f2 ->
                    exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3 |-
                                    exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3] =>
               let ff3 := fresh "ff3" in specialize (H1 _ H); destruct H1 as [ff3 ?]; exists ff3; auto
             |[ e : simplifyZF ?f = ZF_BF (ZBF_Const ?X),
                    H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let H := fresh "H" in
              destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in H2; exfalso; apply H2; auto
             |[H : forall (v : var) (q : Q) (x : QT q), _ |- context[(substitute (?v, conv ?q ?x) _)]] => specialize (H v q x)
             | [H : simplifyZF ?f = ?X _ _ _,
                    H4 : forall (v1 : var) (q1 : Q) (f1 : ZF),
                           simplifyZF ?f = ?X v1 q1 f1 ->
                           exists (v2 : var) (q2 : Q) (f3 : ZF),
                             simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X v2 q2 f3
                             |- exists (v2 : var) (q2 : Q) (f3 : ZF), simplifyZF (substitute (?v, conv ?q ?x) ?f) =
                                                                      ?X v2 q2 f3] =>
               let vv := fresh "vv" in
               let qq := fresh "qq" in
               let ff := fresh "ff" in
               specialize (H4 _ _ _ H); destruct H4 as [vv [qq [ff ?]]]; exists vv, qq, ff; apply H4
             | [H : simplifyZF ?f = ?X _ _ _,
                    H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = _ _,
                         H12 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                                 simplifyZF ?f = ?X v1 q1 f2 ->
                                 exists (v2 : var) (q2 : Q) (f3 : ZF),
                                   simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X v2 q2 f3 |- _ ] =>
               specialize (H12 _ _ _ H); destruct H12 as [? [? [? H12]]]; rewrite H12 in H2; discriminate H2
             |[ H2 : simplifyZF ?f <> ZF_BF (ZBF_Const ?X),
                     e : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const ?X) |- _] =>
              generalize (simp_subst_bf_same f v q x); intro; destruct (simplifyZF f) eqn : ?
             |[H10 : forall f2 f3 : ZF,
                       ?X ?z1 ?z2 = ?X f2 f3 ->
                       exists f4 f5 : ZF,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X f4 f5,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X z1 z2 = X z1 z2) by auto; specialize (H10 _ _ S);
              destruct H10 as [? [? ?]]; rewrite H10 in e; discriminate e
             |[H13 : forall f2 : ZF,
                       ZF_Not ?z = ZF_Not f2 ->
                       exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_Not f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] =>
              let S := fresh "S" in
              assert (S : ZF_Not z = ZF_Not z) by auto; specialize (H13 _ S);
              destruct H13 as [? ?]; rewrite H13 in e; discriminate e
             |[H14 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                       ?X ?v0 ?q0 ?z = ?X v1 q1 f2 ->
                       exists (v2 : var) (q2 : Q) (f3 : ZF),
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X v2 q2 f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X v0 q0 z = X v0 q0 z) by auto; specialize (H14 _ _ _ S);
              destruct H14 as [? [? [? H14]]]; rewrite H14 in e; discriminate e
             | [Heqz0 : simplifyZF ?f1 = _ _ _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [Heqz0 : simplifyZF ?f1 = _ _ _ _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [Heqz0 : simplifyZF ?f1 = ZF_Not _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [z: ZBF, Heqz : simplifyZF ?f1 = ZF_BF _,
                               e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] => destruct z
             |[H17 : forall e1 e2 : ZExp,
                       ZF_BF (?X ?z ?z0) = ZF_BF (?X e1 e2) ->
                       exists e3 e4 : ZExp,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (?X e3 e4),
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const _) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H17 _ _ S);
              destruct H17 as [? [? H17]]; rewrite H17 in e; discriminate e
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Max ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_max f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Min ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_min f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[ H16 : forall c : Val,
                        ZF_BF (ZBF_Const ?v0) = ZF_BF (ZBF_Const c) ->
                        simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const c),
                  e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const ?X),
                  H2 : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (ZBF_Const v0) = ZF_BF (ZBF_Const v0)) by auto; specialize (H16 _ S);
              rewrite H16 in e; inversion e; rewrite e in H2; exfalso; apply H2; auto
             | [|- context[simplifyZF (substitute _ (ZF_Or _ _))]] => simpl
             | [H : simplifyZF (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Imp _ _))]] => simpl
             | [H : simplifyZF (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Not _))]] => simpl
             | [H : simplifyZF (ZF_Not _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Forall _ _ _))]] => simpl
             | [H : simplifyZF (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Exists _ _ _))]] => simpl
             | [H : simplifyZF (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [H : _ _ _ _ = ZF_Not _ |- _] => discriminate H
             |[|- exists (v2 : var) (q2 : Q) (f2 : ZF),
                    simplifyZF
                      (if var_eq_dec ?v0 ?v
                       then ?X ?v ?q ?f
                       else ?X ?v ?q (substitute (?v0, conv ?q0 ?x) ?f)) =
                    ?X v2 q2 f2] =>
              destruct (var_eq_dec v0 v); simpl;
              [exists v, q, (simplifyZF f) | exists v, q, (simplifyZF (substitute (v0, conv q0 x) f))]; auto
             |[|- exists f3 : ZF, ZF_Not ?A = ZF_Not f3] => exists A; auto
           end.

  (* Substitution doesn't change the form of simplified result on logic forms *)
  Lemma simp_subst_other_same:
    forall f v q x,
      (forall f1 f2, simplifyZF f = ZF_And f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_And f3 f4)) /\
      (forall f1 f2, simplifyZF f = ZF_Or f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_Or f3 f4)) /\
      (forall f1 f2, simplifyZF f = ZF_Imp f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_Imp f3 f4)) /\
      (forall f1, simplifyZF f = ZF_Not f1 -> (exists f2, simplifyZF (substitute (v, conv q x) f) = ZF_Not f2)) /\
      (forall v1 q1 f1, simplifyZF f = ZF_Forall v1 q1 f1->
                        (exists v2 q2 f2, simplifyZF (substitute (v, conv q x) f) = ZF_Forall v2 q2 f2)) /\
      (forall v1 q1 f1, simplifyZF f = ZF_Exists v1 q1 f1->
                        (exists v2 q2 f2, simplifyZF (substitute (v, conv q x) f) = ZF_Exists v2 q2 f2)).
  Proof. induction f; intros; solve_other_same. Qed.

  Ltac solve_simp :=
    repeat match goal with
             | [|- context[match judge (simplifyZF ?A) with _ => _ end]] => destruct (judge (simplifyZF A))
             | [H : ?A = _ |- context[?A]] => rewrite H
             | [H : _ /\ _ |- _] => destruct H
             | [|- ?A = ?A] => auto
             | [|- substitute (_, conv _ _) (ZF_BF (ZBF_Const ?A)) = ZF_BF (ZBF_Const ?A)] => simpl; auto
             | [H : forall (v : var) (q : Q) (x : QT q),
                      substitute (v, conv q x) (simplifyZF ?f) = simplifyZF (substitute (v, conv q x) ?f) |-
                      context [substitute (?vv, conv ?qq ?xx) (simplifyZF ?f)]] => rewrite H
             | [|- substitute (_, conv _ _) (ZF_And _ _) = _] => simpl substitute at 1
             | [H1 : simplifyZF ?f = ZF_BF (ZBF_Const Top),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Btm) |- _ ]
               => let H := fresh "H" in
                  destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; clear H; inversion H2
             | [H : Btm = Top |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [H : Top = Btm |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [ H1 : simplifyZF ?f = ZF_BF (ZBF_Const ?X),
                      H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?X) |- _ ] =>
               let H := fresh "H" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; exfalso; apply H2; auto
             | [H1 : simplifyZF ?f = ZF_BF (ZBF_Const Btm),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Top) |- _ ]
               => let H := fresh "H" in
                  destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; clear H; inversion H2
             | [H : simplifyZF ?f = ZF_BF (ZBF_Const ?X) |-
                ZF_BF (ZBF_Const ?X) = simplifyZF (substitute (?v, conv ?q ?x) ?f)] =>
               let X := fresh "X" in
               destruct (simp_subst_bf_same f v q x) as [X _]; specialize (X _ H); rewrite X; auto
             | [H : simplifyZF ?f = ZF_BF (ZBF_Const ?X) |-
                substitute (?v, conv ?q ?x) (ZF_BF (ZBF_Const ?X)) = simplifyZF (substitute (?v, conv ?q ?x) ?f)] =>
               let X := fresh "X" in
               destruct (simp_subst_bf_same f v q x) as [X _]; specialize (X _ H); rewrite X; simpl; auto
             |[ H1 : simplifyZF ?f <> ZF_BF (ZBF_Const ?X),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const ?X) |- _] =>
              generalize (simp_subst_bf_same f v q x); intro; generalize (simp_subst_other_same f v q x); intro;
              destruct (simplifyZF f) eqn : ?
             |[H10 : forall f2 f3 : ZF,
                       ?X ?z1 ?z2 = ?X f2 f3 ->
                       exists f4 f5 : ZF,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X f4 f5,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X z1 z2 = X z1 z2) by auto; specialize (H10 _ _ S);
              destruct H10 as [? [? ?]]; rewrite H10 in e; discriminate e
             |[H13 : forall f2 : ZF,
                       ZF_Not ?z = ZF_Not f2 ->
                       exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_Not f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] =>
              let S := fresh "S" in
              assert (S : ZF_Not z = ZF_Not z) by auto; specialize (H13 _ S);
              destruct H13 as [? ?]; rewrite H13 in e; discriminate e
             |[H14 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                       ?X ?v0 ?q0 ?z = ?X v1 q1 f2 ->
                       exists (v2 : var) (q2 : Q) (f3 : ZF),
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X v2 q2 f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X v0 q0 z = X v0 q0 z) by auto; specialize (H14 _ _ _ S);
              destruct H14 as [? [? [? H14]]]; rewrite H14 in e; discriminate e
             | [z: ZBF, Heqz : simplifyZF ?f1 = ZF_BF _,
                               e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] => destruct z
             |[H17 : forall e1 e2 : ZExp,
                       ZF_BF (?X ?z ?z0) = ZF_BF (?X e1 e2) ->
                       exists e3 e4 : ZExp,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (?X e3 e4),
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const _) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H17 _ _ S);
              destruct H17 as [? [? H17]]; rewrite H17 in e; discriminate e
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Max ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_max f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Min ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_min f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[ H16 : forall c : Val,
                        ZF_BF (ZBF_Const ?v0) = ZF_BF (ZBF_Const c) ->
                        simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const c),
                  e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const ?X),
                  H2 : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (ZBF_Const v0) = ZF_BF (ZBF_Const v0)) by auto; specialize (H16 _ S);
              rewrite H16 in e; inversion e; rewrite e in H2; exfalso; apply H2; auto
             | [|- context[substitute _ (ZF_And _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Or _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Imp _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Not _) ]] => simpl
             | [|- context[substitute _ (ZF_Forall _ _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Exists _ _ _) ]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplifyZF (ZF_Forall _ _ _)]] => simpl
             | [|- context[simplifyZF (ZF_Exists _ _ _)]] => simpl
           end.


  (* simplification and substitution are commutative. *)
  Lemma simp_subst_same: forall f v q x, substitute (v, conv q x) (simplifyZF f) = simplifyZF (substitute (v, conv q x) f).
  Proof. induction f; intros; simpl substitute at 2; simpl; try (destruct z; simpl; auto); solve_simp. Qed.

  Ltac solve_cnt :=
    repeat match goal with
             | [|- _ /\ _ ] => split
             | [z : ZBF, z0 : ZBF |- satisfied (ZF_BF ?z) /\ satisfied (ZF_BF ?z0) <-> _] => destruct z, z0
             | [z : ZBF, z0 : ZBF |- dissatisfied (ZF_BF ?z) \/ dissatisfied (ZF_BF ?z0) <-> _] => destruct z, z0
             | [|- context [match (judge ?X) with _ => _ end]] => destruct (judge X)
             | [e : ZF_BF ?X = ZF_BF (ZBF_Const _) |- context[ZF_BF ?X]] => rewrite e in *; clear e
             | [|- context[satisfied (ZF_BF (ZBF_Const Top))]] => rewrite satisfied_unfold; simpl
             | [|- context[satisfied (ZF_BF (ZBF_Const Btm))]] => rewrite satisfied_unfold; simpl
             | [|- context[dissatisfied (ZF_BF (ZBF_Const Top))]] => rewrite dissatisfied_unfold; simpl
             | [|- context[dissatisfied (ZF_BF (ZBF_Const Btm))]] => rewrite dissatisfied_unfold; simpl
             | [|- ?A = ?A /\ ?X <-> ?X] => intuition
             | [|- ?X /\ ?A = ?A <-> ?X] => intuition
             | [|- Btm = Top /\ _ <-> Btm = Top] => intuition
             | [|- ?X /\ Btm = Top <-> Btm = Top] => intuition
             | [|- Top = Btm \/ ?X <-> ?X] => intuition
             | [|- ?X \/ Top = Btm <-> ?X] => intuition
             | [|- ?X = ?X \/ _ <-> ?Y = ?Y ] => intuition
             | [|- _ \/ ?X = ?X <-> ?Y = ?Y ] => intuition
             | [|- Btm = Top \/ ?X <-> ?X] => intuition
             | [|- ?X \/ Btm = Top <-> ?X] => intuition
             | [|- Top = Btm /\ _ <-> Top = Btm] => intuition
             | [|- _ /\ Top = Btm <-> Top = Btm] => intuition
             | [|- Btm = Top /\ _ <-> Top = Btm] => intuition
             | [|- ?A = ?B <-> ?B = ?A] => intuition
             | [|- ?A = ?A <-> ?B = ?B] => intuition
             | [H : Btm = Top |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [H : Top = Btm |- _] => generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition
             | [|- satisfied ?A /\ satisfied ?B <-> satisfied (ZF_And ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A \/ dissatisfied ?B <-> dissatisfied (ZF_And ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [|- satisfied ?A \/ satisfied ?B <-> satisfied (ZF_Or ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A /\ dissatisfied ?B <-> dissatisfied (ZF_Or ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A \/ satisfied ?B <-> satisfied (ZF_Imp ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- satisfied ?X /\ ?A = ?A <-> dissatisfied (ZF_Not ?X)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; intuition
             | [|- satisfied ?A /\ dissatisfied ?B <-> dissatisfied (ZF_Imp ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [e : ZF_BF (_ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion e
             | [e : ZF_BF (_ _ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion e
             | [e : _ _ _ = ZF_BF _ |- _] => inversion e
             | [e : ZF_Not _ = ZF_BF _ |- _] => inversion e
             | [e : _ _ _ _ = ZF_BF _ |- _] => inversion e
             | [|- dissatisfied ?A \/ Btm = Top <-> satisfied (ZF_Not ?A)] =>
               let H := fresh "H"
               in split; intro H;
                  [rewrite satisfied_unfold; destruct H as [H | H];
                   [assumption | generalize top_neq_btm; intro; rewrite H in *; exfalso; intuition] |
                   rewrite satisfied_unfold in H; left; apply H]
             | [|- dissatisfied ?X <-> satisfied (ZF_Not ?X)] => rewrite satisfied_unfold; tauto
             | [|- satisfied ?X <-> dissatisfied (ZF_Not ?X)] => rewrite dissatisfied_unfold; tauto
           end.

  (* Simplification keeps the validity. *)
  Lemma simplify_ok: forall f, (satisfied f <-> satisfied (simplifyZF f)) /\
                               (dissatisfied f <-> dissatisfied (simplifyZF f)).
  Proof.
    intros; remember (length_zform f); assert (length_zform f <= n) by omega; clear Heqn; revert f H;
    induction n; intros.
    exfalso; destruct f; simpl in H; omega.
    destruct f; simpl.
    apply eliminate_ok.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    rewrite satisfied_unfold; rewrite dissatisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    rewrite satisfied_unfold; rewrite dissatisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    split; [rewrite satisfied_unfold; rewrite DST1, SAT2 | rewrite dissatisfied_unfold; rewrite SAT1, DST2];
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S : length_zform f <= n) by omega;
    destruct (IHn _ S) as [SAT DST]; split; [rewrite satisfied_unfold; rewrite DST | rewrite dissatisfied_unfold; rewrite SAT];
    clear H S SAT DST IHn n; destruct (simplifyZF f); solve_cnt.

    simpl in H; apply le_S_n in H; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold;
    split; split; intros; [| | destruct H0 as [x H0] | destruct H0 as [x H0]];
    assert (S : length_zform (substitute (v, conv q x) f) <= n) by (rewrite <- substitute_length_inv; assumption);
    destruct (IHn _ S) as [SAT DST];
    [rewrite simp_subst_same | rewrite <- simp_subst_same in SAT |
     exists x; rewrite simp_subst_same | exists x; rewrite <- simp_subst_same in DST]; intuition.

    simpl in H; apply le_S_n in H; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold;
    split; split; intros; [destruct H0 as [x H0] | destruct H0 as [x H0] | |];
    assert (S : length_zform (substitute (v, conv q x) f) <= n) by (rewrite <- substitute_length_inv; assumption);
    destruct (IHn _ S) as [SAT DST];
    [exists x; rewrite simp_subst_same | exists x; rewrite <- simp_subst_same in SAT |
            rewrite simp_subst_same | rewrite <- simp_subst_same in DST]; intuition.
  Qed.

End SimplifyArith.
