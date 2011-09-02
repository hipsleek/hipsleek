
Require Import ZArith.
Require Import Znumtheory.
Require Import FunctionalExtensionality.


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

Module HoareLogic.

Definition var : Type := nat.
Definition num : Type := Z.

Inductive nExpr : Type :=
  | Num: forall n : num, nExpr
  | Var: forall v : var, nExpr
  | nNeg: forall ne : nExpr, nExpr
  | Plus: forall ne1 ne2 : nExpr, nExpr
  | Minus: forall ne1 ne2 : nExpr, nExpr
  | Times: forall ne1 ne2 : nExpr, nExpr.

Definition ctx : Type := var -> num.

(* This piece of black magic makes the "*" be the type-level product 
    operator, as opposed to the multiplacation operator on nums. *)
Open Local Scope Z_scope.
(* Obviously, since it is black magic, don't remove it! :-) *)

Fixpoint neEval (g : ctx) (ne : nExpr) : num :=
  match ne with
   | Num n => n
   | Var x => g x
   | nNeg ne => 0 - (neEval g ne)
   | Plus ne1 ne2 => (neEval g ne1) + (neEval g ne2)
   | Minus ne1 ne2 => (neEval g ne1) - (neEval g ne2)
   | Times ne1 ne2 => (neEval g ne1) * (neEval g ne2)
  end.

Inductive bExpr : Type :=
  | T : bExpr
  | F : bExpr
  | bNeg : forall be : bExpr, bExpr
  | And : forall be1 be2 : bExpr, bExpr
  | Or : forall be1 be2 : bExpr, bExpr
  | LT : forall ne1 ne2 : nExpr, bExpr.

Fixpoint beEval (g : ctx) (be : bExpr) : Prop :=
  match be with
   | T => True
   | F => False
   | bNeg be => ~(beEval g be)
   | And be1 be2 => (beEval g be1) /\ (beEval g be2)
   | Or be1 be2 => (beEval g be1) \/ (beEval g be2)
   | LT ne1 ne2 => (neEval g ne1) < (neEval g ne2)
  end.

(* This restores the operators to the usual meanings *)
Close Local Scope Z_scope.
Open Local Scope type_scope.
(* Again, don't remove this or the script will break in strange ways. *)

Inductive Coms : Type :=
  | Assign : forall (x : var) (e: nExpr), Coms
  | Seq : forall c1 c2 : Coms, Coms
  | If : forall (b : bExpr) (c1 c2 : Coms), Coms
  | While : forall (b : bExpr) (c : Coms), Coms
  | Crash.

Inductive ctl : Type :=
  | kStop : ctl
  | kSeq : forall (c : Coms) (k : ctl), ctl.

Definition state : Type := ctx * ctl.

Definition upd_ctx (g : ctx) (x : var) (n : num) : ctx :=
  fun x' => if eq_nat_dec x x' then n else g x'.

(* We define step as a relation of two states *)
Inductive step : state -> state -> Prop :=
  | stepA: forall g x e n k g',
      n = neEval g e ->
      g' = upd_ctx g x n ->
      step (g, kSeq (Assign x e) k) (g', k)
  | stepS: forall g c1 c2 k,
      step (g, kSeq (Seq c1 c2) k) (g, kSeq c1 (kSeq c2 k))
  | stepI1: forall g b c1 c2 k,
      beEval g b ->
      step (g, kSeq (If b c1 c2) k) (g, kSeq c1 k)
  | stepI2: forall g b c1 c2 k,
      ~beEval g b ->
      step (g, kSeq (If b c1 c2) k) (g, kSeq c2 k)
  | stepW1: forall g b c k,
      beEval g b ->
      step (g, kSeq (While b c) k) (g, kSeq c (kSeq (While b c) k))
  | stepW2: forall g b c k,
      ~beEval g b ->
      step (g, kSeq (While b c) k) (g, k).

Inductive stepstar : state -> state -> Prop :=
  | stepsZ: forall s, 
    stepstar s s
  | stepsS: forall s s' s'',
    step s s' ->
    stepstar s' s'' ->
    stepstar s s''.

Definition assertion : Type := ctx -> Prop.

Definition assertAnd (P Q : assertion) : assertion :=
  fun g => P g /\ Q g.
Notation "P && Q" := (assertAnd P Q).

Definition Implies (P Q: assertion) : Prop :=
  forall g, P g -> Q g.
Notation "P |-- Q" := (Implies P Q) (at level 30).

Definition assertbEval (b : bExpr) : assertion :=
  fun g => beEval g b.
Notation "[ b ]" := (assertbEval b).

Definition assertReplace (x : var) (e : nExpr) (psi : assertion) : assertion :=
  fun g => psi (upd_ctx g x (neEval g e)).
Notation "[ x => e @ psi ]" := (assertReplace x e psi).

Definition can_step (st : state) : Prop :=
  exists st', step st st'.

Definition safely_halted (st : state) : Prop :=
  match st with (g, k) => k = kStop end.

Definition safe (st : state) : Prop :=
  forall st', stepstar st st' -> can_step st' \/ safely_halted st'.

Definition guards (P : assertion) (k : ctl) :=
  forall g, P g -> safe (g, k).

Definition HTuple (pre : assertion) (c : Coms) (post : assertion) : Prop :=
  forall k, guards post k -> guards pre (kSeq c k).

Lemma HT_Seq: forall a1 c1 a2 c2 a3,
  HTuple a1 c1 a2 ->
  HTuple a2 c2 a3 ->
  HTuple a1 (Seq c1 c2) a3.
Proof.
  admit.
Qed.


Lemma HT_Asgn: forall x e psi,
  HTuple [x => e @ psi] (Assign x e) psi.
Proof.
  admit.
Qed.

Lemma HT_If: forall phi b c1 psi c2,
  HTuple (phi && [b]) c1 psi ->
  HTuple (phi && [bNeg b]) c2 psi ->
  HTuple phi (If b c1 c2) psi.
Proof.
admit.
Qed.


Lemma HT_While: forall psi b c,
  HTuple (psi && [b]) c psi ->
  HTuple psi (While b c) (psi && [bNeg b]).
Proof.
  admit.
Qed.

Lemma HT_Implied: forall phi phi' psi psi' c,
  phi' |-- phi ->
  HTuple phi c psi ->
  psi |-- psi' ->
  HTuple phi' c psi'.
Proof.
  do 12 intro.
  apply H in H3.
  spec H0 k.
  apply H0.
  do 2 intro.
  apply H2.
  apply H1.
  trivial.
  trivial.
Qed.


Definition x : var := 0.
Definition y : var := 1.
Definition z : var := 2.
Open Local Scope Z_scope.

Definition neq (ne1 ne2 : nExpr) : bExpr :=
  Or (LT ne1 ne2) (LT ne2 ne1).

Definition factorial_prog : Coms := 
  Seq (Assign y (Num 1))                              (* y := 1 *)
 (Seq (Assign z (Num 0))                              (* z := 0 *)
 (While (neq (Var z) (Var x))                          (* while z <> x { *)
    (Seq (Assign z (Plus (Var z) (Num 1)))        (* z := z + 1 *)
    (Assign y (Times (Var y) (Var z)))                 (* y := y * z *)
    )                                                                    (* } *) 
 )
 ).

Definition Top : assertion := fun _ => True.

Open Local Scope nat_scope.

Fixpoint factorial (n : nat) :=
  match n with
   | O => 1
   | S n' => n * (factorial n')
 end.

Open Local Scope Z_scope.

Lemma factorial_good:
  HTuple Top factorial_prog (fun g => g y = Z_of_nat (factorial (Zabs_nat (g x)))).
Proof.
  apply HT_Seq with (fun g => g y = 1).
  replace Top with ([y => (Num 1) @ (fun g : ctx => g y = 1)]).
  apply HT_Asgn.
    extensionality g.
    unfold assertReplace, Top, upd_ctx.
    simpl.
    apply prop_ext.
    firstorder.
  apply HT_Seq with (fun g :ctx => g z = 0 /\ g y = 1).
  replace (fun g : var -> Z => g y = 1)  with 
               ([z => (Num 0) @ (fun g :ctx => g z = 0 /\ g y = 1)]).
  apply HT_Asgn.
    extensionality g.
    unfold assertReplace, Top, upd_ctx.
    simpl.
    apply prop_ext.
    firstorder.
  apply HT_Implied with 
    (fun g => g z >= 0 /\ g y = Z_of_nat (factorial (Zabs_nat (g z))))
    ((fun g => g z >= 0 /\ g y = Z_of_nat (factorial (Zabs_nat (g z)))) && 
      [bNeg (neq (Var z) (Var x))]).
    repeat intro.
    destruct H.
    rewrite H, H0.
    simpl.
    firstorder.
  apply HT_While.
  apply HT_Implied with
    (fun g => g z >=0 /\ (g y) * ((g z) + 1) = Z_of_nat (factorial (Zabs_nat ((g z) + 1))))
    (fun g : ctx => g z - 1 >= 0 /\ g y = Z_of_nat (factorial (Zabs_nat (g z)))).
    repeat intro.
    destruct H.
    destruct H.
    clear H0.
    rewrite H1.
    split; auto.
    remember (g z) as n.
    clear -H.
    destruct n; auto.
    simpl.
    rewrite <- Pplus_one_succ_r.
    rewrite nat_of_P_succ_morphism.
    simpl.
    remember (factorial (nat_of_P p)).
    clear.
    rewrite Zpos_succ_morphism.
    rewrite inj_plus.
    rewrite inj_mult.
    rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
    ring.
    elimtype False.
    auto with zarith.
  apply HT_Seq with (fun g => g z - 1 >= 0 /\ g y * g z = Z_of_nat (factorial (Zabs_nat (g z)))).
  replace (fun g : var -> Z => g z >= 0 /\ g y * (g z + 1) = Z_of_nat (factorial (Zabs_nat (g z + 1)))) with
    [z => (Plus (Var z) (Num 1)) @ (fun g : var -> Z => g z - 1 >= 0 /\ g y * g z = Z_of_nat (factorial (Zabs_nat (g z))))].
  apply HT_Asgn.
    extensionality g.
    apply prop_ext.
    firstorder.
    unfold upd_ctx in H.
    simpl in H.
    auto with zarith.
    simpl.
    unfold upd_ctx.
    simpl.
    auto with zarith.
  replace (fun g : var -> Z => g z - 1 >= 0 /\ g y * g z = Z_of_nat (factorial (Zabs_nat (g z)))) with 
    [y => (Times (Var y) (Var z)) @ (fun g : var -> Z => g z - 1>= 0 /\ g y = Z_of_nat (factorial (Zabs_nat (g z))))].
  apply HT_Asgn.
    extensionality g.
    apply prop_ext.
    firstorder.
    repeat intro; firstorder.
    repeat intro.
    destruct H.
    destruct H.
    rewrite H1.
    simpl in H0.
    destruct (Ztrichotomy (g z) (g x)).
    contradiction H0; auto.
    destruct H2.
    rewrite <- H2.
    trivial.
    contradiction H0.
    right.
    apply Zgt_lt .
    trivial.
Qed.

Print factorial_good.

End HoareLogic.