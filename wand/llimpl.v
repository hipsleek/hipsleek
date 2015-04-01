Require ll.
Require Import ZArith.
Require Import Sets.Ensembles.
Require Import Coq.Lists.List.

Module Mllimpl <: ll.Mll.

Definition A := list nat.
Definition node := nat.
Definition null_node := 0.

Inductive HF : Type :=
  | H_emp : HF
  | H_ptto : nat -> Z -> nat -> HF
  | H_star : HF -> HF -> HF
  | H_and : HF -> HF -> HF
  | H_imp : HF -> HF -> HF
  | H_not : HF -> HF
  | H_eq : nat -> nat -> HF
  | H_cons : A -> nat -> A -> HF
  | H_reverse : A -> A -> HF
  | H_append : A -> A -> A -> HF
  | H_isempty : A -> HF
  | H_ll : nat -> A -> HF.

Definition formula := HF.  
Definition star := H_star.
Definition and := H_and.
Definition imp := H_imp.
Definition not := H_not.
Definition eq := H_eq.
Definition ptto_node := H_ptto.

Definition cons := H_cons.
Definition reverse := H_reverse.
Definition append := H_append.
Definition isempty := H_isempty.
Definition ll := H_ll.

Definition heap := Ensemble nat.

Definition empty_heap := Empty_set nat.

Definition heap_union h1 h2 := Union nat h1 h2.

Definition heap_is_disjoint h1 h2 := Disjoint nat h1 h2.

Inductive LL (n:nat) (l:A) : heap -> Prop :=
  | NIL_LL : LL n l empty_heap
  | CONS_LL : forall h h1 h2 n1 n2, h = heap_union h1 h2
              -> heap_is_disjoint h1 h2 
              -> n1 > 0 -> n1 = (hd 0 l)
              -> LL n2 (tl l) h1 -> LL n l h.

Fixpoint satis (f:formula) (h:heap) :Prop := 
match f with
  | H_emp => h = empty_heap
  | H_ptto n _ _ => n > 0
  | H_star f1 f2 => exists h1 h2, h = heap_union h1 h2 /\ heap_is_disjoint h1 h2 /\
                    satis f1 h1 /\ satis f2 h2  
  | H_and f1 f2 => satis f1 h /\ satis f2 h
  | H_imp f1 f2 => satis f1 h -> satis f2 h 
  | H_not f => ~(satis f h)
  | H_eq n1 n2 => n1 = n2
  | H_cons l n l1 => l = n::l1
  | H_reverse l l1 => l = (rev l1)
  | H_append l l1 l2 => l = l1 ++ l2
  | H_isempty l => l = nil
  | H_ll n l => LL n l h
end.

Definition valid (f:formula) := forall h, satis f h.

(*
Lemma axiom_1 : forall L1 v Lt L La L2, valid (imp (and (cons L v Lt) (and (append Lt L1 L2) (cons La v L1))) (and (cons La v Lt) (append L La L2))).
intros.
unfold valid.
intros.
unfold satis;simpl.
intros.
destruct H,H.
destruct H1.
destruct H0.
destruct H3.
split.
split.
apply H3.
split.
destruct H4.
subst.
split.
apply H3.
apply H2.
Qed.
*)

Lemma axiom_1 : forall Lt Tr L v,exists Le Lv Lr, valid (imp (and (cons L v Lt) (reverse Tr Lt)) (and (and (and (append Lr Tr Lv) (reverse Lr L)) (cons Lv v Le)) (isempty Le))).
intros.
unfold valid.
intros.
unfold satis;simpl.
intros.
exists nil.
exists (v::nil).
exists (rev L).
split.
destruct H.
subst.
split.
split.
assert ((v::Lt) = (v::Lt)++nil).
apply eq_sym.
apply app_nil_r.
simpl. tauto.
tauto.
tauto.
tauto.
(*
apply app_comm_cons.
induction Lt.
simpl.
tauto.
apply IHLt.
apply rev_unit.
apply rev_unit.
destruct H.
destruct H0.
subst Lt.
subst v.
unfold hd in H1.
destruct L in H1.
exfalso. omega.
induction L.
simpl.
auto.
unfold tl. destruct L. simpl.
destruct L.
apply app_nil_r.
destruct L.
simpl.
exfalso.
subst.
tauto.*)
Qed.

Lemma axiom_2 : forall L, valid (imp (isempty L) (reverse L L)).
intros.
unfold valid.
intros.
unfold satis;simpl.
intros.
subst.
tauto.
(*apply eq_sym.*)
(*apply app_nil_l.*)
Qed.

Lemma axiom_3 : forall L L1, valid (imp (isempty L) (append L1 L L1)).
intros.
unfold valid. intros.
unfold satis. simpl.
intros.
subst.
apply app_nil_l .

(*

destruct H.
destruct H0,H0.
destruct H1.
clear H0.
exfalso.
omega. 
exfalso.
omega.
contradiction.
simpl in H0.
omega.
assert (null=0). auto. 
simpl.
exists nil.
intros.
exists 0.
split. split.
simpl. auto.
simpl. auto. auto.*)

Qed.

Lemma axiom_4 : forall v Lp L, valid (imp (cons L v Lp) (not (isempty L))).
intros.
unfold valid.
intros.
unfold satis. simpl. intros.
subst.
apply sym_not_eq.
apply nil_cons.
(*
Lemma axiom : forall l x v p, valid (imp (eq x 0) (lookup l x v p)).
intros.
unfold valid. intros.
unfold satis. simpl.
intros.
left.
*)
Qed.

End Mllimpl.