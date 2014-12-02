Require linkedlist.
Require Import ZArith.
Require Import Sets.Ensembles.
Require Import Coq.Lists.List.

Module Mlinkedlistimpl <: linkedlist.Mlinkedlist.

Definition A := list nat.
Definition node := nat.
Definition null_node := 0.

Inductive HF : Type :=
  | H_emp : HF
  | H_ptto : nat -> Z -> nat -> HF
  | H_star : HF -> HF -> HF
  | H_and : HF -> HF -> HF
  | H_imp : HF -> HF -> HF
  | H_eq : nat -> nat -> HF
  | H_lookup : A -> nat -> Z -> nat -> HF
  | H_update : A -> nat -> Z -> nat -> A -> HF
  | H_reverse : A -> A -> HF
  | H_append : A -> A -> A -> HF
  | H_isempty : A -> HF
  | H_ll : nat -> A -> HF.

Definition formula := HF.  
Definition star := H_star.
Definition and := H_and.
Definition imp := H_imp.
Definition eq := H_eq.
Definition ptto_node := H_ptto.

Definition lookup := H_lookup. 
Definition update := H_update.
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
  | H_eq n1 n2 => n1 = n2
  | H_lookup l n1 _ n2 => n1 = (hd 0 l) /\ n2 = hd 0 (tl l) /\ n1 > 0
  | H_update l1 n1 _ n2 l2 => n1 = (hd 0 l2) /\ n2 = hd 0 (tl l2) /\ tl (tl l1) = tl (tl l2)
  | H_reverse l l1 => l = (rev l1)
  | H_append l l1 l2 => l = l1 ++ l2
  | H_isempty l => l = nil
  | H_ll n l => LL n l h
end.

Definition valid (f:formula) := forall h, satis f h.

Lemma axiom_1 : forall p L L1 x v p1, valid (imp (and (lookup L x v p) (update L x v p1 L1)) (lookup L1 x v p1)).
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
apply H0.
split.
apply H3.
apply H2.
Qed.

Lemma axiom_2 : forall L, valid (imp (isempty L) (reverse L L)).
intros.
unfold valid.
intros.
unfold satis;simpl.
intros.
subst.
tauto.
Qed.

Lemma axiom_3 : forall L L1, valid (imp (isempty L) (append L1 L L1)).
intros.
unfold valid.
intros.
unfold satis;simpl.
intros.
subst.
(*apply eq_sym.*)
apply app_nil_l.
Qed.

Lemma axiom_4 : forall x v p L, valid (imp (and (eq x 0) (lookup L x v p)) (isempty L)).
intros.
unfold valid. intros.
unfold satis. simpl.
intros. 
destruct H.
destruct H0,H0.
destruct H1.
clear H0.
exfalso.
omega. 

(*
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

(*
Lemma axiom : forall l x v p, valid (imp (eq x 0) (lookup l x v p)).
intros.
unfold valid. intros.
unfold satis. simpl.
intros.
left.
*)

End Mlinkedlistimpl.