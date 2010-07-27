Require Import Arith.
Require Import List.

Require Import ZArith.
Open Scope Z_scope.


Module Type OBJ.

Parameter Obj : Type.  (* Generic objects that are to be sorted *)

Axiom obj_eq_dec : forall x y:Obj, {x=y} + {x<>y}.

Parameters obj1 obj2 obj3: Obj.
Axiom obj_doubleton : obj1 <> obj2.

Parameter klt : Obj -> Obj -> Prop. (* key ordering *)
Parameter keq : Obj -> Obj -> Prop. (* key equality *)

Parameter new_obj : Z -> Obj.
Axiom new_obj_unique : forall y z, y <> z -> new_obj y <> new_obj z.
Axiom new_obj_lt : forall y z, y < z -> klt (new_obj y) (new_obj z).
Axiom new_obj_eq : forall y z, y = z -> keq (new_obj y) (new_obj z).

(* klt is a total order, keq is an equivalence relation *)
Axiom key_dec : forall a b:Obj, {klt a b} + {keq a b} + {klt b a}.
Axiom keq_dec : forall a b:Obj, {keq a b} + {~ (keq a b)}.

Axiom keq_refl : forall a, keq a a.
Axiom keq_sym : forall a b, keq a b -> keq b a.
Axiom keq_trans : forall a b c, keq a b -> keq b c -> keq a c.

Axiom klt_antirefl : forall a, ~ klt a a.
Axiom klt_total : forall a b:Obj, ~ (keq a b) -> {klt a b} + {klt b a}.
Axiom klt_trans : forall a b c, klt a b -> klt b c -> klt a c.

Axiom keq_klt_left: forall x y z, keq x y -> klt x z -> klt y z.
Axiom keq_klt_right: forall x y z, keq x y -> klt z x -> klt z y.

Axiom Obj_eq_dec: forall a b:Obj, {a=b}+{~ a=b}.
Axiom Obj_keq_doubleton : ~ keq obj2 obj3.
Axiom Obj_keq_choice : forall x:Obj, exists y:Obj, ~ keq x y.
Axiom Obj_keq_choice2 : forall x y:Obj, ~ keq x y -> 
                     exists z:Obj, ~ keq z x /\ ~ keq z y.

(* Notations *)

Notation "x &< y" := (klt x y) (at level 70, no associativity).
Notation "x &= y" := (keq x y) (at level 70, no associativity).
Definition kle x y := klt x y \/ keq x y.
Notation "x &<= y" := (kle x y) (at level 70, no associativity).

End OBJ.

Module ZZ:OBJ with Definition Obj := prod Z Z
              with Definition klt := fun (x y:prod Z Z) => fst x < fst y
              with Definition keq := fun (x y:prod Z Z) => fst x = fst y.

Definition Obj := prod Z Z.
Definition new_obj := fun (i : Z) => (i, i).

Lemma new_obj_unique: forall y z, y <> z -> new_obj y <> new_obj z.
Proof.
  intros. unfold new_obj. intro. inversion H0. rewrite H2 in H. contradict H. apply H3.
Save.

Lemma obj_eq_dec : forall x y:Obj, {x=y} + {x<>y}.
Proof.
intros. destruct x. destruct y. destruct (Z_eq_dec z z1). subst.
destruct (Z_eq_dec z0 z2). subst. left. reflexivity. right.
intro. inversion H. apply n. assumption. right. intro.
inversion H. apply n. assumption.
Save.

Definition obj1 := (1,1) .
Definition obj2 := (2,2) .
Definition obj3 := (3,3) .

Lemma obj_doubleton : obj1 <> obj2.
Proof.
unfold obj1. unfold obj2.
intro. inversion H.
Save.

Definition klt (x y:Obj) := fst x < fst y.
Definition keq (x y:Obj) := fst x = fst y.

Lemma new_obj_lt : forall y z, y < z -> klt (new_obj y) (new_obj z).
Proof.
  intros. unfold klt, new_obj, fst. apply H.
Save.

Lemma new_obj_eq : forall y z, y = z -> keq (new_obj y) (new_obj z).
Proof.
  intros. unfold keq, new_obj, fst. apply H.
Save.

Lemma key_dec : forall a b:Obj, {klt a b} + {keq a b} + {klt b a}.
Proof.
intros. destruct a. destruct b. unfold klt. unfold keq. simpl.
destruct (Ztrichotomy_inf z z1). destruct s. left. left. assumption.
left. right. assumption. right. apply Zgt_lt. assumption.
Save.

Lemma keq_dec : forall a b:Obj, {keq a b} + {~ (keq a b)}.
Proof.
intros. unfold keq. destruct a. destruct b. simpl.
destruct (Z_eq_dec z z1). left. assumption.
right. assumption.
Save.

Lemma keq_refl : forall a, keq a a.
Proof.
intros. destruct a. unfold keq. simpl. reflexivity.
Save.

Lemma keq_sym : forall a b, keq a b -> keq b a.
Proof.
intros. destruct a. destruct b. unfold keq. unfold keq in H.
simpl. simpl in H. subst. reflexivity.
Save.

Lemma keq_trans : forall a b c, keq a b -> keq b c -> keq a c.
Proof.
unfold keq. intros. destruct a. destruct b. destruct c.
simpl. simpl in H0. simpl in H.
subst. reflexivity.
Save.

Lemma klt_antirefl : forall a, ~ klt a a.
Proof.
intros. destruct a. unfold klt. simpl.
apply Zlt_irrefl.
Save.

Lemma klt_total : forall a b:Obj, ~ (keq a b) -> {klt a b} + {klt b a}.
Proof.
unfold keq. unfold klt. intros a b. destruct a. destruct b. simpl.
destruct (Ztrichotomy_inf z z1).
destruct s.
intro. left. assumption. intro. destruct (H e).
intro. right. apply Zgt_lt. assumption.
Save.

Lemma klt_trans : forall a b c, klt a b -> klt b c -> klt a c.
Proof.
unfold klt. intros a b c. destruct a. destruct b. destruct c. simpl.
intros. apply Zlt_trans with (m:=z1). assumption. assumption.
Save.

Lemma keq_klt_left: forall x y z, keq x y -> klt x z -> klt y z.
Proof.
unfold keq. unfold klt. intros x y z. destruct x. destruct y. destruct z.
simpl. intros. subst. assumption.
Save.

Lemma keq_klt_right: forall x y z, keq x y -> klt z x -> klt z y.
Proof.
intros x y z. unfold keq. unfold klt. destruct x. destruct y. destruct z.
simpl. intros. subst. assumption.
Save.

Lemma Obj_eq_dec: forall a b:Obj, {a=b}+{~ a=b}.
Proof.
exact obj_eq_dec.
Save.

Lemma Obj_keq_doubleton : ~ keq obj2 obj3.
Proof.
unfold keq. unfold obj2. unfold obj3. simpl. omega.
Save.

Lemma Obj_keq_choice : forall x:Obj, exists y:Obj, ~ keq x y.
Proof.
intros. unfold keq. destruct x. exists (z+1,z0). simpl. omega.
Save.

Lemma Obj_keq_choice2 : forall x y:Obj, ~ keq x y -> 
                     exists z:Obj, ~ keq z x /\ ~ keq z y.
Proof.
unfold keq. intros. destruct x. destruct y. simpl. simpl in H.
destruct (Ztrichotomy z z1).
exists (z1+1,0). simpl. omega.
destruct H0. destruct (H H0).
exists (z+1,0). simpl. omega.
Save.

(* Notations *)

Notation "x &< y" := (klt x y) (at level 70, no associativity).
Notation "x &= y" := (keq x y) (at level 70, no associativity).
Definition kle x y := klt x y \/ keq x y.
Notation "x &<= y" := (kle x y) (at level 70, no associativity).

End ZZ.

Module STSORT (O:OBJ).

Export O.

Lemma non_nil : forall l (x:Obj) l', l = x::l' -> l <> nil.
Proof.
intros. destruct l. inversion H. intro. inversion H0.
Save.

Open Scope nat_scope.

Lemma length_non_nil : forall l, 0 < length l -> l <> nil (A:=Obj).
Proof.
intros. destruct l. elimtype False. simpl in H. unfold lt in H. inversion H. intro. inversion H0.
Save.

Lemma keq_kle_left : forall x y z, keq x y -> kle x z -> kle y z.
Proof.
intros. destruct H0. unfold kle. left. apply (keq_klt_left x y z H) in H0.
assumption. unfold kle. right. apply keq_sym in H.
apply (keq_trans y x z H H0).
Save.

(* Convenient decidability lemmas *)
Lemma klt_kle_dec : forall x y, {x &< y} + {y &<= x}.
Proof.
intros. destruct (key_dec x y). destruct s. left. assumption.
right. unfold kle. right. apply keq_sym. assumption. right.
unfold kle. left. assumption.
Save.

Lemma kle_klt_dec : forall x y, {x &<= y} + {y &< x}.
Proof.
intros. destruct (key_dec x y). left. unfold kle. destruct s. left.
assumption. right. assumption. right. assumption.
Save.

Lemma klt_not_keq : forall x y, x &< y -> ~ x &= y.
intros. intro. apply (klt_antirefl y).
apply (keq_klt_left x y y). assumption. assumption.
Save.

Lemma kle_trans : forall x y z, kle x y -> kle y z -> kle x z.
Proof.
unfold kle. intros. destruct H. destruct H0. left. 
apply klt_trans with (b:=y). assumption. assumption.
left. apply keq_klt_right with (x := y).
assumption. assumption. destruct H0. left.
apply keq_sym in H. apply keq_klt_left with (x:=y).
assumption. assumption. right.
apply keq_trans with (b:=y). assumption. assumption.
Save.

Lemma kle_klt_trans : forall x y z, kle x y -> klt y z -> klt x z.
Proof.
intros.
unfold kle in H.
destruct H.
apply (klt_trans x y z H H0).
apply keq_sym in H.
apply (keq_klt_left y x z H H0).
Save.

Lemma klt_kle_trans : forall x y z, klt x y -> kle y z -> klt x z.
Proof.
intros. destruct H0. apply (klt_trans x y z H H0).
apply (keq_klt_right y z x H0 H).
Save.

(* Binary minima operators *)

Definition kmin (x y:Obj) 
           := if kle_klt_dec x y then x else y.

(* Minimum of a list *)

Fixpoint kminlopt (l:list Obj) {struct l} : option Obj := (* helper minimum *)
  match l with
   | nil => None
   | x :: l => let y := kminlopt l
               in match y with
                  | None =>  Some x
                  | Some z => Some (kmin x z)
                  end
  end.

Lemma kminlopt_none : 
   forall l, kminlopt l = None -> l = nil.
Proof.
intro. destruct l. reflexivity. simpl. destruct (kminlopt l).
intro. inversion H. intro. inversion H.
Save.

Lemma kminlopt_some : 
   forall l, l<>nil -> {x:Obj | Some x = kminlopt l}.
Proof.
intros. destruct l. elimtype False. apply H. reflexivity. simpl.
destruct (kminlopt l). exists (kmin o o0). 
reflexivity. exists o.
reflexivity.
Defined.

Lemma kminlopt_some_gminlopt :
   forall l (H:l<>nil) x, Some x = kminlopt l -> proj1_sig (kminlopt_some l H) = x.
Proof.
intros.
destruct (kminlopt_some l H).
simpl.
rewrite <- H0 in e.
inversion e.
reflexivity.
Save.

Lemma kminlopt_singleton :
   forall x, Some x = kminlopt (x::nil).
Proof.
intros. simpl. reflexivity.
Save.

Lemma kminlopt_cons :
   forall x l (H:l<>nil) ,
     Some (kmin x (proj1_sig (kminlopt_some l H))) =
             kminlopt (x::l).
Proof.
intros. unfold kmin. destruct (kle_klt_dec x ((proj1_sig (kminlopt_some l H)))).
destruct (kminlopt_some l H). simpl in k. simpl. destruct l.
elimtype False. apply H. reflexivity. destruct (kminlopt (o::l)).
f_equal. injection e. intro. subst. unfold kmin. destruct (kle_klt_dec x o0).
reflexivity. elimtype False. apply (kle_klt_trans x o0 x k) in k0.
apply (klt_antirefl x k0). reflexivity. 
destruct (kminlopt_some l H). simpl in *|-*.
rewrite <- e. f_equal. unfold kmin. destruct (kle_klt_dec x x0).
elimtype False. apply (kle_klt_trans x x0 x k0) in k.
apply (klt_antirefl x k). reflexivity.
Save.

(* The actual minimum for keys *)
Definition kminl (l : list Obj) (H : l <> nil) := proj1_sig (kminlopt_some l H).

Lemma kminl_non_nil : forall (l:list Obj) (H1 H2:l<>nil), kminl l H1 = kminl l H2.
Proof.
intros. destruct l. elimtype False. apply H1. reflexivity. unfold kminl. reflexivity.
Save.

Lemma kminlopt_kminl : forall (l : list Obj) (H:l <> nil), kminlopt l = Some (kminl l H).
Proof.
intros. unfold kminl. destruct l. elimtype False. apply H. reflexivity. simpl. destruct (kminlopt l). f_equal. f_equal.
Save.

Lemma kminl_singleton : forall x (H:x::nil<>nil), x = kminl (x::nil) H.
Proof.
intros. assert (Some x = Some (kminl (x::nil) H)). rewrite <- (kminlopt_kminl (x::nil) H).
apply kminlopt_singleton. revert H0. generalize (kminl (x::nil) H). intros. inversion H0. reflexivity.
Save.

Lemma kminl_cons: forall x l (H:l<>nil) (H1:x::l<>nil), kminl (x::l) H1 = kmin x (kminl l H).
Proof.
intros. unfold kminl at 1. destruct (kminlopt_some (x::l) H1).
simpl. rewrite <- (kminlopt_cons x l H) in e. destruct (kminlopt_some l H).
simpl in e. inversion e. f_equal. rewrite (kminlopt_kminl l H) in e0. inversion e0. reflexivity.
Save.

Fixpoint kminl2 (x:Obj) (l:list Obj) :=
   match l with
   | nil => x
   | y :: l' => kmin x (kminl2 y l')
   end.

Lemma kminl_kminl2 : forall x l (H:x::l<>nil), kminl (x::l) H = kminl2 x l.
Proof.
fix circ 2. destruct l. intros. rewrite <- (kminl_singleton x H). simpl. reflexivity.
intro. rewrite (kminl_cons x (o::l) (non_nil (o::l) o l (refl_equal (o::l))) H).
simpl. f_equal. apply circ.
Save.

Lemma keq_kminl2 : forall x y l, keq x y -> kminl2 x l &= kminl2 y l.
Proof.
intros.
destruct l.
simpl. assumption. simpl. unfold kmin. destruct (kle_klt_dec x (kminl2 o l)).
destruct (kle_klt_dec y (kminl2 o l)). assumption. elimtype False. destruct k.
apply (keq_klt_left x y) in H0. apply (klt_trans y (kminl2 o l) y H0) in k0.
apply (klt_antirefl y) in k0. assumption. assumption.
apply (keq_sym x (kminl2 o l)) in H0. apply (keq_klt_left (kminl2 o l) x y H0) in k0.
apply (keq_klt_left x y y H) in k0. apply (klt_antirefl y) in k0. assumption.
destruct (kle_klt_dec y (kminl2 o l)). elimtype False. apply (kle_klt_trans y (kminl2 o l) x k0) in k.
apply (klt_not_keq y x) in k. apply k. apply keq_sym. assumption. apply keq_refl.
Save.

Lemma kle_kminl2 : forall x y l, x &<= y -> kminl2 x l &<= kminl2 y l.
Proof.
intros. destruct l. simpl. assumption.
simpl. unfold kmin. destruct (kle_klt_dec x (kminl2 o l)).
destruct (kle_klt_dec y (kminl2 o l)). assumption. assumption.
destruct (kle_klt_dec y (kminl2 o l)). 
apply (klt_kle_trans (kminl2 o l) x y k) in H.
unfold kle. left. assumption. unfold kle. right. apply keq_refl.
Save.

Fixpoint remove (a:Obj) (l:list Obj) {struct l} :=
  match l with 
  | nil => nil
  | x::l' => if (keq_dec x a) then l' else x::(remove a l')
  end.

Lemma remove_keq : forall a b l, keq a b -> remove a l = remove b l.
Proof.
fix circ 3. intros. destruct l.
reflexivity. simpl. destruct (keq_dec o a). destruct (keq_dec o b). reflexivity.
elimtype False. apply (keq_trans o a b k) in H. apply n. assumption.
destruct (keq_dec o b). apply (fun z => keq_trans a b o z (keq_sym o b k)) in H.
elimtype False. apply n. apply (keq_sym a o H).
rewrite (circ a b l H). reflexivity.
Save.

Inductive sorted : list Obj -> Prop :=
  | sorted_nil : sorted nil
  | sorted_singleton : forall x, sorted (x::nil)
  | sorted_cons : forall x y l, x &<= y -> sorted (y::l) -> sorted (x::y::l).

Lemma sorted_tail : forall x l, sorted (x::l) -> sorted l.
Proof.
intros. inversion H. constructor. assumption.
Save.

Lemma sorted_remove :
  forall x l, sorted l -> sorted (remove x l).
Proof.
fix circ 3. intros. destruct H. simpl. constructor. simpl. destruct (keq_dec x0 x). constructor.
constructor. assert (IH := circ x (y::l) H0). revert H0 IH.
assert (exists l', l' = (y::l)).
exists (y::l). reflexivity. destruct H0. rewrite <- H0.
intros. simpl. destruct (keq_dec x0 x). assumption. subst.
simpl in IH|-*. destruct (keq_dec y x).
destruct l. constructor. constructor. inversion H1. apply (kle_trans x0 y o H H3).
assumption. constructor. assumption. assumption.
Save.

Lemma remove_length : 
   forall l (H:l<>nil), length l = S (length (remove (kminl l H) l)).
Proof.
fix circ 1. 
Show Proof.
intros. destruct l. elimtype False. apply H. reflexivity. assert (IH := circ l).
destruct l. simpl. rewrite <- (kminl_singleton o H). destruct (keq_dec o o). reflexivity.
elimtype False. apply n. apply keq_refl. 
rewrite (kminl_cons o (o0::l) (non_nil (o0::l) o0 l (refl_equal (o0::l))) H).
unfold kmin. destruct (kle_klt_dec o (kminl (o0 :: l) (non_nil (o0 :: l) o0 l (refl_equal (o0 :: l))))).
simpl. destruct (keq_dec o o). reflexivity. elimtype False. apply n. apply keq_refl.
change (length (o::o0::l)) with (S (length (o0::l))).
f_equal. unfold remove. fold remove.
destruct (keq_dec o (kminl (o0::l) (non_nil (o0::l) o0 l (refl_equal (o0::l))))).
reflexivity. rewrite (IH (non_nil (o0::l) o0 l (refl_equal (o0::l)))). simpl.
destruct ( keq_dec o0 (kminl (o0 :: l) (non_nil (o0 :: l) o0 l (refl_equal (o0 :: l))))).
reflexivity. simpl. f_equal. 
Save.

Lemma remove_length2 : forall x l, length (x::l) = S (length (remove (kminl2 x l) (x::l))).
Proof.
fix circ 2.
intros. destruct l.
simpl. destruct (keq_dec x x). reflexivity. elimtype False. apply n. apply keq_refl.
assert (exists y, y = o::l). exists (o::l). reflexivity. destruct H. rewrite <- H.
simpl. destruct (keq_dec x (kminl2 x x0)). reflexivity. simpl. rewrite H.
unfold kminl2. fold kminl2. unfold kmin. destruct (kle_klt_dec x (kminl2 o l)).
rewrite H in n. elimtype False. apply n. simpl. unfold kmin.
destruct (kle_klt_dec x (kminl2 o l)). apply keq_refl. destruct k.
elimtype False. apply (klt_trans x (kminl2 o l) x H0) in k0. apply (klt_antirefl x).
assumption. assumption. rewrite <- circ. reflexivity.
Save.

Lemma  le_kminl2_remove : forall o o0 l, o &<= kminl2 o0 l -> o &<= kminl2 o0 (remove o l).
Proof.
fix circ 3. intros. destruct l. simpl in H|-*. assumption.
simpl in H|-*. destruct (keq_dec o1 o). unfold kmin in H.
destruct (kle_klt_dec o0 (kminl2 o1 l)). 
apply (keq_sym o1 o) in k. apply (keq_kle_left o o1 o0 k) in H.
assert (H0 := kle_kminl2 o1 o0 l H).
apply (keq_kle_left o1 o (kminl2 o0 l) (keq_sym o o1 k)).
apply (kle_trans o1 o0 (kminl2 o0 l) H).
apply (kle_trans o0 (kminl2 o1 l) (kminl2 o0 l) k0 H0).
apply (kle_trans o (kminl2 o1 l) (kminl2 o0 l) H).
apply (keq_kle_left o o1 (kminl2 o1 l) (keq_sym o1 o k)) in H.
assert (H0 := kle_klt_trans o1 (kminl2 o1 l) o0 H k0).
assert (H1 := or_introl (o1 &= o0) H0). change ( o1 &< o0 \/ o1 &= o0) with (o1 &<= o0) in H1.
apply (kle_kminl2 o1 o0 l H1). simpl. unfold kmin.
destruct (kle_klt_dec o0 (kminl2 o1 (remove o l))).
unfold kmin in H. destruct (kle_klt_dec o0 (kminl2 o1 l)).
assumption. apply (kle_klt_trans o (kminl2 o1 l) o0 H) in k0.
unfold kle. left. assumption. apply circ.
unfold kmin in H. destruct (kle_klt_dec o0 (kminl2 o1 l)).
apply (kle_trans o o0 (kminl2 o1 l) H k0). assumption.
Save.

Lemma kminl2_remove : forall o l, kminl2 o l &<= kminl2 o (remove (kminl2 o l) l).
Proof.
fix circ 2. intros. destruct l.
simpl. unfold kle. right. apply keq_refl.
simpl. unfold kmin. destruct (kle_klt_dec o (kminl2 o0 l)).
destruct (keq_dec o0 o). destruct l. simpl. unfold kle. right. apply keq_refl.
simpl. unfold kmin. destruct (kle_klt_dec o (kminl2 o1 l)). unfold kle. right. apply keq_refl.
elimtype False. apply (klt_kle_trans (kminl2 o1 l) o (kminl2 o0 (o1::l)) k1) in k.
simpl in k. unfold kmin in k. destruct (kle_klt_dec o0 (kminl2 o1 l)).
apply (kle_klt_trans o0 (kminl2 o1 l) o k2) in k1. apply (klt_not_keq o0 o) in k1.
apply k1. assumption. apply (klt_antirefl (kminl2 o1 l)) in k. assumption.
simpl. unfold kmin. destruct (kle_klt_dec o (kminl2 o0 (remove o l))).
unfold kle. right. apply keq_refl. revert k.  
apply le_kminl2_remove. destruct (keq_dec o0 (kminl2 o0 l)).
apply (kle_kminl2 o0 o l). unfold kle. left. apply (keq_klt_left (kminl2 o0 l) o0 o (keq_sym o0 (kminl2 o0 l) k0)).
assumption. simpl. unfold kmin. destruct (kle_klt_dec o (kminl2 o0 (remove (kminl2 o0 l) l))).
unfold kle. left. assumption. apply circ.
Save.

Fixpoint selsorth (l:list Obj) (n:nat) {struct n} :=
  match n with
  | 0 => nil
  | S n => 
      match l with
      | nil => nil
      | z::l' =>  
          let x := (kminl2 z l') in
          x :: (selsorth (remove x l) n)
      end
  end.

Definition selsort l := selsorth l (length l).

Lemma kminl_kle1 : forall x l H H', kle x (kminl l H) -> x = kminl (x::l) H'.
Proof.
intros. destruct l. unfold kminl. apply kminl_singleton. rewrite (kminl_cons x (o::l) H H'). unfold kmin. 
destruct (kle_klt_dec x (kminl (o::l) H)). reflexivity. destruct H0. 
apply (klt_trans x (kminl (o::l) H) x H0) in k. elimtype False. apply (klt_antirefl x k). 
apply keq_sym in H0. apply (keq_klt_left (kminl (o::l) H) x x H0) in k. elimtype False. apply (klt_antirefl x k).
Save.

Lemma kminl_kle2 : forall x l H H', klt (kminl l H) x -> kminl l H = kminl (x::l) H'.
Proof.
intros. destruct l. elimtype False. apply H. reflexivity. rewrite (kminl_cons x (o::l) H H' ).
unfold kmin. revert H0. generalize (kminl (o::l) H). intros. destruct (kle_klt_dec x o0). 
apply (kle_klt_trans x o0 x k) in H0. elimtype False. apply (klt_antirefl x H0). reflexivity.
Save.

Lemma kle_kminl : forall x o l H, x &<= kminl (o::l) H -> x &<= o.
Proof.
intros. destruct l. rewrite <- (kminl_singleton o) in H0.
assumption. assert (H1 := non_nil (o0::l) o0 l (refl_equal (o0::l))).
destruct (kle_klt_dec o (kminl (o0::l) H1)). rewrite <- (kminl_kle1 o (o0::l) H1 H k) in H0.
assumption. rewrite <- (kminl_kle2 o (o0::l) H1 H k) in H0. 
assert (H2 := or_introl (keq (kminl (o0::l) H1) o) k). pattern (kminl (o0::l) H1), o in H2.
fold kle in H2. apply kle_trans with (y:= kminl (o0::l) H1). assumption. assumption.
Save.

Lemma sorted_kminl :
  forall l x (H:l<>nil) , x &<= kminl l H -> sorted l -> sorted (x::l).
Proof.
intros. destruct l. elimtype False. apply H. reflexivity. constructor. 
apply (kle_kminl x o l H).
assumption. assumption.
Save.

Lemma sorted_kle : forall (x y:Obj) (l:list Obj), kle x y -> sorted (y::l) -> sorted (x::l).
Proof.
intros. inversion H0. constructor. constructor. apply kle_trans with (y:=y).
assumption. assumption. assumption.
Save.

Lemma selsorth_not_nil:
  forall l n, l<>nil -> length l <= n -> selsorth l n <> nil.
Proof.
intros. destruct n. inversion H0. destruct l. elimtype False. apply H. reflexivity.
simpl in H2. inversion H2. simpl. destruct l. assumption. simpl in H0. apply le_S_n in H0.
destruct l. 
simpl. destruct (keq_dec o o). intro. inversion H1. intro. inversion H1.
intro. inversion H1.
Save.

Lemma selsort_length : forall l n, length l <= n -> length l = length (selsorth l n).
Proof.
fix circ 2. intros. destruct n. destruct l. reflexivity. inversion H. 
simpl.
destruct l. reflexivity.
change (length (o::l)) with (S (length l)).
change (length ((kminl2 o l)::(selsorth (remove (kminl2 o l) (o::l))n))) with (S (length (selsorth (remove (kminl2 o l) (o::l)) n))).
rewrite <- circ. rewrite <- remove_length2. reflexivity.
apply le_S_n. rewrite <- remove_length2. assumption.
Save.

Lemma kminl2_kminl2 : forall x y l, kminl2 x (y::l) &<= kminl2 y l.
Proof.
intros. destruct l.
simpl. unfold kmin. destruct (kle_klt_dec x y). assumption. unfold kle. right. apply keq_refl.
change (kminl2 x (y::o::l)) with (kmin x (kminl2 y (o::l))).
unfold kmin. destruct (kle_klt_dec x (kminl2 y (o::l))). assumption.
unfold kle. right. apply keq_refl.
Save.

Lemma selsort_helper :
  forall l n, length l <= n -> sorted (selsorth l n).
Proof.
fix circ 2. intros. destruct n. simpl. constructor. simpl. destruct l. constructor. 
assert (IH := fun l => circ l n). destruct n. simpl. constructor. simpl.
destruct (keq_dec o (kminl2 o l)). destruct l. constructor. constructor.
apply kminl2_kminl2. 
change (kminl2 o0 l :: selsorth (remove (kminl2 o0 l) (o0 :: l)) n) with (selsorth (o0::l) (S n)).
apply IH. simpl in H |- * . apply (le_S_n (S (length l)) (S n) H).
constructor. apply kminl2_remove. assert (H0 := (IH (o::(remove (kminl2 o l) l)))).
simpl in H0. cut (S (length (remove (kminl2 o l) l)) <= S n). intro. apply H0 in H1. clear H0.
cut (selsorth (if keq_dec o (kminl2 o (remove (kminl2 o l) l))
               then remove (kminl2 o l) l
               else o :: remove (kminl2 o (remove (kminl2 o l) l)) (remove (kminl2 o l) l)) n
     = selsorth (remove (kminl2 o (remove (kminl2 o l) l)) (o :: remove (kminl2 o l) l)) n).
intro. rewrite <- H0. assumption. clear H1 circ. destruct (keq_dec o (kminl2 o (remove (kminl2 o l) l))). 
rewrite (remove_keq (kminl2 o (remove (kminl2 o l) l)) o (o::remove (kminl2 o l) l) (keq_sym o (kminl2 o (remove (kminl2 o l) l)) k)).
simpl. destruct (keq_dec o o). reflexivity. elimtype False. apply n1. apply keq_refl. f_equal. simpl. 
destruct (keq_dec o (kminl2 o (remove (kminl2 o l) l))). elimtype False. apply n1. assumption. reflexivity. clear H0.
assert (H0 := remove_length2 o l). simpl in H0. destruct (keq_dec o (kminl2 o l)). elimtype False. apply n0. assumption.
simpl in H0. inversion H0. simpl in H. apply (le_S_n (length l) (S n) H).
Save.

Theorem selsort_correct :
  forall l, sorted (selsort l).
Proof.
intros. unfold selsort.
apply selsort_helper. constructor.
Save.

Inductive first_occurrence : Obj -> list Obj -> Obj -> Prop :=
  first_occurrence_head : forall x l y, keq x y -> first_occurrence x (y::l) y
| first_occurrence_tail : forall x z l y, ~ keq x y -> first_occurrence x l z -> first_occurrence x (y::l) z.

Lemma first_occurrence_keq :
  forall x y l, first_occurrence x l y -> x &= y.
Proof.
intros. induction H. assumption. assumption.
Save.

Lemma keq_first_occurrence :
  forall x y z l, x &= y -> first_occurrence x l z -> first_occurrence y l z.
Proof.
intros. induction H0. constructor. apply (keq_trans y x y0). apply keq_sym.
assumption. assumption. constructor. intro. apply H0. apply (keq_trans x y y0).
assumption. assumption. apply IHfirst_occurrence. assumption.
Save.

Lemma first_occurrence_first : 
   forall x y l, first_occurrence x l y -> first_occurrence y l y.
Proof.
intros. induction H. constructor. apply keq_refl. assert (x &= z).
apply first_occurrence_keq with (l:=l). assumption. 
apply (keq_first_occurrence x z z (y::l)). assumption. constructor. 
assumption. assumption.
Save.

Inductive stable_ind : list Obj -> list Obj -> Prop :=
  stable_ind_nil : stable_ind nil nil
| stable_ind_cons : forall x l l', first_occurrence x l' x -> 
                       stable_ind l (remove x l') -> stable_ind (x::l) l'.

Inductive stable_ind' : list Obj -> list Obj -> Prop :=
  stable_ind_nil' : stable_ind' nil nil
| stable_ind_cons' : forall x y l l', first_occurrence x l' y -> 
                       stable_ind' l (remove x l') -> stable_ind' (y::l) l'.

Lemma stable_ind_ind' : 
   forall l l', stable_ind l l' -> stable_ind' l l'.
Proof.
intros. induction H. constructor. apply (stable_ind_cons' x x).
assumption. assumption.
Save.

Lemma stable_ind_ind'' :
  forall l l', stable_ind' l l' -> stable_ind l l'.
Proof.
intros. induction H. constructor. constructor. 
apply first_occurrence_first with (x:=x). assumption.
assert (remove x l' = remove y l'). apply remove_keq.
apply first_occurrence_keq with (l:=l'). assumption. rewrite <- H1. assumption.
Save.

Fixpoint filter (x:Obj) (l:list Obj) :=
  match l with
  | nil => nil
  | y :: l' => if (keq_dec x y) then y::(filter x l') else filter x l'
  end.

Definition stable (l l': list Obj) :=
  forall (x:Obj), filter x l = filter x l'.

Lemma kminl2_first : forall x l, keq x (kminl2 x l) -> x = kminl2 x l.
intros. destruct l. simpl. reflexivity. simpl in H|-*. unfold kmin in H|-*.
destruct (kle_klt_dec x (kminl2 o l)). reflexivity. elimtype False.
apply (klt_not_keq (kminl2 o l) x) in k. apply k. 
apply (keq_sym x (kminl2 o l)) in H. assumption.
Save.

Lemma filter_remove : forall x y l, filter x (remove y l) = remove y (filter x l).
Proof.
fix circ 3. intros. destruct l. simpl. reflexivity. simpl. destruct (keq_dec o y).
destruct (keq_dec x o). simpl. destruct (keq_dec o y). reflexivity. elimtype False.
apply n. assumption. clear circ. revert l. fix circ 1. intro. destruct l. simpl.
reflexivity. simpl. destruct (keq_dec x o0). simpl. destruct (keq_dec o0 y).
elimtype False. apply n. apply (keq_sym o y) in k. apply (keq_trans x o0 y k0) in k1.
apply (keq_trans x y o k1) in k. assumption. rewrite (circ l) at 1. reflexivity.
apply (circ l). simpl. destruct (keq_dec x o). simpl. destruct (keq_dec o y).
elimtype False. apply n. assumption. rewrite (circ x y l) at 1. reflexivity.
rewrite (circ x y l) at 1. reflexivity.
Save.

Lemma first_occurrence_filter:
   forall x y l l', filter x l = y::l' -> first_occurrence x l y.
Proof.
fix circ 3. intros. destruct l. simpl in H. inversion H. destruct (Obj_eq_dec o y).
rewrite e. constructor 1. simpl in H. destruct (keq_dec x o). subst. assumption.
assert (H0 := circ x y l l' H). apply first_occurrence_keq in H0.
assumption. simpl in H. constructor 2. destruct (keq_dec x o). inversion H.
elimtype False. apply n. assumption. assumption. destruct (keq_dec x o).
inversion H. elimtype False. apply n. assumption. apply circ with (l':=l').
assumption.
Save.

Lemma filter_first_occurrence :
   forall x y l, first_occurrence x l y -> exists l', filter x l = y::l'.
Proof.
fix circ 4. intros. destruct H. simpl. destruct (keq_dec x y).
exists (filter x l). reflexivity. elimtype False. apply n. assumption.
simpl. destruct (keq_dec x y). elimtype False. apply H. assumption.
apply circ. assumption.
Save.

Lemma first_occ_selsort : forall o l n, length l <= n -> first_occurrence o (selsorth (o::l) (S n)) o.
Proof.
intros. simpl. destruct (keq_dec o (kminl2 o l)). apply kminl2_first in k. rewrite <- k.
constructor. apply keq_refl. revert n o l n0 H. fix circ 1. intros. destruct n.
inversion H. destruct l. simpl. constructor. apply keq_refl. elimtype False.
simpl in H1. inversion H1. constructor. assumption. simpl.
destruct (keq_dec o (kminl2 o (remove (kminl2 o l) l))). apply kminl2_first in k.
rewrite <- k. constructor. apply keq_refl. apply circ. assumption. clear circ. clear n1.
revert n o l n0 H. fix circ 1. intros. destruct n. destruct l. simpl. constructor.
simpl. inversion H. destruct l. simpl. destruct (keq_dec o0 (kmin o o0)). simpl.
constructor. simpl in n0. unfold kmin in *|-*. elimtype False. destruct (kle_klt_dec o o0).
apply n0. apply keq_refl. apply n. apply keq_refl. inversion H1. inversion H1. destruct l.
simpl. apply le_O_n. simpl. destruct (keq_dec o0 (kmin o (kminl2 o0 l))). simpl in H.
apply le_S_n in H. assumption. simpl. apply le_n_S. 
cut (kmin o (kminl2 o0 l) = kminl2 (kmin o o0) l). intros. rewrite H0. apply circ.
rewrite <- H0. intro. simpl in n0. apply n1.
change (kmin o (kminl2 o0 l)) with (kminl2 o (o0::l)).
change (kmin o (kminl2 o0 l)) with (kminl2 o (o0::l)) in H1.
change (kmin o (kminl2 o0 l)) with (kminl2 o (o0::l)) in H0.
change (kmin o (kminl2 o0 l)) with (kminl2 o (o0::l)) in n1.
change (kmin o (kminl2 o0 l)) with (kminl2 o (o0::l)) in n0.
rewrite H0 in H1. apply kminl2_first in H1. rewrite H0. rewrite <- H1. rewrite H0 in n0.
rewrite <- H1 in n0. unfold kmin in n0|-*. destruct (kle_klt_dec o o0). elimtype False.
apply n0. apply keq_refl. apply keq_refl. simpl in H. apply (le_S_n (length l) (S n) H).
clear n1 H n0 circ n. revert l. intro. destruct l. simpl. reflexivity. simpl.
unfold kmin. destruct (kle_klt_dec o0 (kminl2 o1 l)). destruct (kle_klt_dec o o0).
destruct (kle_klt_dec o (kminl2 o1 l)). reflexivity. elimtype False. 
apply (kle_trans o o0 (kminl2 o1 l) k0) in k. apply (klt_antirefl o).
apply (kle_klt_trans o (kminl2 o1 l) o k) in k1. assumption. 
destruct (kle_klt_dec o0 (kminl2 o1 l)). reflexivity. elimtype False.
apply (kle_klt_trans o0 (kminl2 o1 l) o0 k) in k1. apply (klt_antirefl o0).
assumption. destruct (kle_klt_dec o (kminl2 o1 l)). destruct (kle_klt_dec o o0).
destruct (kle_klt_dec o (kminl2 o1 l)). reflexivity. elimtype False.
apply (kle_klt_trans o (kminl2 o1 l) o k0) in k2. apply (klt_antirefl o).
assumption. destruct (kle_klt_dec o0 (kminl2 o1 l)).
apply (kle_klt_trans o0 (kminl2 o1 l) o0 k2) in k. elimtype False. apply (klt_antirefl o0).
assumption. apply (klt_kle_trans o0 o (kminl2 o1 l) k1) in k0.
apply (klt_trans o0 (kminl2 o1 l) o0 k0) in k2. elimtype False. apply (klt_antirefl o0).
assumption. destruct (kle_klt_dec o o0). destruct (kle_klt_dec o (kminl2 o1 l)).
apply (kle_klt_trans o (kminl2 o1 l) o k2) in k0. elimtype False. apply (klt_antirefl o).
assumption. reflexivity. destruct (kle_klt_dec o0 (kminl2 o1 l)).
apply (kle_klt_trans o0 (kminl2 o1 l) o0 k2) in k. elimtype False. apply (klt_antirefl o0).
assumption. reflexivity.
Save.

Lemma kmin_assoc : forall a b c, kmin a (kmin b c) = kmin (kmin a b) c.
Proof.
intros. unfold kmin. destruct (kle_klt_dec b c). destruct (kle_klt_dec a b).
destruct (kle_klt_dec a c). reflexivity. elimtype False. apply (klt_kle_trans c a b k1) in k0.
apply (klt_kle_trans c b c k0) in k. apply (klt_antirefl c). assumption.
destruct (kle_klt_dec b c). reflexivity. apply (klt_kle_trans c b c k1) in k.
apply (klt_antirefl c) in k. destruct k. destruct (kle_klt_dec a c). destruct (kle_klt_dec a b).
destruct (kle_klt_dec a c). reflexivity. apply (klt_kle_trans c a c k2) in k0.
apply (klt_antirefl c) in k0. destruct k0. destruct (kle_klt_dec b c).
apply (klt_kle_trans c b c k) in k2. apply (klt_antirefl c) in k2. destruct k2.
apply (klt_kle_trans b a c k1) in k0. apply (klt_trans b c b k0) in k.
apply (klt_antirefl b) in k. destruct k. destruct (kle_klt_dec a b). destruct (kle_klt_dec a c).
apply (klt_kle_trans c a c k0) in k2. apply (klt_antirefl c) in k2. destruct k2. reflexivity.
destruct (kle_klt_dec b c). apply (klt_kle_trans c b c k) in k2. apply (klt_antirefl c) in k2.
destruct k2. reflexivity.
Save.

Lemma kmin_first : forall a b, a &= b -> kmin a b = a.
Proof.
intros. unfold kmin. destruct (kle_klt_dec a b). reflexivity. elimtype False.
apply (klt_not_keq b a k). apply keq_sym. assumption.
Save.

Lemma keq_kmin_kminl2 : forall a b l, a &= b -> kmin a (kminl2 b l) = kminl2 a l.
Proof.
intros. destruct l. unfold kmin. simpl. destruct (kle_klt_dec a b). reflexivity. elimtype False. 
apply (klt_not_keq b a k). apply keq_sym. assumption. simpl. rewrite kmin_assoc.
f_equal. apply kmin_first. assumption.
Save.

Lemma helper1 : forall a b l,
       ~ kminl2 a (b::l) &= a -> kminl2 a (b::l) = kminl2 b l.
Proof.
simpl. unfold kmin. intros a b l. destruct (kle_klt_dec a (kminl2 b l)).
intro. elimtype False. apply H. apply keq_refl. intro. reflexivity.
Save.

Lemma helper2 : forall a b l, 
         a &= kminl2 a l ->
         ~ b &= kminl2 b (a::l) ->
              remove (kminl2 b (a::l)) (a::l) = l.
Proof.
fix circ 3. simpl. unfold kmin. intros. destruct (kle_klt_dec b (kminl2 a l)).
elimtype False. apply H0. apply keq_refl. destruct (keq_dec a (kminl2 a l)).
reflexivity. destruct l. elimtype False. apply n. assumption. elimtype False.
apply n. assumption.
Save.

Lemma helper3 : forall a b l,
   ~ a &= kminl2 a (b::l) ->
   ~ b &= kminl2 b l ->
          remove (kminl2 a (b::l)) (b::l) = b :: remove (kminl2 b l) l.
Proof.
simpl. unfold kmin. intros. destruct (kle_klt_dec a (kminl2 b l)). elimtype False.
apply H. apply keq_refl. destruct (keq_dec b (kminl2 b l)).
elimtype False. apply H0. assumption. reflexivity.
Save.

Lemma helper4 : forall a l n, 
        ~ a &= kminl2 a l -> length l <= n -> length (a :: remove (kminl2 a l) l) <= n.
Proof.
fix circ 3. simpl. intros. destruct n. destruct l. elimtype False. apply H. simpl.
apply keq_refl. inversion H0. apply le_n_S. destruct l. elimtype False. apply H.
simpl. apply keq_refl. simpl. destruct (keq_dec o (kmin a (kminl2 o l))).
simpl in H0. apply le_S_n. assumption. assert (~ (kminl2 a (o::l)) &= a).
intro. apply H. apply keq_sym. assumption. apply (helper1 a o l) in H1.
simpl in H1. rewrite H1. apply (circ o l n). simpl in H. unfold kmin in H,H1,n0.
destruct (kle_klt_dec a (kminl2 o l)). elimtype False. apply H. apply keq_refl.
assumption. apply le_S_n. assumption. 
Save.

Lemma remove_selsorth : forall o l n, 
            length l <= n -> remove o (selsorth (o::l) (S n)) = selsorth l n.
Proof.
fix circ 3. intros. simpl. destruct n. destruct l. simpl. destruct (keq_dec o o).
reflexivity. elimtype False. apply n. apply keq_refl. simpl. 
destruct (keq_dec (kmin o (kminl2 o0 l)) o). reflexivity. inversion H.
destruct (keq_dec (kminl2 o l) o). destruct (keq_dec o (kminl2 o l)). reflexivity.
elimtype False. apply n0. apply keq_sym. assumption. destruct (keq_dec o (kminl2 o l)).
elimtype False. apply n0. apply keq_sym. assumption. simpl selsorth at 2. destruct l.
simpl in n1. elimtype False. apply n1. apply keq_refl. f_equal. apply helper1. assumption.
simpl selsorth at 2. destruct (keq_dec o0 (kminl2 o0 l)). rewrite <- (circ o l n).
f_equal. f_equal. f_equal. apply helper2. assumption. assumption. simpl in H.
apply (le_S_n (length l) n) in H. assumption. 
rewrite <- (circ o (o0::remove (kminl2 o0 l) l) n). f_equal. f_equal. f_equal. apply helper3.
assumption. assumption. apply helper4. assumption. simpl in H. 
apply (le_S_n (length l) n) in H. assumption.
Save.

Lemma remove_selsorth_gen : forall x y l n, 
            length l <= n -> x &= y ->
                 remove x (selsorth (y::l) (S n)) = selsorth l n.
Proof.
fix circ 4. intros. simpl. destruct n. destruct l. simpl. destruct (keq_dec y x).
reflexivity. elimtype False. apply n. apply (keq_sym x y H0). simpl. 
destruct (keq_dec (kmin y (kminl2 o l)) x). reflexivity. inversion H.
destruct (keq_dec y (kminl2 y l)). destruct (keq_dec (kminl2 y l) x). reflexivity.
elimtype False. apply n0. apply keq_sym. apply (keq_trans x y (kminl2 y l) H0 k). 
destruct (keq_dec (kminl2 y l) x).
elimtype False. apply n0. apply (keq_trans (kminl2 y l) x y k) in H0.
apply keq_sym. assumption. simpl selsorth at 2. destruct l.
simpl in n1. elimtype False. apply n1. apply keq_sym. 
assumption. f_equal. apply helper1. 
intro.
apply n1.
apply (keq_trans (kminl2 y (o::l)) y x H1 (keq_sym x y H0)).
simpl selsorth at 2. destruct (keq_dec o (kminl2 o l)). rewrite <- (circ x y l n).
f_equal. f_equal. f_equal. apply helper2. assumption. assumption. simpl in H.
apply (le_S_n (length l) n) in H. assumption. assumption. 
rewrite <- (circ x y (o::remove (kminl2 o l) l) n). f_equal. f_equal. f_equal. apply helper3.
assumption. assumption. apply helper4. assumption. simpl in H. 
apply (le_S_n (length l) n) in H. assumption. assumption.
Save.


Theorem selsort_stable_ind : forall l, stable_ind l (selsort l).
fix circ 1. destruct l. constructor. constructor. clear circ.  
apply first_occ_selsort. constructor. unfold selsort.  
rewrite remove_selsorth with (n:=length l). apply circ. constructor.
Save.

Lemma first_occurrence_dec :
   forall x y l, first_occurrence x l y \/ ~ first_occurrence x l y.
Proof.
fix circ 3. intros. destruct l. right. intro. inversion H.
destruct (keq_dec x o). destruct (obj_eq_dec o y). left.
rewrite e. constructor. rewrite e in k. assumption. right. intro.
apply n. inversion H. subst. reflexivity. subst. elimtype False.
apply H3. assumption. destruct (circ x y l). left. constructor.
assumption. assumption. right. intro. apply H. inversion H0.
subst. elimtype False. apply n. assumption. assumption.
Save.

Lemma first_occurrence_dec_gen:
  forall x l, {exists y, first_occurrence x l y} + 
                     {~ exists y, first_occurrence x l y}.
Proof.
fix circ 2. intros. destruct l. right. intro. inversion H. inversion H0.
destruct (keq_dec x o). left. exists o. constructor. assumption.
destruct (circ x l). left. destruct e. exists x0. constructor.
assumption. assumption. right. intro. apply n0. destruct H.
inversion H. subst. elimtype False. apply n. assumption. subst.
exists x0. assumption.
Save.

Lemma first_occurrence_remove_length :
  forall x y l, first_occurrence x l y -> length l = S (length (remove x l)).
Proof.
fix circ 3. intros. destruct l. inversion H. inversion H. simpl.
f_equal. destruct (keq_dec y x). reflexivity. elimtype False.
apply n. apply keq_sym. assumption. simpl. f_equal. 
destruct (keq_dec o x). reflexivity. subst. simpl. apply (circ x y l).
assumption.
Save.

Lemma first_occurrence_remove_singleton :
   forall x l, first_occurrence x l x -> remove x l = nil -> l = x::nil.
Proof.
intros. destruct H. simpl in H0. destruct (keq_dec y y).
subst. reflexivity. inversion H0. simpl in H0.
destruct (keq_dec y z). subst. inversion H1. inversion H0.
Save.

Lemma first_occurrence_append :
  forall x y l l1 l2, l = l1++l2 -> first_occurrence x l y ->
     first_occurrence x l1 y \/ 
        (forall z, ~ first_occurrence x l1 z) /\ first_occurrence x l2 y.
Proof.
fix circ 7. intros. destruct H0. destruct l1. right. split. 
intros. intro. inversion H1. simpl in H. rewrite <- H. 
constructor. assumption. inversion H. subst. left. constructor. 
assumption. destruct l1. simpl in H. right. split. intro. intro. 
inversion H2. rewrite <- H. constructor. assumption. assumption.
inversion H. assert (H00 := circ x z l l1 l2 H4 H1). subst.
destruct H00. left. constructor. assumption. assumption. destruct H2.
right. split. intro. intro. inversion H4. subst. apply H0. assumption.
subst. apply (H2 z0). assumption. assumption.
Save.

Lemma stable_f_nil :
  forall f, (forall l, stable_ind l (f l)) -> f nil = nil.
Proof.
intros. assert (H0:= H nil). inversion H0. reflexivity.
Save.

Lemma stable_f_singleton :
  forall f, (forall l, stable_ind l (f l)) ->
              forall x, f (x::nil) = x::nil.
Proof.
intros. assert (H0 := H (x::nil)). inversion H0. subst.
inversion H5. 
apply (first_occurrence_remove_singleton x (f (x::nil)) H3 (sym_eq H1)).
Save.

Lemma stable_ind_length :
  forall l l', stable_ind l l' -> length l = length l'.
Proof.
fix circ 1. intros. destruct l. inversion H. reflexivity.
destruct l'. inversion H. inversion H2. simpl. f_equal.
inversion_clear H. simpl in H1. destruct (keq_dec o0 o).
apply circ. assumption. 
assert (H2 := circ l (o0::remove o l') H1).
rewrite H2. clear circ l H1 H2. revert o o0 H0 n.
induction l'. intros. inversion H0. elimtype False.
apply n. rewrite H2. assumption. inversion H5.
intros. simpl. destruct (keq_dec a o). reflexivity.
f_equal. apply IHl'. inversion H0. subst. elimtype False.
apply n. assumption. assumption. assumption.
Save.

Lemma first_occurrence_first_eq :
  forall x y z l, x &= y -> 
        first_occurrence x (y::l) z -> y = z.
Proof.
intros. inversion_clear H0. reflexivity. elimtype False.
apply H1. assumption.
Save.

Lemma first_occurrence_remove:
  forall x y z l,
     ~ x &= y -> first_occurrence x (remove y l) z -> 
            first_occurrence x l z.
Proof.
fix circ 4. intros. destruct l. simpl in H0. inversion H0.
simpl in H0. destruct (keq_dec o y). constructor.
intro. apply H. apply (keq_trans x o y H1 k).
assumption. inversion H0. subst. constructor.
assumption. subst. constructor. assumption.
apply (circ x y z l H H6).
Save.

Lemma stable_first_occurrence :
  forall x y l l', stable_ind l l' ->
      first_occurrence x l y -> first_occurrence x l' y.
Proof.
fix circ 6. intros. destruct H0. inversion H. subst.
apply (keq_first_occurrence y x y l' (keq_sym x y H0) H3).
destruct l'. inversion H. inversion H4. inversion H.
subst. inversion H4. subst. simpl in H6. 
destruct (keq_dec y y). constructor. assumption.
apply (circ x z l l' H6 H1).
elimtype False. apply n. assumption. subst. simpl in H6.
destruct (keq_dec o y). elimtype False. apply H7.
apply (keq_sym o y k).
assert (H00 := circ x z l (o::remove y l') H6 H1).
inversion H00. subst. constructor. assumption.
subst. constructor. assumption.
apply first_occurrence_remove with (y:=y).
assumption. assumption.
Save.

Lemma stable_ind_comm_helper :
  forall l l' n, length l = n -> length l' = n -> 
                    stable_ind l l' -> stable_ind l' l.
Proof.
fix circ 3. intros. destruct n. destruct l. destruct l'. constructor.
inversion H0. inversion H. destruct l. inversion H. destruct l'.
inversion H0. inversion H1. subst. constructor. 
destruct (obj_eq_dec o0 o). rewrite e. constructor. apply (keq_refl).
constructor. inversion H4. elimtype False. apply n0. rewrite H5.
reflexivity. intro. apply H7. apply (keq_sym o0 o H10).
inversion H4. subst. elimtype False. apply n0. reflexivity.
subst. simpl in H6. destruct (keq_dec o0 o). elimtype False.
apply H7. apply (keq_sym o0 o k).
assert (stable_ind (o0::remove o l') l). apply circ with (n:=n).
inversion H. reflexivity. simpl. 
rewrite <- (first_occurrence_remove_length o o l').
inversion H0. reflexivity. assumption. assumption. inversion H2.
assumption. simpl in H6. destruct (keq_dec o0 o). simpl.
destruct (keq_dec o o0). apply circ with (n:=n). inversion H.
reflexivity. inversion H0. reflexivity. assumption. elimtype False.
apply n0. apply (keq_sym o0 o k). simpl. destruct (keq_dec o o0).
elimtype False. apply n0. apply (keq_sym o o0 k). 
apply circ with (n:=n). simpl.
rewrite <- (first_occurrence_remove_length o0 o0 l).
inversion H. reflexivity. assert (stable_ind (o0::remove o l') l).
apply circ with (n:=n). inversion H. reflexivity. simpl.
rewrite <- (first_occurrence_remove_length o o l').
inversion H0. reflexivity. inversion H4. subst. elimtype False.
apply n1. assumption. assumption. assumption. inversion H2.
assumption. inversion H0. reflexivity. constructor. inversion H4.
subst. elimtype False. apply n1. assumption. assumption.
assert (stable_ind (o0::remove o l') l). apply circ with (n:=n).
inversion H. reflexivity. simpl.
rewrite <- (first_occurrence_remove_length o o l').
inversion H0. reflexivity. inversion H4. subst. elimtype False.
apply n1. assumption. assumption. assumption. inversion H2.
subst. assert (circ0 := fun (l l':list Obj) => circ l l' n).
destruct n. simpl in H. simpl in H0. inversion H. inversion H0.
destruct l. destruct l'. constructor. inversion H8. inversion H5.
apply circ with (n := n).
assert (H00:=first_occurrence_remove_length o o l').
inversion H0. rewrite H5 in H00. cut (first_occurrence o l' o).
intro. assert (H01 := H00 H3). inversion H01. reflexivity.
assert (stable_ind (o0::remove o l') l). apply circ0.
inversion H. reflexivity. simpl. rewrite H00. reflexivity.
inversion H4. subst. elimtype False. apply n1. assumption.
assumption. assumption. inversion H4. subst. elimtype False.
apply n1. assumption. assumption.
assert (H00:=first_occurrence_remove_length o0 o0 l).
inversion H. rewrite H5 in H00. assert (H01 := H00 H7).
inversion H01. reflexivity. assumption.
Save.

Lemma stable_ind_comm:
  forall l l', stable_ind l l' -> stable_ind l' l.
Proof.
intros.
apply stable_ind_comm_helper with (n:=length l).
reflexivity. symmetry. apply stable_ind_length.
assumption. assumption.
Save.

Lemma stable_first_occurrence_converse :
 forall x y l l', stable_ind l l' ->
   first_occurrence x l' y -> first_occurrence x l y.
Proof.
intros.
assert (H00 := stable_ind_comm l l' H).
apply stable_first_occurrence with (l:=l').
assumption. assumption.
Save.

Lemma stable_ind_f_arg_nil :
  forall f, (forall l, stable_ind l (f l)) ->
     forall l', f l' = nil -> l' = nil.
Proof.
intros. destruct l'. reflexivity. assert (H1 := H (o::l')).
rewrite H0 in H1. assert (H2 := stable_ind_length (o::l') nil H1).
simpl in H2. inversion H2.
Save.

Lemma remove_equal_helper :
  forall l, (forall x, remove x l = nil) -> l = nil.
Proof.
intros. destruct l. reflexivity. assert (H1 := H obj2).
assert (H2 := H obj3). simpl in H1. simpl in H2.
destruct (keq_dec o obj2). destruct (keq_dec o obj3).
elimtype False. apply Obj_keq_doubleton.
apply (keq_trans obj2 o obj3 (keq_sym o obj2 k) k0).
inversion H2. inversion H1.
Save.

Lemma remove_equal_helper3 :
  forall x y l l', x <> y -> 
      (forall z, remove z (x::l) = remove z (y::l')) -> False.
Proof.
intros. destruct (keq_dec x y). assert (H00 := Obj_keq_choice x).
destruct H00. assert (H00 := H0 x0). simpl in H00. 
destruct (keq_dec x x0). apply H1. assumption. destruct (keq_dec y x0).
apply n. apply (keq_trans x y x0 k k0). inversion H00. apply H.
assumption. assert (H00 := Obj_keq_choice2 x y n). destruct H00.
destruct H1. assert (H00 := H0 x0). simpl in H00.
destruct (keq_dec x x0). apply H1. apply (keq_sym x x0 k).
destruct (keq_dec y x0). apply H2. apply (keq_sym y x0 k).
inversion H00. apply H. assumption.
Save.

Lemma remove_equal_helper2 :
  forall x y l l', 
       (forall z, remove z (x::l) = remove z (y::l')) ->
             x = y.
Proof.
intros. destruct (obj_eq_dec x y). assumption.
elimtype False. apply (remove_equal_helper3 x y l l' n H).
Save.

Lemma remove_equal :
  forall l l' n, length l = n -> 
       (forall x, remove x l = remove x l') -> l = l'.
Proof.
fix circ 3. intros l l' n H00 H. assert (H2 := H obj2).
assert (H3 := H obj3). destruct n. destruct l. destruct l'.
reflexivity. 
assert (o::l' = nil). apply (remove_equal_helper (o::l')).
intro. rewrite <- H. reflexivity. inversion H0. destruct l'.
apply (remove_equal_helper (o::l)). intro. rewrite H. reflexivity.
inversion H00. destruct l. inversion H00. destruct l'.
apply (remove_equal_helper (o::l)). assumption. inversion H00.
clear H00. assert (H00 := remove_equal_helper2 o o0 l l' H).
rewrite H00. f_equal. apply (circ l l' n H1). rewrite H00 in H.
intro. assert (H01 := H x). simpl in H01. destruct (keq_dec o0 x).
rewrite H01. reflexivity. inversion H01. reflexivity.
Save.

Inductive fst_occ_dcmp : 
            Obj -> list Obj -> Obj -> list Obj -> list Obj -> Prop 
          :=
  fst_occ_dcmp_hd : 
          forall x l y, x &= y -> fst_occ_dcmp x (y::l) y nil l
| fst_occ_dcmp_tl : 
          forall x y l z l1 l2, 
              ~ x &= y -> fst_occ_dcmp x l z l1 l2 ->
                                 fst_occ_dcmp x (y::l) z (y::l1) l2.

Lemma fst_occ_dcmp_append :
  forall x l y l1 l2, fst_occ_dcmp x l y l1 l2 -> l = l1 ++ y::l2.
Proof.
fix circ 2. intros. destruct l. inversion H. inversion H. subst.
simpl. reflexivity. subst. simpl. f_equal. inversion H. subst.
apply (circ x l y l3 l2 H9).
Save.

Lemma first_occurrence_fst_occ_dcmp :
  forall x l y, first_occurrence x l y -> 
                     exists l1, exists l2, fst_occ_dcmp x l y l1 l2.
Proof.
fix circ 2. intros. destruct l. inversion H. inversion H. subst.
exists nil. exists l. constructor. assumption. subst.
assert (H00 := circ x l y H5). destruct H00. destruct H0.
exists (o::x0). exists x1. constructor. assumption. assumption.
Save.

Lemma fst_occ_dcmp_first_occurrence:
  forall x l y l1 l2,
     fst_occ_dcmp x l y l1 l2 -> first_occurrence x l y.
Proof.
fix circ 2. intros. destruct l. inversion H. inversion H. subst.
constructor. assumption. subst. constructor. assumption.
apply (circ x l y l3 l2 H7).
Save.

Lemma fst_occ_dcmp_remove :
  forall x l y l1 l2,
      fst_occ_dcmp x l y l1 l2 -> remove x l = l1 ++ l2.
Proof.
fix circ 6. intros. destruct H. simpl. destruct (keq_dec y x).
reflexivity. elimtype False. apply n. exact (keq_sym x y H).
simpl. destruct (keq_dec y x). elimtype False. apply H.
exact (keq_sym y x k). f_equal. apply circ with (y:=z).
assumption. 
Save.

Lemma fst_occ_dcmp_length :
  forall x l y l1 l2, 
       fst_occ_dcmp x l y l1 l2 -> length l = S (length (l1++l2)).
Proof.
fix circ 6. intros. destruct H. reflexivity. simpl. f_equal.
apply (circ x l z l1 l2 H0).
Save.

Lemma keq_fst_occ_dcmp :
  forall x y l z l1 l2, x &= y ->
    fst_occ_dcmp x l z l1 l2 -> fst_occ_dcmp y l z l1 l2.
Proof.
fix circ 8. intros. destruct H0. constructor. 
apply (keq_trans y x y0 (keq_sym x y H) H0).
constructor. intro. apply H0.
apply (keq_trans x y y0 H H2).
apply (circ x y l z l1 l2 H H1).
Save.

Lemma fst_occ_dcmp_prefix:
  forall x y l l1 l2 l',
    fst_occ_dcmp x l y l1 l2 -> fst_occ_dcmp x (l++l') y l1 (l2++l').
Proof.
fix circ 7. intros. destruct H. simpl. constructor. assumption.
simpl. constructor. assumption. apply circ with (y:=z). assumption.
Save.

Lemma first_occurrence_neq :
  forall x y z l1 l2, 
    ~ x &= z -> first_occurrence x (l1++z::l2) y -> 
                         first_occurrence x (l1++l2) y.
Proof.
fix circ 4. intros. destruct l1. inversion H0. subst. elimtype False.
apply H. assumption. subst. simpl. assumption. simpl in H0.
inversion H0. simpl. constructor. assumption. simpl. subst. constructor.
assumption. apply circ with (z:=z). assumption. assumption.
Save.

Lemma not_first_occurrence :
  forall x y l1 l2 l' l'',
    ~ (exists z, first_occurrence x l1 z) -> 
        fst_occ_dcmp x l2 y l' l'' ->
          fst_occ_dcmp x (l1++l2) y (l1++l') l''.
Proof.
induction l1. simpl. intros. assumption. simpl. intros. constructor.
intro. apply H. exists a. constructor. assumption. apply IHl1.
intro. apply H. destruct H1. destruct (keq_dec x a). exists a.
constructor. assumption. exists x0. constructor. assumption.
assumption. assumption.
Save.

Lemma fst_occ_dcmp_not_first_occurrence:
  forall x y l l1 l2, 
    fst_occ_dcmp x l y l1 l2 -> forall z, ~ first_occurrence x l1 z.
Proof.
fix circ 4. intros. intro. destruct l1. inversion H0. inversion H.
inversion H0. subst. apply H6. assumption. subst. inversion H0.
subst. apply H6. assumption. subst. 
assert (H00 := circ x y l0 l1 l2 H8).
apply (H00 z). assumption.
Save.

Lemma fst_occ_dcmp_pattern_match:
  forall x y l1 l2 l1' l2',
  ~ (exists z, first_occurrence x l1 z) -> 
  ~ (exists z, first_occurrence x l1' z) ->
     x &= y -> l1++y::l2 = l1'++y::l2' -> l1=l1' /\ l2=l2'.
Proof.
fix circ 3. intros. destruct l1. destruct l1'. split. reflexivity.
inversion H2. reflexivity. inversion H2. elimtype False. apply H0.
exists o. constructor. subst. assumption. destruct l1'.
elimtype False. apply H. inversion H2. exists y. constructor.
assumption. inversion H2. subst. split. f_equal.
assert (~ exists z, first_occurrence x l1' z).
intro. apply H0. destruct (keq_dec x o0). exists o0.
constructor. assumption. destruct H3. exists x0. constructor.
assumption. assumption. 
assert (~ exists z, first_occurrence x l1 z).
intro. apply H. destruct (keq_dec x o0). exists o0. constructor.
assumption. destruct H4. exists x0. constructor. assumption.
assumption. assert (H00 := circ x y l1 l2 l1' l2' H4 H3 H1 H5).
destruct H00. assumption. 
assert (~ exists z, first_occurrence x l1' z).
intro. apply H0. destruct (keq_dec x o0). exists o0.
constructor. assumption. destruct H3. exists x0. constructor.
assumption. assumption. 
assert (~ exists z, first_occurrence x l1 z).
intro. apply H. destruct (keq_dec x o0). exists o0.
constructor. assumption. destruct H4. exists x0.
constructor. assumption. assumption.
assert (H00 := circ x y l1 l2 l1' l2' H4 H3 H1 H5).
destruct H00. assumption.
Save.

Lemma fst_occ_dcmp_keq :
  forall x y l l1 l2, fst_occ_dcmp x l y l1 l2 -> x &= y.
Proof.
fix circ 6. intros. destruct H. assumption.
apply (circ x z l l1 l2 H0).
Save.

Lemma stable_ind_fst_occ_dcmp_helper:
  forall y z x0 x5 x3,
    fst_occ_dcmp y (x0++z::x5++y::x3) y (x0++z::x5) x3 ->
      remove y (x0++x5++y::x3) = x0 ++ x5 ++ x3.
Proof.
induction x0. simpl. intros. inversion H. subst.
apply fst_occ_dcmp_remove with (y:=y).
assumption. intros. inversion H. subst. simpl.
destruct (keq_dec a y). elimtype False.
apply H5. apply (keq_sym a y k). f_equal.
apply IHx0. assumption.
Save.

Lemma not_first_occurrence_head:
  forall x a l, ~ x &= a ->
    (forall z, ~ first_occurrence x l z) -> 
       forall z, ~ first_occurrence x (a::l) z.
destruct l. intros. intro. inversion H1. subst.
apply H. assumption. subst. inversion H7.
intros. intro. inversion H1. subst. apply H.
assumption. subst. clear H1. clear H5. apply (H0 z).
assumption.
Save.

Lemma not_first_occurrence_tail:
  forall x a l,
    (forall z, ~ first_occurrence x (a::l) z) -> 
       forall z, ~ first_occurrence x l z.
Proof.
intros. intro. destruct (keq_dec x a). apply (H a).
constructor. assumption. apply (H z). constructor.
assumption. assumption. 
Save.

Lemma not_first_occurrence_first_occurrence:
  forall x y l1 l2,
    x &= y -> (forall z, ~ first_occurrence x l1 z) -> 
        first_occurrence x (l1++y::l2) y.
Proof.
induction l1. simpl. intros. constructor. assumption. simpl.
intros. destruct (keq_dec x a). elimtype False. apply (H0 a).
constructor. assumption. constructor. assumption. apply IHl1.
assumption. apply (not_first_occurrence_tail x a l1 H0).
Save.

Lemma not_first_occurrence_append:
  forall x l1 l2,
    (forall z, ~ first_occurrence x l1 z) -> 
         (forall z, ~ first_occurrence x l2 z) -> 
              (forall z, ~ first_occurrence x (l1++l2) z).
Proof.
induction l1. intros. simpl. exact (H0 z). intros.
intro. inversion H1. subst. clear H1. apply (H z).
constructor. assumption. subst. clear H1.
assert (H00 := not_first_occurrence_tail x a l1 H).
apply (IHl1 l2 H00 H0 z). assumption.
Save.

Lemma stable_ind_fst_occ_dcmp_helper2:
  forall y z x2 x4 x1,
    fst_occ_dcmp y (x2 ++ y :: x4 ++ z :: x1) y x2 (x4 ++ z :: x1) ->
      remove y (x2 ++ y :: x4 ++ x1) = (x2 ++ x4) ++ x1.
Proof.
induction x2. simpl. intros. destruct (keq_dec y y). reflexivity.
elimtype False. apply n. apply keq_refl. simpl. intros.
inversion H. subst. destruct (keq_dec a y). elimtype False.
apply H5. apply (keq_sym a y k). f_equal. apply IHx2. assumption.
Save.

Lemma stable_ind_fst_occ_dcmp :
  forall x l y l1 l2 l',
     stable_ind l l' -> fst_occ_dcmp x l y l1 l2 ->
       exists l1', exists l2',
         fst_occ_dcmp x l' y l1' l2' /\ stable_ind (l1++l2) (l1'++l2').
Proof.
fix circ 8. intros. destruct H0. inversion H. subst.
apply (keq_first_occurrence y x y l' (keq_sym x y H0)) in H3.
apply first_occurrence_fst_occ_dcmp in H3. destruct H3.
destruct H1. exists x0. exists x1. split. assumption.
simpl. apply (keq_fst_occ_dcmp x y l' y x0 x1 H0) in H1.
rewrite (fst_occ_dcmp_remove y l' y x0 x1 H1) in H5.
assumption. inversion H. subst.
assert (H00 := circ x l z l1 l2 (remove y l') H6 H1).
destruct H00. destruct H2. destruct H2. 
apply first_occurrence_fst_occ_dcmp in H4.
destruct H4. destruct H4. assert (H00 := H4).
apply fst_occ_dcmp_remove in H4. rewrite H4 in H6.
rewrite H4 in H2. assert (H01 := H00).
apply fst_occ_dcmp_append in H00. rewrite H00.
assert (H02 := fst_occ_dcmp_first_occurrence x (x2++x3) z x0 x1 H2).
apply (first_occurrence_append x z (x2++x3) x2 x3) in H02.
destruct H02. apply first_occurrence_fst_occ_dcmp in H5.
destruct H5. destruct H5. exists x4. exists (x5++y::x3).
split. apply fst_occ_dcmp_prefix. assumption. simpl.
constructor. apply fst_occ_dcmp_append in H5. 
rewrite H00 in H01. rewrite H5 in H01. 
rewrite app_ass in H01. simpl in H01.
apply fst_occ_dcmp_first_occurrence in H01.
apply first_occurrence_neq with (z:=z).
apply fst_occ_dcmp_first_occurrence in H1.
apply first_occurrence_keq in H1.
intro. apply H0.
apply (keq_trans x z y H1 (keq_sym y z H7)).
assumption. clear circ. assert (H20 := H2).
apply fst_occ_dcmp_append in H20.
assert (H10 := H1). apply fst_occ_dcmp_append in H10.
cut (remove y (x4++x5++y::x3) = x0++x1).
intros. rewrite H7. assumption. clear H. clear H6. clear H3.
assert (H50 := H5). apply fst_occ_dcmp_append in H50.
rewrite H50 in H20. rewrite app_ass in H20. simpl in H20.
assert (H21 := fst_occ_dcmp_not_first_occurrence x z (x2++x3) x0 x1 H2).
assert (H51 := fst_occ_dcmp_not_first_occurrence x z x2 x4 x5 H5).
assert (x4=x0 /\ x5++x3=x1).
apply fst_occ_dcmp_pattern_match with (y:=z) (x:=x).
intro. destruct H. apply (H51 x6). assumption. intro. destruct H.
apply (H21 x6). assumption. apply fst_occ_dcmp_keq in H1.
assumption. assumption. destruct H. subst. rewrite app_ass in H01.
simpl in H01. apply stable_ind_fst_occ_dcmp_helper with (z:=z).
assumption. destruct H5. apply first_occurrence_fst_occ_dcmp in H7.
destruct H7. destruct H7. exists (x2++y::x4). exists x5. split.
apply not_first_occurrence. intro. destruct H8. apply (H5 x6).
assumption. constructor. assumption. assumption. simpl.
rewrite (app_ass x2 (y::x4) x5). simpl. constructor. 
apply not_first_occurrence_first_occurrence. apply keq_refl.
apply fst_occ_dcmp_not_first_occurrence with (y:=y) (l:=l') (l2:=x3).
assumption. clear circ. assert (H20 := H2). 
apply fst_occ_dcmp_append in H20. assert (H10 := H1).
apply fst_occ_dcmp_append in H10. 
cut (remove y (x2++y::x4++x5) = x0++x1).
intros. rewrite H8. assumption. clear H. clear H6. clear H3.
assert (H70 := H7). apply fst_occ_dcmp_append in H70.
rewrite H70 in H20.
assert (H21 := fst_occ_dcmp_not_first_occurrence x z (x2++x3) x0 x1 H2).
assert (H71 := fst_occ_dcmp_not_first_occurrence x z x3 x4 x5 H7).
assert (x2++x4=x0 /\ x5=x1). 
apply fst_occ_dcmp_pattern_match with (y:=z) (x:=x).
cut (forall z, ~ first_occurrence x (x2++x4) z). intro. intro.
destruct H3. apply (H x6). assumption. apply not_first_occurrence_append.
assumption. assumption. intro. destruct H. apply (H21 x6). assumption.
apply fst_occ_dcmp_keq in H2. assumption. rewrite app_ass. assumption.
destruct H. subst. apply stable_ind_fst_occ_dcmp_helper2 with (z:=z).
assumption. reflexivity.
Save.

Lemma fst_occ_dcmp_filter :
  forall x l y l1 l2, 
    fst_occ_dcmp x l y l1 l2 -> filter x l = y::(filter x l2).
Proof.
fix circ 6. intros. destruct H. simpl. destruct (keq_dec x y).
reflexivity. elimtype False. apply n. assumption. simpl.
destruct (keq_dec x y). elimtype False. apply H. assumption.
assert (H00 := circ x l z l1 l2 H0). assumption.
Save.

Lemma fst_occ_dcmp_filter2 :
  forall x l y l1 l2, 
    fst_occ_dcmp x l y l1 l2 -> filter x l = y::(filter x (l1++l2)).
Proof.
fix circ 6. intros. destruct H. simpl. destruct (keq_dec x y).
reflexivity. elimtype False. apply n. assumption. simpl.
destruct (keq_dec x y). elimtype False. apply H. assumption.
apply circ. assumption.
Save.

Lemma not_keq_not_first_occurrence_filter :
  forall x y z l, ~ y &= x -> ~ first_occurrence x (filter y l) z.
Proof.
intros. intro. apply H. clear H. revert l x y z H0. fix circ 1.
intros. destruct l. inversion H0. simpl in H0. destruct (keq_dec y o).
inversion H0. subst. apply (keq_trans y z x k (keq_sym x z H4)).
subst. apply circ in H5. assumption. apply circ in H0. assumption.
Save.

Lemma not_first_occurrence_remove :
  forall x l, (forall y, ~ first_occurrence x l y) -> remove x l = l.
Proof.
fix circ 2. intros. destruct l. reflexivity. simpl. destruct (keq_dec o x).
elimtype False. apply (H o). constructor. apply (keq_sym o x k). f_equal.
apply circ. intros. intro. apply (H y). constructor. intro. apply n.
apply (keq_sym x o H1). assumption.
Save.

Lemma stable_ind_stable:
 forall l l', stable_ind l l' -> stable l l'.
Proof.
unfold stable. fix circ 3. intros. destruct H. reflexivity. 
assert (H000 := circ l (remove x0 l') H0 x). simpl.
destruct (keq_dec x x0). rewrite H000. assert (H01 := H).
apply first_occurrence_fst_occ_dcmp in H01.
destruct H01. destruct H1. assert (H01 := H1).
apply fst_occ_dcmp_remove in H1. rewrite H1.
apply (keq_fst_occ_dcmp x0 x l' x0 x1 x2 (keq_sym x x0 k)) in H01.
apply fst_occ_dcmp_filter2 in H01. rewrite H01. reflexivity.
rewrite H000. assert (H01 := H). 
apply first_occurrence_fst_occ_dcmp in H01. destruct H01.
destruct H1. rewrite filter_remove.
assert (H00 := fun z => not_keq_not_first_occurrence_filter x0 x z l' n).
apply not_first_occurrence_remove in H00. assumption.
Save.


Theorem selsort_stable : forall l, stable l (selsort l).
Proof.
intros. apply stable_ind_stable. apply selsort_stable_ind.
Save.

Fixpoint kinsert x l :=
  match l with
     nil => x::nil
  |  y::l' => if (klt_kle_dec y x) then y::(kinsert x l') else x::y::l'
  end.

Fixpoint insertion_sort l :=
  match l with
     nil => nil
  |  x::l' => kinsert x (insertion_sort l')
 end.

Lemma sorted_kminl2_tail :
  forall l x, sorted (x::l) -> kminl2 x l = x.
Proof.
induction l. simpl. reflexivity. intros. inversion H. subst.
apply IHl in H4. simpl. unfold kmin. 
destruct (kle_klt_dec x (kminl2 a l)). reflexivity.
rewrite H4 in k. elimtype False.
apply (klt_antirefl x (kle_klt_trans x a x H2 k)).
Save.

Theorem insertion_sort_correct:
  forall l, sorted (insertion_sort l).
Proof.
induction l. constructor. simpl. revert IHl. 
generalize (insertion_sort l). induction l0.
intro. constructor. intro. inversion IHl. subst.
simpl. destruct (klt_kle_dec a0 a). constructor.
unfold kle. left. assumption. constructor. 
constructor. assumption. constructor. subst.
simpl. destruct (klt_kle_dec a0 a). 
destruct (klt_kle_dec y a). constructor.
assumption. assert (H0 := IHl0 H2). simpl in H0.
destruct (klt_kle_dec y a). assumption. inversion H0.
subst. elimtype False.
apply (klt_antirefl y (klt_kle_trans y a y k0 k1)).
constructor. unfold kle. left. assumption. constructor.
assumption. inversion IHl. assumption. constructor.
assumption. assumption.
Save.

Lemma first_occurrence_kinsert_insertion_sort :
  forall l a, first_occurrence a (kinsert a l) a.
Proof.
induction l. constructor. apply keq_refl. intro. simpl.
destruct (klt_kle_dec a a0). constructor. intro.
apply keq_sym in H. apply (klt_not_keq a a0 k H).
apply IHl. constructor. apply keq_refl.
Save.

Lemma remove_kinsert :
  forall l a, remove a (kinsert a l) = l.
Proof.
induction l.
simpl.
intro.
destruct (keq_dec a a).
reflexivity.
elimtype False.
apply n.
apply keq_refl.
intro.
simpl.
destruct (klt_kle_dec a a0).
simpl.
destruct (keq_dec a a0).
elimtype False.
apply (klt_not_keq a a0 k k0).
f_equal.
apply IHl.
simpl.
destruct (keq_dec a0 a0).
reflexivity.
elimtype False.
apply n.
apply keq_refl.
Save.

Lemma stable_ind_insertion_sort:
  forall l, stable_ind l (insertion_sort l).
Proof.
induction l.
constructor.
simpl.
constructor.
apply first_occurrence_kinsert_insertion_sort.
rewrite remove_kinsert.
assumption.
Save.

Theorem stable_insertion_sort :
  forall l, stable l (insertion_sort l).
Proof.
intro.
apply stable_ind_stable.
apply stable_ind_insertion_sort.
Save.

Fixpoint partition x l := 
  match l with
    nil => (nil,nil)
  | y::l' => let (ll,lh) := partition x l'
             in if (klt_kle_dec y x) then (y::ll,lh)
                                     else (ll,y::lh)
  end.

Fixpoint qsorth l n {struct n} :=
  match n with
  | 0 => nil
  | S n' =>
     match l with
     | nil => nil
     | x::l' => let (ll,lh) := partition x l'
             in (qsorth ll n')++x::(qsorth lh n')
     end
  end.


Definition qsort l := qsorth l (length l).

Fixpoint kmaxl a l :=
  match l with
  | nil => a
  | x::l' => if (klt_kle_dec a x) then kmaxl x l' else kmaxl a l'
  end.

Lemma sorted_append:
  forall a l1 l2, sorted (l1++(a::nil)) -> sorted (a::l2) -> sorted (l1++a::l2).
Proof.
fix circ 2. intros. destruct l1. assumption. simpl. simpl in H.
assert (IH := circ a l1 l2). destruct l1. simpl. simpl in H.
inversion H. subst. constructor. assumption. assumption.
simpl. constructor. inversion H. subst. assumption. apply IH.
simpl. inversion H. assumption. assumption.
Save.

Lemma length_fst_partition:
  forall n o l, length l <= n -> length (fst (partition o l)) <= n.
Proof.
fix circ 1. intros. destruct n. inversion H. destruct l.
simpl. constructor. inversion H1. destruct l. simpl.
apply le_O_n. simpl in H. apply le_S_n in H. simpl.
rewrite (surjective_pairing (partition o l)).
destruct (klt_kle_dec o0 o). simpl. apply le_n_S. apply circ.
assumption. simpl. constructor. apply circ. assumption.
Save.

Lemma kmaxl_head_kle :
  forall a b l, kmaxl a l = b -> a &<= b.
Proof.
fix circ 3. intros. destruct l. simpl in H.
subst. unfold kle. right. apply keq_refl.
simpl in H. destruct (klt_kle_dec a o).
assert (IH := circ o b l H).
unfold kle. left. apply klt_kle_trans with (y:=o).
assumption. assumption. apply (circ a b l). assumption.
Save.

Lemma sorted_suffix :
  forall a l, kmaxl a l = a -> sorted l -> sorted (l++a::nil).
Proof.
fix circ 2. intros. destruct l. constructor. assert (IH := circ a l).
destruct l. simpl. constructor. simpl in H. destruct (klt_kle_dec a o).
unfold kle. left. subst. assumption. assumption. 
constructor. simpl. constructor. inversion H0. assumption. apply IH.
clear IH. inversion H0. clear x y H1 H2 H4.
change (kmaxl a (o::o0::l)) with 
  (if klt_kle_dec a o then kmaxl o (o0::l) else kmaxl a (o0::l)) in H. 
destruct (klt_kle_dec a o). apply kmaxl_head_kle in H.
destruct (klt_antirefl a (klt_kle_trans a o a k H)).
assumption.  inversion H0. assumption.
Save.

Lemma kmaxl_fst_partition:
  forall o l, kmaxl o (fst (partition o l)) = o.
Proof.
fix circ 2. intros. destruct l. reflexivity. simpl.
rewrite (surjective_pairing (partition o l)).
destruct (klt_kle_dec o0 o). simpl. destruct (klt_kle_dec o o0).
apply (klt_trans o o0 o k0) in k.
apply (klt_antirefl o) in k. destruct k. apply circ. simpl. apply circ.
Save.

Lemma length_snd_partition:
  forall n o l, length l <= n -> length (snd (partition o l)) <= n.
Proof.
fix circ 1. intros. destruct n. destruct l. constructor. inversion H.
destruct l. constructor. apply circ. inversion H. assumption. simpl in H.
apply le_S_n in H. simpl. rewrite (surjective_pairing (partition o l)).
destruct (klt_kle_dec o0 o). simpl. constructor. apply circ.
assumption. simpl. apply le_n_S. apply circ. apply H.
Save.

Lemma kminl2_head :
  forall a o l, kminl2 a (o::l) = a -> a &<= o.
Proof.
intros. destruct l. simpl in H. unfold kmin in H.
destruct (kle_klt_dec a o). assumption. subst.
unfold kle. left. assumption. simpl in H.
unfold kmin in H. destruct (kle_klt_dec o (kminl2 o0 l)).
destruct (kle_klt_dec a o). assumption. subst. unfold kle.
right. apply keq_refl. destruct (kle_klt_dec a (kminl2 o0 l)).
apply (kle_klt_trans a (kminl2 o0 l) o k0) in k.
unfold kle. left. assumption. rewrite H in k0. elimtype False.
apply (klt_antirefl a k0).
Save.

Lemma sorted_head :
  forall a l, kminl2 a l = a -> sorted l -> sorted (a::l).
Proof.
intros. destruct l. constructor. constructor. apply kminl2_head with (l:=l).
assumption. assumption.
Save.

Lemma kminl_snd_partition:
  forall o l, kminl2 o (snd (partition o l)) = o.
Proof.
fix circ 2. intros. destruct l. reflexivity. simpl.
rewrite (surjective_pairing (partition o l)).
destruct (klt_kle_dec o0 o). simpl. apply circ. simpl.
unfold kmin.
destruct (kle_klt_dec o (kminl2 o0 (snd (partition o l)))).
reflexivity.
apply kle_kminl2 with (l:= snd (partition o l)) in k.
apply (kle_klt_trans (kminl2 o (snd (partition o l))) 
           (kminl2 o0 (snd (partition o l))) o k) in k0.
rewrite (circ o l) in k0. apply (klt_antirefl o) in k0.
destruct k0.
Save.

Lemma kmaxl_kmaxl_left :
  forall a b l1 l2, a &< b ->
       kmaxl a ((kmaxl b l1)::l2) = kmaxl b ((kmaxl b l1)::l2).
Proof.
fix circ 3. intros. destruct l1. simpl.
destruct (klt_kle_dec b b). destruct (klt_antirefl b k).
destruct (klt_kle_dec a b). reflexivity.
destruct (klt_antirefl a (klt_kle_trans a b a H k0)).
change (kmaxl b (o::l1)) with (if klt_kle_dec b o then kmaxl o l1 else kmaxl b l1).
destruct (klt_kle_dec b o). rewrite (circ a o l1). rewrite (circ b o l1).
reflexivity. assumption. apply klt_trans with (b:=b).
assumption. assumption. apply circ. assumption.
Save.

Lemma kmaxl_kmaxl_right :
  forall a b l1 l2, b &<= a ->
       kmaxl a (l1++(kmaxl b l2)::nil) = kmaxl a (l1++(kmaxl a l2)::nil).
Proof.
fix circ 3. intros. destruct l1. simpl. 
destruct (klt_kle_dec a (kmaxl b l2)).
destruct (klt_kle_dec a (kmaxl a l2)).
clear circ. revert a b H k k0.
induction l2. intros. simpl in k0.
destruct (klt_antirefl a k0). simpl.
intros. destruct (klt_kle_dec b a).
destruct (klt_kle_dec a0 a).
reflexivity. apply IHl2. assumption. assumption. assumption.
destruct (klt_kle_dec a0 a). symmetry. apply IHl2. assumption.
apply kle_klt_trans with (y:=a0). assumption. assumption.
apply kle_klt_trans with (y:=a0). assumption. assumption.
apply IHl2. assumption. assumption. assumption.
clear circ. revert a b H k k0. induction l2. simpl.
intros. destruct (klt_antirefl a (klt_kle_trans a b a k H)).
simpl. intros. destruct (klt_kle_dec b a). 
destruct (klt_kle_dec a0 a).
destruct (klt_antirefl a0 (klt_kle_trans a0 (kmaxl a l2) a0 k k0)).
apply IHl2. assumption. assumption. assumption.
destruct (klt_kle_dec a0 a). elimtype False. apply (klt_antirefl a0).
apply klt_kle_trans with (y:=a). assumption. apply kle_trans with (y:=b).
assumption. assumption. apply IHl2. assumption. assumption. assumption. 
destruct (klt_kle_dec a (kmaxl a l2)). clear circ. revert a b H k k0.
induction l2. reflexivity. simpl. intros. destruct (klt_kle_dec b a).
destruct (klt_kle_dec a0 a).
destruct (klt_antirefl a0 (klt_kle_trans a0 (kmaxl a l2) a0 k0 k)).
apply IHl2 with (b:=a). assumption. assumption. assumption.
destruct (klt_kle_dec a0 a). elimtype False. apply (klt_antirefl a0).
apply klt_kle_trans with (y:=a). assumption. apply kle_trans with (y:=b).
assumption. assumption. apply IHl2 with (b:=b). assumption. assumption.
assumption. reflexivity. simpl. destruct (klt_kle_dec a o).
rewrite (circ o b l1 l2). rewrite (circ o a l1 l2). reflexivity.
unfold kle. left. assumption. unfold kle. left. 
apply kle_klt_trans with (y:=a). assumption. assumption.
apply circ. assumption.
Save.

Lemma kmaxl_append : 
 forall a l1 l2, kmaxl a (l1++l2) = kmaxl a ((kmaxl a l1)::(kmaxl a l2):: nil).
Proof.
fix circ 2. intros. destruct l1. simpl. destruct (klt_kle_dec a a).
destruct (klt_antirefl a k). destruct (klt_kle_dec a (kmaxl a l2)).
reflexivity. clear circ k. revert a k0. induction l2. reflexivity.
intros. simpl. simpl in k0. destruct (klt_kle_dec a0 a).
rewrite (IHl2 a) in k0. 
destruct (klt_antirefl a0 (klt_kle_trans a0 a a0 k k0)).
unfold kle. left. apply kle_klt_trans with (y:=a0). assumption.
assumption. apply IHl2. assumption. 
change (kmaxl a ((o::l1)++l2)) with
  (if klt_kle_dec a o then kmaxl o (l1++l2) else kmaxl a (l1++l2)).
change (kmaxl a (o::l1)) with 
          (if klt_kle_dec a o then kmaxl o l1 else kmaxl a l1).
destruct (klt_kle_dec a o). rewrite kmaxl_kmaxl_left.
change (kmaxl o l1::kmaxl a l2::nil) with
         ((kmaxl o l1::nil)++(kmaxl a l2::nil)).
rewrite kmaxl_kmaxl_right. apply circ. unfold kle. left. assumption.
assumption. apply circ.
Save.

Lemma kmaxl_append2 :
  forall a l1 x l2, 
     kmaxl a (l1++x::l2) = kmaxl a ((kmaxl a l1)::x::(kmaxl a l2)::nil).
Admitted.

Lemma kmaxl_partition2:
  forall o o0 l, kmaxl o ((kmaxl o (fst (partition o0 l)))::o0::
                            (kmaxl o (snd (partition o0 l)))::nil) = kmaxl o (o0::l).
Admitted.

Lemma kminl2_append2:
  forall o l1 o0 l2, kminl2 o (l1++o0::l2) =
          kminl2 o ((kminl2 o l1)::o0::(kminl2 o l2)::nil).
Admitted.

Lemma kminl_partition2:
  forall o o0 l, kminl2 o ((kminl2 o (fst (partition o0 l)))::o0::
                            (kminl2 o (snd (partition o0 l)))::nil) = kminl2 o (o0::l).
Admitted.

Lemma kmaxl_qsorth :
  forall n l o, length l <= n -> kmaxl o (qsorth l n) = kmaxl o l.
Proof.
fix circ 1. intros. destruct n. destruct l. reflexivity. inversion H.
destruct l. reflexivity. simpl in H. apply le_S_n in H. simpl.
rewrite (surjective_pairing (partition o0 l)). rewrite kmaxl_append2.
rewrite circ. rewrite circ. rewrite kmaxl_partition2. simpl. reflexivity.
apply length_snd_partition. assumption. apply length_fst_partition.
assumption.
Save.

Lemma kminl_qsorth :
  forall n l o, length l <= n -> kminl2 o (qsorth l n) = kminl2 o l.
Proof.
fix circ 1. intros. destruct n. destruct l. reflexivity. inversion H.
destruct l. reflexivity. simpl in H. apply le_S_n in H. simpl.
rewrite (surjective_pairing (partition o0 l)).
rewrite kminl2_append2. rewrite circ. rewrite circ. 
rewrite kminl_partition2. reflexivity. 
apply length_snd_partition. assumption. 
apply length_fst_partition. assumption.
Save.

Lemma qsorth_correct :
  forall n l, length l <= n -> sorted (qsorth l n).
Proof.
intro. apply (lt_wf_ind n). intros. destruct n0. constructor.
destruct l. constructor. simpl. 
rewrite (surjective_pairing (partition o l)).
apply sorted_append.
assert (sorted (qsorth (fst (partition o l)) n0)).
apply H. unfold lt. constructor. simpl in H0.
apply le_S_n in H0. apply length_fst_partition.
assumption. apply sorted_suffix. simpl in H0.
apply le_S_n in H0. rewrite kmaxl_qsorth.
apply kmaxl_fst_partition. apply length_fst_partition.
assumption. assumption. apply sorted_head. 
rewrite kminl_qsorth. apply kminl_snd_partition.
simpl in H0. apply le_S_n in H0. 
apply length_snd_partition. assumption.
apply H. unfold lt. constructor. simpl in H0.
apply le_S_n in H0. apply length_snd_partition.
assumption.
Save.

End STSORT.

Module StsortZZ := STSORT ZZ.
Export StsortZZ.
Import BinInt.

Open Scope Z_scope.

Check 1.

Goal sorted ((1,1)::(2,2)::(3,3)::nil).
repeat constructor.
Save Test.

