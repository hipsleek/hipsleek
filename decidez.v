(* Simple tactic that tried to decide (in)equalities on Z *)
Require Export ZArith.
Require Export List.

Ltac decideZin X :=
  match X with
  | ?Y \/ ?Z => decideZin Y; decideZin Z
  | ?Y /\ ?Z => decideZin Y; decideZin Z
  | ~ (?Y) => decideZin Y
  | Zge (?Y) (?Z) => destruct (dec_Zge Y Z)
  | Zgt (?Y) (?Z) => destruct (dec_Zgt Y Z)
  | Zle (?Y) (?Z) => destruct (dec_Zle Y Z)
  | Zlt (?Y) (?Z) => destruct (dec_Zlt Y Z)
  | eq (?Y) (?Z) => destruct (dec_eq Y Z)
  | ?Z => idtac
end.

Ltac decideZ :=
  match goal with
   | |- ?X => decideZin X
end.

Require Import ZArith.
Require Import Classical.

Ltac hyp :=
  match goal with
  | H : ?A = Z0 |- _ => try rewrite H in *; clear H A
  | H : ?A = Zpos _ |- _ => compute in H; try rewrite H in *; clear H A
  | H : ?A = ?B |- _ => try rewrite H in *; clear H A
  | H : ?A = _ |- _ => try rewrite -> H in *; clear H A
  | H : _ = ?A |- _ => try rewrite <- H in *; clear H A
  | H : ?A /\ ?B |- _ => destruct H
  | H : exists A : _, _ |- _ => destruct H
  | H : ?A \/ ?B |- _ => destruct H
  | H : ~ ~ _ |- _ => let X := fresh "H" in assert (X := NNPP _ H); clear H
  | |- forall A : _, _=> intro
  | |- ~ ?X => intro
  | |- ?A \/ ?B => elim (classic A); intro; [left; assumption | right]
(*  | |- ?A \/ ?B => elim (classic B); intro; [right; assumption | left]*)
  | |- ?A /\ ?B => split
  | |- exists A : _, _ =>
       try (exists 0%Z; repeat hyp; auto with *; reflexivity );
       try (exists 1%Z; repeat hyp; auto with *; reflexivity );
       try (exists 2%Z; repeat hyp; auto with *; reflexivity );
       try (exists 3%Z; repeat hyp; auto with *; reflexivity );
       match goal with
       | X : Z |- _ =>
         exists X%Z; repeat hyp; auto with *; reflexivity
       end

  | H1 : ?x = ?y, H2 : ?x <> ?y |- _ => contradict H2; assumption
  
  | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H
  | H : nil = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H; destruct H

  | H : _ :: _ = nil |- _ => symmetry in H; elimtype False; contradict H; apply nil_cons
  | H : nil = _ :: _ |- _ => elimtype False; contradict H; apply nil_cons
  
  | H : In ?x nil |- _ => contradict H
  | H : In ?x ?L |- nil = ?L => elimtype False
  | H : In ?x ?L |- ?L = nil => elimtype False
  | H : In ?x (?y :: ?L) |- _ => apply in_inv in H; destruct H
  
  | |- nil <> _ :: _ => apply nil_cons
  | |- _ :: _ <> nil => symmetry; apply nil_cons
  | |- nil = _ :: _ => elimtype False
  | |- _ :: _ = nil => elimtype False
  
  | |- ?x :: ?L = ?L => elimtype False
  | |- ?L = ?x :: ?L => elimtype False

  | H : ~ _ |- False => contradict H
end.

Ltac hyp2 :=
  match goal with
  | H : (?X = ?X) |- _ => clear H
  end.
  
Lemma helper : (forall a b:Z, a < b -> b <= a + 1 -> b = a + 1)%Z.
auto with *.
Qed.

Ltac hyp3 :=
  match goal with
  | H : (Zlt ?X ?Y), H2: (Zle ?Y (Zplus ?X (Zpos xH))) |- _ => 
    let Z := fresh "H" in assert (Z := helper _ _ H H2); clear H H2
  end.
  
Ltac hyp4 :=
  match goal with
  | H : ?X, H2: ?X |- _ => clear H2
  end.

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
    | H : context f [rev (?L ++ ?x :: (@nil Z))] |- _ => apply_rev_unit x L
    | |- context f [rev (?L ++ ?x :: (@nil Z))] => apply_rev_unit x L
    | H : context f [(?L1 ++ ?L2) ++ ?L3] |- _ => apply_app_ass L1 L2 L3
    | |- context f [(?L1 ++ ?L2) ++ ?L3] => apply_app_ass L1 L2 L3
    | H : context f [(?x :: (@nil Z)) ++ ?L] |- _ => simpl_x_nil_app x L
    | |- context f [(?x :: (@nil Z)) ++ ?L] => simpl_x_nil_app x L
    | H : context f [?L ++ (@nil Z)] |- _ => apply_app_nil L
    | |- context f [?L ++ (@nil Z)] => apply_app_nil L
    | H : context f [(@nil Z) ++ ?L] |- _ => apply_nil_app L
    | |- context f [(@nil Z) ++ ?L] => apply_nil_app L
    | H : context f [hd 0%Z (?x :: ?L)] |- _ => simpl_head_cons x L
    | |- context f [hd 0%Z (?x :: ?L)] => simpl_head_cons x L
    | H : context f [tail (@nil Z)] |- _ => simpl_tail_nil
    | |- context f [tail (@nil Z)] => simpl_tail_nil
    | H : context f [tail (?x :: ?L)] |- _ => simpl_tail_cons x L
    | |- context f [tail (?x :: ?L)] => simpl_tail_cons x L
    | H : context f [length (@nil Z)] |- _ => simpl_length_nil
    | |- context f [length (@nil Z)] => simpl_length_nil
    | H : context f [length (?x :: ?L)] |- _ => simpl_length_cons x L
    | |- context f [length (?x :: ?L)] => simpl_length_cons x L
    | H : context f [length (?L1 ++ ?L2)] |- _ => apply_app_length L1 L2
    | |- context f [length (?L1 ++ ?L2)] => apply_app_length L1 L2
    | H : context f [length (rev ?L)] |- _ => apply_rev_length L
    | |- context f [length (rev ?L)] => apply_rev_length L
    | H : context f [rev (@nil Z)] |- _ => simpl_rev_nil
    | |- context f [rev (@nil Z)] => simpl_rev_nil
    | H : context f [rev (?x :: ?L)] |- _ => simpl_rev_cons x L
    | |- context f [rev (?x :: ?L)] => simpl_rev_cons x L
    | H : context f [rev (?L1 ++ ?L2)] |- _ => apply_distr_rev L1 L2
    | |- context f [rev (?L1 ++ ?L2)] => apply_distr_rev L1 L2
    | H : context f [rev (rev ?L)] |- _ => apply_rev_involutive L
    | |- context f [rev (rev ?L)] => apply_rev_involutive L
    | H : context f [Z_of_nat 0] |- _ => simpl_Z_of_nat_const 0
    | |- context f [Z_of_nat 0] => simpl_Z_of_nat_const 0
    | H : context f [Z_of_nat 1] |- _ => simpl_Z_of_nat_const 1
    | |- context f [Z_of_nat 1] => simpl_Z_of_nat_const 1
    | H : context f [Z_of_nat (?x1 + ?x2)] |- _ => apply_inj_plus x1 x2
    | |- context f [Z_of_nat (?x1 + ?x2)] => apply_inj_plus x1 x2
end.
  