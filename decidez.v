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
  | H1 : ?x = ?y, H2 : ?x <> ?y |- _ => contradict H2
  | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H
  | H : nil = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H; destruct H
  | H : _ :: _ = nil |- _ => symmetry in H; elimtype False; contradict H
  | H : nil = _ :: _ |- _ => elimtype False; contradict H
  | H : In ?x nil |- _ => contradict H
  | H : In ?x ?L |- nil = ?L => elimtype False
  | H : In ?x (?y :: ?L) |- _ => apply in_inv in H; destruct H
  | H : length ?L1 + 1 = length ?L2 |- ?L1 = ?L2 => elimtype False
  | H : length ?L1 + 1 = length ?L2 |- ?L2 = ?L1 => elimtype False
  | H : length ?L1 = length ?L2 + 1 |- ?L1 = ?L2 => elimtype False
  | H : length ?L1 = length ?L2 + 1 |- ?L2 = ?L1 => elimtype False
  | |- nil <> _ :: _ => apply nil_cons
  | |- _ :: _ <> nil => symmetry; apply nil_cons
  | |- nil = _ :: _ => elimtype False
  | |- _ :: _ = nil => elimtype False
  | |- ?x :: ?L = ?L => elimtype False
  | |- ?L = ?x :: ?L => elimtype False
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
  | |- Z_of_nat _ = Z_of_nat _ => f_equal
  | |- ?x :: _ = ?x :: _ => f_equal
  | |- rev ?L1 ++ ?x :: ?L2 = rev (?x :: ?L1) ++ ?L2 =>
	change (x :: L1) with ((x :: nil) ++ L1);
	change (x :: L2) with ((x :: nil) ++ L2);
	change (rev((x :: nil) ++ L1)) with (rev L1 ++ rev (x :: nil));
	change (rev(x::nil)) with (x::nil);
	generalize (x :: nil); intro;
	generalize (rev L1); intro
  | |- rev (?x :: ?L1) ++ ?L2 = rev ?L1 ++ ?x :: ?L2 =>
	change (x :: L1) with ((x :: nil) ++ L1);
	change (x :: L2) with ((x :: nil) ++ L2);
	change (rev((x :: nil) ++ L1)) with (rev L1 ++ rev (x :: nil));
	change (rev(x::nil)) with (x::nil);
	generalize (x :: nil); intro;
	generalize (rev L1); intro
  | H : (?x + 1 < Z_of_nat (length (?y :: ?L)))%Z |- (?x < Z_of_nat (length (?L)))%Z =>
    change (length (y :: L)) with (1 + length L) in H;
    replace (Z_of_nat (1 + length L)) with (Z_of_nat 1 + Z_of_nat (length L))%Z in H;
    change (Z_of_nat 1) with 1%Z in H
 | |- ?L1 ++ ?L2 ++ ?L3 = (?L1 ++ ?L2) ++ ?L3 =>
	apply ass_app
  | |- (?L1 ++ ?L2) ++ ?L3 = ?L1 ++ ?L2 ++ ?L3 =>
	apply app_ass
  | |- Z_of_nat (?x + ?y) = (Z_of_nat (?x) + Z_of_nat (?y))%Z =>
    apply inj_plus
  | |- (Z_of_nat (?x) + Z_of_nat (?y))%Z = Z_of_nat (?x + ?y) =>
    symmetry; apply inj_plus
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
  