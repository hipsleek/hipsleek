(* Simple tactic that tried to decide (in)equalities on Z *)
Require Export ZArith.

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
  