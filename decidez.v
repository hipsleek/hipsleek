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
