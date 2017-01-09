Require Import ZArith.

Module Type Mfib.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter not : formula -> formula.
  Parameter leq : Z -> Z -> formula.
  Parameter fib : Z -> Z -> formula.
  Axiom axiom_1 : forall n, valid (imp (leq n 0) (fib n 0)).
  Axiom axiom_2 : forall n, valid (imp (and (leq 1 n) (leq n 2)) (fib n 1)).
  Axiom axiom_3 :  forall n f1 f2, valid (imp (and (not (leq n 0)) (and (fib n f1) (fib (n+1) f2))) (fib (n+2) (f1+f2))).
  Axiom entail_1 : forall n m, valid (imp (and (fib 1 n) (fib 2 m)) (and (leq n m) (leq m n))).
  Axiom entail_2 : forall n m p, valid (imp (and (and (leq n 1) (leq 1 n)) (and (fib n p) (fib (n+1) m))) (and (leq m p) (leq p m))).
End Mfib.
