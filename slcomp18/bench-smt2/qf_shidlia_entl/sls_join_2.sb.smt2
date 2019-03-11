(set-logic QF_SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode) (val Int)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec ls ((x_1 Refnode) (y_2 Refnode) (l_3 Int) (u_4 Int)) Bool
  (or
   (and
    (pto x_1 (c_node y_2 l_3))
    (= l_3 u_4))
   (exists
    ((t_5 Refnode) (a_6 Int))
    (and
     (sep
      (pto x_1 (c_node t_5 l_3))
      (ls t_5 y_2 a_6 u_4))
     (and
      (<= a_6 u_4)
      (<= l_3 a_6))))))

(check-sat)

;; entailment: ls(x,y,l1,u1) * ls(y,z,l2,u2) & u1<=l2 |- ls(x,z,l1,u2)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l1 Int)
(declare-const u1 Int)
(declare-const z Refnode)
(declare-const l2 Int)
(declare-const u2 Int)

(assert
 (and
  (sep
   (ls x y l1 u1)
   (ls y z l2 u2))
  (<= u1 l2)))

(assert
 (not
  (ls x z l1 u2)))

(check-sat)
