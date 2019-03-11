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

(define-fun-rec sls ((x_1 Refnode) (y_2 Refnode) (l_3 Int) (u_4 Int)) Bool
  (or
   (and
    (pto x_1 (c_node y_2 l_3))
    (= l_3 u_4))
   (exists
    ((t_5 Refnode) (a_6 Int))
    (and
     (sep
      (pto x_1 (c_node t_5 l_3))
      (sls t_5 y_2 a_6 u_4))
     (and
      (<= 0 (- u_4 a_6))
      (<= l_3 a_6))))))


(check-sat)

;; entailment: sls(x,y,l1,u1) * sls(y,z,l2,u2) * sls(z,t,l3,u3) & u1<=l2 & u2<=l3 |- sls(x,t,l1,u3)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l1 Int)
(declare-const u1 Int)
(declare-const z Refnode)
(declare-const l2 Int)
(declare-const u2 Int)
(declare-const t Refnode)
(declare-const l3 Int)
(declare-const u3 Int)

(assert
 (and
  (sep
   (sls x y l1 u1)
   (sls y z l2 u2)
   (sls z t l3 u3))
  (and
   (<= u1 l2)
   (<= u2 l3))))

(assert
 (not
  (sls x t l1 u3)))

(check-sat)
