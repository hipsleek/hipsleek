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

;; entailment: sls(t,w,301,u4) * sls(x,y,l1,100) * sls(y,z,101,u2) * sls(z,t,l3,300) & u2<=l3 |- sls(x,w,l1,u4)

(declare-const t Refnode)
(declare-const w Refnode)
(declare-const u4 Int)
(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l1 Int)
(declare-const z Refnode)
(declare-const u2 Int)
(declare-const l3 Int)
(declare-const k300 Int)
(declare-const k301 Int)
(declare-const k100 Int)
(declare-const k101 Int)

(assert
 (and
  (sep
   (sls t w k301 u4)
   (sls x y l1 k100)
   (sls y z k101 u2)
   (sls z t l3 k300))
  (<= u2 l3) (= k100 100) (= k101 101) (= k300 300) (= k301 301)))

(assert
 (not
  (sls x w l1 u4)))

(check-sat)
