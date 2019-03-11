(set-logic SHIDLIA)
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
      (<= a_6 u_4)
      (<= l_3 a_6))))))


(check-sat)

;; entailment: sls(x,y,l1,100) * sls(y,z,l2,200) * sls(z,t,201,u3) & 100<=l2 |- (exists r,l3,l4,l5. r->node{t,l5} * sls(x,r,l3,l4) & l4<=l5)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l1 Int)
(declare-const z Refnode)
(declare-const l2 Int)
(declare-const t Refnode)
(declare-const u3 Int)
(declare-const k100 Int)
(declare-const k200 Int)
(declare-const k201 Int)

(assert
 (and
  (sep
   (sls x y l1 k100)
   (sls y z l2 k200)
   (sls z t k201 u3))
   (= k100 100)
   (= k200 200)
   (= k201 201)
  (<= 100 l2)))

(assert
 (not
  (exists
   ((r Refnode) (l3 Int) (l4 Int) (l5 Int))
   (and
    (sep
     (pto r (c_node t l5))
     (sls x r l3 l4))
    (<= l4 l5)))))

(check-sat)
