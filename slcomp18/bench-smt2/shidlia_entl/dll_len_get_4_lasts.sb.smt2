(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode) (prev Refnode)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (len_5 Int)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (and
     (= (- len_5 1) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode) (k Int))
    (and
     (sep
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 k))
     (= k (- len_5 1))
     (<= 1 (- len_5 1))))))

(check-sat)

;; entailment: dll(x,y,z,t,1000) |- (exists u1,u2,u3,u4. u2->node{u3,u1} * u3->node{u4,u2} * u4->node{z,u3} * z->node{t,u4} * dll(x,y,u1,u2,996))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const k1000 Int)
(declare-const k996  Int)

(assert
 (and (= k1000 1000) (= k996 996)
 (dll x y z t k1000)))

(assert
 (not
  (exists
   ((u1 Refnode) (u2 Refnode) (u3 Refnode) (u4 Refnode))
   (sep
    (pto u2 (c_node u3 u1))
    (pto u3 (c_node u4 u2))
    (pto u4 (c_node z u3))
    (pto z (c_node t u4))
    (dll x y u1 u2 k996)))))

(check-sat)
