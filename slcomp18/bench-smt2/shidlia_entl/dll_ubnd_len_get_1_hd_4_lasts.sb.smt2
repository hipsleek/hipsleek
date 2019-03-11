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

;; entailment: dll(x,y,z,t,n) & 1000<=n |- (exists u1,u2,u3,u4,u5. u3->node{u4,u2} * u4->node{u5,u3} * u5->node{z,u4} * x->node{u1,y} * z->node{t,u5} * dll(u1,x,u2,u3,n-5))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const n Int)

(assert
 (and
  (dll x y z t n)
  (<= 1000 n)))

(assert
 (not
  (exists
   ((u1 Refnode) (u2 Refnode) (u3 Refnode) (u4 Refnode) (u5 Refnode) (k Int))
   (and
   (sep
    (pto u3 (c_node u4 u2))
    (pto u4 (c_node u5 u3))
    (pto u5 (c_node z u4))
    (pto x (c_node u1 y))
    (pto z (c_node t u5))
    (dll u1 x u2 u3 k)) (= k (+ n (- 5)))))))

(check-sat)
