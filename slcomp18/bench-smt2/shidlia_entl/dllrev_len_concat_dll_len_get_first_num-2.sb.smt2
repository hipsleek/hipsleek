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

(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (l_5 Int)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (and
     (= (+ l_5 (- 1)) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode) (k Int))
    (and
     (sep
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 k))
     (= k (+ l_5 (- 1)))
     (<= 1 (+ l_5 (- 1)))))))

;; heap predicates

(define-fun-rec dll_rev ((hd_7 Refnode) (p_8 Refnode) (tl_9 Refnode) (n_10 Refnode) (l_11 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node n_10 p_8))
    (and
     (= (+ l_11 (- 1)) 0)
     (= hd_7 tl_9)))
   (exists
    ((x_12 Refnode) (k Int))
    (and
     (sep
      (pto tl_9 (c_node n_10 x_12))
      (dll_rev hd_7 p_8 x_12 tl_9 k))
     (= k (+ l_11 (- 1)))
     (<= 1 (+ l_11 (- 1)))))))


(check-sat)

;; entailment: dll(x,y,z,t,200) * dll_rev(u,v,y,x,100) |- (exists w. u->node{w,v} * dll_rev(w,u,z,t,299))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const u Refnode)
(declare-const v Refnode)
(declare-const k100 Int)
(declare-const k200 Int)
(declare-const k299 Int)

(assert
 (and (= k100 100) (= k200 200) (= k299 299)
 (sep
  (dll x y z t k200)
  (dll_rev u v y x k100))))

(assert
 (not
  (exists
   ((w Refnode))
   (sep
    (pto u (c_node w v))
    (dll_rev w u z t k299)))))

(check-sat)
