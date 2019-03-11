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
     (= (+ len_5 (- 1)) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode) (k Int))
    (and
     (sep
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 k))
     (= k (+ len_5 (- 1)))
     (<= 1 (+ len_5 (- 1)))))))

;; heap predicates

(define-fun-rec dll_rev ((hd_7 Refnode) (p_8 Refnode) (tl_9 Refnode) (n_10 Refnode) (len_11 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node n_10 p_8))
    (and
     (= (+ len_11 (- 1)) 0)
     (= hd_7 tl_9)))
   (exists
    ((x_12 Refnode) (k Int))
    (and
     (sep
      (pto tl_9 (c_node n_10 x_12))
      (dll_rev hd_7 p_8 x_12 tl_9 k))
     (= k (+ len_11 (- 1)))
     (<= 1 (+ len_11 (- 1)))))))

(check-sat)

;; entailment: dll(x,y,z,t,n) * dll_rev(u,v,y,x,m) & 3<=n |- (exists w,r,p,q,m1,n1. u->node{w,v} * z->node{t,r} * dll(q,p,r,z,n1) * dll_rev(w,u,p,q,m1) & m1+n1=m+n-2)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const n Int)
(declare-const u Refnode)
(declare-const v Refnode)
(declare-const m Int)

(assert
 (and
  (sep
   (dll x y z t n)
   (dll_rev u v y x m))
  (<= 3 n)))

(assert
 (not
  (exists
   ((w Refnode) (r Refnode) (p Refnode) (q Refnode) (m1 Int) (n1 Int))
   (and
    (sep
     (pto u (c_node w v))
     (pto z (c_node t r))
     (dll q p r z n1)
     (dll_rev w u p q m1))
    (= (+ m1 n1) (+ m n (- 2)))))))

(check-sat)
