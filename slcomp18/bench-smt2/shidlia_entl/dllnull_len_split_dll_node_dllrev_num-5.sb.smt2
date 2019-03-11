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

;; heap predicates

(define-fun-rec dllnull ((hd_7 Refnode) (p_8 Refnode) (l_9 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node (as nil Refnode) p_8))
    (= (+ l_9 (- 1)) 0))
   (exists
    ((x_10 Refnode) (k Int))
    (and
     (sep
      (pto hd_7 (c_node x_10 p_8))
      (dllnull x_10 hd_7 k))
     (= k (+ l_9 (- 1)))
     (<= 1 (+ l_9 (- 1)))))))

(check-sat)

;; entailment: dllnull(x,y,n) & 100<=n & n1<20 & 1<=n1 |- (exists z,t,u,v,n2. t->node{v,z} * dll(x,y,z,t,n1) * dll_rev(v,t,u,nil,n2) & 80<=n2)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const n Int)
(declare-const n1 Int)

(assert
 (and
  (dllnull x y n)
  (and
   (<= 100 n)
   (< n1 20)
   (<= 1 n1))))

(assert
 (not
  (exists
   ((z Refnode) (t Refnode) (u Refnode) (v Refnode) (n2 Int))
   (and
    (sep
     (pto t (c_node v z))
     (dll x y z t n1)
     (dll_rev v t u (as nil Refnode) n2))
    (<= 80 n2)))))

(check-sat)
