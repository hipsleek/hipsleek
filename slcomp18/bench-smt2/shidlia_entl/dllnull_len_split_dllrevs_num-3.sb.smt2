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

(define-fun-rec dll_rev ((hd_7 Refnode) (p_8 Refnode) (tl_9 Refnode) (n_10 Refnode) (l_11 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node n_10 p_8))
    (and
     (= (- l_11 1) 0)
     (= hd_7 tl_9)))
   (exists
    ((x_12 Refnode) (k Int))
    (and
     (sep
      (pto tl_9 (c_node n_10 x_12))
      (dll_rev hd_7 p_8 x_12 tl_9 k))
     (= k (- l_11 1))
     (<= 1 (- l_11 1))))))

;; heap predicates

(define-fun-rec dllnull ((hd_7 Refnode) (p_8 Refnode) (l_9 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node (as nil Refnode) p_8))
    (= (- l_9 1) 0))
   (exists
    ((x_10 Refnode) (k Int))
    (and
     (sep
      (pto hd_7 (c_node x_10 p_8))
      (dllnull x_10 hd_7 k))
     (= k (- l_9 1))
     (<= 1 (- l_9 1))))))

(check-sat)

;; entailment: dllnull(x,y,100) |- (exists z,t,u. dll_rev(t,z,u,nil,80) * dll_rev(x,y,z,t,20))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const k100 Int)
(declare-const k80 Int)
(declare-const k20 Int)

(assert
 (and (= k100 100) (= k80 80) (= k20 20)
 (dllnull x y k100)))

(assert
 (not
  (exists
   ((z Refnode) (t Refnode) (u Refnode))
   (sep
    (dll_rev t z u (as nil Refnode) k80)
    (dll_rev x y z t k20)))))

(check-sat)
