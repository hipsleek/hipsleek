(set-logic QF_SHID)
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

(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (= hd_1 tl_3))
   (exists
    ((x_5 Refnode))
    (sep
     (pto hd_1 (c_node x_5 p_2))
     (dll x_5 hd_1 tl_3 n_4)))))

;; heap predicates

(define-fun-rec dllnull ((hd_6 Refnode) (p_7 Refnode)) Bool
  (or
   (pto hd_6 (c_node (as nil Refnode) p_7))
   (exists
    ((x_8 Refnode))
    (sep
     (pto hd_6 (c_node x_8 p_7))
     (dllnull x_8 hd_6)))))

(check-sat)

;; entailment: t->node{nil,z} * dll(x,y,z,t) |- dllnull(x,y)

(declare-const t Refnode)
(declare-const z Refnode)
(declare-const x Refnode)
(declare-const y Refnode)

(assert
 (sep
  (pto t (c_node (as nil Refnode) z))
  (dll x y z t)))

(assert
 (not
  (dllnull x y)))

(check-sat)
