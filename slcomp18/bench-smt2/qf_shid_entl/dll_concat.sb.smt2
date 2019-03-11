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

(check-sat)

;; entailment: dll(u,v,y,x) * dll(x,y,z,t) |- dll(u,v,z,t)

(declare-const u Refnode)
(declare-const v Refnode)
(declare-const y Refnode)
(declare-const x Refnode)
(declare-const z Refnode)
(declare-const t Refnode)

(assert
 (sep
  (dll u v y x)
  (dll x y z t)))

(assert
 (not
  (dll u v z t)))

(check-sat)
