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

(define-fun-rec dll_rev ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (= hd_1 tl_3))
   (exists
    ((x_5 Refnode))
    (sep
     (pto tl_3 (c_node n_4 x_5))
     (dll_rev hd_1 p_2 x_5 tl_3)))))

(check-sat)

;; entailment: dll_rev(u,v,y,x) * dll_rev(x,y,z,t) |- dll_rev(u,v,z,t)

(declare-const u Refnode)
(declare-const v Refnode)
(declare-const y Refnode)
(declare-const x Refnode)
(declare-const z Refnode)
(declare-const t Refnode)

(assert
 (sep
  (dll_rev u v y x)
  (dll_rev x y z t)))

(assert
 (not
  (dll_rev u v z t)))

(check-sat)
