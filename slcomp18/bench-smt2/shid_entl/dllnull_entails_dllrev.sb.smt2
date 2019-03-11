(set-logic SHID)
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

;; entailment: dllnull(x,y) |- (exists t. dll_rev(x,y,t,nil))

(declare-const x Refnode)
(declare-const y Refnode)

(assert
 (dllnull x y))

(assert
 (not
  (exists
   ((t Refnode))
   (dll_rev x y t (as nil Refnode)))))

(check-sat)
