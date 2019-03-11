(set-logic QF_SHID)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec ls ((x_2 Refnode) (y_3 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_2 y_3))
   (exists
    ((u_4 Refnode))
    (sep
     (pto x_2 (c_node u_4))
     (ls u_4 y_3)))))

;; heap predicates

(define-fun-rec ls2 ((x_5 Refnode) (y_6 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_5 y_6))
   (exists
    ((u_7 Refnode))
    (sep
     (pto x_5 (c_node u_7))
     (ls2 u_7 y_6)))
   (exists
    ((u_8 Refnode) (v_9 Refnode))
    (sep
     (pto u_8 (c_node v_9))
     (pto x_5 (c_node u_8))
     (ls2 v_9 y_6)))))

(check-sat)

;; entailment: ls(x,x1) * ls(x1,x2) * ls(x2,x3) |- ls2(x,x3)

(declare-const x Refnode)
(declare-const x1 Refnode)
(declare-const x2 Refnode)
(declare-const x3 Refnode)

(assert
 (sep
  (ls x x1)
  (ls x1 x2)
  (ls x2 x3)))

(assert
 (not
  (ls2 x x3)))

(check-sat)
