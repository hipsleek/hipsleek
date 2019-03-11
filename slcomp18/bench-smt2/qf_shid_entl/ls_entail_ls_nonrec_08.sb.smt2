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

(define-fun-rec ls_nonrec ((x_5 Refnode) (y_6 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_5 y_6))
   (exists
    ((u_7 Refnode))
    (sep
     (pto x_5 (c_node u_7))
     (ls u_7 y_6)))
   (exists
    ((u_8 Refnode) (v_9 Refnode))
    (sep
     (pto u_8 (c_node v_9))
     (pto x_5 (c_node u_8))
     (ls v_9 y_6)))))

(check-sat)

;; entailment: x1->node{x2} * ls(x,x1) * ls(x2,x3) * ls(x3,x4) * ls(x4,x5) |- ls_nonrec(x,x5)

(declare-const x1 Refnode)
(declare-const x2 Refnode)
(declare-const x Refnode)
(declare-const x3 Refnode)
(declare-const x4 Refnode)
(declare-const x5 Refnode)

(assert
 (sep
  (pto x1 (c_node x2))
  (ls x x1)
  (ls x2 x3)
  (ls x3 x4)
  (ls x4 x5)))

(assert
 (not
  (ls_nonrec x x5)))

(check-sat)
