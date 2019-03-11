(set-logic SHID)
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

(define-fun-rec ls ((x_1 Refnode) (y_2 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_1 y_2))
   (exists
    ((u_3 Refnode))
    (sep
     (pto x_1 (c_node u_3))
     (ls u_3 y_2)))))

(check-sat)

;; entailment: ls(x,y) |- (exists t. ls(t,y) * ls(x,t))

(declare-const x Refnode)
(declare-const y Refnode)

(assert
 (ls x y))

(assert
 (not
  (exists
   ((t Refnode))
   (sep
    (ls t y)
    (ls x t)))))

(check-sat)
