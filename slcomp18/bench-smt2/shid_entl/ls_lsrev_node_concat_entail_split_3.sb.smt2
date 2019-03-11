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

;; heap predicates

(define-fun-rec lsrev ((x_4 Refnode) (y_5 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_4 y_5))
   (exists
    ((u_6 Refnode))
    (sep
     (pto u_6 (c_node y_5))
     (lsrev x_4 u_6)))))

(check-sat)

;; entailment: y->node{z} * ls(z,t) * lsrev(x,y) |- (exists u,v. x->node{u} * ls(u,v) * lsrev(v,t))

(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const x Refnode)

(assert
 (sep
  (pto y (c_node z))
  (ls z t)
  (lsrev x y)))

(assert
 (not
  (exists
   ((u Refnode) (v Refnode))
   (sep
    (pto x (c_node u))
    (ls u v)
    (lsrev v t)))))

(check-sat)
