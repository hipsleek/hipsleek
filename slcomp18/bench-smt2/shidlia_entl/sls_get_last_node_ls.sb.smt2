(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode) (val Int)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec ls ((x_2 Refnode) (y_3 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_2 y_3))
   (exists
    ((anon_4 Int) (t_5 Refnode))
    (sep
     (pto x_2 (c_node t_5 anon_4))
     (ls t_5 y_3)))))

;; heap predicates

(define-fun-rec sls ((x_1 Refnode) (y_2 Refnode) (l_3 Int) (u_4 Int)) Bool
  (or
   (and
    (pto x_1 (c_node y_2 l_3))
    (= l_3 u_4))
   (exists
    ((t_5 Refnode) (a_6 Int))
    (and
     (sep
      (pto x_1 (c_node t_5 l_3))
      (sls t_5 y_2 a_6 u_4))
     (and
      (<= a_6 u_4)
      (<= l_3 a_6))))))


(check-sat)

;; entailment: sls(x,y,l,u) |- (exists t. t->node{y,u} * ls(x,t))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l Int)
(declare-const u Int)

(assert
 (sls x y l u))

(assert
 (not
  (exists
   ((t Refnode))
   (sep
    (pto t (c_node y u))
    (ls x t)))))

(check-sat)
