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

;; entailment: x->node{h,v} * sls(h,y,l,u) & v<=l |- (exists t,r. t->node{y,u} * sls(x,t,v,r) & r<=u)

(declare-const x Refnode)
(declare-const h Refnode)
(declare-const v Int)
(declare-const y Refnode)
(declare-const l Int)
(declare-const u Int)

(assert
 (and
  (sep
   (pto x (c_node h v))
   (sls h y l u))
  (<= v l)))

(assert
 (not
  (exists
   ((t Refnode) (r Int))
   (and
    (sep
     (pto t (c_node y u))
     (sls x t v r))
    (<= r u)))))

(check-sat)
