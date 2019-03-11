(set-logic SHIDLIA)
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

(define-fun-rec ls ((x_1 Refnode) (y_2 Refnode) (n_3 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= n_3 0)
     (= x_1 y_2)))
   (exists
    ((u_4 Refnode) (k Int))
    (and
     (sep
      (pto x_1 (c_node u_4))
      (ls u_4 y_2 k))
      (= k (- n_3 1))
     (<= 0 (- n_3 1))))))

(check-sat)

;; entailment: ls(x,y,1000) |- (exists u,v,t,w,r. r->node{y} * t->node{w} * u->node{v} * v->node{t} * x->node{u} * ls(w,r,995))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const k1000 Int)
(declare-const k995 Int)

(assert
 (and (= k1000 1000) (= k995 995)
 (ls x y k1000)))

(assert
 (not
  (exists
   ((u Refnode) (v Refnode) (t Refnode) (w Refnode) (r Refnode))
   (sep
    (pto r (c_node y))
    (pto t (c_node w))
    (pto u (c_node v))
    (pto v (c_node t))
    (pto x (c_node u))
    (ls w r k995)))))

(check-sat)
