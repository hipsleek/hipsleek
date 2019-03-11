(set-logic SHIDLIA)
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

(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (l_5 Int)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (and
     (= (+ l_5 (- 1)) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode) (k Int))
    (and
     (sep
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 k))
     (= k (+ l_5 (- 1)))
     (<= 1 (+ l_5 (- 1)))))))

;; heap predicates

(define-fun-rec lsrev ((x_8 Refnode) (y_9 Refnode) (len_10 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= len_10 0)
     (= x_8 y_9)))
   (exists
    ((anon_11 Refnode) (u_12 Refnode) (k Int))
    (and
     (sep
      (pto u_12 (c_node y_9 anon_11))
      (lsrev x_8 u_12 k))
     (= k (- len_10 1))
     (<= 0 (- len_10 1))))))

(check-sat)

;; entailment: dll(x,y,z,t,n) & 100<=n |- (exists m,u. x->node{u,y} * lsrev(u,t,m) & 99<=m)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const n Int)

(assert
 (and
  (dll x y z t n)
  (<= 100 n)))

(assert
 (not
  (exists
   ((m Int) (u Refnode))
   (and
    (sep
     (pto x (c_node u y))
     (lsrev u t m))
    (<= 99 m)))))

(check-sat)
