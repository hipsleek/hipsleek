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

(define-fun-rec dll ((hd_2 Refnode) (p_3 Refnode) (tl_4 Refnode) (n_5 Refnode) (len_6 Int)) Bool
  (or
   (and
    (pto hd_2 (c_node n_5 p_3))
    (and
     (= (+ len_6 (- 1)) 0)
     (= hd_2 tl_4)))
   (exists
    ((x_7 Refnode) (k Int))
    (and
     (sep
      (pto hd_2 (c_node x_7 p_3))
      (dll x_7 hd_2 tl_4 n_5 k))
     (= k (+ len_6 (- 1)))
     (<= 1 (+ len_6 (- 1)))))))

;; heap predicates

(define-fun-rec dll_rev ((hd_8 Refnode) (p_9 Refnode) (tl_10 Refnode) (n_11 Refnode) (len_12 Int)) Bool
  (or
   (and
    (pto hd_8 (c_node n_11 p_9))
    (and
     (= (+ len_12 (- 1)) 0)
     (= hd_8 tl_10)))
   (exists
    ((x_13 Refnode) (k Int))
    (and
     (sep
      (pto tl_10 (c_node n_11 x_13))
      (dll_rev hd_8 p_9 x_13 tl_10 k))
     (= k (+ len_12 (- 1)))
     (<= 1 (+ len_12 (- 1)))))))

(check-sat)

;; entailment: dll(v,u,z,t,200) * dll_rev(x,y,u,v,n) & 100<=n |- (exists u_1. z->node{t,u_1} * dll(x,y,u_1,z,n+199))

(declare-const v Refnode)
(declare-const u Refnode)
(declare-const z Refnode)
(declare-const t Refnode)
(declare-const x Refnode)
(declare-const y Refnode)
(declare-const n Int)
(declare-const k200 Int)
(declare-const k Int)

(assert
 (and
  (sep
   (dll v u z t k200)
   (dll_rev x y u v n))
  (= k200 200) (= k (+ n 199))
  (<= 100 n)))

(assert
 (not
  (exists
   ((u_1 Refnode))
   (sep
    (pto z (c_node t u_1))
    (dll x y u_1 z k)))))

(check-sat)
