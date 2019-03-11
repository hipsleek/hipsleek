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

(define-fun-rec dllnull ((hd_7 Refnode) (p_8 Refnode) (l_9 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node (as nil Refnode) p_8))
    (= (+ l_9 (- 1)) 0))
   (exists
    ((x_10 Refnode) (k Int))
    (and
     (sep
      (pto hd_7 (c_node x_10 p_8))
      (dllnull x_10 hd_7 k))
     (= k (+ l_9 (- 1)))
     (<= 1 (+ l_9 (- 1)))))))

(check-sat)

;; entailment: dllnull(x,y,100) & n1<=20 & 1<=n1 |- (exists z,t,u,n2. dll(t,z,u,nil,n2) * dll(x,y,z,t,n1) & 80<=n2)

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const n1 Int)
(declare-const k100 Int)

(assert
 (and
  (dllnull x y k100)
  (and (= k100 100)
   (<= n1 20)
   (<= 1 n1))))

(assert
 (not
  (exists
   ((z Refnode) (t Refnode) (u Refnode) (n2 Int))
   (and
    (sep
     (dll t z u (as nil Refnode) n2)
     (dll x y z t n1))
    (<= 80 n2)))))

(check-sat)
