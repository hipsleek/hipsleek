(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (left Refnode) (right Refnode)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec tree ((x_5 Refnode) (s_6 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= (as nil Refnode) x_5)
     (= s_6 0)))
   (exists
    ((l_7 Refnode) (r_8 Refnode) (s2_10 Int) (k Int))
    (and
     (sep
      (pto x_5 (c_node l_7 r_8))
      (tree l_7 k)
      (tree r_8 s2_10))
      (= k (- s_6 s2_10 1))
      (<= 0 s2_10)
      (<= 0 k)))))

;; heap predicates

(define-fun-rec tseg ((x_11 Refnode) (y_12 Refnode) (s_13 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= s_13 0)
     (= x_11 y_12)))
   (exists
    ((l_14 Refnode) (r_15 Refnode) (s2_17 Int) (k Int))
    (and
     (sep
      (pto x_11 (c_node l_14 r_15))
      (tree l_14 k)
      (tseg r_15 y_12 s2_17))
     (= k (- s_13 s2_17 1))
     (<= 0 k )))
   (exists
    ((l_18 Refnode) (r_19 Refnode) (s2_21 Int) (k Int))
    (and
     (sep
      (pto x_11 (c_node l_18 r_19))
      (tree r_19 s2_21)
      (tseg l_18 y_12 k))
     (= k (- s_13 s2_21 1))
     (<= 0 s2_21)))))

(check-sat)

;; entailment: tree(x,n) * tseg(u,v,m) * tseg(v,t,l) & 10<=n & 20<=m |- (exists a,b,c,d,p,q. tseg(c,d,q) * tseg(x,b,p))

(declare-const x Refnode)
(declare-const n Int)
(declare-const u Refnode)
(declare-const v Refnode)
(declare-const m Int)
(declare-const t Refnode)
(declare-const l Int)

(assert
 (and
  (sep
   (tree x n)
   (tseg u v m)
   (tseg v t l))
  (and
   (<= 10 n)
   (<= 20 m))))

(assert
 (not
  (exists
   ((b Refnode) (c Refnode) (d Refnode) (p Int) (q Int))
   (sep
    (tseg c d q)
    (tseg x b p)))))

(check-sat)
