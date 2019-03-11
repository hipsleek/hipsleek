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

(define-fun-rec elseg ((x_1 Refnode) (y_2 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_1 y_2))
   (exists
    ((u_3 Refnode) (v_4 Refnode))
    (sep
     (pto u_3 (c_node v_4))
     (pto x_1 (c_node u_3))
     (elseg v_4 y_2)))))

;; heap predicates

(define-fun-rec olseg ((x_5 Refnode) (y_6 Refnode)) Bool
  (or
   (pto x_5 (c_node y_6))
   (exists
    ((u_7 Refnode) (v_8 Refnode))
    (sep
     (pto u_7 (c_node v_8))
     (pto x_5 (c_node u_7))
     (olseg v_8 y_6)))))

;; heap predicates

(define-fun-rec ls ((x_9 Refnode) (y_10 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_9 y_10))
   (exists
    ((u_11 Refnode))
    (sep
     (pto x_9 (c_node u_11))
     (ls u_11 y_10)))))

;; heap predicates

(define-fun-rec ls_all ((x_12 Refnode) (y_13 Refnode)) Bool
  (or
   (elseg x_12 y_13)
   (olseg x_12 y_13)))

(check-sat)

;; entailment: elseg(u,y) * ls_all(x,u) |- ls(x,y)

(declare-const u Refnode)
(declare-const y Refnode)
(declare-const x Refnode)

(assert
 (sep
  (elseg u y)
  (ls_all x u)))

(assert
 (not
  (ls x y)))

(check-sat)
