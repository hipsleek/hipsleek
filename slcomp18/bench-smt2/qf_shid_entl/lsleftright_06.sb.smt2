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

(define-fun-rec lsl ((x_2 Refnode) (y_3 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_2 y_3))
   (exists
    ((u_4 Refnode))
    (sep
     (pto x_2 (c_node u_4))
     (lsl u_4 y_3)))))

;; heap predicates

(define-fun-rec lsr ((x_5 Refnode) (y_6 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_5 y_6))
   (exists
    ((u_7 Refnode))
    (sep
     (pto u_7 (c_node y_6))
     (lsr x_5 u_7)))))

;; heap predicates

(define-fun-rec lslr ((x_8 Refnode) (y_9 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_8 y_9))
   (exists
    ((u_10 Refnode))
    (sep
     (pto x_8 (c_node u_10))
     (lslr u_10 y_9)))
   (exists
    ((u_11 Refnode))
    (sep
     (pto u_11 (c_node y_9))
     (lslr x_8 u_11)))))

;; heap predicates

(define-fun-rec lsa ((x_12 Refnode) (y_13 Refnode)) Bool
  (or
   (lsl x_12 y_13)
   (lsr x_12 y_13)))

(check-sat)

;; entailment: lsl(x,x1) * lsr(x1,y) |- lsr(x,y)

(declare-const x Refnode)
(declare-const x1 Refnode)
(declare-const y Refnode)

(assert
 (sep
  (lsl x x1)
  (lsr x1 y)))

(assert
 (not
  (lsr x y)))

(check-sat)
