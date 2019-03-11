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

(define-funs-rec (
	(ls ((x_2 Refnode) (y_3 Refnode)) Bool)
	(ls2 ((x_5 Refnode) (y_6 Refnode)) Bool)
	(ls_even ((x_10 Refnode) (y_11 Refnode)) Bool)
	(ls_odd ((x_13 Refnode) (y_14 Refnode)) Bool)
		)
		(
  (or
   (and
    (_ emp Refnode node)
    (= x_2 y_3))
   (exists
    ((u_4 Refnode))
    (sep
     (pto x_2 (c_node u_4))
     (ls u_4 y_3))))

;; heap predicates

  (or
   (and
    (_ emp Refnode node)
    (= x_5 y_6))
   (exists
    ((u_7 Refnode))
    (sep
     (pto x_5 (c_node u_7))
     (ls2 u_7 y_6)))
   (exists
    ((u_8 Refnode) (v_9 Refnode))
    (sep
     (pto u_8 (c_node v_9))
     (pto x_5 (c_node u_8))
     (ls2 v_9 y_6))))

;; heap predicates

  (or
   (and
    (_ emp Refnode node)
    (= x_10 y_11))
   (exists
    ((u_12 Refnode))
    (sep
     (pto x_10 (c_node u_12))
     (ls_odd u_12 y_11))))

;; heap predicates

  (or
   (pto x_13 (c_node y_14))
   (exists
    ((u_15 Refnode))
    (sep
     (pto x_13 (c_node u_15))
     (ls_even u_15 y_14))))
     		)
)

(check-sat)

;; entailment: ls2(v,y) * ls2(x,u) * ls_even(u,v) |- ls(x,y)

(declare-const v Refnode)
(declare-const y Refnode)
(declare-const x Refnode)
(declare-const u Refnode)

(assert
 (sep
  (ls2 v y)
  (ls2 x u)
  (ls_even u v)))

(assert
 (not
  (ls x y)))

(check-sat)
