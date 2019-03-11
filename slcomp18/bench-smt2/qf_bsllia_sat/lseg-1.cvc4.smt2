(set-logic QF_BSLLIA)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))
(declare-const loc0 Loc)

(declare-const hd Loc)
(declare-const tl Loc)
(declare-const z Loc)
(declare-const w Loc)

(define-fun acyc_lseg1 ((x Loc) (y Loc) (i Int)) Bool (or (and (= x y) (= i 0) (_ emp Loc Loc)) (and (distinct x y) (sep (pto x z) (and (= z y) (= (- i 1) 0) (_ emp Loc Loc))))))

(define-fun lseg1 ((u Loc) (v Loc) (j Int)) Bool (or (and (= u v) (= j 0) (_ emp Loc Loc)) (sep (pto u w) (and (= w v) (= (- j 1) 0) (_ emp Loc Loc)))))

;------- f -------
(assert (= z w))
;-----------------

(assert (acyc_lseg1 hd tl 1))
(assert (not (lseg1 hd tl 1)))

(check-sat)
;(get-model)
