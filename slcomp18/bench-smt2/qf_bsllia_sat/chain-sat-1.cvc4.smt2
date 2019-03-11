(set-logic QF_BSLLIA)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))

(declare-const loc0 Loc)

(declare-const u Loc)
(declare-const v Loc)
(declare-const y Loc)
(declare-const t Loc)

(define-fun pos0 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (and (pto a y) (= (- i 1) 0)))))

(define-fun neg0 ((z Loc) (b Loc) (j Int)) Bool (or (and (not (pto z b)) (= j 0)) (sep (pto z b) (and (not (pto b t)) (= (- j 1) 0)))))

;------- f -------
(assert (not (= t y)))
;-----------------

(assert (pos0 u v 1))
(assert (not (neg0 u v 1)))

(check-sat)
;(get-model)
