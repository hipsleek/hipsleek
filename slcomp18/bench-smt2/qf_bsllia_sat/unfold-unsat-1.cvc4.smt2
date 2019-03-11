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
(declare-const b Loc)
(declare-const t Loc)
(declare-const d Loc)

(define-fun pos0 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (and (pto y b) (= (- i 1) 0)))))

(define-fun neg0 ((z Loc) (c Loc) (j Int)) Bool (or (and (pto z c) (= j 0)) (sep (not (pto z c)) (and (pto t d) (= (- j 1) 0)))))

;------- f -------
(assert (= t u))
(assert (= d v))
;-----------------

(assert (pos0 u v 1))
(assert (not (neg0 u v 1)))

(check-sat)
;(get-model)
