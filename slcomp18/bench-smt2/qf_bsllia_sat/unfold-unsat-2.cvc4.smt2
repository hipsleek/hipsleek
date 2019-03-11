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
(declare-const y0 Loc)
(declare-const b0 Loc)
(declare-const t Loc)
(declare-const d Loc)
(declare-const t0 Loc)
(declare-const d0 Loc)

(define-fun pos1 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (or (and (pto y b) (= (- i 1) 0)) (sep (pto y b) (and (pto y0 b0) (= (- (- i 1) 1) 0)))))))

(define-fun neg1 ((z Loc) (c Loc) (j Int)) Bool (or (and (pto z c) (= j 0)) (sep (not (pto z c)) (or (and (pto t d) (= (- j 1) 0)) (sep (not (pto t d)) (and (pto t0 d0) (= (- (- j 1) 1) 0)))))))

;------- f -------
(assert (= t y0))
(assert (= d b0))
(assert (= t0 y0))
(assert (= d0 b0))
;-----------------

(assert (pos1 u v 2))
(assert (not (neg1 u v 2)))

(check-sat)
;(get-model)
