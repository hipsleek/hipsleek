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
(declare-const y0 Loc)
(declare-const y00 Loc)
(declare-const y000 Loc)
(declare-const t Loc)
(declare-const t0 Loc)
(declare-const t00 Loc)
(declare-const t000 Loc)

(define-fun pos3 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (or (and (pto a y) (= (- i 1) 0)) (sep (pto a y) (or (and (pto y y0) (= (- (- i 1) 1) 0)) (sep (pto y y0) (or (and (pto y0 y00) (= (- (- (- i 1) 1) 1) 0)) (sep (pto y0 y00) (and (pto y00 y000) (= (- (- (- (- i 1) 1) 1) 1) 0)))))))))))

(define-fun neg3 ((z Loc) (b Loc) (j Int)) Bool (or (and (not (pto z b)) (= j 0)) (sep (pto z b) (or (and (not (pto b t)) (= (- j 1) 0)) (sep (pto b t) (or (and (not (pto t t0)) (= (- (- j 1) 1) 0)) (sep (pto t t0) (or (and (not (pto t0 t00)) (= (- (- (- j 1) 1) 1) 0)) (sep (pto t0 t00) (and (not (pto t00 t000)) (= (- (- (- (- j 1) 1) 1) 1) 0)))))))))))

;------- f -------
(assert (= t y))
(assert (= t0 y0))
(assert (= t00 y00))
(assert (not (= t000 y000)))
;-----------------

(assert (pos3 u v 4))
(assert (not (neg3 u v 4)))

(check-sat)
;(get-model)
