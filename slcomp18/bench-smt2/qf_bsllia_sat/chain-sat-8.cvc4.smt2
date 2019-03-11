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
(declare-const y0000 Loc)
(declare-const y00000 Loc)
(declare-const y000000 Loc)
(declare-const y0000000 Loc)
(declare-const t Loc)
(declare-const t0 Loc)
(declare-const t00 Loc)
(declare-const t000 Loc)
(declare-const t0000 Loc)
(declare-const t00000 Loc)
(declare-const t000000 Loc)
(declare-const t0000000 Loc)

(define-fun pos7 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (or (and (pto a y) (= (- i 1) 0)) (sep (pto a y) (or (and (pto y y0) (= (- (- i 1) 1) 0)) (sep (pto y y0) (or (and (pto y0 y00) (= (- (- (- i 1) 1) 1) 0)) (sep (pto y0 y00) (or (and (pto y00 y000) (= (- (- (- (- i 1) 1) 1) 1) 0)) (sep (pto y00 y000) (or (and (pto y000 y0000) (= (- (- (- (- (- i 1) 1) 1) 1) 1) 0)) (sep (pto y000 y0000) (or (and (pto y0000 y00000) (= (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 0)) (sep (pto y0000 y00000) (or (and (pto y00000 y000000) (= (- (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 1) 0)) (sep (pto y00000 y000000) (and (pto y000000 y0000000) (= (- (- (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 1) 1) 0)))))))))))))))))))

(define-fun neg7 ((z Loc) (b Loc) (j Int)) Bool (or (and (not (pto z b)) (= j 0)) (sep (pto z b) (or (and (not (pto b t)) (= (- j 1) 0)) (sep (pto b t) (or (and (not (pto t t0)) (= (- (- j 1) 1) 0)) (sep (pto t t0) (or (and (not (pto t0 t00)) (= (- (- (- j 1) 1) 1) 0)) (sep (pto t0 t00) (or (and (not (pto t00 t000)) (= (- (- (- (- j 1) 1) 1) 1) 0)) (sep (pto t00 t000) (or (and (not (pto t000 t0000)) (= (- (- (- (- (- j 1) 1) 1) 1) 1) 0)) (sep (pto t000 t0000) (or (and (not (pto t0000 t00000)) (= (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 0)) (sep (pto t0000 t00000) (or (and (not (pto t00000 t000000)) (= (- (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 1) 0)) (sep (pto t00000 t000000) (and (not (pto t000000 t0000000)) (= (- (- (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 1) 1) 0)))))))))))))))))))

;------- f -------
(assert (= t y))
(assert (= t0 y0))
(assert (= t00 y00))
(assert (= t000 y000))
(assert (= t0000 y0000))
(assert (= t00000 y00000))
(assert (= t000000 y000000))
(assert (not (= t0000000 y0000000)))
;-----------------

(assert (pos7 u v 8))
(assert (not (neg7 u v 8)))

(check-sat)
;(get-model)
