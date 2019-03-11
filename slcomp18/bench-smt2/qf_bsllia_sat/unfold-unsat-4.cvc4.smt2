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
(declare-const y00 Loc)
(declare-const b00 Loc)
(declare-const y000 Loc)
(declare-const b000 Loc)
(declare-const t Loc)
(declare-const d Loc)
(declare-const t0 Loc)
(declare-const d0 Loc)
(declare-const t00 Loc)
(declare-const d00 Loc)
(declare-const t000 Loc)
(declare-const d000 Loc)

(define-fun pos3 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (or (and (pto y b) (= (- i 1) 0)) (sep (pto y b) (or (and (pto y0 b0) (= (- (- i 1) 1) 0)) (sep (pto y0 b0) (or (and (pto y00 b00) (= (- (- (- i 1) 1) 1) 0)) (sep (pto y00 b00) (and (pto y000 b000) (= (- (- (- (- i 1) 1) 1) 1) 0)))))))))))

(define-fun neg3 ((z Loc) (c Loc) (j Int)) Bool (or (and (pto z c) (= j 0)) (sep (not (pto z c)) (or (and (pto t d) (= (- j 1) 0)) (sep (not (pto t d)) (or (and (pto t0 d0) (= (- (- j 1) 1) 0)) (sep (not (pto t0 d0)) (or (and (pto t00 d00) (= (- (- (- j 1) 1) 1) 0)) (sep (not (pto t00 d00)) (and (pto t000 d000) (= (- (- (- (- j 1) 1) 1) 1) 0)))))))))))

;------- f -------
(assert (= t y000))
(assert (= d b000))
(assert (= t0 y000))
(assert (= d0 b000))
(assert (= t00 y000))
(assert (= d00 b000))
(assert (= t000 y000))
(assert (= d000 b000))
;-----------------

(assert (pos3 u v 4))
(assert (not (neg3 u v 4)))

(check-sat)
;(get-model)
