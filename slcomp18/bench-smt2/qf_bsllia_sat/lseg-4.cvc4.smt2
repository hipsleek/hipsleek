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
(declare-const z0 Loc)
(declare-const z00 Loc)
(declare-const z000 Loc)
(declare-const w Loc)
(declare-const w0 Loc)
(declare-const w00 Loc)
(declare-const w000 Loc)

(define-fun acyc_lseg4 ((x Loc) (y Loc) (i Int)) Bool (or (and (= x y) (= i 0) (_ emp Loc Loc)) (and (distinct x y) (sep (pto x z) (or (and (= z y) (= (- i 1) 0) (_ emp Loc Loc)) (and (distinct z y) (sep (pto z z0) (or (and (= z0 y) (= (- (- i 1) 1) 0) (_ emp Loc Loc)) (and (distinct z0 y) (sep (pto z0 z00) (or (and (= z00 y) (= (- (- (- i 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z00 y) (sep (pto z00 z000) (and (= z000 y) (= (- (- (- (- i 1) 1) 1) 1) 0) (_ emp Loc Loc)))))))))))))))

(define-fun lseg4 ((u Loc) (v Loc) (j Int)) Bool (or (and (= u v) (= j 0) (_ emp Loc Loc)) (sep (pto u w) (or (and (= w v) (= (- j 1) 0) (_ emp Loc Loc)) (sep (pto w w0) (or (and (= w0 v) (= (- (- j 1) 1) 0) (_ emp Loc Loc)) (sep (pto w0 w00) (or (and (= w00 v) (= (- (- (- j 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w00 w000) (and (= w000 v) (= (- (- (- (- j 1) 1) 1) 1) 0) (_ emp Loc Loc)))))))))))

;------- f -------
(assert (= z w))
(assert (= z0 w0))
(assert (= z00 w00))
(assert (= z000 w000))
;-----------------

(assert (acyc_lseg4 hd tl 4))
(assert (not (lseg4 hd tl 4)))

(check-sat)
;(get-model)
