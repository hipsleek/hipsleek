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
(declare-const z0000 Loc)
(declare-const z00000 Loc)
(declare-const z000000 Loc)
(declare-const z0000000 Loc)
(declare-const w Loc)
(declare-const w0 Loc)
(declare-const w00 Loc)
(declare-const w000 Loc)
(declare-const w0000 Loc)
(declare-const w00000 Loc)
(declare-const w000000 Loc)
(declare-const w0000000 Loc)

(define-fun acyc_lseg8 ((x Loc) (y Loc) (i Int)) Bool (or (and (= x y) (= i 0) (_ emp Loc Loc)) (and (distinct x y) (sep (pto x z) (or (and (= z y) (= (- i 1) 0) (_ emp Loc Loc)) (and (distinct z y) (sep (pto z z0) (or (and (= z0 y) (= (- (- i 1) 1) 0) (_ emp Loc Loc)) (and (distinct z0 y) (sep (pto z0 z00) (or (and (= z00 y) (= (- (- (- i 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z00 y) (sep (pto z00 z000) (or (and (= z000 y) (= (- (- (- (- i 1) 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z000 y) (sep (pto z000 z0000) (or (and (= z0000 y) (= (- (- (- (- (- i 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z0000 y) (sep (pto z0000 z00000) (or (and (= z00000 y) (= (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z00000 y) (sep (pto z00000 z000000) (or (and (= z000000 y) (= (- (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (and (distinct z000000 y) (sep (pto z000000 z0000000) (and (= z0000000 y) (= (- (- (- (- (- (- (- (- i 1) 1) 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)))))))))))))))))))))))))))

(define-fun lseg8 ((u Loc) (v Loc) (j Int)) Bool (or (and (= u v) (= j 0) (_ emp Loc Loc)) (sep (pto u w) (or (and (= w v) (= (- j 1) 0) (_ emp Loc Loc)) (sep (pto w w0) (or (and (= w0 v) (= (- (- j 1) 1) 0) (_ emp Loc Loc)) (sep (pto w0 w00) (or (and (= w00 v) (= (- (- (- j 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w00 w000) (or (and (= w000 v) (= (- (- (- (- j 1) 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w000 w0000) (or (and (= w0000 v) (= (- (- (- (- (- j 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w0000 w00000) (or (and (= w00000 v) (= (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w00000 w000000) (or (and (= w000000 v) (= (- (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)) (sep (pto w000000 w0000000) (and (= w0000000 v) (= (- (- (- (- (- (- (- (- j 1) 1) 1) 1) 1) 1) 1) 1) 0) (_ emp Loc Loc)))))))))))))))))))

;------- f -------
(assert (= z w))
(assert (= z0 w0))
(assert (= z00 w00))
(assert (= z000 w000))
(assert (= z0000 w0000))
(assert (= z00000 w00000))
(assert (= z000000 w000000))
(assert (= z0000000 w0000000))
;-----------------

(assert (acyc_lseg8 hd tl 8))
(assert (not (lseg8 hd tl 8)))

(check-sat)
;(get-model)
