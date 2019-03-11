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
(declare-const w Loc)
(declare-const w0 Loc)

(define-fun acyc_lseg2 ((x Loc) (y Loc) (i Int)) Bool (or (and (= x y) (= i 0) (_ emp Loc Loc)) (and (distinct x y) (sep (pto x z) (or (and (= z y) (= (- i 1) 0) (_ emp Loc Loc)) (and (distinct z y) (sep (pto z z0) (and (= z0 y) (= (- (- i 1) 1) 0) (_ emp Loc Loc)))))))))

(define-fun lseg2 ((u Loc) (v Loc) (j Int)) Bool (or (and (= u v) (= j 0) (_ emp Loc Loc)) (sep (pto u w) (or (and (= w v) (= (- j 1) 0) (_ emp Loc Loc)) (sep (pto w w0) (and (= w0 v) (= (- (- j 1) 1) 0) (_ emp Loc Loc)))))))

;------- f -------
(assert (= z w))
(assert (= z0 w0))
;-----------------

(assert (acyc_lseg2 hd tl 2))
(assert (not (lseg2 hd tl 2)))

(check-sat)
;(get-model)
