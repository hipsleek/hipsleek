(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))

(declare-const loc0 Loc)

(declare-const w Loc)
(declare-const u1 Loc)
(declare-const u2 Loc)
(declare-const u3 Loc)

(declare-const w1 Loc)
(declare-const w2 Loc)
(declare-const w3 Loc)
(declare-const w4 Loc)
(declare-const w5 Loc)
(declare-const w6 Loc)
(declare-const w7 Loc)
(declare-const w8 Loc)

;------- f -------
(assert (= w1 (as nil Loc)))
(assert (= w2 (as nil Loc)))
(assert (= w3 u3))
(assert (= w4 u3))
(assert (= w5 u2))
(assert (= w6 u2))
(assert (= w7 u1))
(assert (= w8 u1))
;-----------------

(assert (sep (pto w u1) (pto u1 u2) (pto u2 u3) (pto u3 (as nil Loc))))

(assert (not (and (sep (and (sep (and (sep (and (sep (and (_ emp Loc Loc) (= w2 (as nil Loc))) (pto w4 w1)) (sep (pto w4 w2) true)) (pto w6 w3)) (sep (pto w6 w4) true)) (pto w8 w5)) (sep (pto w8 w6) true)) (pto w w7)) (sep (pto w w8) true))))

(check-sat)
;(get-model)
