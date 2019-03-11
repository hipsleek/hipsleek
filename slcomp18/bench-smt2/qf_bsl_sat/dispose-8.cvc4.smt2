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
(declare-const u4 Loc)
(declare-const u5 Loc)
(declare-const u6 Loc)
(declare-const u7 Loc)

(declare-const w1 Loc)
(declare-const w2 Loc)
(declare-const w3 Loc)
(declare-const w4 Loc)
(declare-const w5 Loc)
(declare-const w6 Loc)
(declare-const w7 Loc)
(declare-const w8 Loc)

;------- f -------
(assert (= w1 u2))
(assert (= w2 u3))
(assert (= w3 u4))
(assert (= w4 u5))
(assert (= w5 u6))
(assert (= w6 u7))
(assert (= w7 u1))
(assert (= w8 u1))
;-----------------

(assert (sep (pto w u1) (pto u1 u2) (pto u2 u3) (pto u3 u4) (pto u4 u5) (pto u5 u6) (pto u6 u7) (pto u7 (as nil Loc))))
(assert (not (and (sep (sep (pto w8 w1) (pto w1 w2) (pto w2 w3) (pto w3 w4) (pto w4 w5) (pto w5 w6) (pto w6 (as nil Loc))) (pto w w7)) (sep (pto w w8) true))))

(check-sat)
;(get-model)
