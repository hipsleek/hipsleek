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

(declare-const w1 Loc)
(declare-const w2 Loc)
(declare-const w3 Loc)

;------- f -------
(assert (= w1 u2))
(assert (= w2 u1))
(assert (= w3 u1))
;-----------------

(assert (sep (pto w u1) (pto u1 u2) (pto u2 (as nil Loc))))
(assert (not (and (sep (sep (pto w3 w1) (pto w1 (as nil Loc))) (pto w w2)) (sep (pto w w3) true))))

(check-sat)
;(get-model)
