(set-logic BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))

(declare-const loc0 Loc)

(declare-const w Loc)
(declare-const u Loc)

(declare-const w1 Loc)
(declare-const w2 Loc)
(declare-const w3 Loc)
(declare-const w4 Loc)

;------- f -------
(assert (= w1 (as nil Loc)))
(assert (= w2 (as nil Loc)))
(assert (= w3 u))
(assert (= w4 u))
;-----------------

(assert (sep (pto w u) (pto u (as nil Loc))))
(assert (not (and (sep (and (sep (and (_ emp Loc Loc) (= w2 (as nil Loc))) (pto w4 w1)) (sep (pto w4 w2) true)) (pto w w3)) (sep (pto w w4) true))))

(check-sat)
;(get-model)
