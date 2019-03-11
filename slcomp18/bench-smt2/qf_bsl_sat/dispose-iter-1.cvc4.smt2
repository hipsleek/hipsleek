(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))

(declare-const loc0 Loc)

(declare-const w Loc)
(declare-const w1 Loc)
(declare-const w2 Loc)

;------- f -------
(assert (= w1 (as nil Loc)))
(assert (= w2 (as nil Loc)))
;-----------------

(assert (pto w (as nil Loc)))
(assert (not (and (sep (and (_ emp Loc Loc) (= w2 (as nil Loc))) (pto w w1)) (sep (pto w w2) true))))

(check-sat)
;(get-model)
