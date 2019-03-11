(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))
(declare-const loc0 Loc)

(declare-const u Loc)
(declare-const v Loc)

(declare-const x Loc)
(declare-const y Loc)

;------- f -------
(assert (= x (as nil Loc)))
(assert (= y (as nil Loc)))
;-----------------

(assert (and (sep (pto u (as nil Loc)) (_ emp Loc Loc)) (= v (as nil Loc))))

(assert (not (and (sep (pto u x) (wand (pto u v) (and (= y (as nil Loc)) (sep (pto u (as nil Loc)) (_ emp Loc Loc))))) (sep (pto u y) true))))

(check-sat)
;(get-model)
