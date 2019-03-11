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

(declare-const x0 Loc)
(declare-const y0 Loc)

;------- f -------
(assert (= x0 (as nil Loc)))
(assert (= y0 (as nil Loc)))
;-----------------

(assert (and (sep (pto u (as nil Loc)) (_ emp Loc Loc)) (= v (as nil Loc))))

(assert (not (and (sep (pto u x0) (wand (pto u v) (and (= y0 (as nil Loc)) (sep (pto u (as nil Loc)) (_ emp Loc Loc))))) (sep (pto u y0) true))))

(check-sat)
;(get-model)
