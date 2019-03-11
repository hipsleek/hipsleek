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
(declare-const a1 Loc)
(declare-const a2 Loc)
(declare-const a3 Loc)
(declare-const a4 Loc)
(declare-const a5 Loc)
(declare-const a6 Loc)
(declare-const a7 Loc)

(declare-const x Loc)
(declare-const y Loc)

;------- f -------
(assert (= x a1))
(assert (= y a1))
;-----------------

(assert (and (sep (pto u a1) (pto a1 a2) (pto a2 a3) (pto a3 a4) (pto a4 a5) (pto a5 a6) (pto a6 a7) (pto a7 (as nil Loc))) (= v (as nil Loc))))

(assert (not (and (sep (pto u x) (wand (pto u v) (sep (pto y a2) (pto a2 a3) (pto a3 a4) (pto a4 a5) (pto a5 a6) (pto a6 a7) (pto a7 (as nil Loc)) (pto u (as nil Loc))))) (sep (pto u y) true))))

(check-sat)
;(get-model)
