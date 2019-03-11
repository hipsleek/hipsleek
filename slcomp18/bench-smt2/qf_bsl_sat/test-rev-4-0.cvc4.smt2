(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort Loc 0)
;
(declare-const c0 Loc)

(declare-datatypes (
        (Node 0)
        ) (
        ((node (data Loc) (next Loc)))
        )
)
(declare-heap (Loc Node))
(declare-const loc0 Loc)


(declare-const u Loc)
(declare-const v Loc)
(declare-const a1 Loc)
(declare-const a2 Loc)
(declare-const a3 Loc)

(declare-const nx1 Loc)
(declare-const nx2 Loc)
(declare-const nx3 Loc)
(declare-const dt1 Loc)
(declare-const dt2 Loc)

;------- f -------
(assert (= nx1 a1))
(assert (= nx2 a1))
(assert (= nx3 a1))
(assert (= dt1 c0))
(assert (= dt2 c0))
;-----------------

(assert (and (sep (pto u (node c0 a1)) (pto a1 (node c0 a2)) (pto a2 (node c0 a3)) (pto a3 (node c0 (as nil Loc)))) (= v (as nil Loc))))

(assert (not (and (sep (pto u (node c0 nx3)) true) (and (sep (pto u (node dt1 nx1)) (wand (pto u (node dt1 v)) (sep (pto nx2 (node c0 a2)) (pto a2 (node c0 a3)) (pto a3 (node c0 (as nil Loc))) (pto u (node c0 (as nil Loc)))))) (sep (pto u (node dt2 nx2)) true)))))

(check-sat)
;(get-model)
