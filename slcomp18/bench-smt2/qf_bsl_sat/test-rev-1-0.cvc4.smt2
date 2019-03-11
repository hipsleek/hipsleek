(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

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
(declare-const data0 Node)

(declare-const u Loc)
(declare-const v Loc)

(declare-const nx1 Loc)
(declare-const nx2 Loc)
(declare-const nx3 Loc)
(declare-const dt1 Loc)
(declare-const dt2 Loc)

;------- f -------
(assert (= nx1 (as nil Loc)))
(assert (= nx2 (as nil Loc)))
(assert (= nx3 (as nil Loc)))
(assert (= dt1 c0))
(assert (= dt2 c0))
;-----------------

(assert (and (sep (pto u (node c0 (as nil Loc))) (_ emp Loc Node)) (= v (as nil Loc))))

(assert (not (and (sep (pto u (node c0 nx3)) true) (and (sep (pto u (node dt1 nx1)) (wand (pto u (node dt1 v)) (and (sep (_ emp Loc Node) (pto u (node c0 (as nil Loc)))) (= nx2 (as nil Loc))))) (sep (pto u (node dt2 nx2)) true)))))

(check-sat)
;(get-model)
