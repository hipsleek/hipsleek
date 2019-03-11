(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort Loc 0)
(declare-const c0 Loc)
(declare-datatypes (
        (Node 0)
        ) (
        ((node (data Loc) (next Loc)))
        )
)
(declare-const data0 Node)
(declare-heap (Loc Node))
(declare-const loc0 Loc)

(declare-const w Loc)
(declare-const u Loc)
(declare-const nx1 Loc)
(declare-const nx2 Loc)
(declare-const nx3 Loc)
(declare-const nx4 Loc)
(declare-const dt1 Loc)
(declare-const dt3 Loc)
(declare-const node1 Node)
(declare-const node2 Node)

;------- f -------
(assert (= nx1 (as nil Loc)))
(assert (= nx2 (as nil Loc)))
(assert (= nx3 u))
(assert (= nx4 u))
(assert (= dt1 c0))
(assert (= dt3 c0))
(assert (= node1 (node c0 (as nil Loc))))
(assert (= node2 (node c0 u)))
;-----------------

(assert (sep (pto w (node c0 u)) (pto u (node c0 (as nil Loc)))))

(assert (not (and (sep (pto w (node c0 nx4)) true) (and (sep (and (sep (pto nx3 (node c0 nx2)) true) (and (sep (and (_ emp Loc Node) (= nx1 (as nil Loc))) (pto nx3 node1)) (sep (pto nx3 (node dt1 nx1)) true))) (pto w node2)) (sep (pto w (node dt3 nx3)) true)))))

(check-sat)
;(get-model)
