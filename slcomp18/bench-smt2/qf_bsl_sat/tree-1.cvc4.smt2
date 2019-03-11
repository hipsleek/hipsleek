(set-logic QF_BSL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort Loc 0)
;
(declare-datatypes (
		(Node 0)
		) (
		((node (left Loc) (right Loc)))
		)
)
(declare-heap (Loc Node))
(declare-const loc0 Loc)
(declare-const data0 Node)

(declare-const root Loc)
(declare-const yl Loc)
(declare-const yr Loc)
(declare-const xl Loc)
(declare-const xr Loc)

(define-fun dist_tree1 ((y Loc)) Bool (or (and (= y (as nil Loc)) (_ emp Loc Node)) (and (distinct yl yr) (sep (pto y (node yl yr)) (and (= yl (as nil Loc)) (_ emp Loc Node)) (and (= yr (as nil Loc)) (_ emp Loc Node))))))

(define-fun tree1 ((x Loc)) Bool (or (and (= x (as nil Loc)) (_ emp Loc Node)) (sep (pto x (node xl xr)) (and (= xl (as nil Loc)) (_ emp Loc Node)) (and (= xr (as nil Loc)) (_ emp Loc Node)))))

;------- f -------
(assert (= root (as nil Loc)))
;-----------------

(assert (dist_tree1 root))
(assert (not (tree1 root)))

(check-sat)
;;(get-model)
