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
(declare-const tl0 Loc)
(declare-const tr0 Loc)
(declare-const tl1 Loc)
(declare-const tr1 Loc)
(declare-const xl Loc)
(declare-const xr Loc)
(declare-const xl0 Loc)
(declare-const xr0 Loc)
(declare-const xl1 Loc)
(declare-const xr1 Loc)

(define-fun dist_tree2 ((y Loc)) Bool (or (and (= y (as nil Loc)) (_ emp Loc Node)) (and (distinct yl yr) (sep (pto y (node yl yr)) (or (and (= yl (as nil Loc)) (_ emp Loc Node)) (sep (pto yl (node tl0 tr0)) (and (= tl0 (as nil Loc)) (_ emp Loc Node)) (and (= tr0 (as nil Loc)) (_ emp Loc Node)))) (or (and (= yr (as nil Loc)) (_ emp Loc Node)) (sep (pto yr (node tl1 tr1)) (and (= tl1 (as nil Loc)) (_ emp Loc Node)) (and (= tr1 (as nil Loc)) (_ emp Loc Node))))))))

(define-fun tree2 ((x Loc)) Bool (or (and (= x (as nil Loc)) (_ emp Loc Node)) (sep (pto x (node xl xr)) (or (and (= xl (as nil Loc)) (_ emp Loc Node)) (sep (pto xl (node xl0 xr0)) (and (= xl0 (as nil Loc)) (_ emp Loc Node)) (and (= xr0 (as nil Loc)) (_ emp Loc Node)))) (or (and (= xr (as nil Loc)) (_ emp Loc Node)) (sep (pto xr (node xl1 xr1)) (and (= xl1 (as nil Loc)) (_ emp Loc Node)) (and (= xr1 (as nil Loc)) (_ emp Loc Node)))))))

;------- f -------
(assert (= yl xl))
(assert (= yr xr))
(assert (= tl0 xl0))
(assert (= tr0 xr0))
(assert (= tl1 xl1))
(assert (= tr1 xr1))
;-----------------

(assert (distinct root (as nil Loc)))
(assert (distinct yl (as nil Loc)))
(assert (distinct yr (as nil Loc)))

(assert (dist_tree2 root))
(assert (not (tree2 root)))

(check-sat)
;;(get-model)
