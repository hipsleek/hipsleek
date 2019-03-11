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
(declare-const end Loc)
(declare-const yl Loc)
(declare-const yr Loc)
(declare-const yl0 Loc)
(declare-const yr0 Loc)
(declare-const yl1 Loc)
(declare-const yr1 Loc)
(declare-const xl0 Loc)
(declare-const xr0 Loc)
(declare-const xl1 Loc)
(declare-const xr1 Loc)
(declare-const ul Loc)
(declare-const ur Loc)
(declare-const ul0 Loc)
(declare-const ur0 Loc)
(declare-const ul1 Loc)
(declare-const ur1 Loc)
(declare-const tl0 Loc)
(declare-const tr0 Loc)
(declare-const tl1 Loc)
(declare-const tr1 Loc)

(define-fun acyc_tseg2 ((y Loc) (z Loc)) Bool (or (and (= y z) (_ emp Loc Node)) (and (distinct y z) (sep (pto y (node yl yr)) (or (and (= yl z) (_ emp Loc Node)) (and (distinct yl z) (sep (pto yl (node yl0 yr0)) (and (= yl0 z) (_ emp Loc Node)) (and (= yr0 (as nil Loc)) (_ emp Loc Node)))) (and (distinct yl z) (sep (pto yl (node yl0 yr0)) (and (= yl0 (as nil Loc)) (_ emp Loc Node)) (and (= yr0 z) (_ emp Loc Node))))) (or (and (= yr (as nil Loc)) (_ emp Loc Node)) (and (distinct yr z) (sep (pto yr (node xl1 xr1)) (and (= xl1 (as nil Loc)) (_ emp Loc Node)) (and (= xr1 (as nil Loc)) (_ emp Loc Node))))))) (and (distinct y z) (sep (pto y (node yl yr)) (or (and (= yl (as nil Loc)) (_ emp Loc Node)) (and (distinct yl z) (sep (pto yl (node xl0 xr0)) (and (= xl0 (as nil Loc)) (_ emp Loc Node)) (and (= xr0 (as nil Loc)) (_ emp Loc Node))))) (or (and (= yr z) (_ emp Loc Node)) (and (distinct yr z) (sep (pto yr (node yl1 yr1)) (and (= yl1 z) (_ emp Loc Node)) (and (= yr1 (as nil Loc)) (_ emp Loc Node)))) (and (distinct yr z) (sep (pto yr (node yl1 yr1)) (and (= yl1 (as nil Loc)) (_ emp Loc Node)) (and (= yr1 z) (_ emp Loc Node)))))))))

(define-fun tseg2 ((u Loc) (v Loc)) Bool (or (and (= u v) (_ emp Loc Node)) (sep (pto u (node ul ur)) (or (and (= ul v) (_ emp Loc Node)) (sep (pto ul (node ul0 ur0)) (and (= ul0 v) (_ emp Loc Node)) (and (= ur0 (as nil Loc)) (_ emp Loc Node))) (sep (pto ul (node ul0 ur0)) (and (= ul0 (as nil Loc)) (_ emp Loc Node)) (and (= ur0 v) (_ emp Loc Node)))) (or (and (= ur (as nil Loc)) (_ emp Loc Node)) (sep (pto ur (node tl1 tr1)) (and (= tl1 (as nil Loc)) (_ emp Loc Node)) (and (= tr1 (as nil Loc)) (_ emp Loc Node))))) (sep (pto u (node ul ur)) (or (and (= ul (as nil Loc)) (_ emp Loc Node)) (sep (pto ul (node tl0 tr0)) (and (= tl0 (as nil Loc)) (_ emp Loc Node)) (and (= tr0 (as nil Loc)) (_ emp Loc Node)))) (or (and (= ur v) (_ emp Loc Node)) (sep (pto ur (node ul1 ur1)) (and (= ul1 v) (_ emp Loc Node)) (and (= ur1 (as nil Loc)) (_ emp Loc Node))) (sep (pto ur (node ul1 ur1)) (and (= ul1 (as nil Loc)) (_ emp Loc Node)) (and (= ur1 v) (_ emp Loc Node)))))))

;------- f -------
(assert (= yl ul))
(assert (= yr ur))
(assert (= yl0 ul0))
(assert (= yr0 ur0))
(assert (= yl1 ul1))
(assert (= yr1 ur1))
(assert (= xl0 tl0))
(assert (= xr0 tr0))
(assert (= xl1 tl1))
(assert (= xr1 tr1))
;-----------------

(assert (distinct root end))
(assert (distinct yl end))
(assert (distinct yr end))
(assert (distinct yl (as nil Loc)))
(assert (distinct yr (as nil Loc)))

(assert (acyc_tseg2 root end))
(assert (not (tseg2 root end)))

(check-sat)
;(get-model)
