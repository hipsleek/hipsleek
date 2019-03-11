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
(declare-const ul Loc)
(declare-const ur Loc)

(define-fun acyc_tseg1 ((y Loc) (z Loc)) Bool (or (and (= y z) (_ emp Loc Node)) (and (distinct y z) (sep (pto y (node yl yr)) (and (= yl z) (_ emp Loc Node)) (and (= yr (as nil Loc)) (_ emp Loc Node)))) (and (distinct y z) (sep (pto y (node yl yr)) (and (= yl (as nil Loc)) (_ emp Loc Node)) (and (= yr z) (_ emp Loc Node))))))

(define-fun tseg1 ((u Loc) (v Loc)) Bool (or (and (= u v) (_ emp Loc Node)) (sep (pto u (node ul ur)) (and (= ul v) (_ emp Loc Node)) (and (= ur (as nil Loc)) (_ emp Loc Node))) (sep (pto u (node ul ur)) (and (= ul (as nil Loc)) (_ emp Loc Node)) (and (= ur v) (_ emp Loc Node)))))

;------- f -------
(assert (= yl ul))
(assert (= yr ur))
;-----------------

(assert (distinct root end))

(assert (acyc_tseg1 root end))
(assert (not (tseg1 root end)))

(check-sat)
;(get-model)
