(set-logic QF_SHID)

(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

; Sorts for locations, one by cell sort
(declare-sort Refnode2 0)

; Types of cells in the heap

(declare-datatypes (
	(node2 0)
	) (
	((c_node2 (prev Refnode2) (next Refnode2) ))
	)
)

; Type of heap

(declare-heap (Refnode2 node2) 
)
; User defined predicates
(define-funs-rec (
	(dll ((in Refnode2)(p Refnode2)) Bool
	)

	(dll_e1 ((in Refnode2)(q Refnode2)) Bool
	)

	(dll_e2 ((in Refnode2)(q Refnode2)) Bool
	)

	(node2_e1 ((in Refnode2)(p Refnode2)(q Refnode2)) Bool
	)

	(dll_e3 ((in Refnode2)(p Refnode2)) Bool
	)
		)
		((or 
		(and 
			(= (as nil Refnode2) in)
			(_ emp Refnode2 node2)
		)

	(exists ((p_20 Refnode2)(self_21 Refnode2)(q_19 Refnode2))
	 
		(and 
			(= p p_20)
			(= in self_21)
		(sep 
			(pto in (c_node2 p_20 q_19 ))
			(dll q_19 self_21 )
		)

		)

		)

	)
	(exists ((p1 Refnode2)(s Refnode2)(q1 Refnode2))
	 
		(and 
			(= in s)
			(= q p1)
		(sep 
			(dll q1 s )
			(pto in (c_node2 p1 q1 ))
		)

		)

		)

	(exists ((s Refnode2)(p1 Refnode2)(p2 Refnode2)(n Refnode2)(q1 Refnode2))
	 
		(and 
			(= n q1)
			(= p1 p2)
			(= in s)
			(= q p2)
		(sep 
			(pto in (c_node2 p1 n ))
			(dll q1 s )
		)

		)

		)

	(exists ((p1 Refnode2)(n1 Refnode2))
	 
		(and 
			(= p p1)
			(= q n1)
			(pto in (c_node2 p1 n1 ))
		)

		)

	(exists ((q Refnode2))
	 
		(and 
			(= p q)
			(dll in q )
		)

		)

		)
)


(check-sat) 
;; variables
(declare-const yprm Refnode2)
(declare-const xprm Refnode2)
(declare-const next0 Refnode2)
(declare-const q Refnode2)
(declare-const y Refnode2)
(declare-const x Refnode2)
(declare-const q1 Refnode2)
(declare-const p1 Refnode2)
(declare-const self Refnode2)
(declare-const p Refnode2)

(assert 
		(and 
			(distinct (as nil Refnode2) yprm)
			(= next0 q)
			(= (as nil Refnode2) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode2) x)
			(= xprm self)
			(= q1 p)
		(sep 
			(dll_e1 yprm p1 )
			(dll q self )
			(pto xprm (c_node2 p yprm ))
		)

		)

)

(assert (not 
		(and 
			(distinct (as nil Refnode2) yprm)
			(= next0 q)
			(= (as nil Refnode2) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode2) x)
			(= xprm self)
			(= q1 p)
		(sep 
			(dll_e2 yprm p1 )
			(dll q self )
			(pto xprm (c_node2 p yprm ))
		)

		)

))

(check-sat)
