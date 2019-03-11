(set-logic QF_SHID)

(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

; Sorts for locations, one by cell sort
(declare-sort Refnode 0)

; Types of cells in the heap

(declare-datatypes (
	(node 0)
	) (
	((c_node (next Refnode) ))
	)
)

; Type of heap

(declare-heap (Refnode node) 
)
; User defined predicates
(define-funs-rec (
	(ll ((in Refnode)) Bool
	)

	(ll_e1 ((in Refnode)) Bool
	)

	(ll_e2 ((in Refnode)) Bool
	)

	(node_e1 ((in Refnode)(q Refnode)) Bool
	)
		)
		((or 
		(and 
			(= (as nil Refnode) in)
			(_ emp Refnode node)
		)

	(exists ((q_18 Refnode))
	 
		(sep 
			(pto in (c_node q_18 ))
			(ll q_18 )
		)

		)

	)
	(exists ((q Refnode))
	 
		(sep 
			(pto in (c_node q ))
			(ll q )
		)

		)

	(exists ((p Refnode)(q Refnode))
	 
		(and 
			(= p q)
		(sep 
			(pto in (c_node p ))
			(ll q )
		)

		)

		)

	(exists ((p Refnode))
	 
		(and 
			(= q p)
			(pto in (c_node p ))
		)

		)

		)
)


(check-sat) 
;; variables
(declare-const v1prm Refnode)
(declare-const xprm Refnode)
(declare-const yprm Refnode)
(declare-const y Refnode)
(declare-const x Refnode)
(declare-const q Refnode)

(assert 
		(and 
			(= v1prm q)
			(distinct (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode) x)
		(sep 
			(ll q )
			(ll y )
			(pto xprm (c_node q ))
		)

		)

)

(assert (not 
		(and 
			(= v1prm q)
			(distinct (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode) x)
			(distinct (as nil Refnode) v1prm)
		(sep 
			(ll v1prm )
			(ll yprm )
			(pto xprm (c_node q ))
		)

		)

))

(check-sat)
