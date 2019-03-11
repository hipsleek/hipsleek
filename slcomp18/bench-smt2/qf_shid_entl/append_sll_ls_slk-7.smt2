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

	(lseg ((in Refnode)(p Refnode)) Bool
	)

	(ll_e1 ((in Refnode)) Bool
	)

	(ll_e2 ((in Refnode)) Bool
	)

	(node_e1 ((in Refnode)(q Refnode)) Bool
	)

	(lseg_e1 ((in Refnode)(p Refnode)) Bool
	)
		)
		((or 
		(and 
			(= (as nil Refnode) in)
			(_ emp Refnode node)
		)

	(exists ((q_20 Refnode))
	 
		(sep 
			(pto in (c_node q_20 ))
			(ll q_20 )
		)

		)

	)
	(or 
		(and 
			(= in p)
			(_ emp Refnode node)
		)

	(exists ((p_19 Refnode)(q_18 Refnode))
	 
		(and 
			(= p p_19)
		(sep 
			(pto in (c_node q_18 ))
			(lseg q_18 p_19 )
		)

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

	(exists ((q Refnode))
	 
		(and 
			(= p q)
			(lseg in p )
		)

		)

		)
)


(check-sat) 
;; variables
(declare-const q Refnode)
(declare-const xprm Refnode)
(declare-const yprm Refnode)
(declare-const x Refnode)
(declare-const y Refnode)

(assert 
		(and 
			(distinct (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode) x)
		(sep 
			(pto xprm (c_node q ))
			(lseg q yprm )
		)

		)

)

(assert (not 
		(and 
			(distinct (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(distinct (as nil Refnode) x)
			(lseg_e1 x y )
		)

))

(check-sat)
