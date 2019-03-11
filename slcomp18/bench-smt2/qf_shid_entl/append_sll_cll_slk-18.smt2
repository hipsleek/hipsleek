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
	(lseg ((in Refnode)(p Refnode)) Bool
	)

	(ll ((in Refnode)) Bool
	)

	(clist ((in Refnode)) Bool
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
			(= in p)
			(_ emp Refnode node)
		)

	(exists ((p_21 Refnode)(q_20 Refnode))
	 
		(and 
			(= p p_21)
		(sep 
			(pto in (c_node q_20 ))
			(lseg q_20 p_21 )
		)

		)

		)

	)
	(or 
		(and 
			(= (as nil Refnode) in)
			(_ emp Refnode node)
		)

	(exists ((q_22 Refnode))
	 
		(sep 
			(pto in (c_node q_22 ))
			(ll q_22 )
		)

		)

	)
	(exists ((self_19 Refnode)(p_18 Refnode))
	 
		(and 
			(= in self_19)
		(sep 
			(pto in (c_node p_18 ))
			(lseg p_18 self_19 )
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
(declare-const next0 Refnode)
(declare-const q Refnode)
(declare-const xprm Refnode)
(declare-const yprm Refnode)
(declare-const y Refnode)
(declare-const x Refnode)

(assert 
		(and 
			(= next0 q)
			(= (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(= y x)
			(distinct (as nil Refnode) x)
		(sep 
			(ll q )
			(pto xprm (c_node yprm ))
		)

		)

)

(assert (not 
		(and 
			(= next0 q)
			(= (as nil Refnode) q)
			(= xprm x)
			(= yprm y)
			(= y x)
			(distinct (as nil Refnode) x)
		(sep 
			(clist x )
			(ll q )
		)

		)

))

(check-sat)
