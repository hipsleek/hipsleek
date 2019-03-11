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
	((c_node (nxt Refnode) ))
	)
)

; Type of heap

(declare-heap (Refnode node) 
)
; User defined predicates
(define-funs-rec (
	(lseg ((in Refnode)(p Refnode)) Bool
	)

	(right1 ((in Refnode)(p Refnode)) Bool
	)

	(right2 ((in Refnode)(p Refnode)) Bool
	)

	(right3 ((in Refnode)(p Refnode)) Bool
	)

	(right4 ((in Refnode)) Bool
	)

	(right5 ((in Refnode)) Bool
	)
		)
		((or 
		(and 
			(= in p)
			(_ emp Refnode node)
		)

	(exists ((a Refnode))
	 
		(sep 
			(pto in (c_node a ))
			(lseg a p )
		)

		)

	)
	(exists ((u Refnode))
	 
		(sep 
			(lseg in u )
			(pto u (c_node p ))
		)

		)

	(exists ((u Refnode))
	 
		(sep 
			(lseg in u )
			(lseg u p )
		)

		)

	(exists ((u Refnode)(u2 Refnode))
	 
		(sep 
			(lseg in u )
			(lseg u u2 )
			(lseg u2 p )
		)

		)

	(exists ((u Refnode)(w Refnode))
	 
		(sep 
			(lseg in u )
			(lseg u w )
		)

		)

	(exists ((w Refnode))
	 
			(lseg in w )
		)

		)
)


(check-sat) 
;; variables
(declare-const x Refnode)
(declare-const p Refnode)

(assert 
			(lseg x p )
)

(assert (not 
			(right2 x p )
))

(check-sat)
