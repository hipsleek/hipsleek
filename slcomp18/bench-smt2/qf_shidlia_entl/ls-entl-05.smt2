(set-logic QF_SHIDLIA)
(set-info :source |
  Zhilin Wu.
  COMPSPEN benchmark.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-21")


; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next RefSll_t) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)
; User defined predicate
(define-fun-rec lls ((in RefSll_t)(len1 Int)(out RefSll_t)(len2 Int)) Bool
	(or 
		(and 
			(= in out)
			(= len1 len2)
			(_ emp RefSll_t Sll_t)
		)

	(exists ((u RefSll_t)(len3 Int))
	 
		(and 
			(= len1 (+ len3 1 ) )
		(sep 
			(pto in (c_Sll_t u ))
			(lls u len3 out len2 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const X RefSll_t)
(declare-const Y RefSll_t)
(declare-const Z RefSll_t)
(declare-const n0 Int)
(declare-const n1 Int)
(declare-const n2 Int)

(assert 
		(and 
			(= n0 (+ n1 2 ) )
			(= n1 (+ n2 1 ) )
		(sep 
			(lls X n0 Y n1 )
			(lls Y n1 Z n2 )
		)

		)

)

(assert (not 
		(and 
			(= n0 (+ n2 3 ) )
			(lls X n0 Z n2 )
		)

))

(check-sat)
