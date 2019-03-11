(set-logic QF_SHIDLIA)
(set-info :source |
  Zhilin Wu.
  COMPSPEN benchmark.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
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
(declare-const y_emp RefSll_t)
(declare-const w_emp RefSll_t)
(declare-const z_emp RefSll_t)
(declare-const n1 Int)
(declare-const n2 Int)

(assert 
		(sep 
			(pto y_emp (c_Sll_t z_emp ))
			(lls y_emp n1 w_emp n2 )
		)

)

(check-sat)
