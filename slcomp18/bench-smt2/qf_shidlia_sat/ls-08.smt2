(set-logic QF_SHIDLIA)
(set-info :source |
  Quang Loc Le.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-22")


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
(define-fun-rec ls ((in RefSll_t)(len1 Int)) Bool
	(or 
		(and 
			(= in (as nil RefSll_t))
			(= len1 0)
			(_ emp RefSll_t Sll_t)
		)

	(exists ((u RefSll_t)(len3 Int))
	 
		(and 
			(= len1 (+ len3 1 ) )
		(sep 
			(pto in (c_Sll_t u ))
			(ls u len3 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const u_emp RefSll_t)
(declare-const n1 Int)

(assert 
		(and 
			(> n1 32000 )
			(ls u_emp n1)
		)

)

(check-sat)
