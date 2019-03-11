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
	((c_Sll_t (next RefSll_t) (data Int) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)
; User defined predicate
(define-fun-rec sls ((in RefSll_t)(dt1 Int)(out RefSll_t)(dt2 Int)) Bool
	(or 
		(and 
			(= in out)
			(= dt1 dt2)
			(_ emp RefSll_t Sll_t)
		)

	(exists ((u RefSll_t)(dt3 Int))
	 
		(and 
			(< dt1 (+ dt3 0 ) )
		(sep 
			(pto in (c_Sll_t u dt1 ))
			(sls u dt3 out dt2 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x_emp RefSll_t)
(declare-const y_emp RefSll_t)
(declare-const w_emp RefSll_t)
(declare-const z_emp RefSll_t)
(declare-const d0 Int)
(declare-const d1 Int)
(declare-const d2 Int)

(assert 
		(and 
			(distinct d0 d1)
			(distinct d1 d2)
		(sep 
			(sls x_emp d0 z_emp d1 )
			(pto z_emp (c_Sll_t y_emp d1 ))
			(sls y_emp d1 w_emp d2 )
		)

		)

)

(check-sat)
