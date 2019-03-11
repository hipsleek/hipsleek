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
			(> dt1 (+ dt3 1 ) )
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
(declare-const X RefSll_t)
(declare-const Y0 RefSll_t)
(declare-const Y1 RefSll_t)
(declare-const Z RefSll_t)
(declare-const a Int)
(declare-const b0 Int)
(declare-const b1 Int)
(declare-const c Int)

(assert 
		(and 
			(> a b0)
			(> b1 c)
			(> b0 b1)
		(sep 
			(sls X a Y0 b0 )
			(pto Y0 (c_Sll_t Y1 b0 ))
			(sls Y1 b1 Z c )
		)

		)

)

(assert (not 
		(and 
			(> a (+ c 3 ) )
			(sls X a Z c )
		)

))

(check-sat)
