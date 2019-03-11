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
(declare-sort RefDll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Dll_t 0)
	) (
	((c_Dll_t (next RefDll_t) (prev RefDll_t) (data Int) ))
	)
)

; Type of heap

(declare-heap (RefDll_t Dll_t) 
)
; User defined predicate
(define-fun-rec sdll ((E RefDll_t)(P RefDll_t)(dt1 Int)(F RefDll_t)(L RefDll_t)(dt2 Int)) Bool
	(or 
		(and 
			(= E F)
			(= P L)
			(= dt1 dt2)
			(_ emp RefDll_t Dll_t)
		)

	(exists ((u RefDll_t)(dt3 Int))
	 
		(and 
			(> dt1 (+ dt3 1 ) )
		(sep 
			(pto E (c_Dll_t u P dt1 ))
			(sdll u E dt3 F L dt2 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x1 RefDll_t)
(declare-const x2 RefDll_t)
(declare-const y0 RefDll_t)
(declare-const y1 RefDll_t)
(declare-const y2 RefDll_t)
(declare-const z RefDll_t)
(declare-const d1 Int)
(declare-const d2 Int)

(assert 
		(and 
			(> d1 (+ d2 3 ) )
		(sep 
			(pto y2 (c_Dll_t x1 y0 d2 ))
			(sdll x1 x2 d1 y1 y2 d2 )
		)

		)

)

(check-sat)
