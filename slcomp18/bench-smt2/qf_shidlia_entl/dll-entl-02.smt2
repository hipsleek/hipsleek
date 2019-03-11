(set-logic QF_SHIDLIA)
(set-info :source |
  Zhilin Wu and Chong Gao.
  COMSPEN benchmark.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-07-07")

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
(declare-const E1 RefDll_t)
(declare-const E2 RefDll_t)
(declare-const E3 RefDll_t)
(declare-const E4 RefDll_t)
(declare-const E5 RefDll_t)
(declare-const E6 RefDll_t)
(declare-const F1 RefDll_t)
(declare-const F2 RefDll_t)
(declare-const F3 RefDll_t)
(declare-const F4 RefDll_t)
(declare-const F5 RefDll_t)
(declare-const F6 RefDll_t)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const y3 Int)
(declare-const y4 Int)
(declare-const y5 Int)

(assert 
		(and 
			(= x4 x5)
			(= x4 y4)
			(= x3 y3)
		(sep 
			(sdll E1 F1 x1 E3 F3 x3 )
			(sdll E2 F2 x2 E4 F4 x4 )
			(sdll E3 F3 x3 E4 F4 x4 )
			(sdll E4 F4 y4 E3 F3 y3 )
			(sdll E3 F3 x3 E5 F5 x5 )
			(sdll E5 F5 y5 E3 F3 y3 )
			(sdll E4 F4 x5 E6 F6 x6 )
		)

		)

)

(assert (not 
		(sep 
			(sdll E1 F1 x1 E3 F3 x3 )
			(sdll E2 F2 x2 E6 F6 x6 )
		)

))

(check-sat)
