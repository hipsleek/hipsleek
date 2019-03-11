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
(declare-sort RefDll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Dll_t 0)
	) (
	((c_Dll_t (next RefDll_t) (prev RefDll_t) ))
	)
)

; Type of heap

(declare-heap (RefDll_t Dll_t) 
)
; User defined predicate
(define-fun-rec ldll ((E RefDll_t)(P RefDll_t)(len1 Int)(F RefDll_t)(L RefDll_t)(len2 Int)) Bool
	(or 
		(and 
			(= E F)
			(= P L)
			(= len1 len2)
			(_ emp RefDll_t Dll_t)
		)

	(exists ((u RefDll_t)(len3 Int))
	 
		(and 
			(= len1 (+ len3 1 ) )
		(sep 
			(pto E (c_Dll_t u P ))
			(ldll u E len3 F L len2 )
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
(declare-const E1_p RefDll_t)
(declare-const E2_p RefDll_t)
(declare-const E3_p RefDll_t)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)

(assert 
		(and 
			(= x1 (+ x2 1 ) )
		(sep 
			(ldll E1 E1_p x1 E2 E2_p x2 )
			(pto E2 (c_Dll_t E3 E2_p ))
			(ldll E2 E2_p x2 E3 E3_p x3 )
		)

		)

)

(assert (not 
			(ldll E1 E1_p x1 E3 E3_p x3 )
))

(check-sat)
