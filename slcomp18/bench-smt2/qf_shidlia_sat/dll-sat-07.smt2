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
			(> x3 x5)
			(distinct E1 E3)
		(sep 
			(ldll E1 F1 x1 E3 F3 x3 )
			(ldll E2 F2 x2 E4 F4 x4 )
			(ldll E3 F3 x3 E4 F4 x4 )
			(ldll E4 F4 y4 E3 F3 y3 )
			(ldll E3 F3 x3 E5 F5 x5 )
			(ldll E5 F5 y5 E3 F3 y3 )
			(ldll E4 F4 x5 E6 F6 x6 )
		)

		)

)

(check-sat)
