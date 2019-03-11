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
(declare-const x1 RefDll_t)
(declare-const x2 RefDll_t)
(declare-const y0 RefDll_t)
(declare-const y1 RefDll_t)
(declare-const y2 RefDll_t)
(declare-const z RefDll_t)
(declare-const n1 Int)
(declare-const n2 Int)

(assert 
		(and 
			(> n1 n2)
		(sep 
			(pto y2 (c_Dll_t x1 y0 ))
			(ldll x1 x2 n1 y1 y2 n2 )
		)

		)

)

(check-sat)
