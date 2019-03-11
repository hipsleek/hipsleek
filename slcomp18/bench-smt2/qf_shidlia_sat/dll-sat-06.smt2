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
	((c_Dll_t (next RefDll_t) (prev RefDll_t) (data Int) ))
	)
)

; Type of heap

(declare-heap (RefDll_t Dll_t) 
)
; User defined predicate
(define-fun-rec lsdll ((E RefDll_t)(P RefDll_t)(dt1 Int)(len1 Int)(F RefDll_t)(L RefDll_t)(dt2 Int)(len2 Int)) Bool
	(or 
		(and 
			(= E F)
			(= P L)
			(= dt1 dt2)
			(= len1 len2)
			(_ emp RefDll_t Dll_t)
		)

	(exists ((u RefDll_t)(dt3 Int)(len3 Int))
	 
		(and 
			(> dt1 (+ dt3 1 ) )
			(= len1 (+ len3 1 ) )
		(sep 
			(pto E (c_Dll_t u P dt1 ))
			(lsdll u E dt3 len3 F L dt2 len2 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x1 RefDll_t)
(declare-const x2 RefDll_t)
(declare-const x3 RefDll_t)
(declare-const x4 RefDll_t)
(declare-const y1 RefDll_t)
(declare-const y2 RefDll_t)
(declare-const y3 RefDll_t)
(declare-const y4 RefDll_t)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const d3 Int)
(declare-const d4 Int)
(declare-const n1 Int)
(declare-const n2 Int)
(declare-const n3 Int)
(declare-const n4 Int)

(assert 
		(and 
			(= n2 (+ n3 1 ) )
			(> n2 (+ n4 1 ) )
			(distinct d1 d2)
			(= x4 y1)
		(sep 
			(lsdll x1 x2 d1 n1 y1 y2 d2 n2 )
			(pto y1 (c_Dll_t x3 y2 d2 ))
			(lsdll x3 x4 d3 n3 y3 y4 d4 n4 )
		)

		)

)

(check-sat)
