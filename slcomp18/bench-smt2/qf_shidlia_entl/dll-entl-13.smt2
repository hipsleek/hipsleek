(set-logic QF_SHIDLIA)
(set-info :source |
  Zhilin Wu and Gao Chong.
  COMPSPEN benchmark.
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
(declare-const E7 RefDll_t)
(declare-const E8 RefDll_t)
(declare-const E9 RefDll_t)
(declare-const E1_prime RefDll_t)
(declare-const E2_prime RefDll_t)
(declare-const E3_prime RefDll_t)
(declare-const E4_prime RefDll_t)
(declare-const E5_prime RefDll_t)
(declare-const E6_prime RefDll_t)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x3_prime Int)
(declare-const x4_prime Int)
(declare-const x5_prime Int)

(assert 
		(and 
			(= E4_prime E7)
			(= E3_prime E8)
			(= E8 E9)
		(sep 
			(ldll E1 E1_prime x1 E3 E3_prime x3 )
			(ldll E2 E2_prime x2 E4 E4_prime x4 )
			(ldll E3 E3_prime x3 E4 E7 x4 )
			(ldll E4 E4_prime x4_prime E3 E8 x3_prime )
			(ldll E3 E3_prime x3 E5 E5_prime x5 )
			(ldll E5 E5_prime x5_prime E3 E9 x3_prime )
			(ldll E4 E4_prime x4 E6 E6_prime x6 )
		)

		)

)

(assert (not 
		(sep 
			(ldll E1 E1_prime x1 E3 E3_prime x3 )
			(ldll E2 E2_prime x2 E6 E6_prime x6 )
		)

))

(check-sat)
