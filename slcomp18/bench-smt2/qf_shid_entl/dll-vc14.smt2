(set-logic QF_SHID)

(set-info :source |
Quang Loc Le Q.Le@tees.ac.uk
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-15")

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

(define-fun-rec dll ((fr RefDll_t)(bk RefDll_t)(pr RefDll_t)(nx RefDll_t)) Bool
	(or 
		(and 
			(= fr nx)
			(= bk pr)
			(_ emp RefDll_t Dll_t)
		)

		(exists ((u RefDll_t))
	 
		(and 
			(distinct fr nx)
			(distinct bk pr)
		(sep 
			(pto fr (c_Dll_t u pr ))
			(dll u bk fr nx )
		)

		)

		)

	)
)


(check-sat) 
;; variables
(declare-const x_emp RefDll_t)
(declare-const y_emp RefDll_t)
(declare-const z_emp RefDll_t)


(assert
		(and 
			(distinct y_emp z_emp)
			(distinct x_emp (as nil RefDll_t))
			(distinct y_emp (as nil RefDll_t))
			(distinct x_emp y_emp)
		(sep 
			(pto x_emp (c_Dll_t y_emp (as nil RefDll_t) ))
			(pto y_emp (c_Dll_t z_emp x_emp ))
		)

		)	
)

(assert (not 
		(and 
			(distinct x_emp z_emp)
			(dll x_emp y_emp (as nil RefDll_t) z_emp )
		)

))

(check-sat)
