(set-logic QF_SHID)

(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2014-05-28")

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
(declare-const w_emp RefDll_t)
(declare-const y_emp RefDll_t)
(declare-const u_emp RefDll_t)

(assert 
		(and 
			(distinct x_emp w_emp)
		(sep 
			(pto x_emp (c_Dll_t w_emp (as nil RefDll_t) ))
			(dll w_emp u_emp x_emp y_emp )
			(pto y_emp (c_Dll_t (as nil RefDll_t) u_emp ))
		)

		)

)

(assert (not 
			(dll x_emp y_emp (as nil RefDll_t) (as nil RefDll_t) )
))

(check-sat)
