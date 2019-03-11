(set-logic QF_SHLID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-18")

;; Doubly-linked lists

(declare-sort RefDll_t 0)

(declare-datatypes (
	(Dll_t 0)
	) (
	((c_Dll_t (next RefDll_t) (prev RefDll_t) ))
	)
)

(declare-heap (RefDll_t Dll_t) 
)

(define-fun-rec dll ((fr RefDll_t)(pr RefDll_t)(nx RefDll_t)(bk RefDll_t)) Bool
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
			(dll u fr nx bk )
		)

		)

		)

	)
)

(define-fun-rec R ((x RefDll_t) (y RefDll_t)) Bool
	(and (distinct x y)
	     (sep (dll x (as nil RefDll_t) (as nil RefDll_t) y)
	          (pto y (c_Dll_t (as nil RefDll_t) (as nil RefDll_t)))
	      )
	)
)

(check-sat) 
;; variables
(declare-const x0 RefDll_t)
(declare-const y0 RefDll_t)

(assert (R x0 y0)
)

(check-sat)
