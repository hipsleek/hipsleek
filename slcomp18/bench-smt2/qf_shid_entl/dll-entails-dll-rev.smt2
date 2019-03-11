(set-logic QF_SHID)

(set-info :source | 
  R. Iosif, A. Rogalewicz and T. Vojnar. 
  Deciding Entailments in Inductive Separation Logic with Tree Automata arXiv:1402.2127. 
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/ 
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

; Sorts for locations, one by cell sort
(declare-sort RefDLL_t 0)

; Types of cells in the heap

(declare-datatypes (
	(DLL_t 0)
	) (
	((c_DLL_t (prev RefDLL_t) (next RefDLL_t) ))
	)
)

; Type of heap

(declare-heap (RefDLL_t DLL_t) 
)
; User defined predicates
(define-funs-rec (
	(DLL_plus ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)

	(DLL_plus_rev ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)
		)
		((or 
		(and 
			(= hd tl)
			(pto hd (c_DLL_t p n ))
		)

	(exists ((x RefDLL_t))
	 
		(sep 
			(pto hd (c_DLL_t p x ))
			(DLL_plus x hd tl n )
		)

		)

	)
	(or 
		(and 
			(= hd tl)
			(pto hd (c_DLL_t p n ))
		)

	(exists ((x RefDLL_t))
	 
		(sep 
			(pto tl (c_DLL_t x n ))
			(DLL_plus_rev hd p x tl )
		)

		)

	)
		)
)


(check-sat) 
;; variables
(declare-const x RefDLL_t)
(declare-const y RefDLL_t)

(assert 
			(DLL_plus x (as nil RefDLL_t) y (as nil RefDLL_t) )
)

(assert (not 
			(DLL_plus_rev x (as nil RefDLL_t) y (as nil RefDLL_t) )
))

(check-sat)
