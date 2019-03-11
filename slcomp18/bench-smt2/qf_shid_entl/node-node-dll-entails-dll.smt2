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
	(points_to ((a RefDLL_t)(b RefDLL_t)(c RefDLL_t)) Bool
	)

	(DLL_plus ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)
		)
		(
			(pto a (c_DLL_t c b ))
	(or 
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
		)
)


(check-sat) 
;; variables
(declare-const x RefDLL_t)
(declare-const c RefDLL_t)
(declare-const y RefDLL_t)
(declare-const a RefDLL_t)

(assert 
		(sep 
			(points_to x y (as nil RefDLL_t) )
			(points_to y a x )
			(DLL_plus a y c (as nil RefDLL_t) )
		)

)

(assert (not 
			(DLL_plus x (as nil RefDLL_t) c (as nil RefDLL_t) )
))

(check-sat)
