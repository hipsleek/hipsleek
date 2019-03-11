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
(declare-sort RefDLL2_t 0)

; Types of cells in the heap

(declare-datatypes (
	(DLL2_t 0)
	) (
	((c_DLL2_t (prev RefDLL2_t) (next RefDLL2_t) (prev2 RefDLL2_t) (next2 RefDLL2_t) (down RefDLL2_t) ))
	)
)

; Type of heap

(declare-heap (RefDLL2_t DLL2_t) 
)
; User defined predicates
(define-funs-rec (
	(DLL1_plus ((hd RefDLL2_t)(p RefDLL2_t)) Bool
	)

	(DLL2_plus ((hd RefDLL2_t)(p RefDLL2_t)(tl RefDLL2_t)(n RefDLL2_t)) Bool
	)

	(DLL2_plus_rev ((hd RefDLL2_t)(p RefDLL2_t)(tl RefDLL2_t)(n RefDLL2_t)) Bool
	)
		)
		((or 
			(pto hd (c_DLL2_t p (as nil RefDLL2_t) (as nil RefDLL2_t) (as nil RefDLL2_t) (as nil RefDLL2_t) ))
	(exists ((x RefDLL2_t))
	 
		(sep 
			(pto hd (c_DLL2_t p x (as nil RefDLL2_t) (as nil RefDLL2_t) (as nil RefDLL2_t) ))
			(DLL1_plus x hd )
		)

		)

	)
	(or (exists ((down_hd RefDLL2_t))
	 
		(and 
			(= hd tl)
		(sep 
			(pto hd (c_DLL2_t (as nil RefDLL2_t) (as nil RefDLL2_t) p n down_hd ))
			(DLL1_plus down_hd hd )
		)

		)

		)

	(exists ((x RefDLL2_t)(down_hd RefDLL2_t))
	 
		(sep 
			(pto hd (c_DLL2_t (as nil RefDLL2_t) (as nil RefDLL2_t) p x down_hd ))
			(DLL1_plus down_hd hd )
			(DLL2_plus x hd tl n )
		)

		)

	)
	(or (exists ((down_hd RefDLL2_t))
	 
		(and 
			(= hd tl)
		(sep 
			(pto hd (c_DLL2_t (as nil RefDLL2_t) (as nil RefDLL2_t) p n down_hd ))
			(DLL1_plus down_hd hd )
		)

		)

		)

	(exists ((x RefDLL2_t)(down_hd RefDLL2_t))
	 
		(sep 
			(pto tl (c_DLL2_t (as nil RefDLL2_t) (as nil RefDLL2_t) x n down_hd ))
			(DLL1_plus down_hd tl )
			(DLL2_plus_rev hd p x tl )
		)

		)

	)
		)
)


(check-sat) 
;; variables
(declare-const x RefDLL2_t)
(declare-const y RefDLL2_t)
(declare-const u RefDLL2_t)
(declare-const v RefDLL2_t)

(assert 
			(DLL2_plus x y u v )
)

(assert (not 
			(DLL2_plus_rev x y u v )
))

(check-sat)
