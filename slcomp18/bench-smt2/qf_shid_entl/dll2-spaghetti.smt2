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
(declare-const hd0 RefDLL2_t)
(declare-const tl0 RefDLL2_t)
(declare-const hd1 RefDLL2_t)
(declare-const tl1 RefDLL2_t)
(declare-const hd2 RefDLL2_t)
(declare-const tl2 RefDLL2_t)
(declare-const hd3 RefDLL2_t)
(declare-const tl3 RefDLL2_t)
(declare-const hd4 RefDLL2_t)
(declare-const tl4 RefDLL2_t)
(declare-const hd5 RefDLL2_t)
(declare-const tl5 RefDLL2_t)
(declare-const hd6 RefDLL2_t)
(declare-const tl6 RefDLL2_t)
(declare-const hd7 RefDLL2_t)
(declare-const tl7 RefDLL2_t)
(declare-const hd8 RefDLL2_t)
(declare-const tl8 RefDLL2_t)
(declare-const hd9 RefDLL2_t)
(declare-const tl9 RefDLL2_t)
(declare-const hd10 RefDLL2_t)
(declare-const tl10 RefDLL2_t)
(declare-const hd11 RefDLL2_t)
(declare-const tl11 RefDLL2_t)
(declare-const hd12 RefDLL2_t)
(declare-const tl12 RefDLL2_t)
(declare-const hd13 RefDLL2_t)
(declare-const tl13 RefDLL2_t)
(declare-const hd14 RefDLL2_t)
(declare-const tl14 RefDLL2_t)
(declare-const hd15 RefDLL2_t)
(declare-const tl15 RefDLL2_t)
(declare-const hd16 RefDLL2_t)
(declare-const tl16 RefDLL2_t)
(declare-const hd17 RefDLL2_t)
(declare-const tl17 RefDLL2_t)
(declare-const hd18 RefDLL2_t)
(declare-const tl18 RefDLL2_t)
(declare-const hd19 RefDLL2_t)
(declare-const tl19 RefDLL2_t)
(declare-const hd20 RefDLL2_t)
(declare-const tl20 RefDLL2_t)

(assert 
		(sep 
			(DLL2_plus hd0 (as nil RefDLL2_t) tl0 hd1 )
			(DLL2_plus hd1 tl0 tl1 hd2 )
			(DLL2_plus hd2 tl1 tl2 hd3 )
			(DLL2_plus hd3 tl2 tl3 hd4 )
			(DLL2_plus hd4 tl3 tl4 hd5 )
			(DLL2_plus hd5 tl4 tl5 hd6 )
			(DLL2_plus hd6 tl5 tl6 hd7 )
			(DLL2_plus hd7 tl6 tl7 hd8 )
			(DLL2_plus hd8 tl7 tl8 hd9 )
			(DLL2_plus hd9 tl8 tl9 hd10 )
			(DLL2_plus hd10 tl9 tl10 hd11 )
			(DLL2_plus hd11 tl10 tl11 hd12 )
			(DLL2_plus hd12 tl11 tl12 hd13 )
			(DLL2_plus hd13 tl12 tl13 hd14 )
			(DLL2_plus hd14 tl13 tl14 hd15 )
			(DLL2_plus hd15 tl14 tl15 hd16 )
			(DLL2_plus hd16 tl15 tl16 hd17 )
			(DLL2_plus hd17 tl16 tl17 hd18 )
			(DLL2_plus hd18 tl17 tl18 hd19 )
			(DLL2_plus hd19 tl18 tl19 hd20 )
			(DLL2_plus hd20 tl19 tl20 (as nil RefDLL2_t) )
		)

)

(assert (not 
		(sep 
			(DLL2_plus_rev hd0 (as nil RefDLL2_t) tl0 hd1 )
			(DLL2_plus_rev hd1 tl0 tl1 hd2 )
			(DLL2_plus_rev hd2 tl1 tl2 hd3 )
			(DLL2_plus_rev hd3 tl2 tl3 hd4 )
			(DLL2_plus_rev hd4 tl3 tl4 hd5 )
			(DLL2_plus_rev hd5 tl4 tl5 hd6 )
			(DLL2_plus_rev hd6 tl5 tl6 hd7 )
			(DLL2_plus_rev hd7 tl6 tl7 hd8 )
			(DLL2_plus_rev hd8 tl7 tl8 hd9 )
			(DLL2_plus_rev hd9 tl8 tl9 hd10 )
			(DLL2_plus_rev hd10 tl9 tl10 hd11 )
			(DLL2_plus_rev hd11 tl10 tl11 hd12 )
			(DLL2_plus_rev hd12 tl11 tl12 hd13 )
			(DLL2_plus_rev hd13 tl12 tl13 hd14 )
			(DLL2_plus_rev hd14 tl13 tl14 hd15 )
			(DLL2_plus_rev hd15 tl14 tl15 hd16 )
			(DLL2_plus_rev hd16 tl15 tl16 hd17 )
			(DLL2_plus_rev hd17 tl16 tl17 hd18 )
			(DLL2_plus_rev hd18 tl17 tl18 hd19 )
			(DLL2_plus_rev hd19 tl18 tl19 hd20 )
			(DLL2_plus_rev hd20 tl19 tl20 (as nil RefDLL2_t) )
		)

))

(check-sat)
