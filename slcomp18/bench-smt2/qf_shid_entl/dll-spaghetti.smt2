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
	(DLL ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)

	(DLL_plus ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)

	(DLL_plus_rev ((hd RefDLL_t)(p RefDLL_t)(tl RefDLL_t)(n RefDLL_t)) Bool
	)
		)
		((or 
		(and 
			(= p tl)
			(= hd n)
			(_ emp RefDLL_t DLL_t)
		)

	(exists ((x RefDLL_t))
	 
		(sep 
			(pto hd (c_DLL_t p x ))
			(DLL x hd tl n )
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
(declare-const hd0 RefDLL_t)
(declare-const tl0 RefDLL_t)
(declare-const hd1 RefDLL_t)
(declare-const tl1 RefDLL_t)
(declare-const hd2 RefDLL_t)
(declare-const tl2 RefDLL_t)
(declare-const hd3 RefDLL_t)
(declare-const tl3 RefDLL_t)
(declare-const hd4 RefDLL_t)
(declare-const tl4 RefDLL_t)
(declare-const hd5 RefDLL_t)
(declare-const tl5 RefDLL_t)
(declare-const hd6 RefDLL_t)
(declare-const tl6 RefDLL_t)
(declare-const hd7 RefDLL_t)
(declare-const tl7 RefDLL_t)
(declare-const hd8 RefDLL_t)
(declare-const tl8 RefDLL_t)
(declare-const hd9 RefDLL_t)
(declare-const tl9 RefDLL_t)
(declare-const hd10 RefDLL_t)
(declare-const tl10 RefDLL_t)
(declare-const hd11 RefDLL_t)
(declare-const tl11 RefDLL_t)
(declare-const hd12 RefDLL_t)
(declare-const tl12 RefDLL_t)
(declare-const hd13 RefDLL_t)
(declare-const tl13 RefDLL_t)
(declare-const hd14 RefDLL_t)
(declare-const tl14 RefDLL_t)
(declare-const hd15 RefDLL_t)
(declare-const tl15 RefDLL_t)
(declare-const hd16 RefDLL_t)
(declare-const tl16 RefDLL_t)
(declare-const hd17 RefDLL_t)
(declare-const tl17 RefDLL_t)
(declare-const hd18 RefDLL_t)
(declare-const tl18 RefDLL_t)
(declare-const hd19 RefDLL_t)
(declare-const tl19 RefDLL_t)
(declare-const hd20 RefDLL_t)
(declare-const tl20 RefDLL_t)

(assert 
		(sep 
			(DLL_plus hd0 (as nil RefDLL_t) tl0 hd1 )
			(DLL_plus hd1 tl0 tl1 hd2 )
			(DLL_plus hd2 tl1 tl2 hd3 )
			(DLL_plus hd3 tl2 tl3 hd4 )
			(DLL_plus hd4 tl3 tl4 hd5 )
			(DLL_plus hd5 tl4 tl5 hd6 )
			(DLL_plus hd6 tl5 tl6 hd7 )
			(DLL_plus hd7 tl6 tl7 hd8 )
			(DLL_plus hd8 tl7 tl8 hd9 )
			(DLL_plus hd9 tl8 tl9 hd10 )
			(DLL_plus hd10 tl9 tl10 hd11 )
			(DLL_plus hd11 tl10 tl11 hd12 )
			(DLL_plus hd12 tl11 tl12 hd13 )
			(DLL_plus hd13 tl12 tl13 hd14 )
			(DLL_plus hd14 tl13 tl14 hd15 )
			(DLL_plus hd15 tl14 tl15 hd16 )
			(DLL_plus hd16 tl15 tl16 hd17 )
			(DLL_plus hd17 tl16 tl17 hd18 )
			(DLL_plus hd18 tl17 tl18 hd19 )
			(DLL_plus hd19 tl18 tl19 hd20 )
			(DLL_plus hd20 tl19 tl20 (as nil RefDLL_t) )
		)

)

(assert (not 
		(sep 
			(DLL_plus_rev hd0 (as nil RefDLL_t) tl0 hd1 )
			(DLL_plus_rev hd1 tl0 tl1 hd2 )
			(DLL_plus_rev hd2 tl1 tl2 hd3 )
			(DLL_plus_rev hd3 tl2 tl3 hd4 )
			(DLL_plus_rev hd4 tl3 tl4 hd5 )
			(DLL_plus_rev hd5 tl4 tl5 hd6 )
			(DLL_plus_rev hd6 tl5 tl6 hd7 )
			(DLL_plus_rev hd7 tl6 tl7 hd8 )
			(DLL_plus_rev hd8 tl7 tl8 hd9 )
			(DLL_plus_rev hd9 tl8 tl9 hd10 )
			(DLL_plus_rev hd10 tl9 tl10 hd11 )
			(DLL_plus hd11 tl10 tl11 hd12 )
			(DLL_plus hd12 tl11 tl12 hd13 )
			(DLL_plus hd13 tl12 tl13 hd14 )
			(DLL_plus hd14 tl13 tl14 hd15 )
			(DLL_plus hd15 tl14 tl15 hd16 )
			(DLL_plus hd16 tl15 tl16 hd17 )
			(DLL_plus hd17 tl16 tl17 hd18 )
			(DLL_plus hd18 tl17 tl18 hd19 )
			(DLL_plus hd19 tl18 tl19 hd20 )
			(DLL_plus hd20 tl19 tl20 (as nil RefDLL_t) )
		)

))

(check-sat)
