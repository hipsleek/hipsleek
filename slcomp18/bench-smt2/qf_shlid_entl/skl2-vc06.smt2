(set-logic QF_SHLID)

(set-info :source |
Quang Loc Le Q.Le@tees.ac.uk
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-15")



; Sorts for locations, one by cell sort
(declare-sort RefSL2_t 0)

; Types of cells in the heap

(declare-datatypes (
	(SL2_t 0)
	) (
	((c_SL2_t (n1 RefSL2_t) (n2 RefSL2_t) ))
	)
)

; Type of heap

(declare-heap (RefSL2_t SL2_t) 
)

(define-fun-rec skl1 ((hd RefSL2_t)(ex RefSL2_t)) Bool
	(or 
		(and 
			(= hd ex)
			(_ emp RefSL2_t SL2_t)
		)

		(exists ((tl RefSL2_t))
	 
		(and 
			(distinct hd ex)
		(sep 
			(pto hd (c_SL2_t tl (as nil RefSL2_t) ))
			(skl1 tl ex )
		)

		)

		)

	)
)

(define-fun-rec skl2 ((hd RefSL2_t)(ex RefSL2_t)) Bool
	(or 
		(and 
			(= hd ex)
			(_ emp RefSL2_t SL2_t)
		)

		(exists ((tl RefSL2_t)(Z1 RefSL2_t))
	 
		(and 
			(distinct hd ex)
		(sep 
			(pto hd (c_SL2_t Z1 tl ))
			(skl1 Z1 tl )
			(skl2 tl ex )
		)

		)

		)

	)
)


(check-sat) 
;; variables
(declare-const x1 RefSL2_t)
(declare-const x1_1 RefSL2_t)
(declare-const x1_2 RefSL2_t)
(declare-const x1_3 RefSL2_t)
(declare-const x1_4 RefSL2_t)
(declare-const x2 RefSL2_t)
(declare-const x3 RefSL2_t)
(declare-const x3_1 RefSL2_t)
(declare-const x3_2 RefSL2_t)
(declare-const x4 RefSL2_t)
(declare-const x5 RefSL2_t)
(declare-const x6 RefSL2_t)

(assert 
		(sep 
			(skl2 x4 x5 )
			(pto x5 (c_SL2_t x6 x6 ))
			(pto x1 (c_SL2_t x1_1 x2 ))
			(pto x1_1 (c_SL2_t x1_2 (as nil RefSL2_t) ))
			(skl1 x1_2 x2 )
			(pto x2 (c_SL2_t (as nil RefSL2_t) (as nil RefSL2_t) ))
		)

)

(assert (not 
		(sep
			(skl2 x1 (as nil RefSL2_t) )
			(skl2 x4 x6)
		)
))

(check-sat)
