(set-logic QF_SHLID)

(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


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

(assert 
		(sep 
			(pto x1 (c_SL2_t x1_1 x2 ))
			(pto x1_1 (c_SL2_t x1_2 (as nil RefSL2_t) ))
			(pto x1_2 (c_SL2_t x1_3 (as nil RefSL2_t) ))
			(pto x1_3 (c_SL2_t x1_4 (as nil RefSL2_t) ))
			(pto x1_4 (c_SL2_t x2 (as nil RefSL2_t) ))
			(skl2 x2 x3 )
			(pto x3 (c_SL2_t x3_1 (as nil RefSL2_t) ))
			(pto x3_1 (c_SL2_t x3_2 (as nil RefSL2_t) ))
			(pto x3_2 (c_SL2_t (as nil RefSL2_t) (as nil RefSL2_t) ))
		)

)

(assert (not 
			(skl2 x1 (as nil RefSL2_t) )
))

(check-sat)
