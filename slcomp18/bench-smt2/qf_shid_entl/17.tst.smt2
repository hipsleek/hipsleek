(set-logic QF_SHID)

(set-info :source |
  James Brotherston, Nikos Gorogiannis, and Rasmus Petersen
  A Generic Cyclic Theorem Prover. APLAS, 2012.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2014-05-31")

; Sorts for locations, one by cell sort
(declare-sort RefGTyp 0)

; Types of cells in the heap

(declare-datatypes (
	(GTyp 0)
	) (
	((c_GTyp (f0 RefGTyp) (f1 RefGTyp) ))
	)
)

; Type of heap

(declare-heap (RefGTyp GTyp) 
)
; User defined predicates
(define-funs-rec (
	(BinTree ((x RefGTyp)) Bool
	)

	(BinTreeSeg ((x RefGTyp)(y RefGTyp)) Bool
	)
	)
	((or 
			(_ emp RefGTyp GTyp)
		(exists ((yp RefGTyp)(xp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp yp xp ))
			(BinTree yp )
			(BinTree xp )
		)

		)

		)

	)(or 
		(and 
			(= x y)
			(_ emp RefGTyp GTyp)
		)

		(exists ((xp RefGTyp)(yp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp xp yp ))
			(BinTreeSeg xp y )
			(BinTree yp )
		)

		)

		)

		(exists ((xp RefGTyp)(yp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp xp yp ))
			(BinTree xp )
			(BinTreeSeg yp y )
		)

		)

		)

	)	)
)


(check-sat) 
;; variables
(declare-const x RefGTyp)
(declare-const y RefGTyp)
(declare-const z RefGTyp)

(assert 
		(sep 
			(BinTreeSeg x z )
			(BinTreeSeg z y )
		)

)

(assert (not 
			(BinTreeSeg x y )
))

(check-sat)
