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
	((c_GTyp (f0 RefGTyp) ))
	)
)

; Type of heap

(declare-heap (RefGTyp GTyp) 
)
; User defined predicate
(define-fun-rec ls ((x RefGTyp)(y RefGTyp)) Bool
	(or 
		(and 
			(= x y)
			(_ emp RefGTyp GTyp)
		)

	(exists ((xp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
			(distinct x y)
		(sep 
			(pto x (c_GTyp xp ))
			(ls xp y )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x RefGTyp)
(declare-const y RefGTyp)
(declare-const z RefGTyp)

(assert 
		(sep 
			(ls x y )
			(pto y (c_GTyp z ))
			(ls z (as nil RefGTyp) )
		)

)

(assert (not 
		(sep 
			(ls x z )
			(ls z (as nil RefGTyp) )
		)

))

(check-sat)
