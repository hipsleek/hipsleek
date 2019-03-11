(set-logic QF_SHID)

(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Perez.
  A decision procedure for satisfiability in ssssseparation logic with inductive
  predicates. CSL-LICS, 2014.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

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
; User defined predicates
(define-funs-rec (
	(ListE ((x RefGTyp)(y RefGTyp)) Bool
	)

	(ListO ((x RefGTyp)(y RefGTyp)) Bool
	)

	(ListX ((x RefGTyp)(y RefGTyp)) Bool
	)

	(List ((x RefGTyp)(y RefGTyp)) Bool
	)
		)
		((exists ((xp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp xp ))
			(ListO xp y )
		)

		)

		)

	(or 
		(and 
			(distinct (as nil RefGTyp) x)
			(pto x (c_GTyp y ))
		)

	(exists ((xp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp xp ))
			(ListE xp y )
		)

		)

		)

	)
	(or 
			(ListO x y )
	
			(ListE x y )
	)
	(or 
		(and 
			(distinct (as nil RefGTyp) x)
			(pto x (c_GTyp y ))
		)

	(exists ((xp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp xp ))
			(List xp y )
		)

		)

		)

	)
		)
)


(check-sat) 
;; variables
(declare-const x RefGTyp)
(declare-const y RefGTyp)

(assert 
			(ListX x y )
)

(assert (not 
			(List x y )
))

(check-sat)
