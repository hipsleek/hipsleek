(set-logic QF_SHID)

(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez. 
  A decision procedure for satisfiability in separation logic with inductive 
  predicates. CSL-LICS, 2014. 
  https://github.com/ngorogiannis/cyclist/releases/tag/CSL-LICS14
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
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
	(one ((x RefGTyp)) Bool
	)

	(Q ((y1 RefGTyp)(y2 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)(x2 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
	)

	(succ2circuit ((x1 RefGTyp)(x2 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)) Bool
	)

	(notg ((x RefGTyp)(y RefGTyp)) Bool
	)

	(xorg ((x RefGTyp)(y RefGTyp)(z RefGTyp)) Bool
	)

	(andg ((x RefGTyp)(y RefGTyp)(z RefGTyp)) Bool
	)
		)
		(
		(and 
			(distinct (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	(or 
		(sep 
			(zero y1 )
			(zero y2 )
		)

	(exists ((x1 RefGTyp)(x2 RefGTyp))
	 
		(sep 
			(succ2circuit x1 x2 y1 y2 )
			(Q x1 x2 )
		)

		)

	)
	
		(sep 
			(one x1 )
			(one x2 )
			(Q x1 x2 )
		)

	
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	
		(sep 
			(notg x1 y1 )
			(xorg x1 x2 y2 )
		)

	(or 
		(sep 
			(zero x )
			(one y )
		)

	
		(sep 
			(one x )
			(zero y )
		)

	)
	(or 
		(sep 
			(zero x )
			(zero y )
			(zero z )
		)

	
		(sep 
			(zero x )
			(one y )
			(one z )
		)

	
		(sep 
			(one x )
			(zero y )
			(one z )
		)

	
		(sep 
			(one x )
			(one y )
			(zero z )
		)

	)
	(or 
		(sep 
			(zero x )
			(zero z )
		)

	
		(sep 
			(zero y )
			(zero z )
		)

	
		(sep 
			(one x )
			(one y )
			(one z )
		)

	)
		)
)


(check-sat) 
;; variables
(declare-const x0 RefGTyp)
(declare-const x1 RefGTyp)

(assert 
			(P x0 x1 )
)

(check-sat)
