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

	(Q ((y1 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
	)

	(succ1circuit ((x1 RefGTyp)(y1 RefGTyp)) Bool
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
			(zero y1 )
	(exists ((x1 RefGTyp))
	 
		(sep 
			(succ1circuit x1 y1 )
			(Q x1 )
		)

		)

	)
	
		(sep 
			(one x1 )
			(Q x1 )
		)

	
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	
			(notg x1 y1 )
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

(assert 
			(P x0 )
)

(check-sat)
