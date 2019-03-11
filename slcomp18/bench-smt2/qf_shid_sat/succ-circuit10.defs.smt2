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

	(Q ((y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
	)

	(succ10circuit ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)) Bool
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
			(zero y3 )
			(zero y4 )
			(zero y5 )
			(zero y6 )
			(zero y7 )
			(zero y8 )
			(zero y9 )
			(zero y10 )
		)

	(exists ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp))
	 
		(sep 
			(succ10circuit x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 )
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
		)

		)

	)
	
		(sep 
			(one x1 )
			(one x2 )
			(one x3 )
			(one x4 )
			(one x5 )
			(one x6 )
			(one x7 )
			(one x8 )
			(one x9 )
			(one x10 )
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
		)

	
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	(exists ((z3 RefGTyp)(z4 RefGTyp)(z5 RefGTyp)(z6 RefGTyp)(z7 RefGTyp)(z8 RefGTyp)(z9 RefGTyp)(z10 RefGTyp))
	 
		(sep 
			(notg x1 y1 )
			(xorg x1 x2 y2 )
			(andg x1 x2 z3 )
			(xorg z3 x3 y3 )
			(andg z3 x3 z4 )
			(xorg x4 y4 z4 )
			(andg z4 x4 z5 )
			(xorg x5 y5 z5 )
			(andg z5 x5 z6 )
			(xorg x6 y6 z6 )
			(andg z6 x6 z7 )
			(xorg x7 y7 z7 )
			(andg z7 x7 z8 )
			(xorg x8 y8 z8 )
			(andg z8 x8 z9 )
			(xorg x9 y9 z9 )
			(andg z9 x9 z10 )
			(xorg x10 y10 z10 )
		)

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
(declare-const x2 RefGTyp)
(declare-const x3 RefGTyp)
(declare-const x4 RefGTyp)
(declare-const x5 RefGTyp)
(declare-const x6 RefGTyp)
(declare-const x7 RefGTyp)
(declare-const x8 RefGTyp)
(declare-const x9 RefGTyp)

(assert 
			(P x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 )
)

(check-sat)
