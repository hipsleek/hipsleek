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

	(Q ((y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)(y11 RefGTyp)(y12 RefGTyp)(y13 RefGTyp)(y14 RefGTyp)(y15 RefGTyp)(y16 RefGTyp)(y17 RefGTyp)(y18 RefGTyp)(y19 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp)(x13 RefGTyp)(x14 RefGTyp)(x15 RefGTyp)(x16 RefGTyp)(x17 RefGTyp)(x18 RefGTyp)(x19 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
	)

	(succ19circuit ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp)(x13 RefGTyp)(x14 RefGTyp)(x15 RefGTyp)(x16 RefGTyp)(x17 RefGTyp)(x18 RefGTyp)(x19 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)(y11 RefGTyp)(y12 RefGTyp)(y13 RefGTyp)(y14 RefGTyp)(y15 RefGTyp)(y16 RefGTyp)(y17 RefGTyp)(y18 RefGTyp)(y19 RefGTyp)) Bool
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
			(zero y11 )
			(zero y12 )
			(zero y13 )
			(zero y14 )
			(zero y15 )
			(zero y16 )
			(zero y17 )
			(zero y18 )
			(zero y19 )
		)

	(exists ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp)(x13 RefGTyp)(x14 RefGTyp)(x15 RefGTyp)(x16 RefGTyp)(x17 RefGTyp)(x18 RefGTyp)(x19 RefGTyp))
	 
		(sep 
			(succ19circuit x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 )
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 )
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
			(one x11 )
			(one x12 )
			(one x13 )
			(one x14 )
			(one x15 )
			(one x16 )
			(one x17 )
			(one x18 )
			(one x19 )
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 )
		)

	
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	(exists ((z3 RefGTyp)(z4 RefGTyp)(z5 RefGTyp)(z6 RefGTyp)(z7 RefGTyp)(z8 RefGTyp)(z9 RefGTyp)(z10 RefGTyp)(z11 RefGTyp)(z12 RefGTyp)(z13 RefGTyp)(z14 RefGTyp)(z15 RefGTyp)(z16 RefGTyp)(z17 RefGTyp)(z18 RefGTyp)(z19 RefGTyp))
	 
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
			(andg z10 x10 z11 )
			(xorg x11 y11 z11 )
			(andg z11 x11 z12 )
			(xorg x12 y12 z12 )
			(andg z12 x12 z13 )
			(xorg x13 y13 z13 )
			(andg z13 x13 z14 )
			(xorg x14 y14 z14 )
			(andg z14 x14 z15 )
			(xorg x15 y15 z15 )
			(andg z15 x15 z16 )
			(xorg x16 y16 z16 )
			(andg z16 x16 z17 )
			(xorg x17 y17 z17 )
			(andg z17 x17 z18 )
			(xorg x18 y18 z18 )
			(andg z18 x18 z19 )
			(xorg x19 y19 z19 )
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
(declare-const x10 RefGTyp)
(declare-const x11 RefGTyp)
(declare-const x12 RefGTyp)
(declare-const x13 RefGTyp)
(declare-const x14 RefGTyp)
(declare-const x15 RefGTyp)
(declare-const x16 RefGTyp)
(declare-const x17 RefGTyp)
(declare-const x18 RefGTyp)

(assert 
			(P x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 )
)

(check-sat)
