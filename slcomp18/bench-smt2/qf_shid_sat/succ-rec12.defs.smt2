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

	(Q ((y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)(y11 RefGTyp)(y12 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
	)

	(succ12rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)(y11 RefGTyp)(y12 RefGTyp)) Bool
	)

	(succ11rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)(y11 RefGTyp)) Bool
	)

	(succ10rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)(y10 RefGTyp)) Bool
	)

	(succ9rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)(y9 RefGTyp)) Bool
	)

	(succ8rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)(y8 RefGTyp)) Bool
	)

	(succ7rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)(y7 RefGTyp)) Bool
	)

	(succ6rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)(y6 RefGTyp)) Bool
	)

	(succ5rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)) Bool
	)

	(succ4rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)) Bool
	)

	(succ3rec ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)) Bool
	)

	(succ2rec ((x1 RefGTyp)(x2 RefGTyp)(y1 RefGTyp)(y2 RefGTyp)) Bool
	)

	(succ1rec ((x1 RefGTyp)(y1 RefGTyp)) Bool
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
		)

	(exists ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)(x6 RefGTyp)(x7 RefGTyp)(x8 RefGTyp)(x9 RefGTyp)(x10 RefGTyp)(x11 RefGTyp)(x12 RefGTyp))
	 
		(sep 
			(succ12rec x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 )
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 )
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
			(Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 )
		)

	
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
			(= x8 y8)
			(= x9 y9)
			(= x10 y10)
			(= x11 y11)
			(= x12 y12)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ11rec x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
			(= x8 y8)
			(= x9 y9)
			(= x10 y10)
			(= x11 y11)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ10rec x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
			(= x8 y8)
			(= x9 y9)
			(= x10 y10)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ9rec x2 x3 x4 x5 x6 x7 x8 x9 x10 y2 y3 y4 y5 y6 y7 y8 y9 y10 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
			(= x8 y8)
			(= x9 y9)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ8rec x2 x3 x4 x5 x6 x7 x8 x9 y2 y3 y4 y5 y6 y7 y8 y9 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
			(= x8 y8)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ7rec x2 x3 x4 x5 x6 x7 x8 y2 y3 y4 y5 y6 y7 y8 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
			(= x7 y7)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ6rec x2 x3 x4 x5 x6 x7 y2 y3 y4 y5 y6 y7 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
			(= x6 y6)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ5rec x2 x3 x4 x5 x6 y2 y3 y4 y5 y6 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
			(= x5 y5)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ4rec x2 x3 x4 x5 y2 y3 y4 y5 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
			(= x4 y4)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ3rec x2 x3 x4 y2 y3 y4 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
			(= x3 y3)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ2rec x2 x3 y2 y3 )
			(one x1 )
			(zero y1 )
		)

	)
	(or 
		(and 
			(= x2 y2)
		(sep 
			(zero x1 )
			(one y1 )
		)

		)

	
		(sep 
			(succ1rec x2 y2 )
			(one x1 )
			(zero y1 )
		)

	)
	
		(sep 
			(zero x1 )
			(one y1 )
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

(assert 
			(P x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 )
)

(check-sat)
