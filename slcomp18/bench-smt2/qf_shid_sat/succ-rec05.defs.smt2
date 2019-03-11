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

	(Q ((y1 RefGTyp)(y2 RefGTyp)(y3 RefGTyp)(y4 RefGTyp)(y5 RefGTyp)) Bool
	)

	(P ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp)) Bool
	)

	(zero ((x RefGTyp)) Bool
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
		)

	(exists ((x1 RefGTyp)(x2 RefGTyp)(x3 RefGTyp)(x4 RefGTyp)(x5 RefGTyp))
	 
		(sep 
			(succ5rec x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 )
			(Q x1 x2 x3 x4 x5 )
		)

		)

	)
	
		(sep 
			(one x1 )
			(one x2 )
			(one x3 )
			(one x4 )
			(one x5 )
			(Q x1 x2 x3 x4 x5 )
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

(assert 
			(P x0 x1 x2 x3 x4 )
)

(check-sat)
