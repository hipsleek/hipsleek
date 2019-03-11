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

(define-fun-rec DLL ((x RefGTyp)(y RefGTyp)(z RefGTyp)(w RefGTyp)) Bool
	(or 
		(and 
			(= x y)
			(= z w)
			(_ emp RefGTyp GTyp)
		)

		(exists ((zp RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp zp w ))
			(DLL zp y z x )
		)

		)

		)

	)
)


(check-sat) 
;; variables
(declare-const a RefGTyp)
(declare-const b RefGTyp)
(declare-const x RefGTyp)
(declare-const y RefGTyp)
(declare-const z RefGTyp)
(declare-const w RefGTyp)

(assert 
		(sep 
			(DLL x y z w )
			(DLL a x w b )
		)

)

(assert (not 
			(DLL a y z b )
))

(check-sat)
