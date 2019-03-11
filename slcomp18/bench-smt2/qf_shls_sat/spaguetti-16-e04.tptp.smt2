(set-logic QF_SHLS)

(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status sat)
(set-info :version "2014-05-28")

; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next RefSll_t) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)

(define-fun-rec ls ((in RefSll_t)(out RefSll_t)) Bool
	(or 
		(and 
			(= in out)
			(_ emp RefSll_t Sll_t)
		)

		(exists ((u RefSll_t))
	 
		(and 
			(distinct in out)
		(sep 
			(pto in (c_Sll_t u ))
			(ls u out )
		)

		)

		)

	)
)


(check-sat) 
;; variables
(declare-const x0 RefSll_t)
(declare-const x1 RefSll_t)
(declare-const x2 RefSll_t)
(declare-const x3 RefSll_t)
(declare-const x4 RefSll_t)
(declare-const x5 RefSll_t)
(declare-const x6 RefSll_t)
(declare-const x7 RefSll_t)
(declare-const x8 RefSll_t)
(declare-const x9 RefSll_t)
(declare-const x10 RefSll_t)
(declare-const x11 RefSll_t)
(declare-const x12 RefSll_t)
(declare-const x13 RefSll_t)
(declare-const x14 RefSll_t)
(declare-const x15 RefSll_t)
(declare-const x16 RefSll_t)
(declare-const x17 RefSll_t)
(declare-const x18 RefSll_t)
(declare-const x19 RefSll_t)
(declare-const x20 RefSll_t)

(assert 
		(and 
			(= (as nil RefSll_t) (as nil RefSll_t))
			(distinct x6 x13)
			(distinct x6 x12)
			(distinct x6 x14)
			(distinct x6 x15)
			(distinct x7 x11)
			(distinct x7 x15)
			(distinct x9 x15)
			(distinct x2 x11)
			(distinct x2 x16)
			(distinct x2 x15)
			(distinct x15 x16)
			(distinct x8 x10)
			(distinct x4 x16)
			(distinct x4 x5)
			(distinct x1 x14)
			(distinct x10 x11)
			(distinct x5 x6)
			(distinct x5 x11)
			(distinct x5 x9)
			(distinct x5 x15)
		(sep 
			(ls x10 x12 )
			(ls x16 x11 )
			(ls x1 x2 )
			(ls x4 x15 )
			(ls x14 x13 )
			(ls x15 x14 )
			(ls x2 x16 )
			(ls x12 x11 )
			(ls x9 x11 )
			(ls x11 x13 )
			(ls x6 x13 )
			(ls x6 x7 )
			(ls x6 x3 )
		)

		)

)

(check-sat)
