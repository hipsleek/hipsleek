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
(declare-const x21 RefSll_t)
(declare-const x22 RefSll_t)

(assert 
		(and 
			(= (as nil RefSll_t) (as nil RefSll_t))
			(distinct x6 x16)
			(distinct x6 x17)
			(distinct x6 x12)
			(distinct x3 x18)
			(distinct x3 x7)
			(distinct x3 x10)
			(distinct x3 x13)
			(distinct x3 x9)
			(distinct x3 x15)
			(distinct x7 x11)
			(distinct x7 x16)
			(distinct x7 x12)
			(distinct x9 x10)
			(distinct x9 x14)
			(distinct x12 x18)
			(distinct x12 x13)
			(distinct x12 x15)
			(distinct x2 x11)
			(distinct x2 x4)
			(distinct x2 x7)
			(distinct x2 x14)
			(distinct x15 x16)
			(distinct x8 x13)
			(distinct x4 x9)
			(distinct x1 x11)
			(distinct x1 x4)
			(distinct x1 x7)
			(distinct x1 x10)
			(distinct x1 x2)
			(distinct x13 x16)
			(distinct x13 x17)
			(distinct x10 x11)
			(distinct x5 x14)
		(sep 
			(ls x5 x15 )
			(ls x5 x9 )
			(ls x5 x4 )
			(ls x16 x13 )
			(ls x4 x12 )
			(ls x4 x6 )
			(ls x15 x1 )
			(ls x7 x13 )
		)

		)

)

(check-sat)
