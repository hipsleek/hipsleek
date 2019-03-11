(set-logic QF_SHLS)

(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unsat)
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
(declare-const x23 RefSll_t)
(declare-const x24 RefSll_t)

(assert 
		(and 
			(= (as nil RefSll_t) (as nil RefSll_t))
			(distinct x6 x19)
			(distinct x3 x7)
			(distinct x3 x20)
			(distinct x7 x20)
			(distinct x9 x19)
			(distinct x2 x20)
			(distinct x8 x19)
			(distinct x8 x17)
			(distinct x4 x11)
			(distinct x4 x13)
			(distinct x4 x19)
			(distinct x1 x16)
			(distinct x1 x20)
			(distinct x13 x18)
			(distinct x13 x17)
			(distinct x10 x19)
			(distinct x10 x20)
			(distinct x16 x19)
		(sep 
			(ls x5 x17 )
			(ls x19 x1 )
			(ls x4 x12 )
			(ls x12 x20 )
			(ls x12 x15 )
			(ls x12 x11 )
			(ls x2 x18 )
			(ls x17 x14 )
			(ls x7 x16 )
			(ls x3 x20 )
			(ls x3 x12 )
			(ls x11 x12 )
			(ls x6 x17 )
			(ls x6 x19 )
		)

		)

)

(check-sat)
