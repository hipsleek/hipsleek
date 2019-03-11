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
(declare-const x23 RefSll_t)
(declare-const x24 RefSll_t)
(declare-const x25 RefSll_t)
(declare-const x26 RefSll_t)
(declare-const x27 RefSll_t)
(declare-const x28 RefSll_t)

(assert 
		(and 
			(= (as nil RefSll_t) (as nil RefSll_t))
			(distinct (as nil RefSll_t) x1)
			(distinct (as nil RefSll_t) x2)
			(distinct (as nil RefSll_t) x3)
			(distinct x1 x2)
			(distinct x2 x3)
			(distinct (as nil RefSll_t) x5)
			(distinct (as nil RefSll_t) x6)
			(distinct (as nil RefSll_t) x7)
			(distinct x5 x6)
			(distinct x6 x7)
			(distinct (as nil RefSll_t) x9)
			(distinct (as nil RefSll_t) x10)
			(distinct (as nil RefSll_t) x11)
			(distinct x9 x10)
			(distinct x10 x11)
			(distinct (as nil RefSll_t) x13)
			(distinct (as nil RefSll_t) x14)
			(distinct (as nil RefSll_t) x15)
			(distinct x13 x14)
			(distinct x14 x15)
			(distinct (as nil RefSll_t) x17)
			(distinct (as nil RefSll_t) x18)
			(distinct (as nil RefSll_t) x19)
			(distinct x17 x18)
			(distinct x18 x19)
			(distinct (as nil RefSll_t) x21)
			(distinct (as nil RefSll_t) x22)
			(distinct (as nil RefSll_t) x23)
			(distinct x21 x22)
			(distinct x22 x23)
		(sep 
			(ls x23 x21 )
			(pto x21 (c_Sll_t x23 ))
			(ls x19 x17 )
			(pto x17 (c_Sll_t x19 ))
			(ls x15 x13 )
			(pto x13 (c_Sll_t x15 ))
			(ls x11 x9 )
			(pto x9 (c_Sll_t x11 ))
			(ls x7 x5 )
			(pto x5 (c_Sll_t x7 ))
			(ls x3 x1 )
			(pto x1 (c_Sll_t x3 ))
		)

		)

)

(assert (not 
		(sep 
			(ls x24 x21 )
			(pto x21 (c_Sll_t x24 ))
			(ls x20 x17 )
			(pto x17 (c_Sll_t x20 ))
			(ls x16 x13 )
			(pto x13 (c_Sll_t x16 ))
			(ls x12 x9 )
			(pto x9 (c_Sll_t x12 ))
			(ls x8 x5 )
			(pto x5 (c_Sll_t x8 ))
			(ls x4 x1 )
			(pto x1 (c_Sll_t x4 ))
		)

))

(check-sat)
