(set-logic QF_SHIDLIA)
(set-info :source |
  Quang Loc Le.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-22")


; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (left RefSll_t) (right RefSll_t)))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)
; User defined predicate
(define-fun-rec lss ((x RefSll_t)(y RefSll_t)(len1 Int)) Bool
	(or 
		(and 
			(= y (as nil RefSll_t))
			(= len1 1)
                                (pto x (c_Sll_t (as nil RefSll_t) y))
		)

	(exists ((x1 RefSll_t)(y1 RefSll_t)(n1 Int))
	 
		(and 
			(= len1 (+ n1 2 ) )
		(sep 
			(pto y (c_Sll_t x1 y1))
			(lss x y1 n1 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x RefSll_t)
(declare-const y RefSll_t)
(declare-const n1 Int)
(declare-const k Int)

(assert 
		(and 
                        (= n1 (+ k k))
			(lss x y n1)
		)

)

(check-sat)
