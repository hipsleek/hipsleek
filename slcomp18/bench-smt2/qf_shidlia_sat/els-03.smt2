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
	((c_Sll_t (next RefSll_t) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)
; User defined predicate
(define-fun-rec els ((in RefSll_t)(len1 Int)) Bool
	(or 
		(and 
			(= in (as nil RefSll_t))
			(= len1 0)
			(_ emp RefSll_t Sll_t)
		)

	(exists ((u1 RefSll_t)(u2 RefSll_t)(len3 Int))
	 
		(and 
			(= len1 (+ len3 2 ) )
		(sep 
			(pto in (c_Sll_t u1 ))
                        (pto u1 (c_Sll_t u2 ))
			(els u2 len3 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const u_emp RefSll_t)
(declare-const t_emp RefSll_t)
(declare-const n1 Int)
(declare-const n2 Int)

(assert 
		(and 
			(= n1 (+ n2 n2 1) )
                    (sep
			(els u_emp n1)
                        (els t_emp n2)
                    )
		)

)

(check-sat)
