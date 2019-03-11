(set-logic QF_SHIDLIA)
(set-info :source |
  Zhilin Wu.
  COMPSPEN benchmark.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-21")


; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next RefSll_t) (data Int) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)
; User defined predicate
(define-fun-rec lsls ((in RefSll_t)(dt1 Int)(len1 Int)(out RefSll_t)(dt2 Int)(len2 Int)) Bool
	(or 
		(and 
			(= in out)
			(= dt1 dt2)
			(= len1 len2)
			(_ emp RefSll_t Sll_t)
		)

	(exists ((u RefSll_t)(dt3 Int)(len3 Int))
	 
		(and 
			(< dt1 (+ dt3 0 ) )
			(= len1 (+ len3 1 ) )
		(sep 
			(pto in (c_Sll_t u dt1 ))
			(lsls u dt3 len3 out dt2 len2 )
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const y_emp RefSll_t)
(declare-const w_emp RefSll_t)
(declare-const z_emp RefSll_t)
(declare-const u_emp RefSll_t)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const n1 Int)
(declare-const n2 Int)

(assert 
		(and 
			(= d1 d2)
			(= n1 (+ n2 3 ) )
			(lsls u_emp d1 n1 z_emp d2 n2 )
		)

)

(check-sat)
