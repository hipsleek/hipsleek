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
(declare-const X RefSll_t)
(declare-const Y RefSll_t)
(declare-const Z RefSll_t)
(declare-const U RefSll_t)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const d3 Int)
(declare-const d4 Int)
(declare-const d5 Int)
(declare-const n1 Int)
(declare-const n2 Int)
(declare-const n3 Int)
(declare-const n4 Int)

(assert 
		(and 
			(distinct d1 d2)
			(= d2 d3)
			(= n3 (+ n4 2 ) )
			(= n2 (+ n3 1 ) )
			(< d3 d4)
		(sep 
			(lsls X d1 n1 Y d2 n2 )
			(pto Y (c_Sll_t Z d3 ))
			(lsls Z d4 n3 U d5 n4 )
		)

		)

)

(assert (not 
		(and 
			(< d1 d5)
			(> n1 (+ n4 3 ) )
			(lsls X d1 n1 U d5 n4 )
		)

))

(check-sat)
