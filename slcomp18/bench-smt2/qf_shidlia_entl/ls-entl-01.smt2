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
(declare-sort RefIll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	(Ill_t 0)
	) (
	((c_Sll_t (next RefSll_t) (data RefIll_t) ))
	((c_Ill_t ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) (RefIll_t Ill_t) 
)
; User defined predicate
(define-fun-rec sls ((in RefSll_t)(dt1 RefIll_t)(out RefSll_t)(dt2 RefIll_t)) Bool
	(or 
		(and 
			(= in out)
			(= dt1 dt2)
			(_ emp RefIll_t Ill_t)
		)

	(exists ((u RefSll_t)(dt3 RefIll_t))
	 
		(and 
			(= dt1 dt3)
		(sep 
			(pto in (c_Sll_t u dt1 ))
			(sls u dt3 out dt2 )
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
(declare-const a RefIll_t)
(declare-const b RefIll_t)
(declare-const c RefIll_t)

(assert 
		(sep 
			(sls X a Y b )
			(sls Y b Z c )
		)

)

(assert (not 
			(sls X a Z c )
))

(check-sat)
