(set-logic QF_SHIDLIA)
(set-info :source |
  Quang Loc Le.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-22")


; Sorts for locations, one by cell sort
(declare-sort RefTree_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Tree_t 0)
	) (
	((c_Tree_t (left RefTree_t) (right RefTree_t)))
	)
)

; Type of heap

(declare-heap (RefTree_t Tree_t) 
)
; User defined predicate
(define-fun-rec btree ((x RefTree_t)(len1 Int)) Bool
	(or 
		(and 
			(= x (as nil RefTree_t))
			(= len1 0)
                             (_ emp RefTree_t Tree_t)
		)

	(exists ((l RefTree_t)(r RefTree_t)(n1 Int)(n2 Int))
	 
		(and 
			(= len1 (+ (+ n1 n2) 1 ) )
		(sep 
			(pto x (c_Tree_t l r))
			(btree l n1 )
                        (btree r n2)
		)

		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const x RefTree_t)
(declare-const n1 Int)

(assert 
		(and 
                        (= n1 320001)
			(btree x n1)
		)

)

(check-sat)
