(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-18")

;; Possibly empty null-terminated binary trees

(declare-sort RefBtree_t 0)

(declare-datatypes (
	(Btree_t 0)
	) (
	((c_Btree_t (lson RefBtree_t) (rson RefBtree_t)))
	)
)

(declare-heap (RefBtree_t Btree_t) 
)

(define-fun-rec tree ((r RefBtree_t)) Bool
	(or 
		(and (= r (as nil RefBtree_t))
		     (_ emp RefBtree_t Btree_t)
		)

		(pto r (c_Btree_t (as nil RefBtree_t) (as nil RefBtree_t)))

		(exists ((ls RefBtree_t) (rs RefBtree_t))
	 
		(sep 
			(pto r (c_Btree_t ls rs))
			(tree ls)
			(tree rs)
		)

		)

	)
)

(check-sat) 

;; variables
(declare-const x0 RefBtree_t)

(assert (tree x0)
)

(check-sat)

