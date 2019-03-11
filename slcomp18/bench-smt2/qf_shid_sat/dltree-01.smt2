(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-18")

;; Doubly-linked null-terminated trees
;; Every node points to left child, right child and parent,
;; where the latter is given as 2nd parameter

(declare-sort RefDltree_t 0)

(declare-datatypes (
	(Dltree_t 0)
	) (
	((c_Dltree_t (lson RefDltree_t) (rson RefDltree_t) (parent RefDltree_t) ))
	)
)

(declare-heap (RefDltree_t Dltree_t) 
)

(define-fun-rec dltree ((r RefDltree_t)(p RefDltree_t)) Bool
	(or 
		(pto r (c_Dltree_t (as nil RefDltree_t) (as nil RefDltree_t) p))

		(exists ((ls RefDltree_t) (rs RefDltree_t))
	 
		(and 
			(distinct ls rs)
			(distinct r ls)
			(distinct r rs)
		(sep 
			(pto r (c_Dltree_t ls rs p))
			(dltree ls r)
			(dltree rs r)
		)
		)
		)
	)
)

(check-sat) 
;; variables
(declare-const x0 RefDltree_t)

(assert (dltree x0 (as nil RefDltree_t))
)

(check-sat)


