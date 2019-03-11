(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-21")

;; Nested singly-linked list of acyclic singly-linked lists
;; and acyclic Singly-linked lists

; Sorts for locations, one by cell sort
(declare-sort RefNLL_lvl1_t 0)
(declare-sort RefNLL_lvl2_t 0)

; Types of cells in the heap

(declare-datatypes (
	(NLL_lvl1_t 0)
	(NLL_lvl2_t 0)
	) (
	((c_NLL_lvl1_t (next1 RefNLL_lvl1_t) ))
	((c_NLL_lvl2_t (next2 RefNLL_lvl2_t) (down RefNLL_lvl1_t) ))
	)
)

; Type of heap

(declare-heap (RefNLL_lvl1_t NLL_lvl1_t) (RefNLL_lvl2_t NLL_lvl2_t) 
)

(define-fun-rec sll ((in RefNLL_lvl1_t)(out RefNLL_lvl1_t)) Bool
	(or
		(and (= in out)
                     (_ emp RefNLL_lvl1_t NLL_lvl1_t)
                )
                (exists ((u RefNLL_lvl1_t))
		(and (distinct in out)
		(sep (pto in (c_NLL_lvl1_t u))
		     (sll u out))
		)
		)
	)
)
                
(define-fun-rec nll ((in RefNLL_lvl2_t)(out RefNLL_lvl2_t)) Bool
	(or 
		(and (= in out)
		     (_ emp RefNLL_lvl2_t NLL_lvl2_t)
		)

		(exists ((h RefNLL_lvl1_t) (u RefNLL_lvl2_t))
		(sep 
			(pto in (c_NLL_lvl2_t u h ))
			(sll h (as nil RefNLL_lvl1_t))
			(nll u out)
		)
		)
	)
)

(check-sat) 
;; variables
(declare-const x0 RefNLL_lvl2_t)

(assert (nll x0 (as nil RefNLL_lvl2_t))
)

(check-sat)

