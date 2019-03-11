(set-logic QF_SHID)

(set-info :source | 
  R. Iosif, A. Rogalewicz and T. Vojnar. 
  Deciding Entailments in Inductive Separation Logic with Tree Automata arXiv:1402.2127. 
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/ 
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

; Sorts for locations, one by cell sort
(declare-sort RefTLL_t 0)

; Types of cells in the heap

(declare-datatypes (
	(TLL_t 0)
	) (
	((c_TLL_t (left RefTLL_t) (right RefTLL_t) (next RefTLL_t) (parent RefTLL_t) ))
	)
)

; Type of heap

(declare-heap (RefTLL_t TLL_t) 
)
; User defined predicate
(define-fun-rec TLL_plus ((root RefTLL_t)(pra RefTLL_t)(ll RefTLL_t)(lr RefTLL_t)) Bool
	(or 
		(and 
			(= root ll)
			(pto root (c_TLL_t (as nil RefTLL_t) (as nil RefTLL_t) lr pra ))
		)

	(exists ((l RefTLL_t)(r RefTLL_t)(z RefTLL_t))
	 
		(sep 
			(pto root (c_TLL_t l r (as nil RefTLL_t) pra ))
			(TLL_plus l root ll z )
			(TLL_plus r root z lr )
		)

		)

	)
	)


(check-sat) 
;; variables
(declare-const a RefTLL_t)
(declare-const c RefTLL_t)
(declare-const l RefTLL_t)
(declare-const r RefTLL_t)
(declare-const z RefTLL_t)

(assert 
		(sep 
			(pto a (c_TLL_t l r (as nil RefTLL_t) (as nil RefTLL_t) ))
			(TLL_plus l a c z )
			(TLL_plus r a z (as nil RefTLL_t) )
		)

)

(assert (not 
			(TLL_plus a (as nil RefTLL_t) c (as nil RefTLL_t) )
))

(check-sat)
