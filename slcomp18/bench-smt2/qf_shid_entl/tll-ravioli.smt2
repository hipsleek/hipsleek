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
; User defined predicates
(define-funs-rec (
	(TLL_plus ((root RefTLL_t)(pra RefTLL_t)(ll RefTLL_t)(lr RefTLL_t)) Bool
	)

	(TLL_tail ((root RefTLL_t)(pra RefTLL_t)(ll RefTLL_t)(tr RefTLL_t)(lr RefTLL_t)) Bool
	)
		)
		((or 
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
	(or 
		(and 
			(= root ll)
			(= root tr)
			(pto root (c_TLL_t (as nil RefTLL_t) (as nil RefTLL_t) lr pra ))
		)

	(exists ((l RefTLL_t)(r RefTLL_t)(z RefTLL_t))
	 
		(sep 
			(pto root (c_TLL_t l r (as nil RefTLL_t) pra ))
			(TLL_plus l root ll z )
			(TLL_tail r root z tr lr )
		)

		)

	)
		)
)


(check-sat) 
;; variables
(declare-const root0 RefTLL_t)
(declare-const ll0 RefTLL_t)
(declare-const tr0 RefTLL_t)
(declare-const root1 RefTLL_t)
(declare-const ll1 RefTLL_t)
(declare-const tr1 RefTLL_t)
(declare-const root2 RefTLL_t)
(declare-const ll2 RefTLL_t)
(declare-const tr2 RefTLL_t)
(declare-const root3 RefTLL_t)
(declare-const ll3 RefTLL_t)
(declare-const tr3 RefTLL_t)
(declare-const root4 RefTLL_t)
(declare-const ll4 RefTLL_t)
(declare-const tr4 RefTLL_t)
(declare-const root5 RefTLL_t)
(declare-const ll5 RefTLL_t)
(declare-const tr5 RefTLL_t)
(declare-const root6 RefTLL_t)
(declare-const ll6 RefTLL_t)
(declare-const tr6 RefTLL_t)
(declare-const root7 RefTLL_t)
(declare-const ll7 RefTLL_t)
(declare-const tr7 RefTLL_t)
(declare-const root8 RefTLL_t)
(declare-const ll8 RefTLL_t)
(declare-const tr8 RefTLL_t)
(declare-const root9 RefTLL_t)
(declare-const ll9 RefTLL_t)
(declare-const tr9 RefTLL_t)
(declare-const root10 RefTLL_t)
(declare-const ll10 RefTLL_t)
(declare-const tr10 RefTLL_t)
(declare-const root11 RefTLL_t)
(declare-const ll11 RefTLL_t)
(declare-const tr11 RefTLL_t)
(declare-const root12 RefTLL_t)
(declare-const ll12 RefTLL_t)
(declare-const tr12 RefTLL_t)
(declare-const root13 RefTLL_t)
(declare-const ll13 RefTLL_t)
(declare-const tr13 RefTLL_t)
(declare-const root14 RefTLL_t)
(declare-const ll14 RefTLL_t)
(declare-const tr14 RefTLL_t)
(declare-const root15 RefTLL_t)
(declare-const ll15 RefTLL_t)
(declare-const tr15 RefTLL_t)
(declare-const root16 RefTLL_t)
(declare-const ll16 RefTLL_t)
(declare-const tr16 RefTLL_t)
(declare-const root17 RefTLL_t)
(declare-const ll17 RefTLL_t)
(declare-const tr17 RefTLL_t)
(declare-const root18 RefTLL_t)
(declare-const ll18 RefTLL_t)
(declare-const tr18 RefTLL_t)
(declare-const root19 RefTLL_t)
(declare-const ll19 RefTLL_t)
(declare-const tr19 RefTLL_t)

(assert 
		(sep 
			(TLL_tail root0 (as nil RefTLL_t) ll0 tr0 root1 )
			(TLL_tail root1 tr0 ll1 tr1 root2 )
			(TLL_tail root2 tr1 ll2 tr2 root3 )
			(TLL_tail root3 tr2 ll3 tr3 root4 )
			(TLL_tail root4 tr3 ll4 tr4 root5 )
			(TLL_tail root5 tr4 ll5 tr5 root6 )
			(TLL_tail root6 tr5 ll6 tr6 root7 )
			(TLL_tail root7 tr6 ll7 tr7 root8 )
			(TLL_tail root8 tr7 ll8 tr8 root9 )
			(TLL_tail root9 tr8 ll9 tr9 root10 )
			(TLL_tail root10 tr9 ll10 tr10 root11 )
			(TLL_tail root11 tr10 ll11 tr11 root12 )
			(TLL_tail root12 tr11 ll12 tr12 root13 )
			(TLL_tail root13 tr12 ll13 tr13 root14 )
			(TLL_tail root14 tr13 ll14 tr14 root15 )
			(TLL_tail root15 tr14 ll15 tr15 root16 )
			(TLL_tail root16 tr15 ll16 tr16 root17 )
			(TLL_tail root17 tr16 ll17 tr17 root18 )
			(TLL_tail root18 tr17 ll18 tr18 root19 )
			(TLL_tail root19 tr18 ll19 tr19 (as nil RefTLL_t) )
		)

)

(assert (not 
		(sep 
			(TLL_tail root0 (as nil RefTLL_t) ll0 tr0 root1 )
			(TLL_tail root2 tr1 ll2 tr2 root3 )
			(TLL_tail root5 tr4 ll5 tr5 root6 )
			(TLL_tail root8 tr7 ll8 tr8 root9 )
			(TLL_tail root10 tr9 ll10 tr10 root11 )
			(TLL_tail root7 tr6 ll7 tr7 root8 )
			(TLL_tail root9 tr8 ll9 tr9 root10 )
			(TLL_tail root4 tr3 ll4 tr4 root5 )
			(TLL_tail root13 tr12 ll13 tr13 root14 )
			(TLL_tail root11 tr10 ll11 tr11 root12 )
			(TLL_tail root15 tr14 ll15 tr15 root16 )
			(TLL_tail root12 tr11 ll12 tr12 root13 )
			(TLL_tail root17 tr16 ll17 tr17 root18 )
			(TLL_tail root14 tr13 ll14 tr14 root15 )
			(TLL_tail root6 tr5 ll6 tr6 root7 )
			(TLL_tail root19 tr18 ll19 tr19 (as nil RefTLL_t) )
			(TLL_tail root1 tr0 ll1 tr1 root2 )
			(TLL_tail root16 tr15 ll16 tr16 root17 )
			(TLL_tail root3 tr2 ll3 tr3 root4 )
			(TLL_tail root18 tr17 ll18 tr18 root19 )
		)

))

(check-sat)
