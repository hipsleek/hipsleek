(set-logic QF_SHID)

(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

; Sorts for locations, one by cell sort
(declare-sort Refnode 0)

; Types of cells in the heap

(declare-datatypes (
	(node 0)
	) (
	((c_node (parent Refnode) (left Refnode) (right Refnode) (next Refnode) ))
	)
)

; Type of heap

(declare-heap (Refnode node) 
)
; User defined predicates
(define-funs-rec (
	(tree ((in Refnode)) Bool
	)

	(tll ((in Refnode)(p Refnode)(ll Refnode)(lr Refnode)) Bool
	)

	(right_nil ((in Refnode)) Bool
	)

	(eright_nil ((in Refnode)) Bool
	)

	(right_nnil ((in Refnode)) Bool
	)

	(eright_nnil ((in Refnode)) Bool
	)

	(enode ((in Refnode)(p Refnode)(l Refnode)(r Refnode)(n Refnode)) Bool
	)

	(etll ((in Refnode)(p Refnode)(t Refnode)(r Refnode)) Bool
	)

	(ltll ((in Refnode)(p Refnode)(l Refnode)(r Refnode)(D Refnode)(v Refnode)(t Refnode)) Bool
	)
		)
		((or (exists ((p_35 Refnode)(D1_36 Refnode)(r_37 Refnode)(n_38 Refnode))
	 
		(and 
			(= (as nil Refnode) r_37)
			(pto in (c_node p_35 D1_36 r_37 n_38 ))
		)

		)

	(exists ((p_39 Refnode)(l_40 Refnode)(r_41 Refnode)(D2_42 Refnode))
	 
		(and 
			(distinct (as nil Refnode) r_41)
		(sep 
			(pto in (c_node p_39 l_40 r_41 D2_42 ))
			(tree l_40 )
			(tree r_41 )
		)

		)

		)

	)
	(or (exists ((lr_28 Refnode)(p_21 Refnode)(D1_22 Refnode)(l_23 Refnode))
	 
		(and 
			(= (as nil Refnode) l_23)
			(= in ll)
			(= lr lr_28)
			(pto in (c_node p_21 D1_22 l_23 lr_28 ))
		)

		)

	(exists ((p_29 Refnode)(self_30 Refnode)(ll_31 Refnode)(self_32 Refnode)(z_33 Refnode)(lr_34 Refnode)(l_24 Refnode)(r_25 Refnode)(D2_26 Refnode)(z_27 Refnode))
	 
		(and 
			(distinct (as nil Refnode) r_25)
			(= p p_29)
			(= in self_30)
			(= ll ll_31)
			(= in self_32)
			(= z_33 z_27)
			(= lr lr_34)
		(sep 
			(pto in (c_node p_29 l_24 r_25 D2_26 ))
			(tll l_24 self_30 ll_31 z_27 )
			(tll r_25 self_32 z_33 lr_34 )
		)

		)

		)

	)
	(exists ((p Refnode)(l Refnode)(r Refnode)(n Refnode))
	 
		(and 
			(= (as nil Refnode) r)
			(pto in (c_node p l r n ))
		)

		)

	(exists ((p0 Refnode)(l0 Refnode)(r0 Refnode)(n0 Refnode)(p1 Refnode)(l1 Refnode)(r1 Refnode)(n1 Refnode))
	 
		(and 
			(= p0 p1)
			(= l0 l1)
			(= r0 r1)
			(= n0 n1)
			(= (as nil Refnode) r1)
			(pto in (c_node p0 l0 r0 n0 ))
		)

		)

	(exists ((p Refnode)(l Refnode)(r Refnode)(n Refnode))
	 
		(and 
			(distinct (as nil Refnode) r)
		(sep 
			(pto in (c_node p l r n ))
			(tree l )
			(tree r )
		)

		)

		)

	(exists ((p0 Refnode)(l0 Refnode)(r0 Refnode)(n0 Refnode)(p1 Refnode)(l1 Refnode)(r1 Refnode)(n1 Refnode))
	 
		(and 
			(= p0 p1)
			(= l0 l1)
			(= r0 r1)
			(= n0 n1)
			(= (as nil Refnode) r1)
		(sep 
			(pto in (c_node p0 l0 r0 n0 ))
			(tree l1 )
			(tree r1 )
		)

		)

		)

	(exists ((p0 Refnode)(l0 Refnode)(r0 Refnode)(n0 Refnode))
	 
		(and 
			(= p p0)
			(= l l0)
			(= r r0)
			(= n n0)
			(pto in (c_node p0 l0 r0 n0 ))
		)

		)

	(exists ((p1 Refnode)(t1 Refnode))
	 
		(and 
			(= p p1)
			(= t t1)
			(tll in p1 r t1 )
		)

		)

	(exists ((l1 Refnode))
	 
		(sep 
			(pto in (c_node p l r D ))
			(tll l in v l1 )
			(tll r in l1 t )
		)

		)

		)
)


(check-sat) 
;; variables
(declare-const pprm Refnode)
(declare-const xprm Refnode)
(declare-const vprm Refnode)
(declare-const parent0 Refnode)
(declare-const p Refnode)
(declare-const p1 Refnode)
(declare-const x Refnode)
(declare-const tprm Refnode)
(declare-const t Refnode)
(declare-const D Refnode)
(declare-const r Refnode)
(declare-const n Refnode)

(assert 
		(and 
			(= (as nil Refnode) vprm)
			(= vprm r)
			(= parent0 p)
			(= pprm p1)
			(= xprm x)
			(= tprm t)
			(= (as nil Refnode) r)
			(pto xprm (c_node pprm D r n ))
		)

)

(assert (not 
		(and 
			(= (as nil Refnode) vprm)
			(= vprm r)
			(= parent0 p)
			(= pprm p1)
			(= xprm x)
			(= tprm t)
			(= (as nil Refnode) r)
			(pto xprm (c_node pprm D r n ))
		)

))

(check-sat)
