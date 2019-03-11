(set-logic QF_SHLS)

(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2014-05-28")

; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next RefSll_t) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)

(define-fun-rec ls ((in RefSll_t)(out RefSll_t)) Bool
	(or 
		(and 
			(= in out)
			(_ emp RefSll_t Sll_t)
		)

		(exists ((u RefSll_t))
	 
		(and 
			(distinct in out)
		(sep 
			(pto in (c_Sll_t u ))
			(ls u out )
		)

		)

		)

	)
)


(check-sat) 
;; variables
(declare-const x_emp RefSll_t)
(declare-const y_emp RefSll_t)
(declare-const w_emp RefSll_t)
(declare-const z_emp RefSll_t)
(declare-const u_emp RefSll_t)
(declare-const v_emp RefSll_t)
(declare-const r_emp RefSll_t)
(declare-const s_emp RefSll_t)

(assert 
		(sep 
			(pto x_emp (c_Sll_t y_emp ))
			(ls y_emp w_emp )
			(ls w_emp z_emp )
			(pto z_emp (c_Sll_t u_emp ))
			(pto u_emp (c_Sll_t v_emp ))
			(ls v_emp r_emp )
			(pto r_emp (c_Sll_t s_emp ))
		)

)

(assert (not 
			(ls x_emp s_emp )
))

(check-sat)
