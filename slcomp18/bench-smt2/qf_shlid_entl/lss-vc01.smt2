(set-logic QF_SHLID)

(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


; Sorts for locations, one by cell sort
(declare-sort RefSll_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next1 RefSll_t) (next2 RefSll_t) ))
	)
)

; Type of heap

(declare-heap (RefSll_t Sll_t) 
)

(define-fun-rec lsso ((in RefSll_t)(out RefSll_t)) Bool
	(or 
		(and 
			(= in out)
			(_ emp RefSll_t Sll_t)
		)

		(exists ((u RefSll_t))
	 
		(sep 
			(pto in (c_Sll_t u u ))
			(lsso u out )
		)

		)

	)
)


(check-sat) 
;; variables
(declare-const x_emp RefSll_t)
(declare-const y_emp RefSll_t)
(declare-const z_emp RefSll_t)

(assert 
		(sep 
			(pto x_emp (c_Sll_t y_emp y_emp ))
			(pto y_emp (c_Sll_t z_emp z_emp ))
		)

)

(assert (not 
			(lsso x_emp z_emp )
))

(check-sat)
