(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez.
  A decision procedure for satisfiability in separation logic with inductive
  predicates. To appear at CSL-LICS, 2014.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)



;generic sort 

(declare-sort GTyp 0)

;generic fields 
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))

;predicates 

(define-fun UF ((?x GTyp)) Space 
(tospace (or 

	(and (distinct nil ?x)
		 (tobool (pto ?x  (ref f0 ?x) )
		)
	)


	(exists ((?y GenTyp))
		
		 (and (distinct nil ?x)
			(tobool 
	(sep (pto ?x  (ref f0 ?y) )
		(UF ?y)
	)

		)))

) )
 )


;index vars 
(define-fun alpha1 () SetLoc)

;vars 

;problem 
(define-fun x0 () GenTyp)
(assert (tobool (index alpha1 (UF  x0))))

;;pto 1

;;pto 1


(check-sat)

