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

(define-fun P ((?x GTyp)) Space 
(tospace (or 

	(= nil ?x)


	(and (distinct nil ?x)
		 (tobool (Q ?x ?x)
		)
	)

) )
 )


(define-fun Q ((?x GTyp) (?y GTyp)) Space 
(tospace (or 

	(exists ((?d GenTyp) (?c GenTyp))
		
		 (and (= nil ?y)
		(distinct nil ?x)
			(tobool 
	(sep (pto ?x (sref  (ref f0 ?d)  (ref f1 ?c) ))
		(P ?d)
	)

		)))


	(exists ((?d GenTyp) (?c GenTyp))
		
		 (and (distinct nil ?y)
			(tobool 
	(sep (pto ?y (sref  (ref f0 ?d)  (ref f1 ?c) ))
		(Q ?x ?c)
	)

		)))

) )
 )


;index vars 
(define-fun alpha1 () SetLoc)

;vars 

;problem 
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1))))

;;pto 2

;;pto 2


(check-sat)

