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

(define-fun zero ((?x GTyp)) Space 
 

	(= nil ?x)

 )


(define-fun one ((?x GTyp)) Space 
 

	(distinct nil ?x)

 )


(define-fun and ((?x GTyp) (?y GTyp) (?z GTyp)) Space 
(tospace (or 

	(sep (zero ?x)
		(zero ?z)
	)


	(sep (zero ?y)
		(zero ?z)
	)


	(sep (one ?x)
		(one ?y)
		(one ?z)
	)

) )
 )


(define-fun xor ((?x GTyp) (?y GTyp) (?z GTyp)) Space 
(tospace (or 

	(sep (zero ?x)
		(zero ?y)
		(zero ?z)
	)


	(sep (zero ?x)
		(one ?y)
		(one ?z)
	)


	(sep (one ?x)
		(zero ?y)
		(one ?z)
	)


	(sep (one ?x)
		(one ?y)
		(zero ?z)
	)

) )
 )


(define-fun not ((?x GTyp) (?y GTyp)) Space 
(tospace (or 

	(sep (zero ?x)
		(one ?y)
	)


	(sep (one ?x)
		(zero ?y)
	)

) )
 )


(define-fun succ4circuit ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
 

	(exists ((?z3 GenTyp) (?z4 GenTyp))
		
		 (tobool 
	(sep (not ?x1 ?y1)
		(xor ?x1 ?x2 ?y2)
		(and ?x1 ?x2 ?z3)
		(xor ?z3 ?x3 ?y3)
		(and ?z3 ?x3 ?z4)
		(xor ?x4 ?y4 ?z4)
	)

		)
	)

 )


(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp)) Space 
 

	(sep (one ?x1)
		(one ?x2)
		(one ?x3)
		(one ?x4)
		(Q ?x1 ?x2 ?x3 ?x4)
	)

 )


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
(tospace (or 

	(sep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
		(zero ?y4)
	)


	(exists ((?x1 GenTyp) (?x2 GenTyp) (?x3 GenTyp) (?x4 GenTyp))
		
		 (tobool 
	(sep (succ4circuit ?x1 ?x2 ?x3 ?x4 ?y1 ?y2 ?y3 ?y4)
		(Q ?x1 ?x2 ?x3 ?x4)
	)

		)
	)

) )
 )


;index vars 
(define-fun alpha1 () SetLoc)

;vars 

;problem 
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (zero  x0))))
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (one  x0))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(assert (tobool (index alpha1 (and  x0 x1 x2))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(assert (tobool (index alpha1 (xor  x0 x1 x2))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(assert (tobool (index alpha1 (not  x0 x1))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(assert (tobool (index alpha1 (succ4circuit  x0 x1 x2 x3 x4 x5 x6 x7))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0 x1 x2 x3))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(define-fun x2 () GenTyp)
(define-fun x3 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1 x2 x3))))



(check-sat)

