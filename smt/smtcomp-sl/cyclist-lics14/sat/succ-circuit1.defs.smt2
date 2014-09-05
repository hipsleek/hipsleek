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


(define-fun succ1circuit ((?x1 GTyp) (?y1 GTyp)) Space 
 
(not ?x1 ?y1)
 )


(define-fun P ((?x1 GTyp)) Space 
 

	(sep (one ?x1)
		(Q ?x1)
	)

 )


(define-fun Q ((?y1 GTyp)) Space 
(tospace (or 
(zero ?y1)

	(exists ((?x1 GenTyp))
		
		 (tobool 
	(sep (succ1circuit ?x1 ?y1)
		(Q ?x1)
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
;;(assert (tobool (index alpha1 (succ1circuit  x0 x1))))
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0))))
(define-fun x0 () GenTyp)
(assert (tobool (index alpha1 (Q  x0))))


(check-sat)

