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


(define-fun succ2rec ((?x1 GTyp) (?x2 GTyp) (?y1 GTyp) (?y2 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ1rec ?x2 ?y2)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ1rec ((?x1 GTyp) (?y1 GTyp)) Space 
 

	(sep (zero ?x1)
		(one ?y1)
	)

 )


(define-fun P ((?x1 GTyp) (?x2 GTyp)) Space 
 

	(sep (one ?x1)
		(one ?x2)
		(Q ?x1 ?x2)
	)

 )


(define-fun Q ((?y1 GTyp) (?y2 GTyp)) Space 
(tospace (or 

	(sep (zero ?y1)
		(zero ?y2)
	)


	(exists ((?x1 GenTyp) (?x2 GenTyp))
		
		 (tobool 
	(sep (succ2rec ?x1 ?x2 ?y1 ?y2)
		(Q ?x1 ?x2)
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
;;(define-fun x3 () GenTyp)
;;(assert (tobool (index alpha1 (succ2rec  x0 x1 x2 x3))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(assert (tobool (index alpha1 (succ1rec  x0 x1))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0 x1))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1))))


(check-sat)

