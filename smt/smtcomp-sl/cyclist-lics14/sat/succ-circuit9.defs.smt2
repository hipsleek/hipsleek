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


(define-fun succ9circuit ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp)) Space 
 

	(exists ((?z3 GenTyp) (?z4 GenTyp) (?z5 GenTyp) (?z6 GenTyp) (?z7 GenTyp) (?z8 GenTyp) (?z9 GenTyp))
		
		 (tobool 
	(sep (not ?x1 ?y1)
		(xor ?x1 ?x2 ?y2)
		(and ?x1 ?x2 ?z3)
		(xor ?z3 ?x3 ?y3)
		(and ?z3 ?x3 ?z4)
		(xor ?x4 ?y4 ?z4)
		(and ?z4 ?x4 ?z5)
		(xor ?x5 ?y5 ?z5)
		(and ?z5 ?x5 ?z6)
		(xor ?x6 ?y6 ?z6)
		(and ?z6 ?x6 ?z7)
		(xor ?x7 ?y7 ?z7)
		(and ?z7 ?x7 ?z8)
		(xor ?x8 ?y8 ?z8)
		(and ?z8 ?x8 ?z9)
		(xor ?x9 ?y9 ?z9)
	)

		)
	)

 )


(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp)) Space 
 

	(sep (one ?x1)
		(one ?x2)
		(one ?x3)
		(one ?x4)
		(one ?x5)
		(one ?x6)
		(one ?x7)
		(one ?x8)
		(one ?x9)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9)
	)

 )


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp)) Space 
(tospace (or 

	(sep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
		(zero ?y4)
		(zero ?y5)
		(zero ?y6)
		(zero ?y7)
		(zero ?y8)
		(zero ?y9)
	)


	(exists ((?x1 GenTyp) (?x2 GenTyp) (?x3 GenTyp) (?x4 GenTyp) (?x5 GenTyp) (?x6 GenTyp) (?x7 GenTyp) (?x8 GenTyp) (?x9 GenTyp))
		
		 (tobool 
	(sep (succ9circuit ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9)
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
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(define-fun x10 () GenTyp)
;;(define-fun x11 () GenTyp)
;;(define-fun x12 () GenTyp)
;;(define-fun x13 () GenTyp)
;;(define-fun x14 () GenTyp)
;;(define-fun x15 () GenTyp)
;;(define-fun x16 () GenTyp)
;;(define-fun x17 () GenTyp)
;;(assert (tobool (index alpha1 (succ9circuit  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0 x1 x2 x3 x4 x5 x6 x7 x8))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(define-fun x2 () GenTyp)
(define-fun x3 () GenTyp)
(define-fun x4 () GenTyp)
(define-fun x5 () GenTyp)
(define-fun x6 () GenTyp)
(define-fun x7 () GenTyp)
(define-fun x8 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1 x2 x3 x4 x5 x6 x7 x8))))


(check-sat)

