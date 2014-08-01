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


(define-fun succ5rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ4rec ?x2 ?x3 ?x4 ?x5 ?y2 ?y3 ?y4 ?y5)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ4rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ3rec ?x2 ?x3 ?x4 ?y2 ?y3 ?y4)
		(one ?x1)
		(zero ?y1)
	)

) )
 )


(define-fun succ3rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		 (tobool 
	(sep (zero ?x1)
		(one ?y1)
	)

		)
	)


	(sep (succ2rec ?x2 ?x3 ?y2 ?y3)
		(one ?x1)
		(zero ?y1)
	)

) )
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


(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp)) Space 
 

	(sep (one ?x1)
		(one ?x2)
		(one ?x3)
		(one ?x4)
		(one ?x5)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5)
	)

 )


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp)) Space 
(tospace (or 

	(sep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
		(zero ?y4)
		(zero ?y5)
	)


	(exists ((?x1 GenTyp) (?x2 GenTyp) (?x3 GenTyp) (?x4 GenTyp) (?x5 GenTyp))
		
		 (tobool 
	(sep (succ5rec ?x1 ?x2 ?x3 ?x4 ?x5 ?y1 ?y2 ?y3 ?y4 ?y5)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5)
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
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(define-fun x8 () GenTyp)
;;(define-fun x9 () GenTyp)
;;(assert (tobool (index alpha1 (succ5rec  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(define-fun x6 () GenTyp)
;;(define-fun x7 () GenTyp)
;;(assert (tobool (index alpha1 (succ4rec  x0 x1 x2 x3 x4 x5 x6 x7))))
;;(define-fun x0 () GenTyp)
;;(define-fun x1 () GenTyp)
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(define-fun x5 () GenTyp)
;;(assert (tobool (index alpha1 (succ3rec  x0 x1 x2 x3 x4 x5))))
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
;;(define-fun x2 () GenTyp)
;;(define-fun x3 () GenTyp)
;;(define-fun x4 () GenTyp)
;;(assert (tobool (index alpha1 (P  x0 x1 x2 x3 x4))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(define-fun x2 () GenTyp)
(define-fun x3 () GenTyp)
(define-fun x4 () GenTyp)
(assert (tobool (index alpha1 (Q  x0 x1 x2 x3 x4))))


(check-sat)

