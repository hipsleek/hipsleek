(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez. 
  A decision procedure for satisfiability in separation logic with inductive 
  predicates. To appear at CSL-LICS, 2014. 
  https://github.com/ngorogiannis/cyclist/releases/tag/CSL-LICS14
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version 2014-05-31)




;generic sort 

(declare-sort GTyp 0)

;generic fields 
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))

;predicates 

(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp)) Space 

	(ssep (one ?x1)
		(one ?x2)
		(one ?x3)
		(Q ?x1 ?x2 ?x3)
	)
)


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
	)
)

	(exists ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp))
		
		 (tobool 
	(ssep (succ3circuit ?x1 ?x2 ?x3 ?y1 ?y2 ?y3)
		(Q ?x1 ?x2 ?x3)
	)

		)
	)
))
)


(define-fun succ3circuit ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 

	(tospace (exists ((?z3 GTyp))
		
		 (tobool 
	(ssep (notg ?x1 ?y1)
		(xorg ?x1 ?x2 ?y2)
		(andg ?x1 ?x2 ?z3)
		(xorg ?z3 ?x3 ?y3)
	)

		)
	))
)


(define-fun notg ((?x GTyp) (?y GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?x)
		(one ?y)
	)
)
(tobool 
	(ssep (one ?x)
		(zero ?y)
	)
)))
)


(define-fun xorg ((?x GTyp) (?y GTyp) (?z GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?x)
		(zero ?y)
		(zero ?z)
	)
)
(tobool 
	(ssep (zero ?x)
		(one ?y)
		(one ?z)
	)
)
(tobool 
	(ssep (one ?x)
		(zero ?y)
		(one ?z)
	)
)
(tobool 
	(ssep (one ?x)
		(one ?y)
		(zero ?z)
	)
)))
)


(define-fun andg ((?x GTyp) (?y GTyp) (?z GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?x)
		(zero ?z)
	)
)
(tobool 
	(ssep (zero ?y)
		(zero ?z)
	)
)
(tobool 
	(ssep (one ?x)
		(one ?y)
		(one ?z)
	)
)))
)


(define-fun one ((?x GTyp)) Space 

	(tospace (distinct nil ?x))
)


(define-fun zero ((?x GTyp)) Space 

	(tospace (= nil ?x))
)


;vars 

;problem 
(declare-fun x0 () GTyp)
(declare-fun x1 () GTyp)
(declare-fun x2 () GTyp)

(assert (tobool (P  x0 x1 x2)))

(check-sat)
