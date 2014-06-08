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

(define-fun P ((?x1 GTyp)) Space 

	(ssep (one ?x1)
		(Q ?x1)
	)
)


(define-fun Q ((?y1 GTyp)) Space 
(tospace (or 
(tobool (zero ?y1))

	(exists ((?x1 GTyp))
		
		 (tobool 
	(ssep (succ1circuit ?x1 ?y1)
		(Q ?x1)
	)

		)
	)
))
)


(define-fun succ1circuit ((?x1 GTyp) (?y1 GTyp)) Space 
(notg ?x1 ?y1))


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

(assert (tobool (P  x0)))

(check-sat)
