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
	(ssep (succ1rec ?x1 ?y1)
		(Q ?x1)
	)

		)
	)
))
)


(define-fun succ1rec ((?x1 GTyp) (?y1 GTyp)) Space 

	(ssep (zero ?x1)
		(one ?y1)
	)
)


(define-fun zero ((?x GTyp)) Space 

	(tospace (= nil ?x))
)


(define-fun one ((?x GTyp)) Space 

	(tospace (distinct nil ?x))
)


;vars 

;problem 
(declare-fun x0 () GTyp)

(assert (tobool (P  x0)))

(check-sat)
