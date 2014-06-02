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

(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp)) Space 

	(ssep (one ?x1)
		(one ?x2)
		(one ?x3)
		(one ?x4)
		(one ?x5)
		(one ?x6)
		(one ?x7)
		(one ?x8)
		(one ?x9)
		(one ?x10)
		(one ?x11)
		(one ?x12)
		(one ?x13)
		(one ?x14)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14)
	)
)


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp)) Space 
(tospace (or 
(tobool 
	(ssep (zero ?y1)
		(zero ?y2)
		(zero ?y3)
		(zero ?y4)
		(zero ?y5)
		(zero ?y6)
		(zero ?y7)
		(zero ?y8)
		(zero ?y9)
		(zero ?y10)
		(zero ?y11)
		(zero ?y12)
		(zero ?y13)
		(zero ?y14)
	)
)

	(exists ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp))
		
		 (tobool 
	(ssep (succ14circuit ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14)
	)

		)
	)
))
)


(define-fun succ14circuit ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp)) Space 

	(tospace (exists ((?z3 GTyp) (?z4 GTyp) (?z5 GTyp) (?z6 GTyp) (?z7 GTyp) (?z8 GTyp) (?z9 GTyp) (?z10 GTyp) (?z11 GTyp) (?z12 GTyp) (?z13 GTyp) (?z14 GTyp))
		
		 (tobool 
	(ssep (notg ?x1 ?y1)
		(xorg ?x1 ?x2 ?y2)
		(andg ?x1 ?x2 ?z3)
		(xorg ?z3 ?x3 ?y3)
		(andg ?z3 ?x3 ?z4)
		(xorg ?x4 ?y4 ?z4)
		(andg ?z4 ?x4 ?z5)
		(xorg ?x5 ?y5 ?z5)
		(andg ?z5 ?x5 ?z6)
		(xorg ?x6 ?y6 ?z6)
		(andg ?z6 ?x6 ?z7)
		(xorg ?x7 ?y7 ?z7)
		(andg ?z7 ?x7 ?z8)
		(xorg ?x8 ?y8 ?z8)
		(andg ?z8 ?x8 ?z9)
		(xorg ?x9 ?y9 ?z9)
		(andg ?z9 ?x9 ?z10)
		(xorg ?x10 ?y10 ?z10)
		(andg ?z10 ?x10 ?z11)
		(xorg ?x11 ?y11 ?z11)
		(andg ?z11 ?x11 ?z12)
		(xorg ?x12 ?y12 ?z12)
		(andg ?z12 ?x12 ?z13)
		(xorg ?x13 ?y13 ?z13)
		(andg ?z13 ?x13 ?z14)
		(xorg ?x14 ?y14 ?z14)
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
(declare-fun x3 () GTyp)
(declare-fun x4 () GTyp)
(declare-fun x5 () GTyp)
(declare-fun x6 () GTyp)
(declare-fun x7 () GTyp)
(declare-fun x8 () GTyp)
(declare-fun x9 () GTyp)
(declare-fun x10 () GTyp)
(declare-fun x11 () GTyp)
(declare-fun x12 () GTyp)
(declare-fun x13 () GTyp)

(assert (tobool (P  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)))

(check-sat)
