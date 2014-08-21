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

(define-fun P ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp)) Space 

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
		(one ?x15)
		(one ?x16)
		(one ?x17)
		(one ?x18)
		(one ?x19)
		(one ?x20)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20)
	)
)


(define-fun Q ((?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp)) Space 
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
		(zero ?y15)
		(zero ?y16)
		(zero ?y17)
		(zero ?y18)
		(zero ?y19)
		(zero ?y20)
	)
)

	(exists ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp))
		
		 (tobool 
	(ssep (succ20rec ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20)
		(Q ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20)
	)

		)
	)
))
)


(define-fun succ20rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp) (?y20 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		(= ?x20 ?y20)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ19rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ19rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp) (?y19 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		(= ?x19 ?y19)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ18rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ18rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp) (?y18 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		(= ?x18 ?y18)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ17rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ17rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp) (?y17 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		(= ?x17 ?y17)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ16rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ16rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp) (?y16 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		(= ?x16 ?y16)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ15rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ15rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp) (?y15 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		(= ?x15 ?y15)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ14rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ14rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp) (?y14 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		(= ?x14 ?y14)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ13rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ13rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp) (?y13 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		(= ?x13 ?y13)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ12rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ12rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp) (?y12 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		(= ?x12 ?y12)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ11rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ11rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp) (?y11 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		(= ?x11 ?y11)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ10rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ10rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp) (?y10 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		(= ?x10 ?y10)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ9rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ9rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp) (?y9 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		(= ?x9 ?y9)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ8rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ8rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp) (?y8 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		(= ?x8 ?y8)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ7rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ7rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp) (?y7 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		(= ?x7 ?y7)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ6rec ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ6rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp) (?y6 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		(= ?x6 ?y6)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ5rec ?x2 ?x3 ?x4 ?x5 ?x6 ?y2 ?y3 ?y4 ?y5 ?y6)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ5rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp) (?y5 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		(= ?x5 ?y5)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ4rec ?x2 ?x3 ?x4 ?x5 ?y2 ?y3 ?y4 ?y5)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ4rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp) (?y4 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		(= ?x4 ?y4)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ3rec ?x2 ?x3 ?x4 ?y2 ?y3 ?y4)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ3rec ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?y1 GTyp) (?y2 GTyp) (?y3 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		(= ?x3 ?y3)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ2rec ?x2 ?x3 ?y2 ?y3)
		(one ?x1)
		(zero ?y1)
	)
)))
)


(define-fun succ2rec ((?x1 GTyp) (?x2 GTyp) (?y1 GTyp) (?y2 GTyp)) Space 
(tospace (or 

	(and (= ?x2 ?y2)
		 (tobool 
	(ssep (zero ?x1)
		(one ?y1)
	)

		)
	)

(tobool 
	(ssep (succ1rec ?x2 ?y2)
		(one ?x1)
		(zero ?y1)
	)
)))
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
(declare-fun x14 () GTyp)
(declare-fun x15 () GTyp)
(declare-fun x16 () GTyp)
(declare-fun x17 () GTyp)
(declare-fun x18 () GTyp)
(declare-fun x19 () GTyp)

(assert (tobool (P  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19)))

(check-sat)
