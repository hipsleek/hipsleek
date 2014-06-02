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

(define-fun ls ((?a GTyp)) Space 
(tospace (or 

	(= nil ?a)


	(and (distinct nil ?a)
		 (tobool (I001 ?a)
		)
	)
))
)


(define-fun I27148 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp) (?h GTyp)) Space 
(I4675 ?a ?b ?c ?d ?e ?f ?h))


(define-fun I27149 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp) (?h GTyp)) Space 
(I4676 ?a ?b ?c ?d ?e ?f ?h))


(define-fun I27119 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp) (?h GTyp)) Space 
(tospace (or 

	(and (= nil ?h)
		 (tobool (I27149 ?a ?b ?c ?d ?e ?f ?g ?h)
		)
	)


	(and (distinct nil ?h)
		 (tobool (I27148 ?a ?b ?c ?d ?e ?f ?g ?h)
		)
	)
))
)


(define-fun I4675 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?g)
			(tobool 
	(ssep (pto ?g  (ref f0 ?a00) )
		(I27119 ?a ?b ?c ?d ?e ?f ?g ?a00)
	)

		))
	))
)


(define-fun I10543 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp) (?h GTyp)) Space 
(I4676 ?h ?b ?c ?d ?e ?f ?g))


(define-fun I4703 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?a)
			(tobool 
	(ssep (pto ?a  (ref f0 ?a00) )
		(I10543 ?a ?b ?c ?d ?e ?f ?g ?a00)
	)

		))
	))
)


(define-fun I4676 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp)) Space 
(tospace (or 

	(= nil ?a)


	(and (distinct nil ?a)
		 (tobool (I4703 ?a ?b ?c ?d ?e ?f ?g)
		)
	)
))
)


(define-fun I4621 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp)) Space 
(tospace (or 

	(and (= nil ?g)
		 (tobool (I4676 ?a ?b ?c ?d ?e ?f ?g)
		)
	)


	(and (distinct nil ?g)
		 (tobool (I4675 ?a ?b ?c ?d ?e ?f ?g)
		)
	)
))
)


(define-fun I4523 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?f)
			(tobool 
	(ssep (pto ?f  (ref f0 ?a00) )
		(I4621 ?a ?b ?c ?d ?e ?f ?a00)
	)

		))
	))
)


(define-fun I4584 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp) (?g GTyp)) Space 
(I4524 ?g ?b ?c ?d ?e ?f))


(define-fun I4574 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?a)
			(tobool 
	(ssep (pto ?a  (ref f0 ?a00) )
		(I4584 ?a ?b ?c ?d ?e ?f ?a00)
	)

		))
	))
)


(define-fun I4524 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp)) Space 
(tospace (or 

	(= ?a ?f)


	(and (distinct ?a ?f)
		 (tobool (I4574 ?a ?b ?c ?d ?e ?f)
		)
	)
))
)


(define-fun I4503 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp)) Space 
(tospace (or 

	(and (= nil ?f)
		 (tobool (I4524 ?a ?b ?c ?d ?e ?f)
		)
	)


	(and (distinct nil ?f)
		 (tobool (I4523 ?a ?b ?c ?d ?e ?f)
		)
	)
))
)


(define-fun I798 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?e)
			(tobool 
	(ssep (pto ?e  (ref f0 ?a00) )
		(I4503 ?a ?b ?c ?d ?e ?a00)
	)

		))
	))
)


(define-fun I2074 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp) (?f GTyp)) Space 
(I799 ?a ?f ?c ?d ?e))


(define-fun I833 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?b)
			(tobool 
	(ssep (pto ?b  (ref f0 ?a00) )
		(I2074 ?a ?b ?c ?d ?e ?a00)
	)

		))
	))
)


(define-fun I799 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp)) Space 
(tospace (or 

	(= ?b ?e)


	(and (distinct ?b ?e)
		 (tobool (I833 ?a ?b ?c ?d ?e)
		)
	)
))
)


(define-fun I782 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp)) Space 
(tospace (or 

	(and (= nil ?e)
		 (tobool (I799 ?a ?b ?c ?d ?e)
		)
	)


	(and (distinct nil ?e)
		 (tobool (I798 ?a ?b ?c ?d ?e)
		)
	)
))
)


(define-fun I046 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?d)
			(tobool 
	(ssep (pto ?d  (ref f0 ?a00) )
		(I782 ?a ?b ?c ?d ?a00)
	)

		))
	))
)


(define-fun I341 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp) (?e GTyp)) Space 
(I047 ?a ?e ?c ?d))


(define-fun I088 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?b)
			(tobool 
	(ssep (pto ?b  (ref f0 ?a00) )
		(I341 ?a ?b ?c ?d ?a00)
	)

		))
	))
)


(define-fun I047 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp)) Space 
(tospace (or 

	(= nil ?b)


	(and (distinct nil ?b)
		 (tobool (I088 ?a ?b ?c ?d)
		)
	)
))
)


(define-fun I034 ((?a GTyp) (?b GTyp) (?c GTyp) (?d GTyp)) Space 
(tospace (or 

	(and (= nil ?d)
		 (tobool (I047 ?a ?b ?c ?d)
		)
	)


	(and (distinct nil ?d)
		 (tobool (I046 ?a ?b ?c ?d)
		)
	)
))
)


(define-fun I021 ((?a GTyp) (?b GTyp) (?c GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?c)
			(tobool 
	(ssep (pto ?c  (ref f0 ?a00) )
		(I034 ?a ?b ?c ?a00)
	)

		))
	))
)


(define-fun I022 ((?a GTyp) (?b GTyp) (?c GTyp)) Space 
(I008 ?b ?c))


(define-fun I013 ((?a GTyp) (?b GTyp) (?c GTyp)) Space 
(tospace (or 

	(and (= nil ?c)
		 (tobool (I022 ?a ?b ?c)
		)
	)


	(and (distinct nil ?c)
		 (tobool (I021 ?a ?b ?c)
		)
	)
))
)


(define-fun I007 ((?a GTyp) (?b GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?b)
			(tobool 
	(ssep (pto ?b  (ref f0 ?a00) )
		(I013 ?a ?b ?a00)
	)

		))
	))
)


(define-fun I008 ((?a GTyp) (?b GTyp)) Space 
emp)


(define-fun I003 ((?a GTyp) (?b GTyp)) Space 
(tospace (or 

	(and (= nil ?b)
		 (tobool (I008 ?a ?b)
		)
	)


	(and (distinct nil ?b)
		 (tobool (I007 ?a ?b)
		)
	)
))
)


(define-fun I001 ((?a GTyp)) Space 

	(tospace (exists ((?a00 GTyp))
		
		 (and (distinct nil ?a)
			(tobool 
	(ssep (pto ?a  (ref f0 ?a00) )
		(I003 ?a ?a00)
	)

		))
	))
)


;vars 

;problem 
(declare-fun x0 () GTyp)

(assert (tobool (ls  x0)))

(check-sat)

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1

;;pto 1
