(set-logic QF_S)
(set-info :source |
  James Brotherston, Nikos Gorogiannis, and Rasmus Petersen
  A Generic Cyclic Theorem Prover. APLAS, 2012.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version 2014-05-31)




;generic sort

(declare-sort GTyp 0)

;generic fields
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))



(define-fun RList ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (and (distinct nil ?x)
                 (tobool (pto ?x  (ref f0 ?y) )
                )
        )


        (exists ((?xp GTyp))

                 (and (distinct ?xp nil)
                        (tobool
        (ssep (pto ?xp  (ref f0 ?y) )
                (RList ?x ?xp)
        )

                )))

) )
 )

;;;x->y * RList(y,z) |- RList(x,z) 

(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)

(assert (tobool (ssep
	(pto x (ref f0 y))
	(RList y z)
)))

(assert (not (tobool 
	(RList x z)
)))



(check-sat)

