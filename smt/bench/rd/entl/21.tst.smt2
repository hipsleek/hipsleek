(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Perez.
  A decision procedure for satisfiability in ssssseparation logic with inductive
  predicates. To appear at CSL-LICS, 2014.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)



;generic sort

(declare-sort GTyp 0)

;generic fields
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))




(define-fun ListO ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (and (distinct nil ?x)
                 (tobool (pto ?x  (ref f0 ?y) )
                )
        )


        (exists ((?xp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x  (ref f0 ?xp) )
                (ListE ?xp ?y)
        )

                )))

) )
 )

(define-fun ListE ((?x GTyp) (?y GTyp)) Space
(tospace

        (exists ((?xp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x  (ref f0 ?xp) )
                (ListO ?xp ?y)
        )

                )))

 ))

(define-fun ListX ((?x GTyp) (?y GTyp)) Space
(tospace (or
        (tobool (ListO ?x ?y))
        (tobool (ListE ?x ?y))

) )
 )

 
(define-fun List ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (and (distinct nil ?x)
                 (tobool (pto ?x  (ref f0 ?y) )
                )
        )


        (exists ((?xp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x  (ref f0 ?xp) )
                (List ?xp ?y)
        )

                )))

) )
 )

;;;ListE_1(x,y) \/ ListO_1(x,y) |- List_2(x,y)




(declare-fun x () GTyp)
(declare-fun y () GTyp)

(assert 
	(tobool (ListX x y))
)

(assert (not (tobool
        (List x y)
)))



(check-sat)

