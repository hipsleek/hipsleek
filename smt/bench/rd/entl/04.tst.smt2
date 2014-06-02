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

;;;List(x,y) * List(y,z) |- List(x,z)                   




(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)

(assert (tobool (ssep
        (List x y)
        (List y z)
)))

(assert (not (tobool
        (List x z)
)))




(check-sat)

