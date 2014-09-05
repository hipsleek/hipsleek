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




(define-fun ListO ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (and (distinct nil ?x)
                 (tobool (pto ?x  (ref f0 ?y) )
                )
        )


        (exists ((?xp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x  (ref f0 ?xp) )
                (ListE ?xp ?y)
        )

                )))

) )
 )

(define-fun ListE ((?x GTyp) (?y GTyp)) Space


        (exists ((?xp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x  (ref f0 ?xp) )
                (ListO ?xp ?y)
        )

                )))

 )


;;;ListE(x,y) * ListE(y,z) |- ListE(x,z)              

(define-fun alpha2 () SetLoc)
(define-fun alpha3 () SetLoc)

(define-fun x () GenTyp)
(define-fun y () GenTyp)
(define-fun z () GenTyp)

(assert (tobool (sep
        (index alpha1 (ListE x y))
        (index alpha2 (ListE y z))
)))

(assert (not (tobool
        (index alpha3 (ListE x z))
)))




(check-sat)

