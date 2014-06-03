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




(define-fun BSLL ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (= ?x ?y)


        (exists ((?xp GTyp) (?yp GTyp))

                 (and (distinct ?xp nil)
                        (tobool
        (ssep (pto ?xp (sref  (ref f0 ?yp)  (ref f1 ?y) ))
                (BSLL ?x ?xp)
        )

                )))

) )
 )



(define-fun DLL ((?x GTyp) (?y GTyp) (?z GTyp) (?w GTyp)) Space
(tospace (or

        (and (= ?x ?y)
                (= ?z ?w)
        )


        (exists ((?zp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x (sref  (ref f0 ?zp)  (ref f1 ?w) ))
                (DLL ?zp ?y ?z ?x)
        )

                )))

) )
 )

;;;DLL(x,y,z,w) |- BSLL(z,w)                            



(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)
(declare-fun w () GTyp)

(assert (tobool
        (DLL x y z w)
))

(assert (not (tobool
        (BSLL z w)
)))



(check-sat)

