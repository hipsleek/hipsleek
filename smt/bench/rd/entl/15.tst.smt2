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




(define-fun BinPath ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (= ?x ?y)


        (exists ((?xp GTyp) (?yp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x (sref  (ref f0 ?xp)  (ref f1 ?yp) ))
                (BinPath ?xp ?y)
        )

                )))


        (exists ((?xp GTyp) (?yp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x (sref  (ref f0 ?xp)  (ref f1 ?yp) ))
                (BinPath ?yp ?y)
        )

                )))

) )
 )

;;;BinPath(x,z) * BinPath(z,y) |- BinPath(x,y)          




(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)

(assert (tobool (ssep
        (BinPath x z)
        (BinPath z y)
)))

(assert (not (tobool
        (BinPath x y)
)))



(check-sat)

