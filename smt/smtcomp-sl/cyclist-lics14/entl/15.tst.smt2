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




(define-fun BinPath ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (= ?x ?y)


        (exists ((?xp GenTyp) (?yp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x (sref  (ref f0 ?xp)  (ref f1 ?yp) ))
                (BinPath ?xp ?y)
        )

                )))


        (exists ((?xp GenTyp) (?yp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x (sref  (ref f0 ?xp)  (ref f1 ?yp) ))
                (BinPath ?yp ?y)
        )

                )))

) )
 )

;;;BinPath(x,z) * BinPath(z,y) |- BinPath(x,y)          

(define-fun alpha2 () SetLoc)
(define-fun alpha3 () SetLoc)

(define-fun x () GenTyp)
(define-fun y () GenTyp)
(define-fun z () GenTyp)

(assert (tobool (sep
        (index alpha1 (BinPath x z))
        (index alpha2 (BinPath z y))
)))

(assert (not (tobool
        (index alpha3 (BinPath x y))
)))



(check-sat)

