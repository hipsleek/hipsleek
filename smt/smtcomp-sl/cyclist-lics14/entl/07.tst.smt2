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




(define-fun SLL ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (= ?x ?y)


        (exists ((?xp GenTyp) (?yp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x (sref  (ref f0 ?xp)  (ref f1 ?yp) ))
                (SLL ?xp ?y)
        )

                )))

) )
 )



(define-fun DLL ((?x GTyp) (?y GTyp) (?z GTyp) (?w GTyp)) Space
(tospace (or

        (and (= ?x ?y)
                (= ?z ?w)
        )


        (exists ((?zp GenTyp))

                 (and (distinct nil ?x)
                        (tobool
        (sep (pto ?x (sref  (ref f0 ?zp)  (ref f1 ?w) ))
                (DLL ?zp ?y ?z ?x)
        )

                )))

) )
 )


;;;DLL(x,y,z,w) |- SLL(x,y)            

(define-fun alpha2 () SetLoc)

(define-fun x () GenTyp)
(define-fun y () GenTyp)
(define-fun z () GenTyp)
(define-fun w () GenTyp)

(assert (tobool 
        (index alpha1 (DLL x y z w))
))

(assert (not (tobool
        (index alpha2 (SLL x y))
)))



(check-sat)

