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

;;;DLL(x,y,z,w) * DLL(a,x,w,b) |- DLL(a,y,z,b)    

(define-fun alpha2 () SetLoc)
(define-fun alpha3 () SetLoc)

(define-fun a () GenTyp)
(define-fun b () GenTyp)
(define-fun x () GenTyp)
(define-fun y () GenTyp)
(define-fun z () GenTyp)
(define-fun w () GenTyp)

(assert (tobool (sep
        (index alpha1 (DLL x y z w))
        (index alpha2 (DLL a x w b))
)))

(assert (not (tobool
        (index alpha3 (DLL a y z b))
)))



(check-sat)

