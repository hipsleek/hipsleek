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




(define-fun ls ((?x GTyp) (?y GTyp)) Space
(tospace (or

        (= ?x ?y)


        (exists ((?xp GTyp))

                 (and (distinct nil ?x)
                (distinct ?x ?y)
                        (tobool
        (ssep (pto ?x  (ref f0 ?xp) )
                (ls ?xp ?y)
        )

                )))

) )
 )

;;;x!=z * x->y * ls(y,z) |- ls(x,z) 



(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)

(assert (and (distinct x z)
	(tobool (ssep
        (pto x (ref f0 y))
        (ls y z)
))))

(assert (not (tobool
        (ls x z)
)))




(check-sat)

