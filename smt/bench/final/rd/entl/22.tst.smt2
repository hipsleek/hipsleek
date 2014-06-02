(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Perez.
  A decision procedure for satisfiability in ssssseparation logic with inductive
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

;;;ls(x,y) * y->z * ls(z,nil) |- ls(x,z) * ls(z,nil)





(declare-fun x () GTyp)
(declare-fun y () GTyp)
(declare-fun z () GTyp)

(assert (tobool (ssep
        (ls x y)
	(pto y (ref f0 z))
        (ls z nil)
))))

(assert (not (tobool (ssep
        (ls x z)
        (ls z nil)
))))



(check-sat)

