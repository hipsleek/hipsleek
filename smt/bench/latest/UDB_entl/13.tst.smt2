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





(define-fun BinListFirst ((?x GTyp)) Space
(tospace (or
	(tobool emp)

        (exists ((?yp GTyp) (?xp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x (sref  (ref f0 ?yp)  (ref f1 ?xp) ))
                (BinListFirst ?yp)
        )

                )))

) )
 )



(define-fun BinTree ((?x GTyp)) Space
(tospace (or
	(tobool emp)

        (exists ((?yp GTyp) (?xp GTyp))

                 (and (distinct nil ?x)
                        (tobool
        (ssep (pto ?x (sref  (ref f0 ?yp)  (ref f1 ?xp) ))
                (BinTree ?yp)
                (BinTree ?xp)
        )

                )))

) )
 )

;;;BinListFirst(x) |- BinTree(x)              



(declare-fun x () GTyp)

(assert (tobool 
        (BinListFirst x)
))

(assert (not (tobool
        (BinTree x)
)))



(check-sat)

