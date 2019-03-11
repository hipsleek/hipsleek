(set-logic QF_SHID)

(set-info :source |
  Quang Loc Le Q.Le@tees.ac.uk
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-07-07")

; Sorts for locations, one by cell sort
(declare-sort RefGTyp 0)

; Types of cells in the heap

(declare-datatypes (
	(GTyp 0)
	) (
	((c_GTyp (f0 RefGTyp) (f1 RefGTyp) ))
	)
)

; Type of heap

(declare-heap (RefGTyp GTyp) 
)
; User defined predicates
(define-funs-rec (
	(P ((x RefGTyp)) Bool
	)

	(R ((x RefGTyp)) Bool
	)

	(Q ((x RefGTyp)(y RefGTyp)) Bool
	)

        (S1 ((x RefGTyp)(y RefGTyp)(z RefGTyp)) Bool
	)

	(S2 ((x RefGTyp)(y RefGTyp)(z RefGTyp)(t RefGTyp)) Bool
	)

	(S3 ((x RefGTyp)(y RefGTyp)(z RefGTyp)(t RefGTyp)(v RefGTyp)) Bool
	)
		)
		(
	(or 
		(and 
			(= (as nil RefGTyp) x)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct (as nil RefGTyp) x)
			(Q x x )
		)

	)
	
		(and 
			(distinct (as nil RefGTyp) x)
			(P x )
		)

	(or (exists ((d RefGTyp)(c RefGTyp))
	 
		(and 
			(= (as nil RefGTyp) y)
			(distinct (as nil RefGTyp) x)
		(sep 
			(pto x (c_GTyp d c ))
			(P d )
		)
		)
		)

         (exists ((d RefGTyp)(c RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) y)
		(sep 
			(pto y (c_GTyp d c ))
			(Q x c )
		)
		)
		)

             (exists ((d RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) x)
		        (S1 x y d )

		)

		)

	   
        )
;;S1
        (or (exists ((c RefGTyp))

		(and 
			(= (as nil RefGTyp) (as nil RefGTyp))
		(sep
			(pto y (c_GTyp x c ))
			(pto z (c_GTyp c c ))
			(P z )
		)
		)
		)

             (exists ((c RefGTyp)(d RefGTyp))
	 
		(and 
			(= (as nil RefGTyp) c)
                        (= (as nil RefGTyp) d)
		(sep
                        (pto x (c_GTyp c d ))
			(Q x y)
		)

		)

	    )

	    (exists ((c RefGTyp)(d RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) c)
			(S2 c y z c)
		
		)

	    )

	 )

;;S2
        (or (exists ((c RefGTyp))

		(and 
			(= (as nil RefGTyp) (as nil RefGTyp))
		(sep
			(pto y (c_GTyp x c ))
			(pto z (c_GTyp c x ))
			(P t)
		)
		)
		)

             (exists ((c RefGTyp)(d RefGTyp))
	 
		(and 
			(= (as nil RefGTyp) c)
                        (= (as nil RefGTyp) d)
		(sep
                        (pto x (c_GTyp c d ))
			(Q x y)
		)

		)

	    )

	    (and 
		(= (as nil RefGTyp) y)
		(S1 x y z)
		
	    )

	    (exists ((c RefGTyp)(d RefGTyp))
	 
		(and 
		         (distinct (as nil RefGTyp) c)
		 	(S3 c y z d x)
		

		)

	    )

	 )

;;S3
        (or (exists ((c RefGTyp))

		(and 
			(= (as nil RefGTyp) (as nil RefGTyp))
		(sep
			(pto y (c_GTyp x c ))
			(pto z (c_GTyp c x ))
			(P t)
		)
		)
		)

             (exists ((c RefGTyp)(d RefGTyp))
	 
		(and 
			(= (as nil RefGTyp) c)
                        (= (as nil RefGTyp) d)
		(sep
                        (pto x (c_GTyp c d ))
			(Q x y)
		)

		)

	    )

	    (and 
		(= (as nil RefGTyp) y)
		(S1 x y z)
		
	    )

	    (exists ((c RefGTyp)(d RefGTyp)(e RefGTyp))
	 
		(and 
		         (distinct (as nil RefGTyp) c)
			 (= (as nil RefGTyp) e)
		 	(S2 e y z d)
		

		)

	    )

	 )

     )
)


(check-sat) 
;; variables
(declare-const x0 RefGTyp)

(assert 
			(R x0 )
)

(check-sat)
