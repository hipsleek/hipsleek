(set-logic QF_SHID)

(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez. 
  A decision procedure for satisfiability in separation logic with inductive 
  predicates. CSL-LICS, 2014. 
  https://github.com/ngorogiannis/cyclist/releases/tag/CSL-LICS14
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)

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
	(I001 ((a RefGTyp)) Bool
	)

	(ls ((a RefGTyp)) Bool
	)

	(I4675 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I27148 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I4676 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I27149 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I27119 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I10543 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I4703 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I4621 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I4523 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I4524 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I4584 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I4574 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I4503 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I798 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I799 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I2074 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I833 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I782 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I046 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I047 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I341 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I088 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I034 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I021 ((a RefGTyp)(b RefGTyp)(c RefGTyp)) Bool
	)

	(I008 ((a RefGTyp)(b RefGTyp)) Bool
	)

	(I022 ((a RefGTyp)(b RefGTyp)(c RefGTyp)) Bool
	)

	(I013 ((a RefGTyp)(b RefGTyp)(c RefGTyp)) Bool
	)

	(I007 ((a RefGTyp)(b RefGTyp)) Bool
	)

	(I003 ((a RefGTyp)(b RefGTyp)) Bool
	)
		)
		((exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I003 a a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) a)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct (as nil RefGTyp) a)
			(I001 a )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) g)
		(sep 
			(pto g (c_GTyp a00 (as nil RefGTyp) ))
			(I27119 a b c d e f g a00 )
		)

		)

		)

	
			(I4675 a b c d e f h )
	(or 
		(and 
			(= (as nil RefGTyp) a)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct (as nil RefGTyp) a)
			(I4703 a b c d e f g )
		)

	)
	
			(I4676 a b c d e f h )
	(or 
		(and 
			(= (as nil RefGTyp) h)
			(I27149 a b c d e f g h )
		)

	
		(and 
			(distinct (as nil RefGTyp) h)
			(I27148 a b c d e f g h )
		)

	)
	
			(I4676 h b c d e f g )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I10543 a b c d e f g a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) g)
			(I4676 a b c d e f g )
		)

	
		(and 
			(distinct (as nil RefGTyp) g)
			(I4675 a b c d e f g )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) f)
		(sep 
			(pto f (c_GTyp a00 (as nil RefGTyp) ))
			(I4621 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= a f)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct a f)
			(I4574 a b c d e f )
		)

	)
	
			(I4524 g b c d e f )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I4584 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) f)
			(I4524 a b c d e f )
		)

	
		(and 
			(distinct (as nil RefGTyp) f)
			(I4523 a b c d e f )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) e)
		(sep 
			(pto e (c_GTyp a00 (as nil RefGTyp) ))
			(I4503 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= b e)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct b e)
			(I833 a b c d e )
		)

	)
	
			(I799 a f c d e )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I2074 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) e)
			(I799 a b c d e )
		)

	
		(and 
			(distinct (as nil RefGTyp) e)
			(I798 a b c d e )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) d)
		(sep 
			(pto d (c_GTyp a00 (as nil RefGTyp) ))
			(I782 a b c d a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) b)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct (as nil RefGTyp) b)
			(I088 a b c d )
		)

	)
	
			(I047 a e c d )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I341 a b c d a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) d)
			(I047 a b c d )
		)

	
		(and 
			(distinct (as nil RefGTyp) d)
			(I046 a b c d )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) c)
		(sep 
			(pto c (c_GTyp a00 (as nil RefGTyp) ))
			(I034 a b c a00 )
		)

		)

		)

	
			(_ emp RefGTyp GTyp)
	
			(I008 b c )
	(or 
		(and 
			(= (as nil RefGTyp) c)
			(I022 a b c )
		)

	
		(and 
			(distinct (as nil RefGTyp) c)
			(I021 a b c )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I013 a b a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) b)
			(I008 a b )
		)

	
		(and 
			(distinct (as nil RefGTyp) b)
			(I007 a b )
		)

	)
		)
)


(check-sat) 
;; variables
(declare-const x0 RefGTyp)

(assert 
			(ls x0 )
)

(check-sat)
