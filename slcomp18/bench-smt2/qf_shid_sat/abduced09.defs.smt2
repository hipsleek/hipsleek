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

	(I40239 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I209166 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)(j RefGTyp)) Bool
	)

	(I209106 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I40306 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I209107 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I209073 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I40305 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I60989 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I40341 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I40109 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I40110 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I40192 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I40179 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I40085 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I39957 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I39958 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I40046 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I40035 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I39937 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I182 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I183 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I11677 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I7185 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I166 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I046 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I047 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I063 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I056 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
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
	(or 
		(and 
			(= (as nil RefGTyp) h)
			(I40306 a b c d e f g h )
		)

	
		(and 
			(distinct (as nil RefGTyp) h)
			(I40305 a b c d e f g h )
		)

	)
	
			(I40239 a b c d e f g j )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) i)
		(sep 
			(pto i (c_GTyp a00 (as nil RefGTyp) ))
			(I209166 a b c d e f g h i a00 )
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
			(I40341 a b c d e f g h )
		)

	)
	
			(I40306 a b c d e f g i )
	(or 
		(and 
			(= (as nil RefGTyp) i)
			(I209107 a b c d e f g h i )
		)

	
		(and 
			(distinct (as nil RefGTyp) i)
			(I209106 a b c d e f g h i )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) h)
		(sep 
			(pto h (c_GTyp a00 (as nil RefGTyp) ))
			(I209073 a b c d e f g h a00 )
		)

		)

		)

	
			(I40306 i b c d e f g h )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I60989 a b c d e f g h a00 )
		)

		)

		)

	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) g)
		(sep 
			(pto g (c_GTyp a00 (as nil RefGTyp) ))
			(I40239 a b c d e f g a00 )
		)

		)

		)

	(or 
		(and 
			(= a g)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct a g)
			(I40179 a b c d e f g )
		)

	)
	
			(I40110 h b c d e f g )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I40192 a b c d e f g a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) g)
			(I40110 a b c d e f g )
		)

	
		(and 
			(distinct (as nil RefGTyp) g)
			(I40109 a b c d e f g )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) f)
		(sep 
			(pto f (c_GTyp a00 (as nil RefGTyp) ))
			(I40085 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= b f)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct b f)
			(I40035 a b c d e f )
		)

	)
	
			(I39958 a g c d e f )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I40046 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) f)
			(I39958 a b c d e f )
		)

	
		(and 
			(distinct (as nil RefGTyp) f)
			(I39957 a b c d e f )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) e)
		(sep 
			(pto e (c_GTyp a00 (as nil RefGTyp) ))
			(I39937 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= c e)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct c e)
			(I7185 a b c d e )
		)

	)
	
			(I183 a b f d e )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) c)
		(sep 
			(pto c (c_GTyp a00 (as nil RefGTyp) ))
			(I11677 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) e)
			(I183 a b c d e )
		)

	
		(and 
			(distinct (as nil RefGTyp) e)
			(I182 a b c d e )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) d)
		(sep 
			(pto d (c_GTyp a00 (as nil RefGTyp) ))
			(I166 a b c d a00 )
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
			(I056 a b c d )
		)

	)
	
			(I047 e b c d )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I063 a b c d a00 )
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
