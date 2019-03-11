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

	(I1401 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I244887 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)(j RefGTyp)) Bool
	)

	(I63947 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I1444 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I63948 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I47298 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)(i RefGTyp)) Bool
	)

	(I47255 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I47256 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I47226 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I47186 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I47187 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I47161 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I1443 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I12199 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I8328 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I182 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I183 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I381 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I196 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
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
			(= (as nil RefGTyp) f)
			(I1444 a b c d e f )
		)

	
		(and 
			(distinct (as nil RefGTyp) f)
			(I1443 a b c d e f )
		)

	)
	
			(I1401 a b c d e j )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) i)
		(sep 
			(pto i (c_GTyp a00 (as nil RefGTyp) ))
			(I244887 a b c d e f g h i a00 )
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
			(I8328 a b c d e f )
		)

	)
	
			(I1444 a b c d e i )
	(or 
		(and 
			(= (as nil RefGTyp) i)
			(I63948 a b c d e f g h i )
		)

	
		(and 
			(distinct (as nil RefGTyp) i)
			(I63947 a b c d e f g h i )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) h)
		(sep 
			(pto h (c_GTyp a00 (as nil RefGTyp) ))
			(I47298 a b c d e f g h a00 )
		)

		)

		)

	
			(I1444 a b c d e h )
	(or 
		(and 
			(= (as nil RefGTyp) h)
			(I47256 a b c d e f g h )
		)

	
		(and 
			(distinct (as nil RefGTyp) h)
			(I47255 a b c d e f g h )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) g)
		(sep 
			(pto g (c_GTyp a00 (as nil RefGTyp) ))
			(I47226 a b c d e f g a00 )
		)

		)

		)

	
			(I1444 a b c d e g )
	(or 
		(and 
			(= (as nil RefGTyp) g)
			(I47187 a b c d e f g )
		)

	
		(and 
			(distinct (as nil RefGTyp) g)
			(I47186 a b c d e f g )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) f)
		(sep 
			(pto f (c_GTyp a00 (as nil RefGTyp) ))
			(I47161 a b c d e f a00 )
		)

		)

		)

	
			(I1444 a g c d e f )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I12199 a b c d e f a00 )
		)

		)

		)

	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) e)
		(sep 
			(pto e (c_GTyp a00 (as nil RefGTyp) ))
			(I1401 a b c d e a00 )
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
			(I196 a b c d e )
		)

	)
	
			(I183 f b c d e )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I381 a b c d e a00 )
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
