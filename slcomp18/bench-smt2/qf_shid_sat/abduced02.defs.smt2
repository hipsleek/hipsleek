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

	(I2783 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I79311 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I2834 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I2835 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I50053 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I15080 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I2696 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I2697 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I2749 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I2740 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I2676 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I482 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I483 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I1956 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I510 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I466 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I046 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I008 ((a RefGTyp)(b RefGTyp)) Bool
	)

	(I047 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I034 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I021 ((a RefGTyp)(b RefGTyp)(c RefGTyp)) Bool
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
			(= (as nil RefGTyp) g)
			(I2835 a b c d e f g )
		)

	
		(and 
			(distinct (as nil RefGTyp) g)
			(I2834 a b c d e f g )
		)

	)
	
			(I2783 a b c d e f h )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) g)
		(sep 
			(pto g (c_GTyp a00 (as nil RefGTyp) ))
			(I79311 a b c d e f g a00 )
		)

		)

		)

	(or 
		(and 
			(= b g)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct b g)
			(I15080 a b c d e f g )
		)

	)
	
			(I2835 a h c d e f g )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I50053 a b c d e f g a00 )
		)

		)

		)

	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) f)
		(sep 
			(pto f (c_GTyp a00 (as nil RefGTyp) ))
			(I2783 a b c d e f a00 )
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
			(I2740 a b c d e f )
		)

	)
	
			(I2697 g b c d e f )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I2749 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) f)
			(I2697 a b c d e f )
		)

	
		(and 
			(distinct (as nil RefGTyp) f)
			(I2696 a b c d e f )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) e)
		(sep 
			(pto e (c_GTyp a00 (as nil RefGTyp) ))
			(I2676 a b c d e a00 )
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
			(I510 a b c d e )
		)

	)
	
			(I483 a f c d e )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I1956 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) e)
			(I483 a b c d e )
		)

	
		(and 
			(distinct (as nil RefGTyp) e)
			(I482 a b c d e )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) d)
		(sep 
			(pto d (c_GTyp a00 (as nil RefGTyp) ))
			(I466 a b c d a00 )
		)

		)

		)

	
			(_ emp RefGTyp GTyp)
	
			(I008 c d )
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
