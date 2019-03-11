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

	(I3724 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I21092 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I3725 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I21093 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I21063 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I10117 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)(h RefGTyp)) Bool
	)

	(I3752 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I3670 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I3572 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I3573 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I3633 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)(g RefGTyp)) Bool
	)

	(I3623 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I3552 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I634 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I635 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I2011 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)(f RefGTyp)) Bool
	)

	(I664 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I618 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
	)

	(I046 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I047 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)) Bool
	)

	(I337 ((a RefGTyp)(b RefGTyp)(c RefGTyp)(d RefGTyp)(e RefGTyp)) Bool
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
			(I21063 a b c d e f g a00 )
		)

		)

		)

	
			(I3724 a b c d e f h )
	(or 
		(and 
			(= (as nil RefGTyp) a)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct (as nil RefGTyp) a)
			(I3752 a b c d e f g )
		)

	)
	
			(I3725 a b c d e f h )
	(or 
		(and 
			(= (as nil RefGTyp) h)
			(I21093 a b c d e f g h )
		)

	
		(and 
			(distinct (as nil RefGTyp) h)
			(I21092 a b c d e f g h )
		)

	)
	
			(I3725 h b c d e f g )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I10117 a b c d e f g a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) g)
			(I3725 a b c d e f g )
		)

	
		(and 
			(distinct (as nil RefGTyp) g)
			(I3724 a b c d e f g )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) f)
		(sep 
			(pto f (c_GTyp a00 (as nil RefGTyp) ))
			(I3670 a b c d e f a00 )
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
			(I3623 a b c d e f )
		)

	)
	
			(I3573 g b c d e f )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) a)
		(sep 
			(pto a (c_GTyp a00 (as nil RefGTyp) ))
			(I3633 a b c d e f a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) f)
			(I3573 a b c d e f )
		)

	
		(and 
			(distinct (as nil RefGTyp) f)
			(I3572 a b c d e f )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) e)
		(sep 
			(pto e (c_GTyp a00 (as nil RefGTyp) ))
			(I3552 a b c d e a00 )
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
			(I664 a b c d e )
		)

	)
	
			(I635 a f c d e )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I2011 a b c d e a00 )
		)

		)

		)

	(or 
		(and 
			(= (as nil RefGTyp) e)
			(I635 a b c d e )
		)

	
		(and 
			(distinct (as nil RefGTyp) e)
			(I634 a b c d e )
		)

	)
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) d)
		(sep 
			(pto d (c_GTyp a00 (as nil RefGTyp) ))
			(I618 a b c d a00 )
		)

		)

		)

	(or 
		(and 
			(= b d)
			(_ emp RefGTyp GTyp)
		)

	
		(and 
			(distinct b d)
			(I088 a b c d )
		)

	)
	
			(I047 a e c d )
	(exists ((a00 RefGTyp))
	 
		(and 
			(distinct (as nil RefGTyp) b)
		(sep 
			(pto b (c_GTyp a00 (as nil RefGTyp) ))
			(I337 a b c d a00 )
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
