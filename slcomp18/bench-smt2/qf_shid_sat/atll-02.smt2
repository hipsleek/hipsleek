(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-21")

;; Locally acyclic trees with linked leaves
;; (Note that there can still be a cycle from x3 into an unrelated subtree...)

(declare-sort RefAtll_t 0)

(declare-datatypes (
	(Atll_t 0)
	) (
	((c_Atll_t (lson RefAtll_t) (rson RefAtll_t) (next RefAtll_t) ))
	)
)

(declare-heap (RefAtll_t Atll_t) 
)

(define-fun-rec atll ((r RefAtll_t) (ll RefAtll_t) (rl RefAtll_t)) Bool
	(or 
		(and (distinct r rl) 
		     (= r ll)
		     (pto r (c_Atll_t (as nil RefAtll_t) (as nil RefAtll_t) rl))
		)

		(exists ((ls RefAtll_t) (rs RefAtll_t) (z RefAtll_t))
	 
		(and 
			(distinct r ll)
			(distinct r rl)
		(sep 
			(pto r (c_Atll_t ls rs (as nil RefAtll_t)))
			(atll ls ll z)
			(atll rs z rl)
		)

		)

		)

	)
)

(define-fun-rec R ((x RefAtll_t)(y RefAtll_t)) Bool
	(sep (atll x (as nil RefAtll_t) y)
             (pto y (c_Atll_t (as nil RefAtll_t) (as nil RefAtll_t) (as nil RefAtll_t))
	     )
	)	
)

(check-sat) 
;; variables
(declare-const x0 RefAtll_t)
(declare-const y0 RefAtll_t)

(assert (R x0 y0)
)
(check-sat)
