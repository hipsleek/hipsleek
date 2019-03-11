(set-logic QF_SHLID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-21")

;; Doubly-linked lists

(declare-sort RefDll_t 0)

(declare-datatypes (
	(Dll_t 0)
	) (
	((c_Dll_t (next RefDll_t) (prev RefDll_t) ))
	)
)

(declare-heap (RefDll_t Dll_t)
)

(define-fun-rec dll ((fr RefDll_t)(pr RefDll_t)(nx RefDll_t)(bk RefDll_t)) Bool
	(or
		(and
			(= fr nx)
			(= bk pr)
			(_ emp RefDll_t Dll_t)
		)

		(exists ((u RefDll_t))

		(and
			(distinct fr nx)
			(distinct bk pr)
		(sep
			(pto fr (c_Dll_t u pr ))
			(dll u fr nx bk )
		)

		)

		)

	)
)

(check-sat)
;; variables
(declare-const x0 RefDll_t)
(declare-const y0 RefDll_t)
(declare-const y1 RefDll_t)
(declare-const y2 RefDll_t)
(declare-const y3 RefDll_t)
(declare-const y4 RefDll_t)
(declare-const z0 RefDll_t)
(declare-const z1 RefDll_t)
(declare-const w0 RefDll_t)
(declare-const w1 RefDll_t)

(assert (and
         (distinct x0 y0)
         (distinct y0 z0)
         (distinct z0 w0)
         (= y3 y4)
         (sep (dll x0 (as nil RefDll_t) y0 y1)
              (pto y0 (c_Dll_t y2 (as nil RefDll_t)))
              (pto y2 (c_Dll_t y3 y4))
              (dll y4 (as nil RefDll_t) z0 z1)
              (dll z0 z1 w0 w1)
              (dll w0 w1 (as nil RefDll_t) w0)
              )
             )
)

(check-sat)
