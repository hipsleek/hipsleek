(set-logic QF_SHLID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
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
(declare-const z0 RefDll_t)
(declare-const z1 RefDll_t)
(declare-const w0 RefDll_t)
(declare-const w1 RefDll_t)
(declare-const a0 RefDll_t)
(declare-const a1 RefDll_t)
(declare-const b0 RefDll_t)
(declare-const b1 RefDll_t)
(declare-const c0 RefDll_t)
(declare-const c1 RefDll_t)
(declare-const d0 RefDll_t)
(declare-const d1 RefDll_t)
(declare-const e0 RefDll_t)
(declare-const e1 RefDll_t)

(assert (and
         (distinct x0 y0)
         (distinct y0 z0)
         (distinct z0 a0)
         (distinct z0 a0)
         (distinct a0 b0)
         (distinct b0 c0)
         (distinct c0 d0)
         (distinct d0 e0)
         (sep (dll x0 (as nil RefDll_t) y0 y1)
                  (dll y0 y1 z0 z1)
                  (dll z0 z1 a0 a1)
                  (dll a0 a1 b0 b1)
                  (dll b0 b1 c0 c1)
                  (dll c0 c1 d0 d1)
                  (dll d0 d1 e0 e1)
                  (dll e0 e1 (as nil RefDll_t) x0)
                  )
             )
)

(check-sat)
