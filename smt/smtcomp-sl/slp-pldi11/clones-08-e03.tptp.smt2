(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Pérez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unsat)


(declare-sort Sll_t 0)

(declare-fun f () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(tobool
(ssep (pto ?in (ref f ?u)) (ls ?u ?out)
))))))

(declare-fun nil () Sll_t)

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun t_emp () Sll_t)
(declare-fun x0 () Sll_t)
(declare-fun x1 () Sll_t)
(declare-fun x2 () Sll_t)
(declare-fun x3 () Sll_t)
(declare-fun x4 () Sll_t)
(declare-fun x5 () Sll_t)
(declare-fun x6 () Sll_t)
(declare-fun x7 () Sll_t)
(declare-fun x8 () Sll_t)
(declare-fun x9 () Sll_t)
(declare-fun x10 () Sll_t)
(declare-fun x11 () Sll_t)
(declare-fun x12 () Sll_t)
(declare-fun x13 () Sll_t)
(declare-fun x14 () Sll_t)
(declare-fun x15 () Sll_t)
(declare-fun x16 () Sll_t)
(declare-fun x17 () Sll_t)
(declare-fun x18 () Sll_t)
(declare-fun x19 () Sll_t)
(declare-fun x20 () Sll_t)
(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(assert
  (and 
    (= nil nil)
(distinct nil x1 )
(distinct nil x2 )
(distinct x1 x2 )
(distinct nil x3 )
(distinct nil x4 )
(distinct x3 x4 )
(distinct nil x5 )
(distinct nil x6 )
(distinct x5 x6 )
(distinct nil x7 )
(distinct nil x8 )
(distinct x7 x8 )
(distinct nil x9 )
(distinct nil x10 )
(distinct x9 x10 )
(distinct nil x11 )
(distinct nil x12 )
(distinct x11 x12 )
(distinct nil x13 )
(distinct nil x14 )
(distinct x13 x14 )
(distinct nil x15 )
(distinct nil x16 )
(distinct x15 x16 )
    (tobool (ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))
  )
)
(assert
  (not
        (tobool (ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))
  ))

(check-sat)
