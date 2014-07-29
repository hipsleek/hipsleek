(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unsat)
(set-info :version "2014-05-28")

(declare-sort Sll_t 0)

(declare-fun next () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(and (distinct ?in ?out) (tobool
(ssep (pto ?in (ref next ?u)) (ls ?u ?out)
)))))))

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
(declare-fun x21 () Sll_t)
(declare-fun x22 () Sll_t)
(assert
  (and 
    (= nil nil)
(distinct  x6 x13)
(distinct  x6 x16)
(distinct  x11 x18)
(distinct  x11 x17)
(distinct  x3 x16)
(distinct  x3 x12)
(distinct  x3 x17)
(distinct  x7 x13)
(distinct  x7 x14)
(distinct  x7 x15)
(distinct  x9 x13)
(distinct  x9 x17)
(distinct  x2 x8)
(distinct  x2 x6)
(distinct  x2 x11)
(distinct  x2 x17)
(distinct  x12 x14)
(distinct  x8 x14)
(distinct  x1 x10)
(distinct  x1 x15)
(distinct  x4 x11)
(distinct  x4 x9)
(distinct  x4 x13)
(distinct  x13 x18)
(distinct  x10 x11)
(distinct  x10 x12)
(distinct  x5 x6)
(distinct  x5 x16)
    (tobool 
	(ssep
		(ls  x5 x14) 
		
		(ls  x13 x15) 
		
		(ls  x13 x12) 
		
		(ls  x13 x2) 
		
		(ls  x10 x11) 
		
		(ls  x18 x10) 
		
		(ls  x18 x11) 
		
		(ls  x1 x5) 
		
		(ls  x4 x15) 
		
		(ls  x4 x11) 
		
		(ls  x15 x16) 
		
		(ls  x17 x10) 
		
		(ls  x2 x16) 
		
		(ls  x2 x6) 
		
		(ls  x9 x15) 
		
		(ls  x7 x12) 
		
		(ls  x7 x13) 
		
		(ls  x11 x9) 
		emp
	) )
  )
)

(check-sat)

