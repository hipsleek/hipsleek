(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unknown)
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
(declare-fun x23 () Sll_t)
(declare-fun x24 () Sll_t)
(assert
  (and 
    (= nil nil)
(distinct  x6 x16)
(distinct  x3 x7)
(distinct  x3 x19)
(distinct  x3 x14)
(distinct  x7 x11)
(distinct  x7 x18)
(distinct  x7 x9)
(distinct  x7 x16)
(distinct  x7 x12)
(distinct  x7 x14)
(distinct  x2 x6)
(distinct  x8 x10)
(distinct  x8 x15)
(distinct  x1 x10)
(distinct  x1 x19)
(distinct  x4 x18)
(distinct  x4 x9)
(distinct  x4 x17)
(distinct  x4 x15)
(distinct  x16 x18)
(distinct  x10 x20)
(distinct  x13 x17)
(distinct  x5 x10)
(distinct  x5 x20)
(distinct  x5 x14)
    (tobool 
	(ssep
		(ls  x5 x16) 
		
		(ls  x13 x3) 
		
		(ls  x19 x14) 
		
		(ls  x19 x1) 
		
		(ls  x16 x17) 
		
		(ls  x18 x15) 
		
		(ls  x1 x9) 
		
		(ls  x8 x9) 
		
		(ls  x20 x5) 
		
		(ls  x17 x20) 
		
		(ls  x12 x13) 
		
		(ls  x2 x11) 
		
		(ls  x9 x2) 
		
		(ls  x11 x5) 
		
		(ls  x11 x7) 
		
		(ls  x11 x4) 
		emp
	) )
  )
)

(check-sat)

