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
(assert
  (and 
    (= nil nil)
(distinct  x6 x9)
(distinct  x6 x17)
(distinct  x6 x12)
(distinct  x6 x14)
(distinct  x11 x17)
(distinct  x3 x10)
(distinct  x3 x19)
(distinct  x3 x16)
(distinct  x3 x5)
(distinct  x7 x18)
(distinct  x7 x9)
(distinct  x7 x15)
(distinct  x9 x10)
(distinct  x9 x12)
(distinct  x12 x17)
(distinct  x12 x14)
(distinct  x2 x11)
(distinct  x2 x10)
(distinct  x2 x9)
(distinct  x2 x5)
(distinct  x14 x17)
(distinct  x15 x18)
(distinct  x15 x17)
(distinct  x8 x15)
(distinct  x4 x14)
(distinct  x10 x17)
(distinct  x5 x8)
    (tobool 
	(ssep
		(ls  x19 x2) 
		
		(ls  x18 x13) 
		
		(ls  x18 x11) 
		
		(ls  x1 x14) 
		
		(ls  x1 x13) 
		
		(ls  x8 x19) 
		
		(ls  x15 x17) 
		
		(ls  x15 x16) 
		
		(ls  x14 x18) 
		
		(ls  x14 x11) 
		
		(ls  x14 x8) 
		
		(ls  x2 x10) 
		
		(ls  x17 x5) 
		
		(ls  x17 x19) 
		
		(ls  x9 x3) 
		
		(ls  x9 x4) 
		
		(ls  x9 x8) 
		
		(ls  x7 x16) 
		
		(ls  x7 x1) 
		emp
	) )
  )
)

(check-sat)

