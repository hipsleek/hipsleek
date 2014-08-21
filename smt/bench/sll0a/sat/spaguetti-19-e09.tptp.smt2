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
(distinct  x6 x10)
(distinct  x6 x19)
(distinct  x6 x17)
(distinct  x3 x16)
(distinct  x3 x12)
(distinct  x3 x5)
(distinct  x7 x16)
(distinct  x7 x14)
(distinct  x9 x19)
(distinct  x12 x14)
(distinct  x2 x16)
(distinct  x2 x10)
(distinct  x2 x17)
(distinct  x2 x15)
(distinct  x15 x19)
(distinct  x15 x17)
(distinct  x8 x19)
(distinct  x8 x14)
(distinct  x4 x10)
(distinct  x4 x5)
(distinct  x1 x8)
(distinct  x1 x19)
(distinct  x1 x15)
(distinct  x10 x19)
(distinct  x10 x16)
(distinct  x13 x15)
(distinct  x5 x8)
(distinct  x5 x6)
    (tobool 
	(ssep
		(ls  x5 x1) 
		
		(ls  x16 x9) 
		
		(ls  x19 x17) 
		
		(ls  x13 x5) 
		
		(ls  x13 x15) 
		
		(ls  x18 x15) 
		
		(ls  x18 x5) 
		
		(ls  x1 x4) 
		
		(ls  x8 x9) 
		
		(ls  x8 x3) 
		
		(ls  x14 x10) 
		
		(ls  x15 x17) 
		
		(ls  x2 x1) 
		
		(ls  x12 x15) 
		
		(ls  x9 x1) 
		
		(ls  x7 x15) 
		
		(ls  x3 x7) 
		
		(ls  x11 x1) 
		
		(ls  x6 x10) 
		emp
	) )
  )
)

(check-sat)

