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
(assert
  (and 
    (= nil nil)
(distinct  x6 x15)
(distinct  x7 x11)
(distinct  x7 x14)
(distinct  x9 x10)
(distinct  x9 x12)
(distinct  x2 x4)
(distinct  x2 x16)
(distinct  x2 x9)
(distinct  x12 x15)
(distinct  x8 x10)
(distinct  x1 x13)
(distinct  x1 x10)
(distinct  x1 x17)
(distinct  x4 x10)
(distinct  x4 x14)
(distinct  x4 x15)
(distinct  x13 x16)
(distinct  x5 x6)
(distinct  x5 x9)
    (tobool 
	(ssep
		(ls  x5 x17) 
		
		(ls  x13 x5) 
		
		(ls  x13 x4) 
		
		(ls  x16 x15) 
		
		(ls  x16 x10) 
		
		(ls  x16 x11) 
		
		(ls  x10 x15) 
		
		(ls  x14 x13) 
		
		(ls  x14 x3) 
		
		(ls  x15 x13) 
		
		(ls  x2 x15) 
		
		(ls  x2 x4) 
		
		(ls  x9 x3) 
		emp
	) )
  )
)

(check-sat)

