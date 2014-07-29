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
(assert
  (and 
    (= nil nil)
(distinct  x8 x9)
(distinct  x4 x7)
(distinct  x1 x8)
(distinct  x2 x6)
(distinct  x2 x5)
    (tobool 
	(ssep
		(ls  x2 x5) 
		
		(ls  x2 x7) 
		
		(ls  x9 x8) 
		
		(ls  x9 x6) 
		
		(ls  x7 x1) 
		
		(ls  x3 x4) 
		
		(ls  x8 x2) 
		
		(ls  x8 x3) 
		
		(ls  x8 x4) 
		emp
	) )
  )
)

(check-sat)

