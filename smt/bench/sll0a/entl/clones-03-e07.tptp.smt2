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
(distinct  nil x1)
(distinct  nil x2)
(distinct  nil x4)
(distinct  nil x5)
(distinct  nil x7)
(distinct  nil x8)
    (tobool 
	(ssep
		(ls  x7 x8) 
		
		(pto x8 (ref next x7)) 
		
		(ls  x4 x5) 
		
		(pto x5 (ref next x4)) 
		
		(ls  x1 x2) 
		
		(pto x2 (ref next x1)) 
		emp
	) )
  )
)
(assert
  (not
        (tobool 
	(ssep
		(ls  x9 x8) 
		
		(pto x8 (ref next x9)) 
		
		(ls  x6 x5) 
		
		(pto x5 (ref next x6)) 
		
		(ls  x3 x2) 
		
		(pto x2 (ref next x3)) 
		emp
	) )
  ))

(check-sat)
