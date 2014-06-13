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
(declare-fun x23 () Sll_t)
(declare-fun x24 () Sll_t)
(assert
  (and 
    (= nil nil)
    (tobool 
	(ssep
		(pto x20 (ref next x1)) 
		
		(pto x16 (ref next x10)) 
		
		(pto x1 (ref next x3)) 
		
		(pto x2 (ref next x3)) 
		
		(pto x8 (ref next x1)) 
		
		(ls  x13 x9) 
		
		(pto x12 (ref next x8)) 
		
		(pto x18 (ref next x19)) 
		
		(pto x15 (ref next x7)) 
		
		(pto x3 (ref next x16)) 
		
		(pto x19 (ref next x9)) 
		
		(pto x10 (ref next x8)) 
		
		(pto x17 (ref next x3)) 
		
		(pto x11 (ref next x19)) 
		
		(pto x6 (ref next x13)) 
		
		(ls  x7 x13) 
		
		(pto x14 (ref next x5)) 
		
		(pto x9 (ref next x2)) 
		
		(pto x4 (ref next x6)) 
		
		(pto x5 (ref next x18)) 
		emp
	) )
  )
)
(assert
  (not
        (tobool 
	(ssep
		(ls  x20 x1) 
		
		(ls  x4 x13) 
		
		(ls  x17 x3) 
		
		(ls  x14 x18) 
		
		(ls  x18 x19) 
		
		(ls  x12 x8) 
		
		(ls  x11 x9) 
		
		(ls  x1 x3) 
		
		(ls  x15 x1) 
		emp
	) )
  ))

(check-sat)
