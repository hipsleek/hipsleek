(set-logic QF_S)
(set-info :source |
  James Brotherston, Carsten Fuhs, Nikos Gorogiannis, and Juan Navarro Pérez.
  A decision procedure for satisfiability in separation logic with inductive
  predicates. To appear at CSL-LICS, 2014.
  https://github.com/ngorogiannis/cyclist
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)



;generic sort 

(declare-sort GTyp 0)

;generic fields 
(declare-fun f0 () (Field GTyp GTyp))
(declare-fun f1 () (Field GTyp GTyp))

;predicates 

(define-fun zero ((?x GTyp)) Space 
 

	(= nil ?x)

 )


(define-fun one ((?x GTyp)) Space 
 

	(distinct nil ?x)

 )


(define-fun bool ((?x GTyp)) Space 
(tospace (or 
(zero ?x)
(one ?x)
) )
 )


(define-fun bitvector ((?x1 GTyp) (?x2 GTyp) (?x3 GTyp) (?x4 GTyp) (?x5 GTyp) (?x6 GTyp) (?x7 GTyp) (?x8 GTyp) (?x9 GTyp) (?x10 GTyp) (?x11 GTyp) (?x12 GTyp) (?x13 GTyp) (?x14 GTyp) (?x15 GTyp) (?x16 GTyp) (?x17 GTyp) (?x18 GTyp) (?x19 GTyp) (?x20 GTyp) (?x21 GTyp) (?x22 GTyp) (?x23 GTyp) (?x24 GTyp) (?x25 GTyp) (?x26 GTyp) (?x27 GTyp) (?x28 GTyp) (?x29 GTyp) (?x30 GTyp)) Space 
 

	(sep (bool ?x1)
		(bool ?x2)
		(bool ?x3)
		(bool ?x4)
		(bool ?x5)
		(bool ?x6)
		(bool ?x7)
		(bool ?x8)
		(bool ?x9)
		(bool ?x10)
		(bool ?x11)
		(bool ?x12)
		(bool ?x13)
		(bool ?x14)
		(bool ?x15)
		(bool ?x16)
		(bool ?x17)
		(bool ?x18)
		(bool ?x19)
		(bool ?x20)
		(bool ?x21)
		(bool ?x22)
		(bool ?x23)
		(bool ?x24)
		(bool ?x25)
		(bool ?x26)
		(bool ?x27)
		(bool ?x28)
		(bool ?x29)
		(bool ?x30)
	)

 )


;index vars 
(define-fun alpha1 () SetLoc)

;vars 

;problem 
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (zero  x0))))
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (one  x0))))
;;(define-fun x0 () GenTyp)
;;(assert (tobool (index alpha1 (bool  x0))))
(define-fun x0 () GenTyp)
(define-fun x1 () GenTyp)
(define-fun x2 () GenTyp)
(define-fun x3 () GenTyp)
(define-fun x4 () GenTyp)
(define-fun x5 () GenTyp)
(define-fun x6 () GenTyp)
(define-fun x7 () GenTyp)
(define-fun x8 () GenTyp)
(define-fun x9 () GenTyp)
(define-fun x10 () GenTyp)
(define-fun x11 () GenTyp)
(define-fun x12 () GenTyp)
(define-fun x13 () GenTyp)
(define-fun x14 () GenTyp)
(define-fun x15 () GenTyp)
(define-fun x16 () GenTyp)
(define-fun x17 () GenTyp)
(define-fun x18 () GenTyp)
(define-fun x19 () GenTyp)
(define-fun x20 () GenTyp)
(define-fun x21 () GenTyp)
(define-fun x22 () GenTyp)
(define-fun x23 () GenTyp)
(define-fun x24 () GenTyp)
(define-fun x25 () GenTyp)
(define-fun x26 () GenTyp)
(define-fun x27 () GenTyp)
(define-fun x28 () GenTyp)
(define-fun x29 () GenTyp)
(assert (tobool (index alpha1 (bitvector  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29))))



(check-sat)

