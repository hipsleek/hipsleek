(set-logic QF_S)
(set-info :source | 
  R. Iosif, A. Rogalewicz and T. Vojnar. 
  Deciding Entailments in Inductive Separation Logic with Tree Automata arXiv:1402.2127. 
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/ 
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)

;generic sort

(declare-sort DLL_t 0)

;generic fields

(declare-fun prev () (Field DLL_t DLL_t))
(declare-fun next () (Field DLL_t DLL_t))

; use this for compact smt2 definition of the points-to proposition
; 
; (define-fun points_to ((?a DLL_t) (?b DLL_t) (?c DLL_t)) Space
; 	    (pto ?a (sref (ref next ?b) (ref prev ?c)))
; )

;; DLL(hd,p,tl,n) ::= p=tl & hd=n & emp | \E x. hd->x,p * DLL(x,hd,tl,n)

(define-fun DLL ((?hd DLL_t) (?p DLL_t) (?tl DLL_t) (?n DLL_t)) Space
  (tospace (or 
    (and (tobool emp) (= ?p ?tl) (= ?hd ?n))
    (exists ((?x DLL_t)) (tobool (ssep (pto ?hd (sref (ref next ?x) (ref prev ?p)))
 	      	      	               (DLL ?x ?hd ?tl ?n))))
)))

;; DLL_plus(hd,p,tl,n)::= hd->n,p & hd=tl | \E x. hd->x,p * DLL_plus(x,hd,tl,n)

(define-fun DLL_plus ((?hd DLL_t) (?p DLL_t) (?tl DLL_t) (?n DLL_t)) Space
  (tospace (or 
    (and (tobool (pto ?hd (sref (ref next ?n) (ref prev ?p)))) (= ?hd ?tl))
    (exists ((?x DLL_t)) (tobool (ssep (pto ?hd (sref (ref next ?x) (ref prev ?p)))
 	      	      	               (DLL_plus ?x ?hd ?tl ?n))))
)))


;; DLL_plus_rev(hd,p,tl,n)::= hd->n,p & hd=tl | \E x. tl->n,x * DLL_plus_rev(hd,p,x,tl)

(define-fun DLL_plus_rev ((?hd DLL_t) (?p DLL_t) (?tl DLL_t) (?n DLL_t)) Space
  (tospace (or 
    (and (tobool (pto ?hd (sref (ref next ?n) (ref prev ?p)))) (= ?hd ?tl))
      (exists ((?x DLL_t)) (tobool (ssep (pto ?tl (sref (ref next ?n) (ref prev ?x)))
 	      	      	                 (DLL_plus_rev ?hd ?p ?x ?tl))))
)))

(declare-fun hd0 () DLL_t)
(declare-fun tl0 () DLL_t)
(declare-fun hd1 () DLL_t)
(declare-fun tl1 () DLL_t)
(declare-fun hd2 () DLL_t)
(declare-fun tl2 () DLL_t)
(declare-fun hd3 () DLL_t)
(declare-fun tl3 () DLL_t)
(declare-fun hd4 () DLL_t)
(declare-fun tl4 () DLL_t)
(declare-fun hd5 () DLL_t)
(declare-fun tl5 () DLL_t)
(declare-fun hd6 () DLL_t)
(declare-fun tl6 () DLL_t)
(declare-fun hd7 () DLL_t)
(declare-fun tl7 () DLL_t)
(declare-fun hd8 () DLL_t)
(declare-fun tl8 () DLL_t)
(declare-fun hd9 () DLL_t)
(declare-fun tl9 () DLL_t)
(declare-fun hd10 () DLL_t)
(declare-fun tl10 () DLL_t)

(declare-fun hd11 () DLL_t)
(declare-fun tl11 () DLL_t)
(declare-fun hd12 () DLL_t)
(declare-fun tl12 () DLL_t)
(declare-fun hd13 () DLL_t)
(declare-fun tl13 () DLL_t)
(declare-fun hd14 () DLL_t)
(declare-fun tl14 () DLL_t)
(declare-fun hd15 () DLL_t)
(declare-fun tl15 () DLL_t)
(declare-fun hd16 () DLL_t)
(declare-fun tl16 () DLL_t)
(declare-fun hd17 () DLL_t)
(declare-fun tl17 () DLL_t)
(declare-fun hd18 () DLL_t)
(declare-fun tl18 () DLL_t)
(declare-fun hd19 () DLL_t)
(declare-fun tl19 () DLL_t)
(declare-fun hd20 () DLL_t)
(declare-fun tl20 () DLL_t)

(assert (tobool (ssep
		(DLL_plus hd0 nil tl0 hd1)	
		(DLL_plus hd1 tl0 tl1 hd2) 	
		(DLL_plus hd2 tl1 tl2 hd3) 	
		(DLL_plus hd3 tl2 tl3 hd4)	
		(DLL_plus hd4 tl3 tl4 hd5)
		(DLL_plus hd5 tl4 tl5 hd6)
		(DLL_plus hd6 tl5 tl6 hd7)
		(DLL_plus hd7 tl6 tl7 hd8)
		(DLL_plus hd8 tl7 tl8 hd9)
		(DLL_plus hd9 tl8 tl9 hd10)
		(DLL_plus hd10 tl9 tl10 hd11)
		(DLL_plus hd11 tl10 tl11 hd12) 	
		(DLL_plus hd12 tl11 tl12 hd13) 	
		(DLL_plus hd13 tl12 tl13 hd14)	
		(DLL_plus hd14 tl13 tl14 hd15)
		(DLL_plus hd15 tl14 tl15 hd16)
		(DLL_plus hd16 tl15 tl16 hd17)
		(DLL_plus hd17 tl16 tl17 hd18)
		(DLL_plus hd18 tl17 tl18 hd19)
		(DLL_plus hd19 tl18 tl19 hd20)
		(DLL_plus hd20 tl19 tl20 nil)
)))

(assert (not (exists (
	     	     (?hd1 DLL_t) (?tl1 DLL_t)
	     	     (?hd2 DLL_t) (?tl2 DLL_t)
		     (?hd3 DLL_t) (?tl3 DLL_t)
		     (?hd4 DLL_t) (?tl4 DLL_t)
		     (?hd5 DLL_t) (?tl5 DLL_t)
		     (?hd6 DLL_t) (?tl6 DLL_t)
		     (?hd7 DLL_t) (?tl7 DLL_t)
		     (?hd8 DLL_t) (?tl8 DLL_t)
		     (?hd9 DLL_t) (?tl9 DLL_t)
		     (?hd10 DLL_t) (?tl10 DLL_t)		     
		     (?hd11 DLL_t) (?tl11 DLL_t)
	     	     (?hd12 DLL_t) (?tl12 DLL_t)
		     (?hd13 DLL_t) (?tl13 DLL_t)
		     (?hd14 DLL_t) (?tl14 DLL_t)
		     (?hd15 DLL_t) (?tl15 DLL_t)
		     (?hd16 DLL_t) (?tl16 DLL_t)
		     (?hd17 DLL_t) (?tl17 DLL_t)
		     (?hd18 DLL_t) (?tl18 DLL_t)
		     (?hd19 DLL_t) (?tl19 DLL_t)
		     )
	     (tobool (ssep
		(DLL_plus_rev hd0 nil tl0 ?hd1)	
		(DLL_plus_rev ?hd1 tl0 ?tl1 ?hd2) 	
		(DLL_plus_rev ?hd2 ?tl1 ?tl2 ?hd3) 	
		(DLL_plus_rev ?hd3 ?tl2 ?tl3 ?hd4)	
		(DLL_plus_rev ?hd4 ?tl3 ?tl4 ?hd5)
		(DLL_plus_rev ?hd5 ?tl4 ?tl5 ?hd6)
		(DLL_plus_rev ?hd6 ?tl5 ?tl6 ?hd7)
		(DLL_plus_rev ?hd7 ?tl6 ?tl7 ?hd8)
		(DLL_plus_rev ?hd8 ?tl7 ?tl8 ?hd9)
		(DLL_plus_rev ?hd9 ?tl8 ?tl9 ?hd10)
		(DLL_plus_rev ?hd10 ?tl9 ?tl10 ?hd11)
		(DLL_plus ?hd11 ?tl10 ?tl11 ?hd12) 	
		(DLL_plus ?hd12 ?tl11 ?tl12 ?hd13) 	
		(DLL_plus ?hd13 ?tl12 ?tl13 ?hd14)	
		(DLL_plus ?hd14 ?tl13 ?tl14 ?hd15)
		(DLL_plus ?hd15 ?tl14 ?tl15 ?hd16)
		(DLL_plus ?hd16 ?tl15 ?tl16 ?hd17)
		(DLL_plus ?hd17 ?tl16 ?tl17 ?hd18)
		(DLL_plus ?hd18 ?tl17 ?tl18 ?hd19)
		(DLL_plus ?hd19 ?tl18 ?tl19 hd20)
		(DLL_plus hd20 ?tl19 tl20 nil)
)))))

;; UNSAT

(check-sat)
		