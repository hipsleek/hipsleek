(set-logic QF_S)
(set-info :source | 
  R. Iosif, A. Rogalewicz and T. Vojnar. 
  Deciding Entailments in Inductive Separation Logic with Tree Automata arXiv:1402.2127. 
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/ 
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

;generic sort

(declare-sort DLL2_t 0)

;generic fields

(declare-fun prev () (Field DLL2_t DLL2_t))
(declare-fun next () (Field DLL2_t DLL2_t))

(declare-fun prev2 () (Field DLL2_t DLL2_t))
(declare-fun next2 () (Field DLL2_t DLL2_t))
(declare-fun down () (Field DLL2_t DLL2_t))

; use this for compact smt2 definition of the points-to proposition
; 
; (define-fun points_to ((?a DLL2_t) (?b DLL2_t) (?c DLL2_t)) Space
; 	    (pto ?a (sref (ref next ?b) (ref prev ?c)))
; )
; (define-fun points_to2 ((?a DLL2_t) (?b DLL2_t) (?c DLL2_t) (?d DLL2_t)) Space
; 	    (pto ?a (sref (ref next ?b) (ref prev ?c) (ref down ?d)))
; )

;; DLL2_plus(hd,p,tl,n) ::= \E down_hd,down_tl . hd->n,p,down_hd * DLL1_plus(down_hd,hd) & hd=tl 
;; 			    | \E x,down_hd,down_tl. hd->x,p,down_hd * DLL1_plus(down_hd,hd) * DLL2_plus(x,hd,tl,n)

(define-fun DLL2_plus ((?hd DLL2_t) (?p DLL2_t) (?tl DLL2_t) (?n DLL2_t)) Space
  (tospace (or 
    (exists ((?down_hd DLL2_t))
    	    (and (tobool (ssep 
	    	 	 (pto ?hd (sref (ref next2 ?n) (ref prev2 ?p) (ref down ?down_hd))) 
			 (DLL1_plus ?down_hd ?hd)))
		(= ?hd ?tl)))
    (exists ((?x DLL2_t) (?down_hd DLL2_t)) 
    	    (tobool (ssep (pto ?hd (sref (ref next2 ?x) (ref prev2 ?p) (ref down ?down_hd)))
	    	    	  (DLL1_plus ?down_hd ?hd)
 	      	      	  (DLL2_plus ?x ?hd ?tl ?n))))
)))

;; DLL2_plus_rev(hd,p,tl,n) ::= \E down_hd,down_tl . hd->n,p,down_hd * DLL1_plus(down_hd,hd) & hd=tl 
;; 			    | \E x,down_hd,down_tl. tl->n,x,down_hd * DLL1_plus(down_hd,tl) * DLL2_plus_rev(hd,p,x,tl)

(define-fun DLL2_plus_rev ((?hd DLL2_t) (?p DLL2_t) (?tl DLL2_t) (?n DLL2_t)) Space
  (tospace (or 
    (exists ((?down_hd DLL2_t))
    	    (and (tobool (ssep 
	    	 	 (pto ?hd (sref (ref next2 ?n) (ref prev2 ?p) (ref down ?down_hd))) 
			 (DLL1_plus ?down_hd ?hd)))
		(= ?hd ?tl)))
    (exists ((?x DLL2_t) (?down_hd DLL2_t)) 
    	    (tobool (ssep (pto ?tl (sref (ref next2 ?n) (ref prev2 ?x) (ref down ?down_hd)))
	    	    	  (DLL1_plus ?down_hd ?tl)
 	      	      	  (DLL2_plus_rev ?hd ?p ?x ?tl))))
)))

;; DLL1_plus(hd,p) ::= hd->nil,p | \E x. hd->x,p * DLL1_plus(x,hd)

(define-fun DLL1_plus ((?hd DLL2_t) (?p DLL2_t)) Space
  (tospace (or 
    (tobool (pto ?hd (sref (ref next nil) (ref prev ?p))))
    (exists ((?x DLL2_t)) (tobool (ssep (pto ?hd (sref (ref next ?x) (ref prev ?p)))
 	      	      	               	(DLL1_plus ?x ?hd))))
)))


(declare-fun hd0 () DLL2_t)
(declare-fun tl0 () DLL2_t)
(declare-fun hd1 () DLL2_t)
(declare-fun tl1 () DLL2_t)
(declare-fun hd2 () DLL2_t)
(declare-fun tl2 () DLL2_t)
(declare-fun hd3 () DLL2_t)
(declare-fun tl3 () DLL2_t)
(declare-fun hd4 () DLL2_t)
(declare-fun tl4 () DLL2_t)
(declare-fun hd5 () DLL2_t)
(declare-fun tl5 () DLL2_t)
(declare-fun hd6 () DLL2_t)
(declare-fun tl6 () DLL2_t)
(declare-fun hd7 () DLL2_t)
(declare-fun tl7 () DLL2_t)
(declare-fun hd8 () DLL2_t)
(declare-fun tl8 () DLL2_t)
(declare-fun hd9 () DLL2_t)
(declare-fun tl9 () DLL2_t)
(declare-fun hd10 () DLL2_t)
(declare-fun tl10 () DLL2_t)

(declare-fun hd11 () DLL2_t)
(declare-fun tl11 () DLL2_t)
(declare-fun hd12 () DLL2_t)
(declare-fun tl12 () DLL2_t)
(declare-fun hd13 () DLL2_t)
(declare-fun tl13 () DLL2_t)
(declare-fun hd14 () DLL2_t)
(declare-fun tl14 () DLL2_t)
(declare-fun hd15 () DLL2_t)
(declare-fun tl15 () DLL2_t)
(declare-fun hd16 () DLL2_t)
(declare-fun tl16 () DLL2_t)
(declare-fun hd17 () DLL2_t)
(declare-fun tl17 () DLL2_t)
(declare-fun hd18 () DLL2_t)
(declare-fun tl18 () DLL2_t)
(declare-fun hd19 () DLL2_t)
(declare-fun tl19 () DLL2_t)
(declare-fun hd20 () DLL2_t)
(declare-fun tl20 () DLL2_t)

(assert (tobool (ssep
		(DLL2_plus hd0 nil tl0 hd1)	
		(DLL2_plus hd1 tl0 tl1 hd2) 	
		(DLL2_plus hd2 tl1 tl2 hd3) 	
		(DLL2_plus hd3 tl2 tl3 hd4)	
		(DLL2_plus hd4 tl3 tl4 hd5)
		(DLL2_plus hd5 tl4 tl5 hd6)
		(DLL2_plus hd6 tl5 tl6 hd7)
		(DLL2_plus hd7 tl6 tl7 hd8)
		(DLL2_plus hd8 tl7 tl8 hd9)
		(DLL2_plus hd9 tl8 tl9 hd10)
		(DLL2_plus hd10 tl9 tl10 hd11)
		(DLL2_plus hd11 tl10 tl11 hd12) 	
		(DLL2_plus hd12 tl11 tl12 hd13) 	
		(DLL2_plus hd13 tl12 tl13 hd14)	
		(DLL2_plus hd14 tl13 tl14 hd15)
		(DLL2_plus hd15 tl14 tl15 hd16)
		(DLL2_plus hd16 tl15 tl16 hd17)
		(DLL2_plus hd17 tl16 tl17 hd18)
		(DLL2_plus hd18 tl17 tl18 hd19)
		(DLL2_plus hd19 tl18 tl19 hd20)
		(DLL2_plus hd20 tl19 tl20 nil)
)))

(assert (not (exists (
	     	     (?hd1 DLL2_t) (?tl1 DLL2_t)
	     	     (?hd2 DLL2_t) (?tl2 DLL2_t)
		     (?hd3 DLL2_t) (?tl3 DLL2_t)
		     (?hd4 DLL2_t) (?tl4 DLL2_t)
		     (?hd5 DLL2_t) (?tl5 DLL2_t)
		     (?hd6 DLL2_t) (?tl6 DLL2_t)
		     (?hd7 DLL2_t) (?tl7 DLL2_t)
		     (?hd8 DLL2_t) (?tl8 DLL2_t)
		     (?hd9 DLL2_t) (?tl9 DLL2_t)
		     (?hd10 DLL2_t) (?tl10 DLL2_t)		     
		     (?hd11 DLL2_t) (?tl11 DLL2_t)
	     	     (?hd12 DLL2_t) (?tl12 DLL2_t)
		     (?hd13 DLL2_t) (?tl13 DLL2_t)
		     (?hd14 DLL2_t) (?tl14 DLL2_t)
		     (?hd15 DLL2_t) (?tl15 DLL2_t)
		     (?hd16 DLL2_t) (?tl16 DLL2_t)
		     (?hd17 DLL2_t) (?tl17 DLL2_t)
		     (?hd18 DLL2_t) (?tl18 DLL2_t)
		     (?hd19 DLL2_t) (?tl19 DLL2_t)
		     )
	     (tobool (ssep
		(DLL2_plus_rev hd0 nil tl0 ?hd1)	
		(DLL2_plus_rev ?hd1 tl0 ?tl1 ?hd2) 	
		(DLL2_plus_rev ?hd2 ?tl1 ?tl2 ?hd3) 	
		(DLL2_plus_rev ?hd3 ?tl2 ?tl3 ?hd4)	
		(DLL2_plus_rev ?hd4 ?tl3 ?tl4 ?hd5)
		(DLL2_plus_rev ?hd5 ?tl4 ?tl5 ?hd6)
		(DLL2_plus_rev ?hd6 ?tl5 ?tl6 ?hd7)
		(DLL2_plus_rev ?hd7 ?tl6 ?tl7 ?hd8)
		(DLL2_plus_rev ?hd8 ?tl7 ?tl8 ?hd9)
		(DLL2_plus_rev ?hd9 ?tl8 ?tl9 ?hd10)
		(DLL2_plus_rev ?hd10 ?tl9 ?tl10 ?hd11)
		(DLL2_plus_rev ?hd11 ?tl10 ?tl11 ?hd12) 	
		(DLL2_plus_rev ?hd12 ?tl11 ?tl12 ?hd13) 	
		(DLL2_plus_rev ?hd13 ?tl12 ?tl13 ?hd14)	
		(DLL2_plus_rev ?hd14 ?tl13 ?tl14 ?hd15)
		(DLL2_plus_rev ?hd15 ?tl14 ?tl15 ?hd16)
		(DLL2_plus_rev ?hd16 ?tl15 ?tl16 ?hd17)
		(DLL2_plus_rev ?hd17 ?tl16 ?tl17 ?hd18)
		(DLL2_plus_rev ?hd18 ?tl17 ?tl18 ?hd19)
		(DLL2_plus_rev ?hd19 ?tl18 ?tl19 hd20)
		(DLL2_plus_rev hd20 ?tl19 tl20 nil)
)))))

;; UNSAT

(check-sat)
