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

(declare-fun x () DLL2_t)
(declare-fun y () DLL2_t)
(declare-fun u () DLL2_t)
(declare-fun v () DLL2_t)


(assert (tobool
	(DLL2_plus_rev x y u v))
)

(assert (not (tobool
	     (DLL2_plus x y u v))
))

;; UNSAT

(check-sat)
