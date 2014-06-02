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
(declare-sort DLL_t 0)

;generic fields

(declare-fun prev () (Field DLL_t DLL_t))
(declare-fun next () (Field DLL_t DLL_t))
(declare-fun down () (Field DLL_t DLL_t))

; use this for compact smt2 definition of the points-to proposition
; 
; (define-fun points_to ((?a DLL_t) (?b DLL_t) (?c DLL_t)) Space
; 	    (pto ?a (sref (ref next ?b) (ref prev ?c)))
; )
; (define-fun points_to2 ((?a DLL_t) (?b DLL_t) (?c DLL_t) (?d DLL_t)) Space
; 	    (pto ?a (sref (ref next ?b) (ref prev ?c) (ref down ?d)))
; )

;; DLL_plus(hd,p,tl,n) ::= hd->n,p & hd=tl | \E x. hd->x,p * DLL_plus(x,hd,tl,n)

(define-fun DLL_plus ((?hd DLL_t) (?p DLL_t) (?tl DLL_t) (?n DLL_t)) Space
  (tospace (or 
    (and (tobool emp) (= ?hd ?tl))
    (exists ((?x DLL_t)) (tobool (ssep (pto ?hd (sref (ref next ?x) (ref prev ?p)))
 	      	      	               (DLL_plus ?x ?hd ?tl ?n))))
)))

;; DLL2_plus(hd,p,tl,n) ::= \E down_hd,down_tl . hd->n,p,down_hd * DLL_plus(down_hd,hd,down_tl,nil) & hd=tl 
;; 			    | \E x,down_hd,down_tl. hd->x,p,down_hd * DLL_plus(down_hd,hd,down_tl,nil) * DLL2_plus(x,hd,tl,n)

(define-fun DLL2_plus ((?hd DLL_t) (?p DLL_t) (?tl DLL_t) (?n DLL_t)) Space
  (tospace (or 
    (exists ((?down_hd DLL_t) (?down_tl DLL_t))
    	    (and (tobool (ssep 
	    	 	 (pto ?hd (sref (ref next ?n) (ref prev ?p) (ref down ?down_hd))) 
			 (DLL_plus ?down_hd ?hd ?down_tl nil)))
		(= ?hd ?tl)))
    (exists ((?x DLL_t) (?down_hd DLL_t) (?down_tl DLL_t)) 
    	    (tobool (ssep (pto ?hd (sref (ref next ?x) (ref prev ?p) (ref down ?down_hd)))
	    	    	  (DLL_plus ?down_hd ?hd ?down_tl nil)
 	      	      	  (DLL2_plus ?x ?hd ?tl ?n))))
)))


(declare-fun x () DLL_t)
(declare-fun y () DLL_t)
(declare-fun u () DLL_t)
(declare-fun v () DLL_t)

(assert (tobool (DLL2_plus x y u v) 
))

(assert (not (tobool
	(DLL2_plus x y u v)
)))

(check-sat)
