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

(declare-sort TLL_t 0)

;generic fields

(declare-fun left () (Field TLL_t TLL_t))
(declare-fun right () (Field TLL_t TLL_t))
(declare-fun next () (Field TLL_t TLL_t))
(declare-fun parent () (Field TLL_t TLL_t))

; use this for compact smt2 definition of the points-to proposition
; 
; (define-fun points_to ((?a TLL_t) (?b TLL_t) (?c TLL_t) (?d TLL_t) (?e TLL_t)) Space
;	    (pto ?a (sref (ref left ?b) (ref right ?c) (ref parent ?d) (ref next ?e)))
; )

;; TLL(root,par,ll,lr) ::= root->nil,nil,par,lr & root=ll
;;	|\E l,r,z . root->l,r,par,nil * TLL(l,root,ll,z) * TLL(r,root,z,lr)

(define-fun TLL_plus ((?root TLL_t) (?par TLL_t) (?ll TLL_t) (?lr TLL_t)) Space
  (tospace (or
    (and (tobool (pto ?root (sref (ref left nil) (ref right nil) (ref parent ?par) (ref next ?lr)))) (= ?root ?ll))
    (exists ((?l TLL_t) (?r TLL_t) (?z TLL_t))
    	    (tobool (ssep (pto ?root (sref (ref left ?l) (ref right ?r) (ref parent ?par) (ref next nil)))
    	    	 	  (TLL_plus ?l ?root ?ll ?z)
			  (TLL_plus ?r ?root ?z ?lr))))
)))

;; TLLaux(x,p,z,back,top,mright)::=\E up,r,lr. x->back,r,up,nil * TLLaux(up,p,lr,x,top,mright) * tll(r,x,z,lr)
;;	|\E r.  x->back,r,p,nil & top=x * tll(r,x,z,mright)

(define-fun TLL_aux ((?x TLL_t) (?p TLL_t) (?z TLL_t) (?back TLL_t) (?top TLL_t) (?mright TLL_t)) Space
  (tospace (or
  	   (exists ((?up TLL_t) (?r TLL_t) (?lr TLL_t))
	   	   (tobool (ssep (pto ?x (sref (ref left ?back) (ref right ?r) (ref parent ?up) (ref next nil)))
		   (TLL_aux ?up ?p ?lr ?x ?top ?mright)
		   (TLL_plus ?r ?x ?z ?lr))))
	   (exists ((?r TLL_t)) (and (ssep (pto ?x (sref (ref left ?back) (ref right ?r) (ref parent ?p) (ref next nil)))
	   	   		     	   (TLL_plus ?r ?x ?z ?mright))
				     (= ?top ?x)))
)))
		
;; TLLrev(top,p,mleft,mright)::=\E x,up,lr. x->nil,nil,up,lr & x=mleft * TLLaux(up,p,lr,x,top,mright)
;;	| top->nil,nil,p,mright & top=mleft

(define-fun TLL_plus_rev ((?top TLL_t) (?p TLL_t) (?mleft TLL_t) (?mright TLL_t)) Space
  (tospace (or (and (tobool (pto ?top (sref (ref left nil) (ref right nil) (ref parent ?p) (ref next ?mright)))) 
  	       	    (= ?top ?mleft))
  	       (exists ((?x TLL_t) (?up TLL_t) (?lr TLL_t)) 
	       	       (and 
		       	    (tobool (ssep 
			    	    	  (pto ?x (sref (ref left nil) (ref right nil) (ref parent ?up) (ref next ?lr)))
		       	    	    	  (TLL_aux ?up ?p ?lr ?x ?top ?mright)
					  ))
			    (= ?x ?mleft)))
)))

(declare-fun x () TLL_t)
(declare-fun y () TLL_t)
(declare-fun u () TLL_t)
(declare-fun v () TLL_t)

;; TLL(x,y,u,v) |- TLLrev(x,y,u,v)

(assert (tobool (TLL_plus x y u v)
))

(assert (not (tobool 
	(TLL_plus_rev x y u v)
)))

;; UNSAT

(check-sat)