(set-logic QF_S)
(set-info :source | 
  R. Iosif, A. Rogalewicz and T. Vojnar. 
  Deciding Entailments in Inductive Separation Logic with Tree Automata arXiv:1402.2127. 
  http://www.fit.vutbr.cz/research/groups/verifit/tools/slide/ 
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)

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

(declare-fun a () TLL_t)
(declare-fun c () TLL_t)

;; TLL(a,nil,c,nil) |- \E l,r,z . a ->l,r,nil,nil * TLL(l,a,c,z) * TLL(r,a,z,nil) 

(assert (tobool 
	(TLL_plus a nil c nil)
))

(assert (not (exists ((?l TLL_t) (?r TLL_t) (?z TLL_t))
		(tobool (ssep (pto a (sref (ref left ?l) (ref right ?r) (ref parent nil) (ref next nil)))
			      (TLL_plus ?l a c ?z)
			      (TLL_plus ?r a ?z nil))))
))

;; SAT

(check-sat)