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

;; tll_tail(root,par,ll,tr,lr) ::= root->nil,nil,par,lr & root=ll & root=tr
;;	|\E l,r,z . root->l,r,par,nil * tll_plus(l,root,ll,z) * tll_tail(r,root,z,tr,lr)

(define-fun TLL_tail ((?root TLL_t) (?par TLL_t) (?ll TLL_t) (?tr TLL_t) (?lr TLL_t)) Space
  (tospace (or
    (and (tobool (pto ?root (sref (ref left nil) (ref right nil) (ref parent ?par) (ref next ?lr)))) (= ?root ?ll) (= ?root ?tr))
    (exists ((?l TLL_t) (?r TLL_t) (?z TLL_t))
    	    (tobool (ssep (pto ?root (sref (ref left ?l) (ref right ?r) (ref parent ?par) (ref next nil)))
    	    	 	  (TLL_plus ?l ?root ?ll ?z)
			  (TLL_tail ?r ?root ?z ?tr ?lr))))
)))

;; tll(root,par,ll,lr) ::= root->nil,nil,par,lr & root=ll
;;	|\E l,r,z . root->l,r,par,nil * tll(l,root,ll,z) * tll(r,root,z,lr)

(define-fun TLL_plus ((?root TLL_t) (?par TLL_t) (?ll TLL_t) (?lr TLL_t)) Space
  (tospace (or
    (and (tobool (pto ?root (sref (ref left nil) (ref right nil) (ref parent ?par) (ref next ?lr)))) (= ?root ?ll))
    (exists ((?l TLL_t) (?r TLL_t) (?z TLL_t))
    	    (tobool (ssep (pto ?root (sref (ref left ?l) (ref right ?r) (ref parent ?par) (ref next nil)))
    	    	 	  (TLL_plus ?l ?root ?ll ?z)
			  (TLL_plus ?r ?root ?z ?lr))))
)))


(declare-fun root0 () TLL_t)
(declare-fun ll0 () TLL_t)
(declare-fun tr0 () TLL_t)
(declare-fun root1 () TLL_t)
(declare-fun ll1 () TLL_t)
(declare-fun tr1 () TLL_t)
(declare-fun root2 () TLL_t)
(declare-fun ll2 () TLL_t)
(declare-fun tr2 () TLL_t)
(declare-fun root3 () TLL_t)
(declare-fun ll3 () TLL_t)
(declare-fun tr3 () TLL_t)
(declare-fun root4 () TLL_t)
(declare-fun ll4 () TLL_t)
(declare-fun tr4 () TLL_t)
(declare-fun root5 () TLL_t)
(declare-fun ll5 () TLL_t)
(declare-fun tr5 () TLL_t)
(declare-fun root6 () TLL_t)
(declare-fun ll6 () TLL_t)
(declare-fun tr6 () TLL_t)
(declare-fun root7 () TLL_t)
(declare-fun ll7 () TLL_t)
(declare-fun tr7 () TLL_t)
(declare-fun root8 () TLL_t)
(declare-fun ll8 () TLL_t)
(declare-fun tr8 () TLL_t)
(declare-fun root9 () TLL_t)
(declare-fun ll9 () TLL_t)
(declare-fun tr9 () TLL_t)

(declare-fun root10 () TLL_t)
(declare-fun ll10 () TLL_t)
(declare-fun tr10 () TLL_t)
(declare-fun root11 () TLL_t)
(declare-fun ll11 () TLL_t)
(declare-fun tr11 () TLL_t)
(declare-fun root12 () TLL_t)
(declare-fun ll12 () TLL_t)
(declare-fun tr12 () TLL_t)
(declare-fun root13 () TLL_t)
(declare-fun ll13 () TLL_t)
(declare-fun tr13 () TLL_t)
(declare-fun root14 () TLL_t)
(declare-fun ll14 () TLL_t)
(declare-fun tr14 () TLL_t)
(declare-fun root15 () TLL_t)
(declare-fun ll15 () TLL_t)
(declare-fun tr15 () TLL_t)
(declare-fun root16 () TLL_t)
(declare-fun ll16 () TLL_t)
(declare-fun tr16 () TLL_t)
(declare-fun root17 () TLL_t)
(declare-fun ll17 () TLL_t)
(declare-fun tr17 () TLL_t)
(declare-fun root18 () TLL_t)
(declare-fun ll18 () TLL_t)
(declare-fun tr18 () TLL_t)
(declare-fun root19 () TLL_t)
(declare-fun ll19 () TLL_t)
(declare-fun tr19 () TLL_t)

(assert (tobool 
	(ssep (TLL_tail root0 nil ll0 tr0 root1)
	      (TLL_tail root1 tr0 ll1 tr1 root2)
	      (TLL_tail root2 tr1 ll2 tr2 root3)
	      (TLL_tail root3 tr2 ll3 tr3 root4)
	      (TLL_tail root4 tr3 ll4 tr4 root5)
	      (TLL_tail root5 tr4 ll5 tr5 root6)
	      (TLL_tail root6 tr5 ll6 tr6 root7)
	      (TLL_tail root7 tr6 ll7 tr7 root8)
	      (TLL_tail root8 tr7 ll8 tr8 root9)
	      (TLL_tail root9 tr8 ll9 tr9 root10)
	      (TLL_tail root10 tr9 ll10 tr10 root11)
	      (TLL_tail root11 tr10 ll11 tr11 root12)
	      (TLL_tail root12 tr11 ll12 tr12 root13)
	      (TLL_tail root13 tr12 ll13 tr13 root14)
	      (TLL_tail root14 tr13 ll14 tr14 root15)
	      (TLL_tail root15 tr14 ll15 tr15 root16)
	      (TLL_tail root16 tr15 ll16 tr16 root17)
	      (TLL_tail root17 tr16 ll17 tr17 root18)
	      (TLL_tail root18 tr17 ll18 tr18 root19)
	      (TLL_tail root19 tr18 ll19 tr19 nil)
	      )
))

(assert (not (tobool 
	(ssep (TLL_tail root0 nil ll0 tr0 root1)
	      (TLL_tail root2 tr1 ll2 tr2 root3)
	      (TLL_tail root5 tr4 ll5 tr5 root6)
	      (TLL_tail root8 tr7 ll8 tr8 root9)
	      (TLL_tail root10 tr9 ll10 tr10 root11)
	      (TLL_tail root7 tr6 ll7 tr7 root8)
	      (TLL_tail root9 tr8 ll9 tr9 root10)
	      (TLL_tail root4 tr3 ll4 tr4 root5)
	      (TLL_tail root13 tr12 ll13 tr13 root14)
	      (TLL_tail root11 tr10 ll11 tr11 root12)
	      (TLL_tail root15 tr14 ll15 tr15 root16)
	      (TLL_tail root12 tr11 ll12 tr12 root13)
	      (TLL_tail root17 tr16 ll17 tr17 root18)
	      (TLL_tail root14 tr13 ll14 tr14 root15)
	      (TLL_tail root6 tr5 ll6 tr6 root7)
	      (TLL_tail root19 tr18 ll19 tr19 nil)
	      (TLL_tail root1 tr0 ll1 tr1 root2)
	      (TLL_tail root16 tr15 ll16 tr16 root17)
	      (TLL_tail root3 tr2 ll3 tr3 root4)
	      (TLL_tail root18 tr17 ll18 tr18 root19)
	      )
)))

;; UNSAT
(check-sat)
