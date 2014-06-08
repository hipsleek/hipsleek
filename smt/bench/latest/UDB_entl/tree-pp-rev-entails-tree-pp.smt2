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

(declare-sort TPP_t 0)

;generic fields

(declare-fun left () (Field TPP_t TPP_t))
(declare-fun right () (Field TPP_t TPP_t))
(declare-fun parent () (Field TPP_t TPP_t))

; use this for compact smt2 definition of the points-to proposition
; 
; (define-fun points_to ((?a TPP_t) (?b TPP_t) (?c TPP_t) (?d TPP_t)) Space
;	    (pto ?a (sref (ref left ?b) (ref right ?c) (ref parent ?d)))
; )

;; TREEpp(x,back)::=x->nil,nil,back 
;;	| \Ey,z. x -> y,z,back * TREEpp(y,x) * TREEpp(z,x)

(define-fun TPP_plus ((?x TPP_t) (?back TPP_t)) Space
  (tospace (or 
  	   (and (tobool (pto ?x (sref (ref left nil) (ref right nil) (ref parent ?back)))))
	   (exists ((?y TPP_t) (?z TPP_t)) 
			(tobool (ssep (pto ?x (sref (ref left ?y) (ref right ?z) (ref parent ?back)))
				      (TPP_plus ?y ?x)
				      (TPP_plus ?z ?x))))
)))

;; AUX(x,down,top,b)::=\E up,right. x->down,right,up * TREEpp(right,x) * AUX(up,x,top,b)
;;	| \E up,left. x->left,down,up * TREEpp(left,x) * AUX(up,x,top,b)
;;	| \E right.  x->down,right,b & x=top * TREEpp(right,x)
;;	| \E left.  x->left,down,b & x=top * TREEpp(left,x)

(define-fun TPP_aux ((?x TPP_t) (?down TPP_t) (?top TPP_t) (?b TPP_t)) Space
  (tospace (or
  	   (exists ((?up TPP_t) (?right TPP_t))
	   	   (tobool (ssep (pto ?x (sref (ref left ?down) (ref right ?right) (ref parent ?up)))
		   	   	 (TPP_plus ?right ?x)
				 (TPP_aux ?up ?x ?top ?b))))
	   (exists ((?up TPP_t) (?left TPP_t))
	   	   (tobool (ssep (pto ?x (sref (ref left ?left) (ref right ?down) (ref parent ?up)))
		   	   	 (TPP_plus ?left ?x)
				 (TPP_aux ?up ?x ?top ?b))))
	   (exists ((?right TPP_t))
	   	   (and (= ?x ?top)
		   	(tobool (ssep (pto ?x (sref (ref left ?down) (ref right ?right) (ref parent ?b)))
				      (TPP_plus ?right ?x)))))
	   (exists ((?left TPP_t))
	   	   (and (= ?x ?top)
		   	(tobool (ssep (pto ?x (sref (ref left ?left) (ref right ?down) (ref parent ?b)))
				      (TPP_plus ?left ?x)))))
)))

;; TREEpprev(top,b)::=\E x,up. x->nil,nil,up * AUX(up,x,top,b)
;;	| top->nil,nil,b

(define-fun TPP_plus_rev ((?top TPP_t) (?b TPP_t)) Space
  (tospace (or (tobool (pto ?top (sref (ref left nil) (ref right nil) (ref parent ?b))))
  	       (exists ((?x TPP_t) (?up TPP_t)) 
	       	       (tobool (ssep (pto ?x (sref (ref left nil) (ref right nil) (ref parent ?up)))
		       	       	     (TPP_aux ?up ?x ?top ?b))))
)))

(declare-fun x () TPP_t)
(declare-fun y () TPP_t)

;; TREEpprev(x,y) |- TREEpp(x,y)

(assert (tobool (TPP_plus_rev x y)
))

(assert (not (tobool
	(TPP_plus x y)
)))

;; UNSAT

(check-sat)
