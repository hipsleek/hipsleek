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

(declare-fun a () DLL_t)
(declare-fun c () DLL_t)

;; DLL(a,nil,c,nil) |- \E x,n,b . x ->n,b * DLL_plus_rev(a,nil,b,x) * DLL(n,x,c,nil)

(assert (tobool
	(DLL_plus a nil c nil)
))

(assert (not (exists ((?x DLL_t) (?n DLL_t) (?b DLL_t))
		(tobool (ssep (pto ?x (sref (ref next ?n) (ref prev ?b)))
		      	      (DLL_plus_rev a nil ?b ?x)
			      (DLL_plus ?n ?x c nil))))
))

;; SAT

(check-sat)