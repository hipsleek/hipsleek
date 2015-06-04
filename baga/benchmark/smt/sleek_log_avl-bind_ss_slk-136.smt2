(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun xrightprm () node)
(declare-fun n65 () Int)
(declare-fun m53 () Int)
(declare-fun v58prm () Int)
(declare-fun n64 () Int)
(declare-fun Anon23 () Int)
(declare-fun m52 () Int)
(declare-fun flted21 () Int)
(declare-fun n63 () Int)
(declare-fun m51 () Int)
(declare-fun tmpprm () node)
(declare-fun xright () node)
(declare-fun q11 () node)
(declare-fun xleftprm () node)
(declare-fun p11 () node)
(declare-fun xheightprm () Int)
(declare-fun Anon15 () NUM)
(declare-fun x () node)
(declare-fun a () NUM)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun n43 () Int)
(declare-fun n () Int)
(declare-fun n42 () Int)
(declare-fun n41 () Int)
(declare-fun m () Int)
(declare-fun m35 () Int)
(declare-fun m34 () Int)
(declare-fun xvalprm () NUM)
(declare-fun aprm () NUM)


(assert 
(and 
;lexvar(= n65 n41)
(= m53 m35)
(<= 0 n64)
(<= 0 m52)
(= v58prm n64)
(<= 0 Anon23)
(<= 0 flted21)
(= n64 Anon23)
(= m52 flted21)
(<= 0 n63)
(<= 0 m51)
(= flted21 (+ 1 m51))
(<= 0 n42)
(<= 0 m34)
(= n63 n42)
(= m51 m34)
(= tmpprm xright)
(= xright q11)
(= xleftprm p11)
(= xheightprm n43)
(= xvalprm Anon15)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= n43 n)
(<= n41 (+ 1 n42))
(<= (+ 0 n42) (+ n41 1))
(= m (+ (+ m34 1) m35))
(< xvalprm aprm)
(tobool  
(avl xrightprm m52 n64)
 )
)
)

(assert (not 
;lexvar
))

(check-sat)