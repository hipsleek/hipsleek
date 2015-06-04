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











































































































































































(declare-fun m59 () Int)
(declare-fun m58 () Int)
(declare-fun xrightrightprm () node)
(declare-fun q17 () node)
(declare-fun xrightleftprm () node)
(declare-fun p17 () node)
(declare-fun xrightheightprm () Int)
(declare-fun xrightvalprm () node)
(declare-fun Anon25 () node)
(declare-fun n65 () Int)
(declare-fun m53 () Int)
(declare-fun Anon23 () Int)
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
(declare-fun n69 () Int)
(declare-fun n64 () Int)
(declare-fun n70 () Int)
(declare-fun n71 () Int)
(declare-fun m52 () Int)
(declare-fun m57 () Int)
(declare-fun m56 () Int)
(declare-fun n72 () Int)
(declare-fun n73 () Int)


(assert 
(and 
;lexvar(<= 0 n73)
(<= 0 m59)
(<= 0 n71)
(<= 0 m57)
(= n73 n71)
(= m59 m57)
(<= 0 n72)
(<= 0 m58)
(<= 0 n70)
(<= 0 m56)
(= n72 n70)
(= m58 m56)
(= xrightrightprm q17)
(= xrightleftprm p17)
(= xrightheightprm n69)
(= xrightvalprm Anon25)
(= (+ 2 n65) n64)
(<= 0 n65)
(<= 0 m53)
(<= 0 n41)
(<= 0 m35)
(= n65 n41)
(= m53 m35)
(<= 0 n64)
(<= 0 m52)
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
(= n69 n64)
(<= n71 (+ 1 n70))
(<= (+ 0 n70) (+ n71 1))
(= m52 (+ (+ m56 1) m57))
(<= n72 n73)
(tobool (ssep 
(avl xleftprm m53 n65)
(avl xrightrightprm m58 n72)
(avl xrightleftprm m59 n73)
) )
)
)

(assert (not 
(and 
(tobool  
(avl xrightleftprm m60 n74)
 )
)
))

(check-sat)