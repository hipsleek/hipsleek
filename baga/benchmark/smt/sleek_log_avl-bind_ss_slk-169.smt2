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











































































































































































(declare-fun Anon_3947 () Int)
(declare-fun p17 () node)
(declare-fun q17 () node)
(declare-fun p11 () node)
(declare-fun xright_14926 () node)
(declare-fun n69 () Int)
(declare-fun Anon15 () Int)
(declare-fun n43 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun xright () node)
(declare-fun q11 () node)
(declare-fun m34 () Int)
(declare-fun n42 () Int)
(declare-fun m51 () Int)
(declare-fun n63 () Int)
(declare-fun flted21 () Int)
(declare-fun Anon23 () Int)
(declare-fun m52 () Int)
(declare-fun m35 () Int)
(declare-fun n41 () Int)
(declare-fun n64 () Int)
(declare-fun m56 () Int)
(declare-fun n70 () Int)
(declare-fun m57 () Int)
(declare-fun n71 () Int)
(declare-fun m58 () Int)
(declare-fun n72 () Int)
(declare-fun m59 () Int)
(declare-fun n73 () Int)
(declare-fun m53 () Int)
(declare-fun n65 () Int)
(declare-fun flted27_14927 () Int)
(declare-fun flted28_14928 () Int)
(declare-fun lm () Int)
(declare-fun ln () Int)
(declare-fun rlm () Int)
(declare-fun rrm () Int)
(declare-fun v80prm () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((xrightprm node)(flted27 Int)(flted28 Int))(and 
;lexvar(< n73 n72)
(= m52 (+ (+ m56 1) m57))
(<= (+ 0 n70) (+ n71 1))
(<= n71 (+ 1 n70))
(= n69 n64)
(< Anon15 aprm)
(= m (+ (+ m34 1) m35))
(<= (+ 0 n42) (+ n41 1))
(<= n41 (+ 1 n42))
(= n43 n)
(distinct xprm nil)
(= aprm a)
(= xprm x)
(= xright q11)
(= m51 m34)
(= n63 n42)
(<= 0 m34)
(<= 0 n42)
(= flted21 (+ 1 m51))
(<= 0 m51)
(<= 0 n63)
(= m52 flted21)
(= n64 Anon23)
(<= 0 flted21)
(<= 0 Anon23)
(<= 0 m52)
(<= 0 n64)
(= m53 m35)
(= n65 n41)
(<= 0 m35)
(<= 0 n41)
(= (+ 2 n65) n64)
(= m58 m56)
(= n72 n70)
(<= 0 m56)
(<= 0 n70)
(= m59 m57)
(= n73 n71)
(<= 0 m57)
(<= 0 n71)
(= lm m53)
(= ln n65)
(= rlm m59)
(= rrm m58)
(<= 0 m58)
(<= 0 n72)
(<= 0 m59)
(<= 0 n73)
(<= 0 m53)
(<= 0 n65)
(= flted27 (+ (+ (+ rrm lm) 2) rlm))
(= flted28 (+ ln 2))
(<= 0 lm)
(<= 0 ln)
(<= 0 rlm)
(<= 0 rrm)
(= res v80prm)
(tobool (ssep 
(avl v80prm flted27 flted28)
(pto xrightprm (sref (ref val Anon_3947) (ref height n69) (ref left p17) (ref right q17) ))
(pto xprm (sref (ref val Anon15) (ref height n43) (ref left p11) (ref right xrightprm) ))
) )
))
)

(assert (not 
(exists ((flted22 Int)(Anon28 Int))(and 
(= flted22 (+ 1 m))
(<= 0 n)
(<= 0 m)
(tobool  
(avl res flted22 Anon28)
 )
))
))

(check-sat)