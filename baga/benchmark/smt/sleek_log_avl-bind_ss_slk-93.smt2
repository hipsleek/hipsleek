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











































































































































































(declare-fun Anon14_6386 () Int)
(declare-fun p10_6387 () node)
(declare-fun q10_6390 () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun n38_6385 () Int)
(declare-fun n () Int)
(declare-fun n40_6392 () Int)
(declare-fun n39_6389 () Int)
(declare-fun m () Int)
(declare-fun m32_6388 () Int)
(declare-fun m33_6391 () Int)


(assert 
(exists ((n38 Int)(Anon14 Int)(p10 node)(m32 Int)(n39 Int)(q10 node)(m33 Int)(n40 Int))(and 
;lexvar(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= n38 n)
(<= n39 (+ 1 n40))
(<= (+ 0 n40) (+ n39 1))
(= m (+ (+ m33 1) m32))
(tobool (ssep 
(pto xprm (sref (ref val Anon14) (ref height n38) (ref left p10) (ref right q10) ))
(avl p10 m32 n39)
(avl q10 m33 n40)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val xvalprm) (ref height xheightprm) (ref left xleftprm) (ref right xrightprm) ))
 )
)
))

(check-sat)