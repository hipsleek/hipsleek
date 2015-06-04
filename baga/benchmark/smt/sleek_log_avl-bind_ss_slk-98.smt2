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











































































































































































(declare-fun xleftprm () node)
(declare-fun Anon16_6617 () Int)
(declare-fun flted18_6616 () Int)
(declare-fun n44 () Int)
(declare-fun m36 () Int)
(declare-fun tmpprm () node)
(declare-fun xrightprm () node)
(declare-fun q11 () node)
(declare-fun xleft () node)
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
(declare-fun aprm () NUM)
(declare-fun xvalprm () NUM)


(assert 
(exists ((flted18 Int)(Anon16 Int))(and 
;lexvar(<= 0 n44)
(<= 0 m36)
(= flted18 (+ 1 m36))
(<= 0 n41)
(<= 0 m35)
(= n44 n41)
(= m36 m35)
(= tmpprm xleft)
(= xrightprm q11)
(= xleft p11)
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
(<= aprm xvalprm)
(tobool (ssep 
(avl xleftprm flted18 Anon16)
(avl q11 m34 n42)
) )
))
)

(assert (not 
(and 
(tobool  
(avl xleftprm m37 n45)
 )
)
))

(check-sat)