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











































































































































































(declare-fun Anon8_851 () Int)
(declare-fun p4_852 () node)
(declare-fun q4_855 () node)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun n13_850 () Int)
(declare-fun n () Int)
(declare-fun n15_857 () Int)
(declare-fun n14_854 () Int)
(declare-fun m () Int)
(declare-fun m9_853 () Int)
(declare-fun m10_856 () Int)


(assert 
(exists ((n13 Int)(Anon8 Int)(p4 node)(m9 Int)(n14 Int)(q4 node)(m10 Int)(n15 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= n13 n)
(<= n14 (+ 1 n15))
(<= (+ 0 n15) (+ n14 1))
(= m (+ (+ m10 1) m9))
(tobool (ssep 
(pto xprm (sref (ref val Anon8) (ref height n13) (ref left p4) (ref right q4) ))
(avl p4 m9 n14)
(avl q4 m10 n15)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val5prm) (ref height height5prm) (ref left left5prm) (ref right right5prm) ))
 )
)
))

(check-sat)