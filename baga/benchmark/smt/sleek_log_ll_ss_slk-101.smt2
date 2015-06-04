(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun ysprm () node)
(declare-fun q29 () node)
(declare-fun Anon29 () node)
(declare-fun Anon28 () node)
(declare-fun ys4 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next8 () node)
(declare-fun q28 () node)
(declare-fun xs4 () node)
(declare-fun flted42 () Int)
(declare-fun flted43_2335 () Int)
(declare-fun n11 () Int)
(declare-fun m4 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted43 Int))(and 
;lexvar(= (+ m 1) m4)
(= q29 ys4)
(= Anon29 Anon28)
(= (+ flted42 1) n)
(= ys4 ys)
(= xs4 xs)
(= next8 q28)
(= n11 flted42)
(<= 0 m)
(distinct xs4 nil)
(<= 0 flted42)
(= flted43 (+ m4 n11))
(= xsprm nil)
(<= 0 n11)
(<= 0 m4)
(tobool  
(ll ysprm flted43)
 )
))
)

(assert (not 
(exists ((flted44 Int))(and 
(= xsprm nil)
(= flted44 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted44)
 )
))
))

(check-sat)