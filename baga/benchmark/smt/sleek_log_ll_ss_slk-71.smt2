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
(declare-fun q20 () node)
(declare-fun Anon20 () node)
(declare-fun Anon19 () node)
(declare-fun ys1 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next5 () node)
(declare-fun q19 () node)
(declare-fun xs1 () node)
(declare-fun flted30 () Int)
(declare-fun flted31_1642 () Int)
(declare-fun n8 () Int)
(declare-fun m1 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted31 Int))(and 
;lexvar(= (+ m 1) m1)
(= q20 ys1)
(= Anon20 Anon19)
(= (+ flted30 1) n)
(= ys1 ys)
(= xs1 xs)
(= next5 q19)
(= n8 flted30)
(<= 0 m)
(distinct xs1 nil)
(<= 0 flted30)
(= flted31 (+ m1 n8))
(= xsprm nil)
(<= 0 n8)
(<= 0 m1)
(tobool  
(ll ysprm flted31)
 )
))
)

(assert (not 
(exists ((flted32 Int))(and 
(= xsprm nil)
(= flted32 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted32)
 )
))
))

(check-sat)