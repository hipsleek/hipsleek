(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
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

)(exists ((?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(ll ?q ?flted_14_24)
) )
)))))


















































































































































































































(declare-fun ysprm () node)
(declare-fun q59 () node)
(declare-fun Anon59 () node)
(declare-fun Anon58 () node)
(declare-fun ys14 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next18 () node)
(declare-fun q58 () node)
(declare-fun xs14 () node)
(declare-fun flted82 () Int)
(declare-fun flted83_4131 () Int)
(declare-fun n21 () Int)
(declare-fun m14 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted83 Int))(and 
;lexvar(= (+ m 1) m14)
(= q59 ys14)
(= Anon59 Anon58)
(= (+ flted82 1) n)
(= ys14 ys)
(= xs14 xs)
(= next18 q58)
(= n21 flted82)
(<= 0 m)
(distinct xs14 nil)
(<= 0 flted82)
(= flted83 (+ m14 n21))
(= xsprm nil)
(<= 0 n21)
(<= 0 m14)
(tobool  
(ll ysprm flted83)
 )
))
)

(assert (not 
(exists ((flted84 Int))(and 
(= xsprm nil)
(= flted84 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted84)
 )
))
))

(check-sat)