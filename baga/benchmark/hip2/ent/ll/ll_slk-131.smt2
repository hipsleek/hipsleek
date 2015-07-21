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
(declare-fun q47 () node)
(declare-fun Anon47 () node)
(declare-fun Anon46 () node)
(declare-fun ys10 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next14 () node)
(declare-fun q46 () node)
(declare-fun xs10 () node)
(declare-fun flted66 () Int)
(declare-fun flted67_3207 () Int)
(declare-fun n17 () Int)
(declare-fun m10 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted67 Int))(and 
;lexvar(= (+ m 1) m10)
(= q47 ys10)
(= Anon47 Anon46)
(= (+ flted66 1) n)
(= ys10 ys)
(= xs10 xs)
(= next14 q46)
(= n17 flted66)
(<= 0 m)
(distinct xs10 nil)
(<= 0 flted66)
(= flted67 (+ m10 n17))
(= xsprm nil)
(<= 0 n17)
(<= 0 m10)
(tobool  
(ll ysprm flted67)
 )
))
)

(assert (not 
(exists ((flted68 Int))(and 
(= xsprm nil)
(= flted68 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted68)
 )
))
))

(check-sat)