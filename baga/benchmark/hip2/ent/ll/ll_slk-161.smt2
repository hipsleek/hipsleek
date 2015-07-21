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
(declare-fun q56 () node)
(declare-fun Anon56 () node)
(declare-fun Anon55 () node)
(declare-fun ys13 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next17 () node)
(declare-fun q55 () node)
(declare-fun xs13 () node)
(declare-fun flted78 () Int)
(declare-fun flted79_3900 () Int)
(declare-fun n20 () Int)
(declare-fun m13 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted79 Int))(and 
;lexvar(= (+ m 1) m13)
(= q56 ys13)
(= Anon56 Anon55)
(= (+ flted78 1) n)
(= ys13 ys)
(= xs13 xs)
(= next17 q55)
(= n20 flted78)
(<= 0 m)
(distinct xs13 nil)
(<= 0 flted78)
(= flted79 (+ m13 n20))
(= xsprm nil)
(<= 0 n20)
(<= 0 m13)
(tobool  
(ll ysprm flted79)
 )
))
)

(assert (not 
(exists ((flted80 Int))(and 
(= xsprm nil)
(= flted80 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted80)
 )
))
))

(check-sat)