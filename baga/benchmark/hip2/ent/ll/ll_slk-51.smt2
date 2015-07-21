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
(declare-fun q23 () node)
(declare-fun Anon23 () node)
(declare-fun Anon22 () node)
(declare-fun ys2 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next6 () node)
(declare-fun q22 () node)
(declare-fun xs2 () node)
(declare-fun flted34 () Int)
(declare-fun flted35_1359 () Int)
(declare-fun n9 () Int)
(declare-fun m2 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted35 Int))(and 
;lexvar(= (+ m 1) m2)
(= q23 ys2)
(= Anon23 Anon22)
(= (+ flted34 1) n)
(= ys2 ys)
(= xs2 xs)
(= next6 q22)
(= n9 flted34)
(<= 0 m)
(distinct xs2 nil)
(<= 0 flted34)
(= flted35 (+ m2 n9))
(= xsprm nil)
(<= 0 n9)
(<= 0 m2)
(tobool  
(ll ysprm flted35)
 )
))
)

(assert (not 
(exists ((flted36 Int))(and 
(= xsprm nil)
(= flted36 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted36)
 )
))
))

(check-sat)