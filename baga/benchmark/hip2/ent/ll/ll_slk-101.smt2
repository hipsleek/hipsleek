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
(declare-fun q38 () node)
(declare-fun Anon38 () node)
(declare-fun Anon37 () node)
(declare-fun ys7 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next11 () node)
(declare-fun q37 () node)
(declare-fun xs7 () node)
(declare-fun flted54 () Int)
(declare-fun flted55_2514 () Int)
(declare-fun n14 () Int)
(declare-fun m7 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted55 Int))(and 
;lexvar(= (+ m 1) m7)
(= q38 ys7)
(= Anon38 Anon37)
(= (+ flted54 1) n)
(= ys7 ys)
(= xs7 xs)
(= next11 q37)
(= n14 flted54)
(<= 0 m)
(distinct xs7 nil)
(<= 0 flted54)
(= flted55 (+ m7 n14))
(= xsprm nil)
(<= 0 n14)
(<= 0 m7)
(tobool  
(ll ysprm flted55)
 )
))
)

(assert (not 
(exists ((flted56 Int))(and 
(= xsprm nil)
(= flted56 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted56)
 )
))
))

(check-sat)