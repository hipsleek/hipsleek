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
(declare-fun q68 () node)
(declare-fun Anon68 () node)
(declare-fun Anon67 () node)
(declare-fun ys17 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next21 () node)
(declare-fun q67 () node)
(declare-fun xs17 () node)
(declare-fun flted94 () Int)
(declare-fun flted95_4824 () Int)
(declare-fun n24 () Int)
(declare-fun m17 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted95 Int))(and 
;lexvar(= (+ m 1) m17)
(= q68 ys17)
(= Anon68 Anon67)
(= (+ flted94 1) n)
(= ys17 ys)
(= xs17 xs)
(= next21 q67)
(= n24 flted94)
(<= 0 m)
(distinct xs17 nil)
(<= 0 flted94)
(= flted95 (+ m17 n24))
(= xsprm nil)
(<= 0 n24)
(<= 0 m17)
(tobool  
(ll ysprm flted95)
 )
))
)

(assert (not 
(exists ((flted96 Int))(and 
(= xsprm nil)
(= flted96 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted96)
 )
))
))

(check-sat)