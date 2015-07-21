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


















































































































































































































(declare-fun xs () node)
(declare-fun ysprm () node)
(declare-fun ys () node)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm xs)
(= ysprm ys)
(= xsprm nil)
(not )(tobool (ssep 
(ll xs n)
(ll ys m)
) )
)
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