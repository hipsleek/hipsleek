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


















































































































































































































(declare-fun Anon1 () Int)
(declare-fun q1 () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun flted1 () Int)
(declare-fun flted3_191 () Int)
(declare-fun x () node)
(declare-fun n2 () Int)
(declare-fun n1 () Int)


(assert 
(exists ((flted3 Int))(and 
;lexvar(not )(distinct q1 nil)
(distinct x nil)
(= yprm y)
(= xprm x)
(= (+ flted1 1) n1)
(= n1 flted1)
(= n2 n2)
(<= 0 n2)
(<= 0 flted1)
(= flted3 (+ n2 n1))
(<= 0 n1)
(<= 0 n2)
(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref next q1) ))
(ll q1 flted3)
) )
))
)

(assert (not 
(exists ((flted2 Int))(and 
(= flted2 (+ n2 n1))
(<= 0 n2)
(<= 0 n1)
(tobool  
(ll x flted2)
 )
))
))

(check-sat)