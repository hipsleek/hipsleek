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
















































































































































































































































(declare-fun Anon3 () Int)
(declare-fun q3 () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun flted5 () Int)
(declare-fun flted7_577 () Int)
(declare-fun n4 () Int)
(declare-fun n3 () Int)
(declare-fun x () node)
(declare-fun n2 () Int)
(declare-fun n1 () Int)


(assert 
(exists ((flted7 Int))(and 
;lexvar(distinct q3 nil)
(< 0 n1)
(= yprm y)
(= xprm x)
(= (+ flted5 1) n1)
(= n4 flted5)
(= n3 n2)
(<= 0 n2)
(<= 0 flted5)
(= flted7 (+ n3 n4))
(<= 0 n4)
(<= 0 n3)
(tobool (ssep 
(pto xprm (sref (ref val Anon3) (ref next q3) ))
(ll q3 flted7)
) )
))
)

(assert (not 
(exists ((flted6 Int))(and 
(= flted6 (+ n2 n1))
(<= 0 n2)
(<= 0 n1)
(tobool  
(ll x flted6)
 )
))
))

(check-sat)