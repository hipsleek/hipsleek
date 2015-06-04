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
















































































































































































































































(declare-fun Anon74 () Int)
(declare-fun next24 () node)
(declare-fun q74 () node)
(declare-fun v46_5545 () node)
(declare-fun xprm () node)
(declare-fun flted104 () Int)
(declare-fun x () node)
(declare-fun i () Int)


(assert 
(exists ((v46prm node))(and 
;lexvar(= next24 q74)
(= v46prm nil)
(= xprm x)
(< 0 i)
(< 3 4)
(= (+ flted104 1) i)
(tobool (ssep 
(ll q74 flted104)
(pto xprm (sref (ref val Anon74) (ref next v46prm) ))
) )
))
)

(assert (not 
(exists ((flted105 Int))(and 
(= flted105 1)
(<= 0 i)
(tobool  
(ll x flted105)
 )
))
))

(check-sat)