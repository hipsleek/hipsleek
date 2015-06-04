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
















































































































































































































































(declare-fun Anon72 () Int)
(declare-fun next23 () node)
(declare-fun q72 () node)
(declare-fun flted101 () Int)
(declare-fun xprm () node)
(declare-fun v43_5481 () node)
(declare-fun x () node)
(declare-fun i () Int)


(assert 
(exists ((v43prm node))(and 
;lexvar(= next23 q72)
(= (+ flted101 1) i)
(= xprm x)
(< 0 i)
(= v43prm nil)
(tobool (ssep 
(ll q72 flted101)
(pto xprm (sref (ref val Anon72) (ref next v43prm) ))
) )
))
)

(assert (not 
(exists ((flted102 Int))(and 
(= flted102 1)
(<= 0 i)
(tobool  
(ll x flted102)
 )
))
))

(check-sat)