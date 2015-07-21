(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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
(declare-fun v2prm () node)
(declare-fun flted1 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun q1 () node)
(declare-fun n1 () Int)
(declare-fun n2 () Int)


(assert 
(and 
;lexvar(= v2prm q1)
(= (+ flted1 1) n1)
(= xprm x)
(= yprm y)
(distinct x nil)
(distinct q1 nil)
(not )(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref next q1) ))
(ll q1 flted1)
(ll y n2)
) )
)
)

(assert (not 
(and 
(distinct v2prm nil)
(tobool (ssep 
(ll v2prm n1)
(ll yprm n2)
) )
)
))

(check-sat)