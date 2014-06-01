(set-logic QF_S)

(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?q_18 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_18))
(ll ?q_18)
) )
)))))




(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((q node))(and 
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(pto xprm  (ref next q))
(ll y)
) )
))
)

(assert (not 
(exists ((q1 node))(and 
(= nextprm q1)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(pto xprm  (ref next nextprm))
(ll q1)
(ll y)
) )
))
))

(check-sat)