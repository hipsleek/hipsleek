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
(declare-fun q () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(and 
(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(ll y)
(pto xprm  (ref next q))
(emp)
) )
)
)

(assert (not 
(exists ((next0 node))(and 
(= next0prm q)
(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(pto xprm  (ref next next0prm))
(ll q)
(ll y)
(emp)
) )
))
))

(check-sat)