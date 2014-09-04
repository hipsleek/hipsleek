(set-logic QF_S)

(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?q_18 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_18))
(ll ?q_18)
) )
)))))










(declare-fun vprm () boolean)
(declare-fun q () node)
(declare-fun xprm () node)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun x () node)


(assert 
(and 
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(pto xprm  (ref next q))
(ll q)
emp
) )
)
)

(assert (not 
(and 
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll x)
emp
) )
)
))

(check-sat)