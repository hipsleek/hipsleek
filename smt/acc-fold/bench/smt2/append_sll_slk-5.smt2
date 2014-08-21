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










(declare-fun v1prm () node)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun vprm () boolean)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun q () node)


(assert 
(and 
(= v1prm q)
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(ll y)
(pto xprm  (ref next q))
emp
) )
)
)

(assert (not 
(and 
(= v1prm q)
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(distinct v1prm nil)
(tobool (ssep 
(ll v1prm)
(ll yprm)
(pto xprm  (ref next q))
emp
) )
)
))

(check-sat)