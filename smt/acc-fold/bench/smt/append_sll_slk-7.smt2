(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(and 
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q)
) )
))))









(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_13_966prm () boolean)
(declare-fun next_18_1011 () node)
(declare-fun q_993 () node)
(declare-fun Anon_992 () int)
(declare-fun yprm () node)
(declare-fun y () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_993 nil)
(= q_993 nil)
(= next_18_1011 q_993)
(tobool (ssep 
(ll q_993)
(ll y)
(pto xprm (sref (ref val Anon_992) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((Anon_1015 int)(q_1016 node)) (tobool (ll x)))

))

(check-sat)
