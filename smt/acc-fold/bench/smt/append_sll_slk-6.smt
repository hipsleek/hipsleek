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









(declare-fun yprm () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_13_966prm () boolean)
(declare-fun y () node)
(declare-fun Anon_992 () int)
(declare-fun q_993 () node)


(assert 
(and 
(= y nil)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_993 nil)
bvar(distinct q_993 nil)
bvar(= y nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_992) (ref next q_993) ))
(ll q_993)
emp
) )
)
)

(assert (not 
(exists ((Anon_1012 int)(q_1013 node)) (tobool (ll x)))

))

(check-sat)
