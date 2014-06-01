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
(declare-fun v_node_14_963prm () node)
(declare-fun x () node)
(declare-fun v_bool_13_966prm () boolean)
(declare-fun y () node)
(declare-fun Anon_992 () int)
(declare-fun q_993 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_993 nil)
bvar(distinct q_993 nil)
bvar(= v_node_14_963prm q_993)
(tobool (ssep 
(pto xprm (sref (ref val Anon_992) (ref next q_993) ))
(ll q_993)
(ll y)
emp
) )
)
)

(assert (not 
(and 
(distinct v_node_14_963prm nil)
(distinct v_node_14_963prm nil)
(= y nil)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_993 nil)
bvar(distinct q_993 nil)
bvar(= v_node_14_963prm q_993)
(= y nil)
(tobool (ssep 
(ll v_node_14_963prm)
(ll yprm)
(pto xprm (sref (ref val Anon_992) (ref next q_993) ))
emp
) )
)
))

(check-sat)