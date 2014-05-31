(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(declare-fun ll ((?in node))
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
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_node_13_960prm () node)
(declare-fun Anon_992 () int)
(declare-fun q_993 () node)


(assert 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(= v_node_13_960' q_993)
(= v_node_13_960' nil)
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
(distinct x nil)
(= y' y)
(= x' x)
(= v_node_13_960' q_993)
(= v_node_13_960' nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_992) (ref next q_993) ))
(ll q_993)
(ll y)
emp
) )
)
))

(check-sat)