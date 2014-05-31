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

(declare-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_21 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref next ?q) )) (lseg ?q ?p_21)))
)))









(declare-fun xprm () node)
(declare-fun v_node_16_984prm () node)
(declare-fun yprm () TVar[139])
(declare-fun y () TVar[139])
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun Anon_1013 () int)
(declare-fun q_1014 () node)


(assert 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1014 nil)
bvar(distinct q_1014 nil)
bvar(= v_node_16_984' q_1014)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1013) (ref next q_1014) ))
(ll q_1014)
emp
) )
)
)

(assert (not 
(and 
(distinct v_node_16_984' nil)
(distinct v_node_16_984' nil)
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1014 nil)
bvar(distinct q_1014 nil)
bvar(= v_node_16_984' q_1014)
(tobool (ssep 
(ll v_node_16_984prm)
(pto xprm (sref (ref val Anon_1013) (ref next q_1014) ))
emp
) )
)
))

(check-sat)