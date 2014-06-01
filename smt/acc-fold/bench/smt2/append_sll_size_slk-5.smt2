(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_20 int)(?v_21 int)(?q_22 node)) (tobool (ssep (pto ?in (sref (ref val ?v_21) (ref next ?q_22) )) (ll ?q_22 ?flted_7_20))))
)))










(declare-fun yprm () node)
(declare-fun xprm () node)
(declare-fun v_node_16_985prm () node)
(declare-fun n1 () int)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun flted_7_1020 () int)
(declare-fun n2 () int)
(declare-fun v_1021 () int)
(declare-fun q_1022 () node)


(assert 
(and 
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= v_node_16_985prm q_1022)
(tobool (ssep 
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
(ll q_1022 flted_7_1020)
(ll y n2)
emp
) )
)
)

(assert (not 
(and 
ltlt(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= v_node_16_985prm q_1022)
(= n1_1033 flted_7_1020)
(= n2_1034 n2)
(tobool (ssep 
(ll v_node_16_985prm n1_1033)
(ll yprm n2_1034)
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
emp
) )
)
))

(check-sat)