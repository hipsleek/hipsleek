(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_7_20 Int)(?v_21 Int)(?q_22 node))(and 
(= (+ ?flted_7_20 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?v_21) (ref next ?q_22) ))
(ll ?q_22 ?flted_7_20)
) )
)))))











(declare-fun yprm () node)
(declare-fun xprm () node)
(declare-fun v_node_16_985prm () node)
(declare-fun n1 () Int)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun flted_7_1020 () Int)
(declare-fun n2 () Int)
(declare-fun v_1021 () Int)
(declare-fun q_1022 () node)


(assert 
(and 
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= v_node_16_985prm q_1022)
(tobool (ssep 
(ll q_1022 flted_7_1020)
(ll y n2)
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
emp
) )
)
)

(assert (not 
(and 
(< 0 n1_1031)
(< 0 n1_1031)
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= v_node_16_985prm q_1022)
(= n1_1031 flted_7_1020)
(= n2_1032 n2)
(tobool (ssep 
(ll v_node_16_985prm n1_1031)
(ll yprm n2_1032)
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
emp
) )
)
))

(check-sat)