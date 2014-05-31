(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(declare-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_21 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_12) (ref next ?q) )) (ll ?q ?flted_7_21)))
)))









(declare-fun yprm () node)
(declare-fun xprm () node)
(declare-fun v_node_16_984prm () node)
(declare-fun n1 () int)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun flted_7_1019 () int)
(declare-fun n2 () int)
(declare-fun Anon_1020 () int)
(declare-fun q_1021 () node)


(assert 
(and 
(= flted_7_1019+1 n1)
lt(= y' y)
(= x' x)
(distinct q_1021 nil)
bvar(distinct q_1021 nil)
bvar(= v_node_16_984' q_1021)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1020) (ref next q_1021) ))
(ll q_1021 flted_7_1019)
(ll y n2)
emp
) )
)
)

(assert (not 
(and 
ltlt(= flted_7_1019+1 n1)
lt(= y' y)
(= x' x)
(distinct q_1021 nil)
bvar(distinct q_1021 nil)
bvar(= v_node_16_984' q_1021)
(= n1_1032 flted_7_1019)
(= n2_1033 n2)
(tobool (ssep 
(ll v_node_16_984prm n1_1032)
(ll yprm n2_1033)
(pto xprm (sref (ref val Anon_1020) (ref next q_1021) ))
emp
) )
)
))

(check-sat)