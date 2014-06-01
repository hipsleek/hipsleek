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










(declare-fun xprm () node)
(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_node_15_982prm () node)
(declare-fun v_1021 () int)
(declare-fun q_1022 () node)
(declare-fun flted_7_1020 () int)
(declare-fun n2 () int)


(assert 
(and 
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(= v_node_15_982prm q_1022)
(distinct v_node_15_982prm nil)
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
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(= v_node_15_982prm q_1022)
(distinct v_node_15_982prm nil)
(tobool (ssep 
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
(ll q_1022 flted_7_1020)
(ll y n2)
emp
) )
)
))

(check-sat)