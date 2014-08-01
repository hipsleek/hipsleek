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

)(exists ((?v_19 Int)(?q_20 node)(?m_21 Int))(and 
(= ?n (+ 1 ?m_21))
(tobool (ssep 
(pto ?in (sref (ref val ?v_19) (ref next ?q_20) ))
(ll ?q_20 ?m_21)
) )
)))))











(declare-fun xprm () node)
(declare-fun n1 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_node_15_981prm () node)
(declare-fun m_1021 () Int)
(declare-fun n2 () Int)
(declare-fun v_1019 () Int)
(declare-fun q_1020 () node)


(assert 
(and 
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(= v_node_15_981prm q_1020)
(distinct v_node_15_981prm nil)
(tobool (ssep 
(ll q_1020 m_1021)
(ll y n2)
(pto xprm (sref (ref val v_1019) (ref next q_1020) ))
emp
) )
)
)

(assert (not 
(and 
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(= v_node_15_981prm q_1020)
(distinct v_node_15_981prm nil)
(tobool (ssep 
(ll q_1020 m_1021)
(ll y n2)
(pto xprm (sref (ref val v_1019) (ref next q_1020) ))
emp
) )
)
))

(check-sat)