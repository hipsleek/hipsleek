(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?p_23 node2)(?self_24 node2)(?v_20 Int)(?q_21 node2)(?m_22 Int))(and 
(= ?n (+ 1 ?m_22))
(= ?p_23 ?p)
(= ?self_24 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_20) (ref prev ?p_23) (ref next ?q_21) ))
(dll ?q_21 ?self_24 ?m_22)
) )
)))))















(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_node2_20_1003prm () node2)
(declare-fun self_1057 () node2)
(declare-fun m_1060 () Int)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun v_1058 () Int)
(declare-fun p_1056 () node2)
(declare-fun q_1059 () node2)


(assert 
(and 
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= v_node2_20_1003prm q_1059)
(distinct v_node2_20_1003prm nil)
(tobool (ssep 
(dll q_1059 self_1057 m_1060)
(dll y p n)
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next q_1059) ))
emp
) )
)
)

(assert (not 
(and 
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= v_node2_20_1003prm q_1059)
(distinct v_node2_20_1003prm nil)
(tobool (ssep 
(dll q_1059 self_1057 m_1060)
(dll y p n)
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next q_1059) ))
emp
) )
)
))

(check-sat)