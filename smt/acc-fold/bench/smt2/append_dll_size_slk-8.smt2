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
(declare-fun yprm () node2)
(declare-fun n () Int)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun next_21_1068 () node2)
(declare-fun q_1059 () node2)
(declare-fun v_bool_22_1010prm () boolean)
(declare-fun self_1057 () node2)
(declare-fun m_1060 () Int)
(declare-fun v_1058 () Int)
(declare-fun p_1056 () node2)


(assert 
(exists ((p_1168 node2)(self_1169 node2)(v_1170 Int)(q_1171 node2)(m_1172 Int))(and 
(= n (+ 1 m_1172))
(= p_1168 p)
(= self_1169 yprm)
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(= next_21_1068 q_1059)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(tobool (ssep 
(dll q_1059 self_1057 m_1060)
(pto yprm (sref (ref val v_1170) (ref prev p_1168) (ref next q_1171) ))
(dll q_1171 self_1169 m_1172)
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next yprm) ))
emp
) )
))
)

(assert (not 
(exists ((m_1178 Int)(self_1175 node2)(v_1176 Int)(p_1174 node2)(q_1177 node2))(and 
(= n (+ 1 m_1178))
(= p_1174 p)
(= self_1175 yprm)
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(= next_21_1068 q_1059)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= val_23_1007prm v_1176)
(= prev_23_1008prm p_1174)
(= next_23_1009prm q_1177)
(tobool (ssep 
(pto yprm (sref (ref val val_23_1007prm) (ref prev prev_23_1008prm) (ref next next_23_1009prm) ))
(dll q_1059 self_1057 m_1060)
(dll q_1177 self_1175 m_1178)
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next yprm) ))
emp
) )
))
))

(check-sat)