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

)(exists ((?p_24 node2)(?self_25 node2)(?flted_12_21 Int)(?v_22 Int)(?q_23 node2))(and 
(= (+ ?flted_12_21 1) ?n)
(= ?p_24 ?p)
(= ?self_25 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_22) (ref prev ?p_24) (ref next ?q_23) ))
(dll ?q_23 ?self_25 ?flted_12_21)
) )
)))))















(declare-fun yprm () node2)
(declare-fun xprm () node2)
(declare-fun v_node2_26_1015prm () node2)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () Int)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun v_1060 () Int)
(declare-fun p_1057 () node2)
(declare-fun q_1061 () node2)


(assert 
(and 
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(distinct q_1061 nil)
other(distinct q_1061 nil)
other(= v_node2_26_1015prm q_1061)
(tobool (ssep 
(dll q_1061 self_1058 flted_12_1059)
(dll y p n)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
emp
) )
)
)

(assert (not 
(and 
(< 0 m_1185)
(< 0 m_1185)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(distinct q_1061 nil)
other(distinct q_1061 nil)
other(= v_node2_26_1015prm q_1061)
(= q_1184 self_1058)
(= m_1185 flted_12_1059)
(= p_1186 p)
(= n_1187 n)
(tobool (ssep 
(dll v_node2_26_1015prm q_1184 m_1185)
(dll yprm p_1186 n_1187)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
emp
) )
)
))

(check-sat)