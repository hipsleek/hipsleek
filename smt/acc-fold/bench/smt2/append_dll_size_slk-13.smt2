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















(declare-fun v_1060 () Int)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun q_1061 () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun q_1184 () node2)
(declare-fun self_1058 () node2)
(declare-fun p_1186 () Int)
(declare-fun p () Int)
(declare-fun n () Int)
(declare-fun flted_12_1059 () Int)
(declare-fun m_1185 () Int)
(declare-fun n_1187 () Int)
(declare-fun p_1057 () node2)


(assert 
(exists ((flted_18_1193 Int))(and 
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(distinct q_1061 nil)
other(distinct q_1061 nil)
other(= q_1184 self_1058)
(= m_1185 flted_12_1059)
(= p_1186 p)
(= n_1187 n)
(<= 0 n)
(<= 0 flted_12_1059)
(= flted_18_1193 (+ n_1187 m_1185))
(<= 0 m_1185)
(<= 0 n_1187)
(tobool (ssep 
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
(dll q_1061 q_1184 flted_18_1193)
emp
) )
))
)

(assert (not 
(exists ((flted_18_52 Int)(q_55 node2)(flted_18_1251 Int))(and 
(= flted_18_52 (+ n m))
(= q_55 q)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(distinct q_1061 nil)
other(distinct q_1061 nil)
other(= q_1184 self_1058)
(= m_1185 flted_12_1059)
(= p_1186 p)
(= n_1187 n)
(<= 0 n)
(<= 0 flted_12_1059)
(= flted_18_1251 (+ n_1187 m_1185))
(<= 0 m_1185)
(<= 0 n_1187)
otherother(tobool (ssep 
(dll x q_55 flted_18_52)
emp
) )
))
))

(check-sat)