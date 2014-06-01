(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?p_24 node2)(?self_25 node2)(?flted_12_21 int)(?v_22 int)(?q_23 node2)) (tobool (ssep (pto ?in (sref (ref val ?v_22) (ref prev ?p_24) (ref next ?q_23) )) (dll ?q_23 ?self_25 ?flted_12_21))))
)))














(declare-fun yprm () node2)
(declare-fun xprm () node2)
(declare-fun v_node2_26_1015prm () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () int)
(declare-fun p () node2)
(declare-fun n () int)
(declare-fun v_1060 () int)
(declare-fun p_1057 () node2)
(declare-fun q_1061 () node2)


(assert 
(and 
(= flted_12_1059+1 m)
(= p_1057 q)
(= self_1058 xprm)
lt(= yprm y)
(= xprm x)
(distinct q_1061 nil)
(distinct q_1061 nil)
(= v_node2_26_1015prm q_1061)
(tobool (ssep 
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
(dll q_1061 self_1058 flted_12_1059)
(dll y p n)
emp
) )
)
)

(assert (not 
(and 
ltlt(= flted_12_1059+1 m)
(= p_1057 q)
(= self_1058 xprm)
lt(= yprm y)
(= xprm x)
(distinct q_1061 nil)
(distinct q_1061 nil)
(= v_node2_26_1015prm q_1061)
(= q_1188 self_1058)
(= m_1189 flted_12_1059)
(= p_1190 p)
(= n_1191 n)
(tobool (ssep 
(dll v_node2_26_1015prm q_1188 m_1189)
(dll yprm p_1190 n_1191)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
emp
) )
)
))

(check-sat)