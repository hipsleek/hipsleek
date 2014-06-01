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














(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun n () int)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun next_21_1071 () node2)
(declare-fun q_1061 () node2)
(declare-fun v_bool_22_1011prm () boolean)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () int)
(declare-fun v_1060 () int)
(declare-fun p_1057 () node2)


(assert 
(exists ((p_1171 node2)(self_1172 node2)(flted_12_1173 int)(v_1174 int)(q_1175 node2)) (tobool (ssep (ssep (ssep (dll q_1061 self_1058 flted_12_1059) (pto yprm (sref (ref val v_1174) (ref prev p_1171) (ref next q_1175) ))) (dll q_1175 self_1172 flted_12_1173)) (pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) )))))

)

(assert (not 
(exists ((flted_12_1179 int)(self_1178 node2)(v_1180 int)(p_1177 node2)(q_1181 node2)) (tobool (ssep (ssep (ssep (pto yprm (sref (ref val val_23_1008prm) (ref prev prev_23_1009prm) (ref next next_23_1010prm) )) (dll q_1061 self_1058 flted_12_1059)) (dll q_1181 self_1178 flted_12_1179)) (pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) )))))

))

(check-sat)