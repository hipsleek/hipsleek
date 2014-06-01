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
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () int)


(assert 
(exists ((p_1051 node2)(self_1052 node2)(flted_12_1053 int)(v_1054 int)(q_1055 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val v_1054) (ref prev p_1051) (ref next q_1055) )) (dll q_1055 self_1052 flted_12_1053)) (dll y p n))))

)

(assert (not 
(exists ((flted_12_1059 int)(self_1058 node2)(v_1060 int)(p_1057 node2)(q_1061 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val val_20_1001prm) (ref prev prev_20_1002prm) (ref next next_20_1003prm) )) (dll q_1061 self_1058 flted_12_1059)) (dll y p n))))

))

(check-sat)