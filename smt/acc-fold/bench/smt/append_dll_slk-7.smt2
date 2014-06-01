(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_22 node2)(?self_23 node2)(?v_20 int)(?q_21 node2)) (tobool (ssep (pto ?in (sref (ref val ?v_20) (ref prev ?p_22) (ref next ?q_21) )) (dll ?q_21 ?self_23))))
)))














(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun next_21_1043 () node2)
(declare-fun q_1033 () node2)
(declare-fun v_bool_22_990prm () boolean)
(declare-fun self_1031 () node2)
(declare-fun v_1032 () int)
(declare-fun p_1030 () node2)


(assert 
(exists ((p_1123 node2)(self_1124 node2)(v_1125 int)(q_1126 node2)) (tobool (ssep (ssep (ssep (dll q_1033 self_1031) (pto yprm (sref (ref val v_1125) (ref prev p_1123) (ref next q_1126) ))) (dll q_1126 self_1124)) (pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) )))))

)

(assert (not 
(exists ((self_1129 node2)(v_1130 int)(p_1128 node2)(q_1131 node2)) (tobool (ssep (ssep (ssep (pto yprm (sref (ref val val_23_987prm) (ref prev prev_23_988prm) (ref next next_23_989prm) )) (dll q_1033 self_1031)) (dll q_1131 self_1129)) (pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) )))))

))

(check-sat)