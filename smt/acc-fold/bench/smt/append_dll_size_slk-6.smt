(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?p_23 node2)(?self_24 node2)(?flted_12_22 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_23) (ref next ?q) )) (dll ?q ?self_24 ?flted_12_22)))
)))













(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun n () int)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun next_21_1070 () node2)
(declare-fun q_1060 () node2)
(declare-fun v_bool_22_1010prm () boolean)
(declare-fun self_1057 () node2)
(declare-fun flted_12_1058 () int)
(declare-fun Anon_1059 () int)
(declare-fun p_1056 () node2)


(assert 
(exists ((p_1170 node2)(self_1171 node2)(flted_12_1172 int)(Anon_1173 int)(q_1174 node2)) (tobool (ssep (ssep (ssep (dll q_1060 self_1057 flted_12_1058) (pto yprm (sref (ref val Anon_1173) (ref prev p_1170) (ref next q_1174) ))) (dll q_1174 self_1171 flted_12_1172)) (pto xprm (sref (ref val Anon_1059) (ref prev p_1056) (ref next y') ))))

)

(assert (not 
(exists ((flted_12_1178 int)(self_1177 node2)(Anon_1179 int)(p_1176 node2)(q_1180 node2)) (tobool (ssep (ssep (ssep (pto yprm (sref (ref val val_23_1007') (ref prev prev_23_1008') (ref next next_23_1009') )) (dll q_1060 self_1057 flted_12_1058)) (dll q_1180 self_1177 flted_12_1178)) (pto xprm (sref (ref val Anon_1059) (ref prev p_1056) (ref next y') ))))

))

(check-sat)