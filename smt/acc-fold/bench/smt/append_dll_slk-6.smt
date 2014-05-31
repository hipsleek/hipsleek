(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22)))
)))













(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_994prm () boolean)
(declare-fun next_21_1042 () node2)
(declare-fun q_1032 () node2)
(declare-fun v_bool_22_989prm () boolean)
(declare-fun self_1030 () node2)
(declare-fun Anon_1031 () int)
(declare-fun p_1029 () node2)


(assert 
(exists ((p_1122 node2)(self_1123 node2)(Anon_1124 int)(q_1125 node2)) (tobool (ssep (ssep (ssep (dll q_1032 self_1030) (pto yprm (sref (ref val Anon_1124) (ref prev p_1122) (ref next q_1125) ))) (dll q_1125 self_1123)) (pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next y') ))))

)

(assert (not 
(exists ((self_1128 node2)(Anon_1129 int)(p_1127 node2)(q_1130 node2)) (tobool (ssep (ssep (ssep (pto yprm (sref (ref val val_23_986') (ref prev prev_23_987') (ref next next_23_988') )) (dll q_1032 self_1030)) (dll q_1130 self_1128)) (pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next y') ))))

))

(check-sat)