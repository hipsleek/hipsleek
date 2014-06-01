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














(declare-fun v_1060 () int)
(declare-fun v_1180 () int)
(declare-fun q_1181 () node2)
(declare-fun n () int)
(declare-fun p () node2)
(declare-fun self_1178 () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun next_21_1071 () node2)
(declare-fun q_1061 () node2)
(declare-fun yprm () node2)
(declare-fun v_bool_22_1011prm () boolean)
(declare-fun prev_23_1182 () node2)
(declare-fun p_1177 () node2)
(declare-fun xprm () node2)
(declare-fun flted_12_1179 () int)
(declare-fun p_1057 () node2)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () int)


(assert 
(and 
(= flted_12_1179+1 n)
(= p_1177 p)
(= self_1178 yprm)
(= flted_12_1059+1 m)
(= p_1057 q)
(= self_1058 xprm)
lt(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= next_21_1071 q_1061)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= prev_23_1182 p_1177)
(tobool (ssep 
(dll q_1061 self_1058 flted_12_1059)
(dll q_1181 self_1178 flted_12_1179)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) ))
(pto yprm (sref (ref val v_1180) (ref prev xprm) (ref next q_1181) ))
emp
) )
)
)

(assert (not 
(exists ((flted_18_52 int)(q_55 node2)) (tobool (ssep (dll x q_55 flted_18_52) (dll q_1061 self_1058 flted_12_1059))))

))

(check-sat)
