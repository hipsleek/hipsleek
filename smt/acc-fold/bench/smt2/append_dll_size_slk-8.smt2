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















(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun n () Int)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun next_21_1069 () node2)
(declare-fun q_1061 () node2)
(declare-fun v_bool_22_1011prm () boolean)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () Int)
(declare-fun v_1060 () Int)
(declare-fun p_1057 () node2)


(assert 
(exists ((p_1169 node2)(self_1170 node2)(flted_12_1171 Int)(v_1172 Int)(q_1173 node2))(and 
(= (+ flted_12_1171 1) n)
(= p_1169 p)
(= self_1170 yprm)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= next_21_1069 q_1061)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(tobool (ssep 
(dll q_1061 self_1058 flted_12_1059)
(pto yprm (sref (ref val v_1172) (ref prev p_1169) (ref next q_1173) ))
(dll q_1173 self_1170 flted_12_1171)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) ))
emp
) )
))
)

(assert (not 
(exists ((flted_12_1177 Int)(self_1176 node2)(v_1178 Int)(p_1175 node2)(q_1179 node2))(and 
(= (+ flted_12_1177 1) n)
(= p_1175 p)
(= self_1176 yprm)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= next_21_1069 q_1061)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= val_23_1008prm v_1178)
(= prev_23_1009prm p_1175)
(= next_23_1010prm q_1179)
(tobool (ssep 
(pto yprm (sref (ref val val_23_1008prm) (ref prev prev_23_1009prm) (ref next next_23_1010prm) ))
(dll q_1061 self_1058 flted_12_1059)
(dll q_1179 self_1176 flted_12_1177)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) ))
emp
) )
))
))

(check-sat)