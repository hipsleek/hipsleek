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














(declare-fun v_1032 () int)
(declare-fun v_1130 () int)
(declare-fun q_1131 () node2)
(declare-fun p () node2)
(declare-fun self_1129 () node2)
(declare-fun p_1030 () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun next_21_1043 () node2)
(declare-fun q_1033 () node2)
(declare-fun yprm () node2)
(declare-fun v_bool_22_990prm () boolean)
(declare-fun prev_23_1132 () node2)
(declare-fun p_1128 () node2)
(declare-fun self_1031 () node2)


(assert 
(and 
(= p_1128 p)
(= self_1129 yprm)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1043 q_1033)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= prev_23_1132 p_1128)
(tobool (ssep 
(dll q_1033 self_1031)
(dll q_1131 self_1129)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
(pto yprm (sref (ref val v_1130) (ref prev xprm) (ref next q_1131) ))
emp
) )
)
)

(assert (not 
(exists ((q_49 node2)) (tobool (ssep (dll x q_49) (dll q_1033 self_1031))))

))

(check-sat)
