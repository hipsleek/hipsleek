(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?p_22 node2)(?self_23 node2)(?v_20 Int)(?q_21 node2))(and 
(= ?p_22 ?p)
(= ?self_23 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_20) (ref prev ?p_22) (ref next ?q_21) ))
(dll ?q_21 ?self_23)
) )
)))))














(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun p () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun next_21_1041 () node2)
(declare-fun q_1033 () node2)
(declare-fun v_bool_22_990prm () boolean)
(declare-fun self_1031 () node2)
(declare-fun v_1032 () Int)
(declare-fun p_1030 () node2)


(assert 
(exists ((p_1121 node2)(self_1122 node2)(v_1123 Int)(q_1124 node2))(and 
(= p_1121 p)
(= self_1122 yprm)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1041 q_1033)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(tobool (ssep 
(dll q_1033 self_1031)
(pto yprm (sref (ref val v_1123) (ref prev p_1121) (ref next q_1124) ))
(dll q_1124 self_1122)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
))
)

(assert (not 
(exists ((self_1127 node2)(v_1128 Int)(p_1126 node2)(q_1129 node2))(and 
(= p_1126 p)
(= self_1127 yprm)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1041 q_1033)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= val_23_987prm v_1128)
(= prev_23_988prm p_1126)
(= next_23_989prm q_1129)
(tobool (ssep 
(pto yprm (sref (ref val val_23_987prm) (ref prev prev_23_988prm) (ref next next_23_989prm) ))
(dll q_1033 self_1031)
(dll q_1129 self_1127)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
))
))

(check-sat)