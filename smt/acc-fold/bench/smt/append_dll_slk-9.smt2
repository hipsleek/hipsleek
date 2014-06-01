(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22))))
)))













(declare-fun p () node2)
(declare-fun self_1128 () node2)
(declare-fun p_1029 () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_994prm () boolean)
(declare-fun next_21_1042 () node2)
(declare-fun q_1032 () node2)
(declare-fun v_bool_22_989prm () boolean)
(declare-fun prev_23_1131 () node2)
(declare-fun p_1127 () node2)
(declare-fun Anon_1031 () int)
(declare-fun yprm () node2)
(declare-fun Anon_1129 () int)
(declare-fun q_1130 () node2)
(declare-fun self_1030 () node2)


(assert 
(and 
(= p_1127 p)
(= self_1128 yprm)
(= p_1029 q)
(= self_1030 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1032 nil)
bvar(= q_1032 nil)
bvar(= next_21_1042 q_1032)
(distinct yprm nil)
bvar(distinct yprm nil)
bvar(= prev_23_1131 p_1127)
(tobool (ssep 
(dll q_1032 self_1030)
(dll q_1130 self_1128)
(pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next yprm) ))
(pto yprm (sref (ref val Anon_1129) (ref prev xprm) (ref next q_1130) ))
emp
) )
)
)

(assert (not 
(exists ((q_48 node2)) (tobool (ssep (dll x q_48) (dll q_1032 self_1030))))

))

(check-sat)
