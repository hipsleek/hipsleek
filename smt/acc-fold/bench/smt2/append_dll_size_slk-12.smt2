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















(declare-fun v_1060 () Int)
(declare-fun n () Int)
(declare-fun flted_12_1059 () Int)
(declare-fun q () node2)
(declare-fun self_1058 () node2)
(declare-fun m () Int)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun next_21_1069 () Int)
(declare-fun q_1061 () Int)
(declare-fun yprm () node2)
(declare-fun v_bool_22_1011prm () boolean)
(declare-fun p_1057 () node2)


(assert 
(and 
(= q_1061 nil)
(= flted_12_1059 0)
(= q_1061 nil)
(= n 0)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= next_21_1069 q_1061)
(= yprm nil)
other(= yprm nil)
other(tobool (ssep 
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((flted_18_52 Int)(q_55 node2))(and 
(= flted_18_52 (+ n m))
(= q_55 q)
(= q_1061 nil)
(= flted_12_1059 0)
(= q_1061 nil)
(= n 0)
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= next_21_1069 q_1061)
(= yprm nil)
other(= yprm nil)
otherotherother(tobool (ssep 
(dll x q_55 flted_18_52)
emp
) )
))
))

(check-sat)