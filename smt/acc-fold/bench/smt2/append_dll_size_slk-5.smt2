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
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1016prm () boolean)
(declare-fun v_1060 () Int)
(declare-fun p_1057 () node2)
(declare-fun q_1061 () node2)
(declare-fun self_1058 () node2)
(declare-fun flted_12_1059 () Int)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(and 
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(tobool (ssep 
(dll q_1061 self_1058 flted_12_1059)
(dll y p n)
(pto xprm (sref (ref val v_1060) (ref prev p_1057) (ref next q_1061) ))
emp
) )
)
)

(assert (not 
(and 
(= (+ flted_12_1059 1) m)
(= p_1057 q)
(= self_1058 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1061 nil)
bvar(= q_1061 nil)
bvar(= val_21_1005prm v_1060)
(= prev_21_1006prm p_1057)
(= next_21_1007prm q_1061)
(tobool (ssep 
(pto xprm (sref (ref val val_21_1005prm) (ref prev prev_21_1006prm) (ref next next_21_1007prm) ))
(dll q_1061 self_1058 flted_12_1059)
(dll y p n)
emp
) )
)
))

(check-sat)