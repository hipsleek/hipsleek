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

)(exists ((?p_23 node2)(?self_24 node2)(?v_20 Int)(?q_21 node2)(?m_22 Int))(and 
(= ?n (+ 1 ?m_22))
(= ?p_23 ?p)
(= ?self_24 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_20) (ref prev ?p_23) (ref next ?q_21) ))
(dll ?q_21 ?self_24 ?m_22)
) )
)))))















(declare-fun v_1058 () Int)
(declare-fun n () Int)
(declare-fun m_1060 () Int)
(declare-fun q () node2)
(declare-fun self_1057 () node2)
(declare-fun m () Int)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun next_21_1068 () Int)
(declare-fun q_1059 () Int)
(declare-fun yprm () node2)
(declare-fun v_bool_22_1010prm () boolean)
(declare-fun p_1056 () node2)


(assert 
(and 
(= q_1059 nil)
(= m_1060 0)
(= q_1059 nil)
(= n 0)
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(= next_21_1068 q_1059)
(= yprm nil)
other(= yprm nil)
other(tobool (ssep 
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((flted_18_51 Int)(q_54 node2))(and 
(= flted_18_51 (+ n m))
(= q_54 q)
(= q_1059 nil)
(= m_1060 0)
(= q_1059 nil)
(= n 0)
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(= next_21_1068 q_1059)
(= yprm nil)
other(= yprm nil)
otherotherother(tobool (ssep 
(dll x q_54 flted_18_51)
emp
) )
))
))

(check-sat)