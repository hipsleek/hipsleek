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















(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun m () Int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun v_1058 () Int)
(declare-fun p_1056 () node2)
(declare-fun q_1059 () node2)
(declare-fun self_1057 () node2)
(declare-fun m_1060 () Int)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(and 
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(tobool (ssep 
(dll q_1059 self_1057 m_1060)
(dll y p n)
(pto xprm (sref (ref val v_1058) (ref prev p_1056) (ref next q_1059) ))
emp
) )
)
)

(assert (not 
(and 
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= q_1059 nil)
bvar(= q_1059 nil)
bvar(= val_21_1004prm v_1058)
(= prev_21_1005prm p_1056)
(= next_21_1006prm q_1059)
(tobool (ssep 
(pto xprm (sref (ref val val_21_1004prm) (ref prev prev_21_1005prm) (ref next next_21_1006prm) ))
(dll q_1059 self_1057 m_1060)
(dll y p n)
emp
) )
)
))

(check-sat)