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
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(exists ((p_1050 node2)(self_1051 node2)(v_1052 Int)(q_1053 node2)(m_1054 Int))(and 
(= m (+ 1 m_1054))
(= p_1050 q)
(= self_1051 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1052) (ref prev p_1050) (ref next q_1053) ))
(dll q_1053 self_1051 m_1054)
(dll y p n)
emp
) )
))
)

(assert (not 
(exists ((m_1060 Int)(self_1057 node2)(v_1058 Int)(p_1056 node2)(q_1059 node2))(and 
(= m (+ 1 m_1060))
(= p_1056 q)
(= self_1057 xprm)
(< 0 m)
(= yprm y)
(= xprm x)
(= val_20_1000prm v_1058)
(= prev_20_1001prm p_1056)
(= next_20_1002prm q_1059)
(tobool (ssep 
(pto xprm (sref (ref val val_20_1000prm) (ref prev prev_20_1001prm) (ref next next_20_1002prm) ))
(dll q_1059 self_1057 m_1060)
(dll y p n)
emp
) )
))
))

(check-sat)