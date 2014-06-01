(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?v_19 Int)(?q_20 node)(?m_21 Int))(and 
(= ?n (+ 1 ?m_21))
(tobool (ssep 
(pto ?in (sref (ref val ?v_19) (ref next ?q_20) ))
(ll ?q_20 ?m_21)
) )
)))))











(declare-fun xprm () node)
(declare-fun n1 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun n2 () Int)


(assert 
(exists ((v_1015 Int)(q_1016 node)(m_1017 Int))(and 
(= n1 (+ 1 m_1017))
(< 0 n1)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1015) (ref next q_1016) ))
(ll q_1016 m_1017)
(ll y n2)
emp
) )
))
)

(assert (not 
(exists ((m_1021 Int)(v_1019 Int)(q_1020 node))(and 
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(= val_15_979prm v_1019)
(= next_15_980prm q_1020)
(tobool (ssep 
(pto xprm (sref (ref val val_15_979prm) (ref next next_15_980prm) ))
(ll q_1020 m_1021)
(ll y n2)
emp
) )
))
))

(check-sat)