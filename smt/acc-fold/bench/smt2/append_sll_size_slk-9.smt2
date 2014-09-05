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











(declare-fun v_1019 () Int)
(declare-fun n2 () Int)
(declare-fun n1 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun next_20_1039 () node)
(declare-fun q_1020 () node)
(declare-fun m_1021 () Int)


(assert 
(and 
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(= q_1020 nil)
other(= q_1020 nil)
other(= next_20_1039 q_1020)
(tobool (ssep 
(ll q_1020 m_1021)
(ll y n2)
(pto xprm (sref (ref val v_1019) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((flted_12_44 Int))(and 
(= flted_12_44 (+ n2 n1))
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(= q_1020 nil)
other(= q_1020 nil)
other(= next_20_1039 q_1020)
(tobool (ssep 
(ll x flted_12_44)
(ll q_1020 m_1021)
emp
) )
))
))

(check-sat)