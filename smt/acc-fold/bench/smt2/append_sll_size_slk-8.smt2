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
(declare-fun n1 () Int)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun q_1020 () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun n2 () Int)
(declare-fun m_1021 () Int)
(declare-fun n1_1030 () Int)
(declare-fun n2_1031 () Int)


(assert 
(exists ((flted_12_1036 Int))(and 
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1020 nil)
bvar(distinct q_1020 nil)
bvar(= n1_1030 m_1021)
(= n2_1031 n2)
(<= 0 n2)
(<= 0 m_1021)
(= flted_12_1036 (+ n2_1031 n1_1030))
(<= 0 n1_1030)
(<= 0 n2_1031)
(tobool (ssep 
(pto xprm (sref (ref val v_1019) (ref next q_1020) ))
(ll q_1020 flted_12_1036)
emp
) )
))
)

(assert (not 
(exists ((flted_12_44 Int)(flted_12_1040 Int))(and 
(= flted_12_44 (+ n2 n1))
(= n1 (+ 1 m_1021))
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1020 nil)
bvar(distinct q_1020 nil)
bvar(= n1_1030 m_1021)
(= n2_1031 n2)
(<= 0 n2)
(<= 0 m_1021)
(= flted_12_1040 (+ n2_1031 n1_1030))
(<= 0 n1_1030)
(<= 0 n2_1031)
(tobool (ssep 
(ll x flted_12_44)
emp
) )
))
))

(check-sat)