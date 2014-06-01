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

)(exists ((?flted_7_20 Int)(?v_21 Int)(?q_22 node))(and 
(= (+ ?flted_7_20 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?v_21) (ref next ?q_22) ))
(ll ?q_22 ?flted_7_20)
) )
)))))











(declare-fun v_1021 () Int)
(declare-fun n2 () Int)
(declare-fun n1 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun next_20_1040 () node)
(declare-fun q_1022 () node)
(declare-fun flted_7_1020 () Int)


(assert 
(and 
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(= q_1022 nil)
other(= q_1022 nil)
other(= next_20_1040 q_1022)
(tobool (ssep 
(ll q_1022 flted_7_1020)
(ll y n2)
(pto xprm (sref (ref val v_1021) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((flted_12_45 Int))(and 
(= flted_12_45 (+ n2 n1))
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(= q_1022 nil)
other(= q_1022 nil)
other(= next_20_1040 q_1022)
(tobool (ssep 
(ll x flted_12_45)
(ll q_1022 flted_7_1020)
emp
) )
))
))

(check-sat)