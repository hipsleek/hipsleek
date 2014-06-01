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
(declare-fun n1 () Int)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun q_1022 () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun n2 () Int)
(declare-fun flted_7_1020 () Int)
(declare-fun n1_1031 () Int)
(declare-fun n2_1032 () Int)


(assert 
(exists ((flted_12_1037 Int))(and 
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= n1_1031 flted_7_1020)
(= n2_1032 n2)
(<= 0 n2)
(<= 0 flted_7_1020)
(= flted_12_1037 (+ n2_1032 n1_1031))
(<= 0 n1_1031)
(<= 0 n2_1032)
(tobool (ssep 
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
(ll q_1022 flted_12_1037)
emp
) )
))
)

(assert (not 
(exists ((flted_12_45 Int)(flted_12_1041 Int))(and 
(= flted_12_45 (+ n2 n1))
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(distinct q_1022 nil)
bvar(distinct q_1022 nil)
bvar(= n1_1031 flted_7_1020)
(= n2_1032 n2)
(<= 0 n2)
(<= 0 flted_7_1020)
(= flted_12_1041 (+ n2_1032 n1_1031))
(<= 0 n1_1031)
(<= 0 n2_1032)
(tobool (ssep 
(ll x flted_12_45)
emp
) )
))
))

(check-sat)