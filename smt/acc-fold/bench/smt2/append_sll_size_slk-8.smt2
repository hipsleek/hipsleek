(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_20 int)(?v_21 int)(?q_22 node)) (tobool (ssep (pto ?in (sref (ref val ?v_21) (ref next ?q_22) )) (ll ?q_22 ?flted_7_20))))
)))










(declare-fun v_1021 () int)
(declare-fun n2 () int)
(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun next_20_1042 () node)
(declare-fun q_1022 () node)
(declare-fun flted_7_1020 () int)


(assert 
(and 
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(= q_1022 nil)
(= q_1022 nil)
(= next_20_1042 q_1022)
(tobool (ssep 
(ll q_1022 flted_7_1020)
(ll y n2)
(pto xprm (sref (ref val v_1021) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((flted_12_45 int)) (tobool (ssep (ll x flted_12_45) (ll q_1022 flted_7_1020))))

))

(check-sat)