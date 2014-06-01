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










(declare-fun xprm () node)
(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_15_988prm () boolean)
(declare-fun v_1021 () int)
(declare-fun q_1022 () node)
(declare-fun flted_7_1020 () int)
(declare-fun n2 () int)


(assert 
(and 
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(= q_1022 nil)
(= q_1022 nil)
(tobool (ssep 
(pto xprm (sref (ref val v_1021) (ref next q_1022) ))
(ll q_1022 flted_7_1020)
(ll y n2)
emp
) )
)
)

(assert (not 
(and 
(= flted_7_1020+1 n1)
lt(= yprm y)
(= xprm x)
(= q_1022 nil)
(= q_1022 nil)
(= val_20_986prm v_1021)
(= next_20_987prm q_1022)
(tobool (ssep 
(pto xprm (sref (ref val val_20_986prm) (ref next next_20_987prm) ))
(ll q_1022 flted_7_1020)
(ll y n2)
emp
) )
)
))

(check-sat)