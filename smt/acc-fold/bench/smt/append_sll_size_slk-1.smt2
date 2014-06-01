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
(declare-fun n2 () int)


(assert 
(exists ((flted_7_1016 int)(v_1017 int)(q_1018 node)) (tobool (ssep (ssep (pto xprm (sref (ref val v_1017) (ref next q_1018) )) (ll q_1018 flted_7_1016)) (ll y n2))))

)

(assert (not 
(exists ((flted_7_1020 int)(v_1021 int)(q_1022 node)) (tobool (ssep (ssep (pto xprm (sref (ref val val_15_980prm) (ref next next_15_981prm) )) (ll q_1022 flted_7_1020)) (ll y n2))))

))

(check-sat)