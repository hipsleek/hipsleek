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











(declare-fun xprm () node)
(declare-fun n1 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun n2 () Int)


(assert 
(exists ((flted_7_1016 Int)(v_1017 Int)(q_1018 node))(and 
(= (+ flted_7_1016 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1017) (ref next q_1018) ))
(ll q_1018 flted_7_1016)
(ll y n2)
emp
) )
))
)

(assert (not 
(exists ((flted_7_1020 Int)(v_1021 Int)(q_1022 node))(and 
(= (+ flted_7_1020 1) n1)
(< 0 n1)
(= yprm y)
(= xprm x)
(= val_15_980prm v_1021)
(= next_15_981prm q_1022)
(tobool (ssep 
(pto xprm (sref (ref val val_15_980prm) (ref next next_15_981prm) ))
(ll q_1022 flted_7_1020)
(ll y n2)
emp
) )
))
))

(check-sat)