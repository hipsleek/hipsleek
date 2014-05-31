(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_21 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_12) (ref next ?q) )) (ll ?q ?flted_7_21))))
)))









(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun n2 () int)
(declare-fun flted_7_1019 () int)
(declare-fun n1_1032 () int)
(declare-fun n2_1033 () int)
(declare-fun Anon_1020 () int)
(declare-fun q_1021 () node)


(assert 
(exists ((flted_12_1038 int)) (tobool (ssep (pto xprm (sref (ref val Anon_1020) (ref next q_1021) )) (ll q_1021 flted_12_1038))))

)

(assert (not 
(exists ((flted_12_44 int)(flted_12_1042 int)(Anon_1044 int)(q_1045 node)) (tobool (ll x flted_12_44)))

))

(check-sat)
