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









(declare-fun xprm () node)
(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun n2 () int)


(assert 
(exists ((flted_7_1015 int)(Anon_1016 int)(q_1017 node)) (tobool (ssep (ssep (pto xprm (sref (ref val Anon_1016) (ref next q_1017) )) (ll q_1017 flted_7_1015)) (ll y n2))))

)

(assert (not 
(exists ((flted_7_1019 int)(Anon_1020 int)(q_1021 node)) (tobool (ssep (ssep (pto xprm (sref (ref val val_15_979prm) (ref next next_15_980prm) )) (ll q_1021 flted_7_1019)) (ll y n2))))

))

(check-sat)