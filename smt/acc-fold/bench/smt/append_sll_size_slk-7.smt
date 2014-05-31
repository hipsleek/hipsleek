(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(declare-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_21 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_12) (ref next ?q) )) (ll ?q ?flted_7_21)))
)))









(declare-fun n2 () int)
(declare-fun n1 () int)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun next_20_1041 () node)
(declare-fun q_1021 () node)
(declare-fun Anon_1020 () int)
(declare-fun yprm () node)
(declare-fun flted_7_1019 () int)


(assert 
(and 
(= flted_7_1019+1 n1)
lt(= y' y)
(= x' x)
(= q_1021 nil)
(= q_1021 nil)
(= next_20_1041 q_1021)
(tobool (ssep 
(ll q_1021 flted_7_1019)
(ll y n2)
(pto xprm (sref (ref val Anon_1020) (ref next y') ))
emp
) )
)
)

(assert (not 
(exists ((flted_12_44 int)(Anon_1052 TVar[725])(q_1053 TVar[726])) (tobool (ssep (ll x flted_12_44) (ll q_1021 flted_7_1019)))

))

(check-sat)