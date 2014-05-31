(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?p_23 node2)(?self_24 node2)(?flted_12_22 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_23) (ref next ?q) )) (dll ?q ?self_24 ?flted_12_22)))
)))













(declare-fun n () int)
(declare-fun flted_12_1058 () int)
(declare-fun q () node2)
(declare-fun self_1057 () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun next_21_1070 () TVar[789])
(declare-fun q_1060 () TVar[789])
(declare-fun v_bool_22_1010prm () boolean)
(declare-fun Anon_1059 () int)
(declare-fun yprm () node2)
(declare-fun p_1056 () node2)


(assert 
(and 
(= q_1060 nil)
(= flted_12_1058 0)
(= q_1060 nil)
(= n 0)
(= flted_12_1058+1 m)
(= p_1056 q)
(= self_1057 x')
lt(= y' y)
(= x' x)
(= q_1060 nil)
bvar(= q_1060 nil)
bvar(= next_21_1070 q_1060)
(= y' nil)
(= y' nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1059) (ref prev p_1056) (ref next y') ))
emp
) )
)
)

(assert (not 
(exists ((flted_18_51 int)(q_54 node2)(Anon_1227 TVar[1690])(q_1228 TVar[1691])) (tobool (dll x q_54 flted_18_51))

))

(check-sat)