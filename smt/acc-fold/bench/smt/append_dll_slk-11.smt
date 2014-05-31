(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22)))
)))













(declare-fun p_1029 () node2)
(declare-fun q () node2)
(declare-fun yprm () TVar[677])
(declare-fun y () TVar[677])
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_994prm () boolean)
(declare-fun q_1137 () node2)
(declare-fun self_1030 () node2)
(declare-fun p_1138 () TVar[684])
(declare-fun p () TVar[684])
(declare-fun Anon_1031 () int)
(declare-fun q_1032 () node2)


(assert 
(and 
(= p_1029 q)
(= self_1030 x')
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1032 nil)
(distinct q_1032 nil)
(= q_1137 self_1030)
(= p_1138 p)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next q_1032) ))
(dll q_1032 q_1137)
emp
) )
)
)

(assert (not 
(exists ((q_48 node2)(Anon_1177 TVar[1414])(q_1178 TVar[1415])) (tobool (dll x q_48))

))

(check-sat)