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













(declare-fun q () node2)
(declare-fun m () int)
(declare-fun yprm () TVar[865])
(declare-fun y () TVar[865])
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun q_1187 () node2)
(declare-fun self_1057 () node2)
(declare-fun p_1189 () TVar[873])
(declare-fun p () TVar[873])
(declare-fun n () int)
(declare-fun flted_12_1058 () int)
(declare-fun m_1188 () int)
(declare-fun n_1190 () int)
(declare-fun Anon_1059 () int)
(declare-fun q_1060 () node2)
(declare-fun p_1056 () node2)


(assert 
(exists ((flted_18_1196 int)) (tobool (ssep (pto xprm (sref (ref val Anon_1059) (ref prev p_1056) (ref next q_1060) )) (dll q_1060 q_1187 flted_18_1196)))

)

(assert (not 
(exists ((flted_18_51 int)(q_54 node2)(Anon_1245 TVar[1781])(q_1246 TVar[1782])(flted_18_1242 int)) (tobool (dll x q_54 flted_18_51))

))

(check-sat)