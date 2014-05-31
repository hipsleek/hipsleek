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













(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () int)


(assert 
(exists ((p_1050 node2)(self_1051 node2)(flted_12_1052 int)(Anon_1053 int)(q_1054 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val Anon_1053) (ref prev p_1050) (ref next q_1054) )) (dll q_1054 self_1051 flted_12_1052)) (dll y p n)))

)

(assert (not 
(exists ((flted_12_1058 int)(self_1057 node2)(Anon_1059 int)(p_1056 node2)(q_1060 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val val_20_1000') (ref prev prev_20_1001') (ref next next_20_1002') )) (dll q_1060 self_1057 flted_12_1058)) (dll y p n)))

))

(check-sat)