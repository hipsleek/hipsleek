(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_22 node2)(?self_23 node2)(?v_20 int)(?q_21 node2)) (tobool (ssep (pto ?in (sref (ref val ?v_20) (ref prev ?p_22) (ref next ?q_21) )) (dll ?q_21 ?self_23))))
)))














(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun p () node2)


(assert 
(exists ((p_1025 node2)(self_1026 node2)(v_1027 int)(q_1028 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val v_1027) (ref prev p_1025) (ref next q_1028) )) (dll q_1028 self_1026)) (dll y p))))

)

(assert (not 
(exists ((self_1031 node2)(v_1032 int)(p_1030 node2)(q_1033 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val val_20_980prm) (ref prev prev_20_981prm) (ref next next_20_982prm) )) (dll q_1033 self_1031)) (dll y p))))

))

(check-sat)