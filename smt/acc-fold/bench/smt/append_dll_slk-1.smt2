(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22))))
)))













(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun p () node2)


(assert 
(exists ((p_1024 node2)(self_1025 node2)(Anon_1026 int)(q_1027 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val Anon_1026) (ref prev p_1024) (ref next q_1027) )) (dll q_1027 self_1025)) (dll y p))))

)

(assert (not 
(exists ((self_1030 node2)(Anon_1031 int)(p_1029 node2)(q_1032 node2)) (tobool (ssep (ssep (pto xprm (sref (ref val val_20_979prm) (ref prev prev_20_980prm) (ref next next_20_981prm) )) (dll q_1032 self_1030)) (dll y p))))

))

(check-sat)