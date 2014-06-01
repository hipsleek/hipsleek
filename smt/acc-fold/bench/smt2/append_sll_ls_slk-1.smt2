(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?v_22 int)(?q_23 node)) (tobool (ssep (pto ?in (sref (ref val ?v_22) (ref next ?q_23) )) (ll ?q_23))))
)))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_21 node)(?v_19 int)(?q_20 node)) (tobool (ssep (pto ?in (sref (ref val ?v_19) (ref next ?q_20) )) (lseg ?q_20 ?p_21))))
)))










(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((v_1012 int)(q_1013 node)) (tobool (ssep (pto xprm (sref (ref val v_1012) (ref next q_1013) )) (ll q_1013))))

)

(assert (not 
(exists ((v_1015 int)(q_1016 node)) (tobool (ssep (pto xprm (sref (ref val val_17_981prm) (ref next next_17_982prm) )) (ll q_1016))))

))

(check-sat)
