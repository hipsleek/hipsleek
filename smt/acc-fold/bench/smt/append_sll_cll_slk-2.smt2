(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_24 node)(?v_22 int)(?q_23 node)) (tobool (ssep (pto ?in (sref (ref val ?v_22) (ref next ?q_23) )) (lseg ?q_23 ?p_24))))
)))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?v_25 int)(?q_26 node)) (tobool (ssep (pto ?in (sref (ref val ?v_25) (ref next ?q_26) )) (ll ?q_26))))
)))

(define-fun clist ((?in node))
Space (tospace
(exists ((?self_21 node)(?v_19 int)(?p_20 node)) (tobool (ssep (pto ?in (sref (ref val ?v_19) (ref next ?p_20) )) (lseg ?p_20 ?self_21))))
))





















(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((v_1029 int)(q_1030 node)) (tobool (ssep (pto xprm (sref (ref val v_1029) (ref next q_1030) )) (ll q_1030))))

)

(assert (not 
(exists ((v_1032 int)(q_1033 node)) (tobool (ssep (pto xprm (sref (ref val val_22_998prm) (ref next next_22_999prm) )) (ll q_1033))))

))

(check-sat)
