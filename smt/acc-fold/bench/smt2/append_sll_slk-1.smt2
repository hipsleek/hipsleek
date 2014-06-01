(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?v_19 int)(?q_20 node)) (tobool (ssep (pto ?in (sref (ref val ?v_19) (ref next ?q_20) )) (ll ?q_20))))
)))










(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((v_990 int)(q_991 node)) (tobool (ssep (ssep (pto xprm (sref (ref val v_990) (ref next q_991) )) (ll q_991)) (ll y))))

)

(assert (not 
(exists ((v_993 int)(q_994 node)) (tobool (ssep (ssep (pto xprm (sref (ref val val_14_959prm) (ref next next_14_960prm) )) (ll q_994)) (ll y))))

))

(check-sat)