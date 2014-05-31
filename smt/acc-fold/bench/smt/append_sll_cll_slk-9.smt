(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_23 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref next ?q) )) (lseg ?q ?p_23))))
)))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(and 
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q)
) )
))))

(define-fun clist ((?in node))
Space (tospace
(exists ((?self_22 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_14) (ref next ?p) )) (lseg ?p ?self_22))))
))



















(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((Anon_1070 int)(q_1071 node)) (tobool (ssep (pto xprm (sref (ref val Anon_1070) (ref next q_1071) )) (ll q_1071))))

)

(assert (not 
(exists ((Anon_1073 int)(q_1074 node)) (tobool (ssep (pto xprm (sref (ref val val_20_995prm) (ref next next_20_996prm) )) (ll q_1074))))

))

(check-sat)