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





















(declare-fun self () node)


(assert 
(and 
(distinct self nil)
(tobool (ssep 
emp
) )
)
)

(assert (not 
(and 
(distinct self nil)
(distinct self nil)
(tobool (ssep 
emp
) )
)
))

(check-sat)
