(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?v_22 Int)(?q_23 node))(and 
(tobool (ssep 
(pto ?in (sref (ref val ?v_22) (ref next ?q_23) ))
(ll ?q_23)
) )
)))))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(and 
(= ?in ?p)

)(exists ((?p_21 node)(?v_19 Int)(?q_20 node))(and 
(= ?p_21 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?v_19) (ref next ?q_20) ))
(lseg ?q_20 ?p_21)
) )
)))))










(declare-fun xprm () node)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun x () node)


(assert 
(exists ((v_1012 Int)(q_1013 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1012) (ref next q_1013) ))
(ll q_1013)
emp
) )
))
)

(assert (not 
(exists ((v_1015 Int)(q_1016 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= val_17_981prm v_1015)
(= next_17_982prm q_1016)
(tobool (ssep 
(pto xprm (sref (ref val val_17_981prm) (ref next next_17_982prm) ))
(ll q_1016)
emp
) )
))
))

(check-sat)