(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(and 
(= ?in ?p)

)(exists ((?p_24 node)(?v_22 Int)(?q_23 node))(and 
(= ?p_24 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?v_22) (ref next ?q_23) ))
(lseg ?q_23 ?p_24)
) )
)))))

(define-fun ll ((?in node))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?v_25 Int)(?q_26 node))(and 
(tobool (ssep 
(pto ?in (sref (ref val ?v_25) (ref next ?q_26) ))
(ll ?q_26)
) )
)))))

(define-fun clist ((?in node))
Space (tospace
(exists ((?self_21 node)(?v_19 Int)(?p_20 node))(and 
(= ?self_21 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_19) (ref next ?p_20) ))
(lseg ?p_20 ?self_21)
) )
))))





















(declare-fun xprm () node)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun x () node)


(assert 
(exists ((v_1029 Int)(q_1030 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1029) (ref next q_1030) ))
(ll q_1030)
emp
) )
))
)

(assert (not 
(exists ((v_1032 Int)(q_1033 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= val_22_998prm v_1032)
(= next_22_999prm q_1033)
(tobool (ssep 
(pto xprm (sref (ref val val_22_998prm) (ref next next_22_999prm) ))
(ll q_1033)
emp
) )
))
))

(check-sat)