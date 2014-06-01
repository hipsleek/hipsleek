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
(declare-fun v_node_22_1000prm () node)
(declare-fun v_1032 () Int)
(declare-fun q_1033 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= v_node_22_1000prm q_1033)
(distinct v_node_22_1000prm nil)
(tobool (ssep 
(ll q_1033)
(pto xprm (sref (ref val v_1032) (ref next q_1033) ))
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= v_node_22_1000prm q_1033)
(distinct v_node_22_1000prm nil)
(tobool (ssep 
(ll q_1033)
(pto xprm (sref (ref val v_1032) (ref next q_1033) ))
emp
) )
)
))

(check-sat)