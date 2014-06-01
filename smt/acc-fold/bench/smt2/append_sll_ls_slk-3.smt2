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
(declare-fun v_node_17_983prm () node)
(declare-fun v_1015 () Int)
(declare-fun q_1016 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= v_node_17_983prm q_1016)
(distinct v_node_17_983prm nil)
(tobool (ssep 
(ll q_1016)
(pto xprm (sref (ref val v_1015) (ref next q_1016) ))
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= v_node_17_983prm q_1016)
(distinct v_node_17_983prm nil)
(tobool (ssep 
(ll q_1016)
(pto xprm (sref (ref val v_1015) (ref next q_1016) ))
emp
) )
)
))

(check-sat)