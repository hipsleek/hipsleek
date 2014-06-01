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
(declare-fun v_node_23_1003prm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_22_1006prm () boolean)
(declare-fun v_1084 () int)
(declare-fun q_1085 () node)


(assert 
(and 
(distinct x nil)
(= y x)
(= yprm y)
(= xprm x)
(distinct q_1085 nil)
bvar(distinct q_1085 nil)
bvar(= v_node_23_1003prm q_1085)
(tobool (ssep 
(pto xprm (sref (ref val v_1084) (ref next q_1085) ))
(ll q_1085)
emp
) )
)
)

(assert (not 
(and 
(distinct v_node_23_1003prm nil)
(distinct v_node_23_1003prm nil)
(distinct x nil)
(= y x)
(= yprm y)
(= xprm x)
(distinct q_1085 nil)
bvar(distinct q_1085 nil)
bvar(= v_node_23_1003prm q_1085)
(tobool (ssep 
(ll v_node_23_1003prm)
(pto xprm (sref (ref val v_1084) (ref next q_1085) ))
emp
) )
)
))

(check-sat)