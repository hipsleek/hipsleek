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
(declare-fun v_bool_17_989prm () boolean)
(declare-fun v_1015 () int)
(declare-fun q_1016 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1016 nil)
bvar(distinct q_1016 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val v_1015) (ref next q_1016) ))
(ll q_1016)
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1016 nil)
bvar(distinct q_1016 nil)
bvar(= val_18_984prm v_1015)
(= next_18_985prm q_1016)
(tobool (ssep 
(pto xprm (sref (ref val val_18_984prm) (ref next next_18_985prm) ))
(ll q_1016)
emp
) )
)
))

(check-sat)
