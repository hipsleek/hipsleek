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










(declare-fun v_1015 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun q_1016 () node)
(declare-fun v_bool_17_989prm () boolean)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1016 nil)
bvar(distinct q_1016 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val v_1015) (ref next q_1016) ))
(lseg q_1016 yprm)
emp
) )
)
)

(assert (not 
(exists ((y_50 node))(and 
(= y_50 y)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1016 nil)
bvar(distinct q_1016 nil)
bvar(tobool (ssep 
(lseg x y_50)
emp
) )
))
))

(check-sat)