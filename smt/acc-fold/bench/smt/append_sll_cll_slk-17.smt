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



















(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_20_1003prm () boolean)
(declare-fun next_25_1095 () node)
(declare-fun q_1074 () node)
(declare-fun Anon_1073 () int)
(declare-fun yprm () node)


(assert 
(and 
(distinct x nil)
(= y x)
(= yprm y)
(= xprm x)
(= q_1074 nil)
(= q_1074 nil)
(= next_25_1095 q_1074)
(tobool (ssep 
(ll q_1074)
(pto xprm (sref (ref val Anon_1073) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((Anon_1102 int)(p_1103 node)) (tobool (ssep (clist x) (ll q_1074))))

))

(check-sat)
