(set-logic QF_S)

(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?q_20 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_20))
(ll ?q_20)
) )
)))))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(and 
(= ?in ?p)

)(exists ((?p_19 node)(?q_18 node))(and 
(= ?p_19 ?p)
(tobool (ssep 
(pto ?in  (ref next ?q_18))
(lseg ?q_18 ?p_19)
) )
)))))










(declare-fun vprm () boolean)
(declare-fun q () node)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun x () node)
(declare-fun y () node)


(assert 
(and 
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(pto xprm  (ref next q))
(lseg q yprm)
emp
) )
)
)

(assert (not 
(exists ((y1 node))(and 
bvar(distinct q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= y1 y)
(tobool (ssep 
(lseg x y1)
emp
) )
))
))

(check-sat)