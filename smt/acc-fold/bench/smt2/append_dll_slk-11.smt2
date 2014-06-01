(set-logic QF_S)

(declare-sort node2 0)
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?p_20 node2)(?self_21 node2)(?q_19 node2))(and 
(= ?p_20 ?p)
(= ?self_21 ?in)
(tobool (ssep 
(pto ?in (sref (ref prev ?p_20) (ref next ?q_19) ))
(dll ?q_19 ?self_21)
) )
)))))














(declare-fun vprm () boolean)
(declare-fun next () Int)
(declare-fun v1prm () boolean)
(declare-fun q () Int)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun self () node2)
(declare-fun xprm () node2)
(declare-fun p () node2)
(declare-fun q1 () node2)


(assert 
(and 
other(= yprm nil)
(= next q)
bvar(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q1)
(tobool (ssep 
(pto xprm (sref (ref prev p) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((q2 node2))(and 
other(= yprm nil)
(= next q)
bvar(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q1)
(= q2 q1)
(tobool (ssep 
(dll x q2)
emp
) )
))
))

(check-sat)