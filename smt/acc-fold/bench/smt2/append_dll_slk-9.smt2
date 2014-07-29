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














(declare-fun v1prm () node2)
(declare-fun yprm () node2)
(declare-fun xprm () node2)
(declare-fun p1 () node2)
(declare-fun vprm () boolean)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun self () node2)
(declare-fun q2 () node2)
(declare-fun p2 () node2)
(declare-fun q1 () node2)


(assert 
(and 
(= v1prm q1)
other(distinct q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p2 q2)
(tobool (ssep 
(dll q1 self)
(dll y p1)
(pto xprm (sref (ref prev p2) (ref next q1) ))
emp
) )
)
)

(assert (not 
(and 
(= p p1)
(= q self)
(= v1prm q1)
other(distinct q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p2 q2)
(distinct v1prm nil)
(tobool (ssep 
(dll v1prm q)
(dll yprm p)
(pto xprm (sref (ref prev p2) (ref next q1) ))
emp
) )
)
))

(check-sat)