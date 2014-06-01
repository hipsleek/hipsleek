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














(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun vprm () boolean)
(declare-fun next () node2)
(declare-fun v1prm () boolean)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun q1 () node2)
(declare-fun p1 () node2)
(declare-fun self () node2)
(declare-fun p () node2)


(assert 
(exists ((p2 node2)(self1 node2)(q2 node2))(and 
bvar(distinct yprm nil)
(= next q)
bvar(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q1)
(= self1 yprm)
(= p2 p1)
(tobool (ssep 
(dll q2 self1)
(dll q self)
(pto yprm (sref (ref prev p2) (ref next q2) ))
(pto xprm (sref (ref prev p) (ref next yprm) ))
emp
) )
))
)

(assert (not 
(exists ((self2 node2)(p3 node2)(q3 node2))(and 
(= nextprm q3)
(= prevprm p3)
bvar(distinct yprm nil)
(= next q)
bvar(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q1)
(= self2 yprm)
(= p3 p1)
(tobool (ssep 
(pto yprm (sref (ref prev prevprm) (ref next nextprm) ))
(dll q self)
(dll q3 self2)
(pto xprm (sref (ref prev p) (ref next yprm) ))
emp
) )
))
))

(check-sat)