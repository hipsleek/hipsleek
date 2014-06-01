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














(declare-fun q () node2)
(declare-fun prev () Int)
(declare-fun vprm () boolean)
(declare-fun next () node2)
(declare-fun v1prm () boolean)
(declare-fun q1 () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun xprm () node2)
(declare-fun p () node2)
(declare-fun self1 () node2)
(declare-fun yprm () node2)
(declare-fun p1 () Int)
(declare-fun p2 () Int)
(declare-fun q2 () node2)
(declare-fun self () node2)


(assert 
(and 
(= prev p1)
bvar(distinct yprm nil)
(= next q1)
bvar(= q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q2)
(= self1 yprm)
(= p1 p2)
(tobool (ssep 
(dll q self1)
(dll q1 self)
(pto xprm (sref (ref prev p) (ref next yprm) ))
(pto yprm (sref (ref prev xprm) (ref next q) ))
emp
) )
)
)

(assert (not 
(exists ((q3 node2))(and 
(= prev p1)
bvar(distinct yprm nil)
(= next q1)
bvar(= q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p q2)
(= self1 yprm)
(= p1 p2)
(= q3 q2)
(tobool (ssep 
(dll x q3)
(dll q1 self)
emp
) )
))
))

(check-sat)