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
(declare-fun vprm () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun q1 () node2)
(declare-fun self () node2)
(declare-fun p () node2)
(declare-fun p1 () node2)
(declare-fun q () node2)


(assert 
(and 
(distinct vprm nil)
(= vprm q)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p1 q1)
(tobool (ssep 
(dll q self)
(dll y p)
(pto xprm (sref (ref prev p1) (ref next q) ))
emp
) )
)
)

(assert (not 
(and 
(distinct vprm nil)
(= vprm q)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p1 q1)
(tobool (ssep 
(dll q self)
(dll y p)
(pto xprm (sref (ref prev p1) (ref next q) ))
emp
) )
)
))

(check-sat)