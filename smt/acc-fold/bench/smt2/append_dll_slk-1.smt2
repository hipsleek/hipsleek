(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?p_22 node2)(?self_23 node2)(?v_20 Int)(?q_21 node2))(and 
(= ?p_22 ?p)
(= ?self_23 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?v_20) (ref prev ?p_22) (ref next ?q_21) ))
(dll ?q_21 ?self_23)
) )
)))))














(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun p () node2)


(assert 
(exists ((p_1025 node2)(self_1026 node2)(v_1027 Int)(q_1028 node2))(and 
(= p_1025 q)
(= self_1026 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_1027) (ref prev p_1025) (ref next q_1028) ))
(dll q_1028 self_1026)
(dll y p)
emp
) )
))
)

(assert (not 
(exists ((self_1031 node2)(v_1032 Int)(p_1030 node2)(q_1033 node2))(and 
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= val_20_980prm v_1032)
(= prev_20_981prm p_1030)
(= next_20_982prm q_1033)
(tobool (ssep 
(pto xprm (sref (ref val val_20_980prm) (ref prev prev_20_981prm) (ref next next_20_982prm) ))
(dll q_1033 self_1031)
(dll y p)
emp
) )
))
))

(check-sat)