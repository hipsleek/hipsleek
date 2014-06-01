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














(declare-fun v_1032 () Int)
(declare-fun p_1030 () node2)
(declare-fun q () node2)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun q_1033 () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun q_1134 () node2)
(declare-fun self_1031 () node2)
(declare-fun p_1135 () Int)
(declare-fun p () Int)


(assert 
(and 
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1033 nil)
other(distinct q_1033 nil)
other(= q_1134 self_1031)
(= p_1135 p)
(tobool (ssep 
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next q_1033) ))
(dll q_1033 q_1134)
emp
) )
)
)

(assert (not 
(exists ((q_49 node2))(and 
(= q_49 q)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1033 nil)
other(distinct q_1033 nil)
other(= q_1134 self_1031)
(= p_1135 p)
(tobool (ssep 
(dll x q_49)
emp
) )
))
))

(check-sat)