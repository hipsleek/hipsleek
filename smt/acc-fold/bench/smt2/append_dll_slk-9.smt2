(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_22 node2)(?self_23 node2)(?v_20 int)(?q_21 node2)) (tobool (ssep (pto ?in (sref (ref val ?v_20) (ref prev ?p_22) (ref next ?q_21) )) (dll ?q_21 ?self_23))))
)))














(declare-fun yprm () node2)
(declare-fun xprm () node2)
(declare-fun v_node2_26_994prm () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun self_1031 () node2)
(declare-fun p () node2)
(declare-fun v_1032 () int)
(declare-fun p_1030 () node2)
(declare-fun q_1033 () node2)


(assert 
(and 
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1033 nil)
(distinct q_1033 nil)
(= v_node2_26_994prm q_1033)
(tobool (ssep 
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next q_1033) ))
(dll q_1033 self_1031)
(dll y p)
emp
) )
)
)

(assert (not 
(and 
(distinct v_node2_26_994prm nil)
(distinct v_node2_26_994prm nil)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_1033 nil)
(distinct q_1033 nil)
(= v_node2_26_994prm q_1033)
(= q_1138 self_1031)
(= p_1139 p)
(tobool (ssep 
(dll v_node2_26_994prm q_1138)
(dll yprm p_1139)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next q_1033) ))
emp
) )
)
))

(check-sat)