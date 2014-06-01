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
(declare-fun yprm () node2)
(declare-fun q () node2)
(declare-fun self_1031 () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun next_21_1041 () Int)
(declare-fun q_1033 () Int)
(declare-fun v_1032 () Int)
(declare-fun p_1030 () node2)


(assert 
(and 
(= q_1033 nil)
(= q_1033 nil)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1041 q_1033)
(= yprm nil)
(tobool (ssep 
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(and 
(= q_1033 nil)
(= q_1033 nil)
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1041 q_1033)
(= yprm nil)
(tobool (ssep 
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
)
))

(check-sat)