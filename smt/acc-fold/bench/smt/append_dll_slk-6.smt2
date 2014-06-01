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














(declare-fun xprm () node2)
(declare-fun yprm () node2)
(declare-fun q () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_995prm () boolean)
(declare-fun next_21_1043 () node2)
(declare-fun q_1033 () node2)
(declare-fun self_1031 () node2)
(declare-fun p () node2)
(declare-fun v_1032 () int)
(declare-fun p_1030 () node2)


(assert 
(and 
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1043 q_1033)
(distinct yprm nil)
(tobool (ssep 
(dll q_1033 self_1031)
(dll y p)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(and 
(= p_1030 q)
(= self_1031 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
bvar(= q_1033 nil)
bvar(= next_21_1043 q_1033)
(distinct yprm nil)
(tobool (ssep 
(dll q_1033 self_1031)
(dll y p)
(pto xprm (sref (ref val v_1032) (ref prev p_1030) (ref next yprm) ))
emp
) )
)
))

(check-sat)