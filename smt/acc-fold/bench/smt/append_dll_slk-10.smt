(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22))))
)))













(declare-fun p_1029 () node2)
(declare-fun q () node2)
(declare-fun self_1030 () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_994prm () boolean)
(declare-fun next_21_1042 () node)
(declare-fun q_1032 () node)
(declare-fun v_bool_22_989prm () boolean)
(declare-fun Anon_1031 () int)
(declare-fun yprm () node2)


(assert 
(and 
(= q_1032 nil)
(= q_1032 nil)
(= p_1029 q)
(= self_1030 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1032 nil)
bvar(= q_1032 nil)
bvar(= next_21_1042 q_1032)
(= yprm nil)
(= yprm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((q_48 node2)(Anon_1165 int)(q_1166 node)) (tobool (dll x q_48)))

))

(check-sat)
