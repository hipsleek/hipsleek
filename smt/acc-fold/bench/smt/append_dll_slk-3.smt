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













(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_994prm () boolean)
(declare-fun Anon_1031 () int)
(declare-fun p_1029 () node2)
(declare-fun q_1032 () node2)
(declare-fun self_1030 () node2)
(declare-fun p () node2)


(assert 
(and 
(= p_1029 q)
(= self_1030 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1032 nil)
bvar(= q_1032 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next q_1032) ))
(dll q_1032 self_1030)
(dll y p)
emp
) )
)
)

(assert (not 
(and 
(= p_1029 q)
(= self_1030 xprm)
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1032 nil)
bvar(= q_1032 nil)
bvar(= val_21_983prm Anon_1031)
(= prev_21_984prm p_1029)
(= next_21_985prm q_1032)
(tobool (ssep 
(pto xprm (sref (ref val val_21_983prm) (ref prev prev_21_984prm) (ref next next_21_985prm) ))
(dll q_1032 self_1030)
(dll y p)
emp
) )
)
))

(check-sat)