(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_21 node2)(?self_22 node2)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_21) (ref next ?q) )) (dll ?q ?self_22)))
)))













(declare-fun xprm () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_node2_20_982prm () node2)
(declare-fun Anon_1031 () int)
(declare-fun p_1029 () node2)
(declare-fun q_1032 () node2)
(declare-fun self_1030 () node2)
(declare-fun p () node2)


(assert 
(and 
(= p_1029 q)
(= self_1030 x')
(distinct x nil)
(= y' y)
(= x' x)
(= v_node2_20_982' q_1032)
(= v_node2_20_982' nil)
(tobool (ssep 
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
(= self_1030 x')
(distinct x nil)
(= y' y)
(= x' x)
(= v_node2_20_982' q_1032)
(= v_node2_20_982' nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1031) (ref prev p_1029) (ref next q_1032) ))
(dll q_1032 self_1030)
(dll y p)
emp
) )
)
))

(check-sat)