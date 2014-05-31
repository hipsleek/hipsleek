(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(declare-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_23 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref next ?q) )) (lseg ?q ?p_23)))
)))

(declare-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(and 
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q)
) )
))))

(declare-fun clist ((?in node))
Space (tospace
(exists ((?self_22 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_14) (ref next ?p) )) (lseg ?p ?self_22)))
))



















(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_20_1003prm () boolean)
(declare-fun Anon_1073 () int)
(declare-fun q_1074 () node)


(assert 
(and 
(distinct x nil)
(= y x)
(= y' y)
(= x' x)
(= q_1074 nil)
(= q_1074 nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_1073) (ref next q_1074) ))
(ll q_1074)
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= y x)
(= y' y)
(= x' x)
(= q_1074 nil)
(= q_1074 nil)
(= val_25_1001' Anon_1073)
(= next_25_1002' q_1074)
(tobool (ssep 
(pto xprm (sref (ref val val_25_1001') (ref next next_25_1002') ))
(ll q_1074)
emp
) )
)
))

(check-sat)