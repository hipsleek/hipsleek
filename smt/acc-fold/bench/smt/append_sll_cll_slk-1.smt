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
(declare-fun yprm () TVar[63])
(declare-fun y () TVar[63])
(declare-fun x () node)


(assert 
(exists ((Anon_1026 int)(q_1027 node)) (tobool (ssep (pto xprm (sref (ref val Anon_1026) (ref next q_1027) )) (ll q_1027)))

)

(assert (not 
(exists ((Anon_1029 int)(q_1030 node)) (tobool (ssep (pto xprm (sref (ref val val_20_995') (ref next next_20_996') )) (ll q_1030)))

))

(check-sat)