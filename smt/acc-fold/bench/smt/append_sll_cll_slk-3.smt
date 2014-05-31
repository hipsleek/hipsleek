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
(declare-fun yprm () TVar[118])
(declare-fun y () TVar[118])
(declare-fun x () node)
(declare-fun v_bool_20_1003prm () boolean)
(declare-fun Anon_1029 () int)
(declare-fun q_1030 () node)


(assert 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1030 nil)
bvar(distinct q_1030 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val Anon_1029) (ref next q_1030) ))
(ll q_1030)
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1030 nil)
bvar(distinct q_1030 nil)
bvar(= val_21_998' Anon_1029)
(= next_21_999' q_1030)
(tobool (ssep 
(pto xprm (sref (ref val val_21_998') (ref next next_21_999') ))
(ll q_1030)
emp
) )
)
))

(check-sat)