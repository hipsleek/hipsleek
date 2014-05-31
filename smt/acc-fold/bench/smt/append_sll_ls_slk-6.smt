(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

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

(declare-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_21 node)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref next ?q) )) (lseg ?q ?p_21)))
)))









(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun Anon_1013 () int)
(declare-fun q_1014 () node)


(assert 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(distinct q_1014 nil)
bvar(distinct q_1014 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val Anon_1013) (ref next q_1014) ))
(lseg q_1014 y')
emp
) )
)
)

(assert (not 
(exists ((y_48 node)(Anon_1034 TVar[523])(q_1035 TVar[524])) (tobool (lseg x y_48))

))

(check-sat)