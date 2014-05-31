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









(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun next_20_1032 () node)
(declare-fun q_1014 () node)
(declare-fun Anon_1013 () int)
(declare-fun yprm () node)


(assert 
(and 
(distinct x nil)
(= y' y)
(= x' x)
(= q_1014 nil)
(= q_1014 nil)
(= next_20_1032 q_1014)
(tobool (ssep 
(ll q_1014)
(pto xprm (sref (ref val Anon_1013) (ref next y') ))
emp
) )
)
)

(assert (not 
(exists ((y_48 node)(Anon_1042 TVar[567])(q_1043 node)) (tobool (ssep (lseg x y_48) (ll q_1014)))

))

(check-sat)