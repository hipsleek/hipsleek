(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(and 
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q)
) )
))))









(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_13_966prm () boolean)
(declare-fun Anon_992 () int)
(declare-fun q_993 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_993 nil)
(= q_993 nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon_992) (ref next q_993) ))
(ll q_993)
(ll y)
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_993 nil)
(= q_993 nil)
(= val_18_964prm Anon_992)
(= next_18_965prm q_993)
(tobool (ssep 
(pto xprm (sref (ref val val_18_964prm) (ref next next_18_965prm) ))
(ll q_993)
(ll y)
emp
) )
)
))

(check-sat)