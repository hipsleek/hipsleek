(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(and 
(= ?in nil)

)(exists ((?v_19 Int)(?q_20 node))(and 
(tobool (ssep 
(pto ?in (sref (ref val ?v_19) (ref next ?q_20) ))
(ll ?q_20)
) )
)))))










(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_14_967prm () boolean)
(declare-fun v_993 () Int)
(declare-fun q_994 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_994 nil)
other(= q_994 nil)
other(tobool (ssep 
(ll q_994)
(ll y)
(pto xprm (sref (ref val v_993) (ref next q_994) ))
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_994 nil)
other(= q_994 nil)
other(= val_19_965prm v_993)
(= next_19_966prm q_994)
(tobool (ssep 
(pto xprm (sref (ref val val_19_965prm) (ref next next_19_966prm) ))
(ll q_994)
(ll y)
emp
) )
)
))

(check-sat)