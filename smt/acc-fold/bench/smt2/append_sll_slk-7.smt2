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










(declare-fun v_993 () Int)
(declare-fun yprm () Int)
(declare-fun y () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun q_994 () node)
(declare-fun v_bool_14_967prm () boolean)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_994 nil)
bvar(distinct q_994 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val v_993) (ref next q_994) ))
(ll q_994)
emp
) )
)
)

(assert (not 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(distinct q_994 nil)
bvar(distinct q_994 nil)
bvar(tobool (ssep 
(ll x)
emp
) )
)
))

(check-sat)