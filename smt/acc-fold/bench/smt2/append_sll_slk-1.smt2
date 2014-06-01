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


(assert 
(exists ((v_990 Int)(q_991 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(tobool (ssep 
(pto xprm (sref (ref val v_990) (ref next q_991) ))
(ll q_991)
(ll y)
emp
) )
))
)

(assert (not 
(exists ((v_993 Int)(q_994 node))(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= val_14_959prm v_993)
(= next_14_960prm q_994)
(tobool (ssep 
(pto xprm (sref (ref val val_14_959prm) (ref next next_14_960prm) ))
(ll q_994)
(ll y)
emp
) )
))
))

(check-sat)