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









(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((Anon_989 int)(q_990 node)) (tobool (ssep (ssep (pto xprm (sref (ref val Anon_989) (ref next q_990) )) (ll q_990)) (ll y)))

)

(assert (not 
(exists ((Anon_992 int)(q_993 node)) (tobool (ssep (ssep (pto xprm (sref (ref val val_13_958') (ref next next_13_959') )) (ll q_993)) (ll y)))

))

(check-sat)