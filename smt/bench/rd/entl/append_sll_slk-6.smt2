(set-logic QF_S)

(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?q_18 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_18))
(ll ?q_18)
) )
)))))

(define-fun ll_e1 ((?in node))
Space (tospace
(exists ((?q node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q))
(ll ?q)
) )
))))

(define-fun ll_e2 ((?in node))
Space (tospace
(exists ((?p node)(?q node))(and 
(= ?p ?q)
(tobool (ssep 
(pto ?in  (ref next ?p))
(ll ?q)
) )
))))




(define-fun node_e1 ((?in node) (?q node))
Space (tospace
(exists ((?p node))(and 
(= ?p ?q)
(tobool  
(pto ?in  (ref next ?p))
 )
))))







(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun q () node)


(assert 
(and 
(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(ll y)
(pto xprm  (ref next q))
) )
)
)

(assert (not 
(and 
(= q nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(node_e1 xprm q)
(ll q)
(ll y)
) )
)
))

(check-sat)