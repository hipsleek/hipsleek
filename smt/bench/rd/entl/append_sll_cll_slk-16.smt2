(set-logic QF_S)

(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_21 node)(?q_20 node))(and 
(= ?p_21 ?p)
(tobool (ssep 
(pto ?in  (ref next ?q_20))
(lseg ?q_20 ?p_21)
) )
)))))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?q_22 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_22))
(ll ?q_22)
) )
)))))

(define-fun clist ((?in node))
Space (tospace
(exists ((?self_19 node)(?p_18 node))(and 
(= ?self_19 ?in)
(tobool (ssep 
(pto ?in  (ref next ?p_18))
(lseg ?p_18 ?self_19)
) )
))))

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





(define-fun lseg_e1 ((?in node) (?p node))
Space (tospace
(exists ((?q node))(and 
(= ?p ?q)
(tobool  
(lseg ?in ?p)
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
(= y x)
(distinct x nil)
(tobool (ssep 
(ll q)
(pto xprm  (ref next q))
) )
)
)

(assert (not 
(and 
(= q nil)
(= xprm x)
(= yprm y)
(= y x)
(distinct x nil)
(tobool  
(node_e1 xprm q)
 )
)
))

(check-sat)