(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun olseg ((?in node) (?p node))
Space (tospace
(or
(and 
(tobool  
(pto ?in  (ref nxt ?p))
 )
)(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(olseg ?b ?p)
) )
)))))











(declare-fun p () node)
(declare-fun a () node)
(declare-fun b () node)
(declare-fun k () node)
(declare-fun g () node)


(assert 
(and 
(tobool (ssep 
(pto k  (ref nxt b))
(olseg b p)
(pto p  (ref nxt a))
(pto a  (ref nxt b))
(pto b  (ref nxt g))
) )
)
)

(assert (not 
(and 
(tobool  
(olseg k g)
 )
)
))

(check-sat)