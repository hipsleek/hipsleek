(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(and 
(= ?in ?p)

)(exists ((?a node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(lseg ?a ?p)
) )
)))))











(declare-fun x () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(lseg x p)
emp
) )
)
)

(assert (not 
(exists ((u node)(u2 node))(and 
(tobool (ssep 
(lseg x u)
(lseg u u2)
(lseg u2 p)
emp
) )
))
))

(check-sat)