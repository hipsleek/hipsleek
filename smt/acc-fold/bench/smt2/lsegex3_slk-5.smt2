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











(declare-fun p () node)
(declare-fun x () node)


(assert 
(and 
(tobool (ssep 
(lseg x p)
emp
) )
)
)

(assert (not 
(exists ((u node)(w node))(and 
(tobool (ssep 
(lseg x u)
(lseg u w)
emp
) )
))
))

(check-sat)