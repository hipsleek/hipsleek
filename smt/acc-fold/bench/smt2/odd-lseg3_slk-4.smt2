(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun olseg ((?in node) (?p node))
Space (tospace
(or
(and 
(tobool (ssep 
(pto ?in  (ref nxt ?p))
) )
)(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(olseg ?b ?p)
) )
)))))











(declare-fun b () node)
(declare-fun x () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(pto x  (ref nxt b))
(olseg b p)
emp
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(olseg x p)
emp
) )
)
))

(check-sat)