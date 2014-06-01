(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun elseg ((?in node) (?p node))
Space (tospace
(or
(and 
(= ?in ?p)

)(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(elseg ?b ?p)
) )
)))))














(declare-fun q () node)
(declare-fun q2 () node)
(declare-fun x () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(elseg x q)
(pto q  (ref nxt q2))
(pto q2  (ref nxt p))
emp
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(elseg x p)
emp
) )
)
))

(check-sat)