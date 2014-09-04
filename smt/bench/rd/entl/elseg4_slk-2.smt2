(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun elseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(elseg ?b ?p)
) )
)))))










(define-fun right ((?in node) (?p node))
Space (tospace
(exists ((?u node))(and 
(tobool (ssep 
(elseg ?in ?u)
(elseg ?u ?p)
) )
))))





(declare-fun a () node)
(declare-fun x () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(pto x  (ref nxt a))
(pto a  (ref nxt p))
) )
)
)

(assert (not 
(and 
(tobool  
(elseg x p)
 )
)
))

(check-sat)