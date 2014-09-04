(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun elseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?a node)(?b node))
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(elseg ?b ?p)
) )
))))



(declare-fun a () node)
(declare-fun x () node)
(declare-fun p () node)


(assert 
(tobool (ssep 
(pto x  (ref nxt a))
(pto a  (ref nxt p))
emp
 )
)
)

(assert (not 
(tobool (ssep 
(elseg x p)
emp
 )
)
))

(check-sat)