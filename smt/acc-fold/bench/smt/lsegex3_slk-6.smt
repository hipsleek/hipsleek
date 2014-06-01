(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?a node)) (tobool (ssep (pto ?in  (ref nxt ?a)) (lseg ?a ?p))))
)))











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
(exists ((w node)) (tobool (lseg x w)))

))

(check-sat)