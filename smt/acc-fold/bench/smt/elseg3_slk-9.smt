(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun elseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?a node)(?b node)) (tobool (ssep (ssep (pto ?in  (ref nxt ?a)) (pto ?a  (ref nxt ?b))) (elseg ?b ?p))))
)))














(declare-fun a () node)
(declare-fun b () node)
(declare-fun z () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(pto z  (ref nxt a))
(pto a  (ref nxt b))
(elseg b p)
emp
) )
)
)

(assert (not 
(exists ((u node)) (tobool (ssep (elseg z u) (elseg u p))))

))

(check-sat)