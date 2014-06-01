(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?a node)(?m Int)) (tobool (ssep (pto ?in  (ref nxt ?a)) (ll ?a ?m))))
)))
















(declare-fun x () node)
(declare-fun n () Int)


(assert 
(and 
lt(tobool (ssep 
(ll x n)
emp
) )
)
)


(check-sat)