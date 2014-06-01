(set-logic QF_S)

(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?a node)) (tobool (ssep (pto ?in  (ref nxt ?a)) (ll ?a n-1))))
)))
















(declare-fun x () node)
(declare-fun n () int)


(assert 
(and 
gt(tobool (ssep 
(ll x n)
emp
) )
)
)

(assert (not 
(exists ((q node)) (tobool (ssep (pto x  (ref nxt q)) (ll q n-1))))

))

(check-sat)