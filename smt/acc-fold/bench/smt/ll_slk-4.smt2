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
















(declare-fun q () node)
(declare-fun n () int)
(declare-fun x () node)


(assert 
(and 
(tobool (ssep 
(pto x  (ref nxt q))
(ll q n)
emp
) )
)
)

(assert (not 
(exists ((m int)) (tobool (ll x m)))

))

(check-sat)