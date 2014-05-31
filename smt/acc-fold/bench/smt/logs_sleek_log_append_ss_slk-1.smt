(set-logic QF_SLRD)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(declare-fun ll ((?in node) (?n int))
Space (tospace
(or
(exists ((?flted_7_21 int)) (tobool (ssep ((pto ?in(sref (ref val ?Anon_12) (ref next ?q) ))) ((ll ?q ?flted_7_21))))
)))
;other command


(declare-fun TVar__55 () TVar[55])
(declare-fun self () TVar[55])
(declare-fun TVar__54 () TVar[55])
(declare-fun n () int)
(declare-fun TVar__53 () int)
(declare-fun TVar__52 () int)
(declare-fun TVar__51 () TVar[55])
(declare-fun TVar__50 () TVar[55])


(assert (tobool

))

(assert (not (tobool

)))

(check-sat)