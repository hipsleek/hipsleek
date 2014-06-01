(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?flted_7_21 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_12) (ref next ?q) )) (ll ?q ?flted_7_21))))
)))









(declare-fun xprm () node)
(declare-fun n1 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun v_bool_15_987prm () boolean)
(declare-fun Anon_1020 () int)
(declare-fun q_1021 () node)
(declare-fun flted_7_1019 () int)
(declare-fun n2 () int)


(assert 
(and 
(= flted_7_1019+1 n1)
lt(= yprm y)
(= xprm x)
(distinct q_1021 nil)
bvar(distinct q_1021 nil)
bvar(tobool (ssep 
(pto xprm (sref (ref val Anon_1020) (ref next q_1021) ))
(ll q_1021 flted_7_1019)
(ll y n2)
emp
) )
)
)

(assert (not 
(and 
(= flted_7_1019+1 n1)
lt(= yprm y)
(= xprm x)
(distinct q_1021 nil)
bvar(distinct q_1021 nil)
bvar(= val_16_982prm Anon_1020)
(= next_16_983prm q_1021)
(tobool (ssep 
(pto xprm (sref (ref val val_16_982prm) (ref next next_16_983prm) ))
(ll q_1021 flted_7_1019)
(ll y n2)
emp
) )
)
))

(check-sat)