(set-logic QF_S)

(declare-sort node 0)
(declare-fun val () (Field node int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_24 node)(?v_22 int)(?q_23 node)) (tobool (ssep (pto ?in (sref (ref val ?v_22) (ref next ?q_23) )) (lseg ?q_23 ?p_24))))
)))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?v_25 int)(?q_26 node)) (tobool (ssep (pto ?in (sref (ref val ?v_25) (ref next ?q_26) )) (ll ?q_26))))
)))

(define-fun clist ((?in node))
Space (tospace
(exists ((?self_21 node)(?v_19 int)(?p_20 node)) (tobool (ssep (pto ?in (sref (ref val ?v_19) (ref next ?p_20) )) (lseg ?p_20 ?self_21))))
))





















(declare-fun v_1032 () int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v_bool_22_1006prm () boolean)
(declare-fun next_27_1051 () node)
(declare-fun q_1033 () node)


(assert 
(and 
(distinct x nil)
(= yprm y)
(= xprm x)
(= q_1033 nil)
(= q_1033 nil)
(= next_27_1051 q_1033)
(tobool (ssep 
(ll q_1033)
(pto xprm (sref (ref val v_1032) (ref next yprm) ))
emp
) )
)
)

(assert (not 
(exists ((y_57 node)) (tobool (ssep (lseg x y_57) (ll q_1033))))

))

(check-sat)