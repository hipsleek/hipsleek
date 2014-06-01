(set-logic QF_S)

(declare-sort node 0)
(declare-fun parent () (Field node node))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))
(declare-fun next () (Field node node))

(define-fun tree ((?in node))
Space (tospace
(or
(exists ((?flted_11_35 node)) (tobool (pto ?in (sref (ref parent ?Anon_14) (ref left ?D1) (ref right ?flted_11_35) (ref next ?Anon_15) ))))
(and 
(distinct ?r nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?Anon_16) (ref left ?l) (ref right ?r) (ref next ?D2) ))
(tree ?l)
(tree ?r)
) )
))))

(define-fun tll ((?in node) (?p node) (?ll node) (?lr node))
Space (tospace
(or
(exists ((?p_26 node)(?lr_27 node)(?flted_16_25 node)) (tobool (pto ?in (sref (ref parent ?p_26) (ref left ?D1) (ref right ?flted_16_25) (ref next ?lr_27) ))))
(exists ((?p_28 node)(?self_29 node)(?ll_30 node)(?self_31 node)(?z_32 node)(?lr_33 node)) (tobool (ssep (ssep (pto ?in (sref (ref parent ?p_28) (ref left ?l) (ref right ?r) (ref next ?D2) )) (tll ?l ?self_29 ?ll_30 ?z)) (tll ?r ?self_31 ?z_32 ?lr_33))))
)))














(declare-fun l_87prm () node)
(declare-fun tprm () node)
(declare-fun xprm () node)
(declare-fun pprm () node)
(declare-fun v_node_34_1082prm () node)
(declare-fun t () node)
(declare-fun x () node)
(declare-fun p () node)
(declare-fun parent_25_1133 () node)
(declare-fun v_bool_26_1084prm () boolean)
(declare-fun l_1131 () node)
(declare-fun r_1132 () node)
(declare-fun D2_1130 () node)


(assert 
(and 
(distinct r_1132 nil)
(= tprm t)
(= xprm x)
(= pprm p)
(= parent_25_1133 Anon_1129)
(distinct r_1132 nil)
(distinct r_1132 nil)
(distinct r_1132 nil)
(distinct r_1132 nil)
(= v_node_34_1082prm l_1131)
(tobool (ssep 
(tree l_1131)
(pto xprm (sref (ref parent pprm) (ref left l_1131) (ref right r_1132) (ref next D2_1130) ))
(tll r_1132 xprm l_87prm tprm)
emp
) )
)
)

(assert (not 
(and 
(distinct r_1132 nil)
(= tprm t)
(= xprm x)
(= pprm p)
(= parent_25_1133 Anon_1129)
(distinct r_1132 nil)
(distinct r_1132 nil)
(distinct r_1132 nil)
(distinct r_1132 nil)
(= v_node_34_1082prm l_1131)
(tobool (ssep 
(tree v_node_34_1082prm)
(pto xprm (sref (ref parent pprm) (ref left l_1131) (ref right r_1132) (ref next D2_1130) ))
(tll r_1132 xprm l_87prm tprm)
emp
) )
)
))

(check-sat)
