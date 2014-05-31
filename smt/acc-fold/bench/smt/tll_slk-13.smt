(set-logic QF_S)

(declare-sort node 0)
(declare-fun parent () (Field node node))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))
(declare-fun next () (Field node node))

(declare-fun tree ((?in node))
Space (tospace
(or
(exists ((?flted_11_35 node)) (tobool (pto ?in (sref (ref parent ?Anon_14) (ref left ?D1) (ref right ?flted_11_35) (ref next ?Anon_15) )))
(and 
(distinct ?r nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?Anon_16) (ref left ?l) (ref right ?r) (ref next ?D2) ))
(tree ?l)
(tree ?r)
) )
))))

(declare-fun tll ((?in node) (?p node) (?ll node) (?lr node))
Space (tospace
(or
(exists ((?p_26 node)(?lr_27 node)(?flted_16_25 node)) (tobool (pto ?in (sref (ref parent ?p_26) (ref left ?D1) (ref right ?flted_16_25) (ref next ?lr_27) )))
(exists ((?p_28 node)(?self_29 node)(?ll_30 node)(?self_31 node)(?z_32 node)(?lr_33 node)) (tobool (ssep (ssep (pto ?in (sref (ref parent ?p_28) (ref left ?l) (ref right ?r) (ref next ?D2) )) (tll ?l ?self_29 ?ll_30 ?z)) (tll ?r ?self_31 ?z_32 ?lr_33)))
)))















(declare-fun D2_1144 () node)
(declare-fun tprm () node)
(declare-fun pprm () node)
(declare-fun parent_36_1147 () TVar[403])
(declare-fun Anon_1143 () TVar[403])
(declare-fun v_bool_37_1098prm () boolean)
(declare-fun r_1146 () node)
(declare-fun l_1145 () node)
(declare-fun v_node_45_1097prm () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun p () node)
(declare-fun t () node)
(declare-fun res () node)


(assert 
(exists ((l_87 node)) (tobool (ssep (ssep (pto xprm (sref (ref parent p') (ref left l_1145) (ref right r_1146) (ref next D2_1144) )) (tll r_1146 x' l_87' t')) (tll l_1145 x' v_node_45_1097' l_87')))

)

(assert (not 
(exists ((p_85 node)(t_86 node)) (tobool (tll x p_85 res t_86))

))

(check-sat)