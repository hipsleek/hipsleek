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















(declare-fun D1_1141 () node)
(declare-fun tprm () node)
(declare-fun pprm () node)
(declare-fun parent_36_1148 () TVar[333])
(declare-fun Anon_1140 () TVar[333])
(declare-fun flted_11_1139 () node)
(declare-fun v_bool_37_1098prm () boolean)
(declare-fun next_39_1161 () TVar[339])
(declare-fun Anon_1142 () TVar[339])
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun p () node)
(declare-fun t () node)
(declare-fun res () node)


(assert 
(and 
(= flted_11_1139 nil)
(= t' t)
(= x' x)
(= p' p)
(= parent_36_1148 Anon_1140)
(= flted_11_1139 nil)
bvar(= flted_11_1139 nil)
bvar(= next_39_1161 Anon_1142)
(= res x')
(tobool (ssep 
(pto xprm (sref (ref parent p') (ref left D1_1141) (ref right flted_11_1139) (ref next t') ))
emp
) )
)
)

(assert (not 
(exists ((p_85 node)(t_86 node)) (tobool (tll x p_85 res t_86))

))

(check-sat)