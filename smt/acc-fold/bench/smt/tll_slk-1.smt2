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














(declare-fun xprm () node)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun x () node)
(declare-fun pprm () node)
(declare-fun p () node)


(assert 
(exists ((flted_11_1116 node)(Anon_1117 node)(D1_1118 node)(Anon_1119 node)) (tobool (pto xprm (sref (ref parent Anon_1117) (ref left D1_1118) (ref right flted_11_1116) (ref next Anon_1119) ))))

)

(assert (not 
(exists ((Anon_1126 node)(D1_1127 node)(flted_11_1125 node)(Anon_1128 node)) (tobool (pto xprm (sref (ref parent parent_25_1060prm) (ref left left_25_1061prm) (ref right right_25_1062prm) (ref next next_25_1063prm) ))))

))

(check-sat)
