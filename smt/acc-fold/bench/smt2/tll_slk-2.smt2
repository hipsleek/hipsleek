(set-logic QF_S)

(declare-sort node 0)
(declare-fun parent () (Field node node))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))
(declare-fun next () (Field node node))

(define-fun tree ((?in node))
Space (tospace
(or
(exists ((?p_35 node)(?D1_36 node)(?r_37 node)(?n_38 node))(and 
(= ?r_37 nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?p_35) (ref left ?D1_36) (ref right ?r_37) (ref next ?n_38) ))
) )
))(exists ((?p_39 node)(?l_40 node)(?r_41 node)(?D2_42 node))(and 
(distinct ?r_41 nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?p_39) (ref left ?l_40) (ref right ?r_41) (ref next ?D2_42) ))
(tree ?l_40)
(tree ?r_41)
) )
)))))

(define-fun tll ((?in node) (?p node) (?ll node) (?lr node))
Space (tospace
(or
(exists ((?lr_28 node)(?p_21 node)(?D1_22 node)(?l_23 node))(and 
(= ?l_23 nil)
(= ?in ?ll)
(= ?lr_28 ?lr)
(tobool (ssep 
(pto ?in (sref (ref parent ?p_21) (ref left ?D1_22) (ref right ?l_23) (ref next ?lr_28) ))
) )
))(exists ((?p_29 node)(?self_30 node)(?ll_31 node)(?self_32 node)(?z_33 node)(?lr_34 node)(?l_24 node)(?r_25 node)(?D2_26 node)(?z_27 node))(and 
(distinct ?r_25 nil)
(= ?p_29 ?p)
(= ?self_30 ?in)
(= ?ll_31 ?ll)
(= ?self_32 ?in)
(= ?z_33 ?z_27)
(= ?lr_34 ?lr)
(tobool (ssep 
(pto ?in (sref (ref parent ?p_29) (ref left ?l_24) (ref right ?r_25) (ref next ?D2_26) ))
(tll ?l_24 ?self_30 ?ll_31 ?z_27)
(tll ?r_25 ?self_32 ?z_33 ?lr_34)
) )
)))))















(declare-fun xprm () node)
(declare-fun pprm () Int)
(declare-fun p () Int)
(declare-fun x () node)
(declare-fun tprm () Int)
(declare-fun t () Int)


(assert 
(exists ((p1 node)(l node)(r node)(D node))(and 
(= pprm p)
(= xprm x)
(= tprm t)
(distinct r nil)
(tobool (ssep 
(pto xprm (sref (ref parent p1) (ref left l) (ref right r) (ref next D) ))
(tree l)
(tree r)
emp
) )
))
)

(assert (not 
(exists ((p2 node)(l1 node)(r1 node)(D1 node))(and 
(= nextprm D1)
(= rightprm r1)
(= leftprm l1)
(= parentprm p2)
(= pprm p)
(= xprm x)
(= tprm t)
(distinct r1 nil)
(tobool (ssep 
(pto xprm (sref (ref parent parentprm) (ref left leftprm) (ref right rightprm) (ref next nextprm) ))
(tree l1)
(tree r1)
emp
) )
))
))

(check-sat)