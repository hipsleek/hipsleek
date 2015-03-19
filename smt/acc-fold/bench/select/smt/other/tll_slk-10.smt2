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
(tobool  
(pto ?in (sref (ref parent ?p_35) (ref left ?D1_36) (ref right ?r_37) (ref next ?n_38) ))
 )
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
(tobool  
(pto ?in (sref (ref parent ?p_21) (ref left ?D1_22) (ref right ?l_23) (ref next ?lr_28) ))
 )
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

(define-fun enode_nil ((?in node))
Space (tospace
(exists ((?p node)(?l node)(?r node)(?n node))(and 
(= ?r nil)
(tobool  
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?n) ))
 )
))))

(define-fun enode_nnil ((?in node))
Space (tospace
(exists ((?p node)(?l node)(?r node)(?n node))(and 
(distinct ?r nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?n) ))
(tree ?l)
(tree ?r)
) )
))))













(define-fun etll ((?in node) (?p node) (?l node) (?r node) (?D node) (?v node) (?t node))
Space (tospace
(exists ((?lprm node))(and 
(tobool (ssep 
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?D) ))
(tll ?l ?in ?v ?lprm)
(tll ?r ?in ?lprm ?t)
) )
))))



(declare-fun lprm () node)
(declare-fun xprm () node)
(declare-fun tprm () node)
(declare-fun D () node)
(declare-fun l () node)
(declare-fun r () node)
(declare-fun parent () node)
(declare-fun p () node)
(declare-fun pprm () node)
(declare-fun p1 () node)
(declare-fun x () node)
(declare-fun t () node)


(assert 
(and 
(distinct r nil)
(= parent p)
(= pprm p1)
(= xprm x)
(= tprm t)
(tobool (ssep 
(tree l)
(pto xprm (sref (ref parent pprm) (ref left l) (ref right r) (ref next D) ))
(tll r xprm lprm tprm)
) )
)
)

(assert (not 
(and 
(= nextprm D)
(= rightprm r)
(= leftprm l)
(= parentprm pprm)
(distinct r nil)
(= parent p)
(= pprm p1)
(= xprm x)
(= tprm t)
(tobool (ssep 
(pto xprm (sref (ref parent parentprm) (ref left leftprm) (ref right rightprm) (ref next nextprm) ))
(tree l)
(tll r xprm lprm tprm)
) )
)
))

(check-sat)