(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


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

(define-fun right_nil ((?in node))
Space (tospace
(exists ((?p node)(?l node)(?r node)(?n node))(and 
(= ?r nil)
(tobool  
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?n) ))
 )
))))

(define-fun eright_nil ((?in node))
Space (tospace
(exists ((?p0 node)(?l0 node)(?r0 node)(?n0 node)(?p1 node)(?l1 node)(?r1 node)(?n1 node))(and 
(= ?p0 ?p1)
(= ?l0 ?l1)
(= ?r0 ?r1)
(= ?n0 ?n1)
(= ?r1 nil)
(tobool  
(pto ?in (sref (ref parent ?p0) (ref left ?l0) (ref right ?r0) (ref next ?n0) ))
 )
))))


(define-fun right_nnil ((?in node))
Space (tospace
(exists ((?p node)(?l node)(?r node)(?n node))(and 
(distinct ?r nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?n) ))
(tree ?l)
(tree ?r)
) )
))))

(define-fun eright_nnil ((?in node))
Space (tospace
(exists ((?p0 node)(?l0 node)(?r0 node)(?n0 node)(?p1 node)(?l1 node)(?r1 node)(?n1 node))(and 
(= ?p0 ?p1)
(= ?l0 ?l1)
(= ?r0 ?r1)
(= ?n0 ?n1)
(= ?r1 nil)
(tobool (ssep 
(pto ?in (sref (ref parent ?p0) (ref left ?l0) (ref right ?r0) (ref next ?n0) ))
(tree ?l1)
(tree ?r1)
) )
))))


(define-fun enode ((?in node) (?p node) (?l node) (?r node) (?n node))
Space (tospace
(exists ((?p0 node)(?l0 node)(?r0 node)(?n0 node))(and 
(= ?p0 ?p)
(= ?l0 ?l)
(= ?r0 ?r)
(= ?n0 ?n)
(tobool  
(pto ?in (sref (ref parent ?p0) (ref left ?l0) (ref right ?r0) (ref next ?n0) ))
 )
))))










(define-fun etll ((?in node) (?p node) (?t node) (?r node))
Space (tospace
(exists ((?p1 node)(?t1 node))(and 
(= ?p1 ?p)
(= ?t1 ?t)
(tobool  
(tll ?in ?p1 ?r ?t1)
 )
))))


(define-fun ltll ((?in node) (?p node) (?l node) (?r node) (?D node) (?v node) (?t node))
Space (tospace
(exists ((?l1 node))(and 
(tobool (ssep 
(pto ?in (sref (ref parent ?p) (ref left ?l) (ref right ?r) (ref next ?D) ))
(tll ?l ?in ?v ?l1)
(tll ?r ?in ?l1 ?t)
) )
))))


(declare-fun pprm () node)
(declare-fun xprm () node)
(declare-fun parent0 () node)
(declare-fun p () node)
(declare-fun p1 () node)
(declare-fun x () node)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun D () node)
(declare-fun r () node)
(declare-fun n () node)


(assert 
(and 
(= parent0 p)
(= pprm p1)
(= xprm x)
(= tprm t)
(= r nil)
(tobool  
(pto xprm (sref (ref parent pprm) (ref left D) (ref right r) (ref next n) ))
 )
)
)

(assert (not 
(and 
(= parent0 p)
(= pprm p1)
(= xprm x)
(= tprm t)
(= r nil)
(tobool  
(enode xprm pprm D r n)
 )
)
))

(check-sat)