(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))
(declare-fun next () (Field node node))

(define-fun tree ((?in node) (?n Int))
Space (tospace
(or
(exists ((?flted_15_28 node)(?flted_15_29 node))(and 
(= ?flted_15_29 nil)
(= ?flted_15_28 nil)
(= ?n 1)
(tobool  
(pto ?in (sref (ref left ?flted_15_29) (ref right ?flted_15_28) (ref next ?Anon_14) ))
 )
))(exists ((?flted_16_30 node))(and 
(= ?flted_16_30 nil)
(= ?n (+ (+ 1 ?n1) ?n2))
(tobool (ssep 
(pto ?in (sref (ref left ?l) (ref right ?r) (ref next ?flted_16_30) ))
(tree ?l ?n1)
(tree ?r ?n2)
) )
)))))

(define-fun tll ((?in node) (?ll node) (?lr node) (?n Int))
Space (tospace
(or
(exists ((?lr_37 node)(?flted_10_34 node)(?flted_10_35 node))(and 
(= ?flted_10_35 nil)
(= ?flted_10_34 nil)
(= ?in ?ll)
(= ?n 1)
(= ?lr_37 ?lr)
(tobool  
(pto ?in (sref (ref left ?flted_10_35) (ref right ?flted_10_34) (ref next ?lr_37) ))
 )
))(exists ((?ll_38 node)(?z_39 node)(?lr_40 node)(?flted_11_36 node))(and 
(= ?flted_11_36 nil)
(= ?n (+ (+ 1 ?n1) ?n2))
(= ?ll_38 ?ll)
(= ?z_39 ?z)
(= ?lr_40 ?lr)
(tobool (ssep 
(pto ?in (sref (ref left ?l) (ref right ?r) (ref next ?flted_11_36) ))
(tll ?l ?ll_38 ?z ?n1)
(tll ?r ?z_39 ?lr_40 ?n2)
) )
)))))























(declare-fun tprm () node)
(declare-fun xprm () node)
(declare-fun flted11 () node)
(declare-fun n12 () Int)
(declare-fun n11 () Int)
(declare-fun r5 () node)
(declare-fun n13 () Int)
(declare-fun n10 () Int)
(declare-fun l3 () node)
(declare-fun v12prm () node)
(declare-fun l_1123 () node)
(declare-fun l_1122 () node)
(declare-fun n () Int)
(declare-fun t () node)
(declare-fun x () node)
(declare-fun res () node)


(assert 
(exists ((lprm node))(and 
;lexvar(not )(= tprm t)
(= xprm x)
(= n (+ (+ 1 n10) n11))
(= flted11 nil)
(= n12 n11)
(distinct r5 nil)
(= n13 n10)
(distinct l3 nil)
(= res v12prm)
(tobool (ssep 
(pto xprm (sref (ref left l3) (ref right r5) (ref next flted11) ))
(tll r5 lprm tprm n12)
(tll l3 v12prm lprm n13)
) )
))
)

(assert (not 
(exists ((t6 node)(n14 Int))(and 
(= n14 n)
(= t6 t)
(distinct x nil)
(tobool  
(tll x res t6 n14)
 )
))
))

(check-sat)