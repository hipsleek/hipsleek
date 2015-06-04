(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun sll ((?in node) (?n Int) (?sm Int) (?lg Int))
Space (tospace
(or
(exists ((?sm_25 Int)(?flted_14_23 node))(and 
(= ?flted_14_23 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_25 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_25) (ref next ?flted_14_23) ))
 )
))(exists ((?sm_26 Int)(?lg_27 Int)(?flted_15_24 Int))(and 
(= (+ ?flted_15_24 1) ?n)
(distinct ?q nil)
(<= ?sm ?qs)
(= ?sm_26 ?sm)
(= ?lg_27 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_26) (ref next ?q) ))
(sll ?q ?flted_15_24 ?qs ?lg_27)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_30 Int)(?bg_31 Int)(?flted_10_29 Int))(and 
(= (+ ?flted_10_29 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
(= ?sm_30 ?sm)
(= ?bg_31 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_10_29 ?sm_30 ?bg_31)
) )
)))))






































(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun bg1 () Int)
(declare-fun sm1 () Int)
(declare-fun sm2 () Int)
(declare-fun bg2 () Int)
(declare-fun n2 () Int)
(declare-fun n1 () Int)


(assert 
(and 
;lexvar(= xprm x)
(= yprm y)
(= xprm nil)
(tobool (ssep 
(bnd x n1 sm1 bg1)
(sll y n2 sm2 bg2)
) )
)
)

(assert (not 
(exists ((n4 Int)(sm10 Int)(bg6 Int)(flted12 Int)(sm11 Int)(bg7 Int))(and 
(= bg6 bg1)
(= sm10 sm1)
(= n4 n1)
(<= bg2 bg7)
(<= sm11 sm2)
(= flted12 (+ n2 n1))
(<= sm2 bg2)
(<= 1 n2)
(<= 0 n1)
(tobool (ssep 
(sll yprm flted12 sm11 bg7)
(bnd x n4 sm10 bg6)
) )
))
))

(check-sat)