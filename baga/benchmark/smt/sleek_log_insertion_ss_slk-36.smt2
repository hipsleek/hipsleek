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
(declare-fun p1 () node)
(declare-fun y1 () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun d1 () Int)
(declare-fun n () Int)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun sm7 () Int)
(declare-fun sm6 () Int)
(declare-fun bg3 () Int)
(declare-fun flted10 () Int)
(declare-fun sres4 () Int)
(declare-fun lres4 () Int)
(declare-fun flted8 () Int)
(declare-fun flted11_1331 () Int)
(declare-fun sm9_1332 () Int)
(declare-fun bg5_1333 () Int)
(declare-fun n3 () Int)
(declare-fun sm8 () Int)
(declare-fun bg4 () Int)
(declare-fun x () node)
(declare-fun bg1 () Int)
(declare-fun sm1 () Int)
(declare-fun sm2 () Int)
(declare-fun bg2 () Int)
(declare-fun n2 () Int)
(declare-fun n1 () Int)


(assert 
(exists ((flted11 Int)(sm9 Int)(bg5 Int))(and 
;lexvar(= (+ flted8 1) n1)
(<= sm1 d1)
(< d1 bg1)
(= sm6 sm1)
(= bg2 bg1)
(distinct xprm nil)
(= y1 y)
(= xprm x)
(= n n2)
(= xs sm2)
(= xl bg2)
(<= 1 n2)
(<= sm2 bg2)
(= flted10 (+ 1 n))
;eqmin;eqmax(<= 1 n)
(<= xs xl)
(= n2 flted8)
(= sm7 sm6)
(= bg3 bg2)
(= n3 flted10)
(= sm8 sres4)
(= bg4 lres4)
(<= 1 flted10)
(<= sres4 lres4)
(<= 0 flted8)
(= flted11 (+ n3 n2))
(<= sm9 sm8)
(<= bg4 bg5)
(<= 0 n2)
(<= 1 n3)
(<= sm8 bg4)
(tobool (ssep 
(sll yprm flted11 sm9 bg5)
(pto xprm (sref (ref val d1) (ref next p1) ))
(bnd p1 n2 sm7 bg3)
) )
))
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