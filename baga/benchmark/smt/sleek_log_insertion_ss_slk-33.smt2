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






































(declare-fun p1 () node)
(declare-fun yprm () node)
(declare-fun lres3_1177 () Int)
(declare-fun sres3_1176 () Int)
(declare-fun flted9_1175 () Int)
(declare-fun xl () Int)
(declare-fun xs () Int)
(declare-fun sm2 () Int)
(declare-fun n () Int)
(declare-fun n2 () Int)
(declare-fun x () node)
(declare-fun y1 () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun bg2 () Int)
(declare-fun sm6 () Int)
(declare-fun bg1 () Int)
(declare-fun sm1 () Int)
(declare-fun d1 () Int)
(declare-fun flted8 () Int)
(declare-fun n1 () Int)


(assert 
(exists ((flted9 Int)(sres3 Int)(lres3 Int))(and 
;lexvar(<= xs xl)
(<= 1 n)
;eqmax;eqmin(= flted9 (+ 1 n))
(<= sm2 bg2)
(<= 1 n2)
(= xl bg2)
(= xs sm2)
(= n n2)
(= xprm x)
(= y1 y)
(distinct xprm nil)
(= bg2 bg1)
(= sm6 sm1)
(< d1 bg1)
(<= sm1 d1)
(= (+ flted8 1) n1)
(tobool (ssep 
(bnd p1 flted8 sm6 bg2)
(pto xprm (sref (ref val d1) (ref next p1) ))
(sll yprm flted9 sres3 lres3)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val6prm) (ref next next6prm) ))
 )
)
))

(check-sat)