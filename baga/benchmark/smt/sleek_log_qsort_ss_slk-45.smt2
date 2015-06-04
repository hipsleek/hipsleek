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
(exists ((?flted_13_23 node))(and 
(= ?flted_13_23 nil)
(= ?qmin ?sm)
(= ?qmin ?lg)
(= ?n 1)
(tobool  
(pto ?in (sref (ref val ?qmin) (ref next ?flted_13_23) ))
 )
))(exists ((?sm_25 Int)(?lg_26 Int)(?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(<= ?sm ?qs)
(= ?sm_25 ?sm)
(= ?lg_26 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_25) (ref next ?q) ))
(sll ?q ?flted_14_24 ?qs ?lg_26)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_29 Int)(?bg_30 Int)(?flted_9_28 Int))(and 
(= (+ ?flted_9_28 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
(= ?sm_29 ?sm)
(= ?bg_30 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_9_28 ?sm_29 ?bg_30)
) )
)))))
























































































(declare-fun p2_1604 () node)
(declare-fun xs () node)
(declare-fun xsprm () node)
(declare-fun bg6_1601 () Int)
(declare-fun sm8_1600 () Int)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun d2_1603 () Int)
(declare-fun flted9_1602 () Int)
(declare-fun n () Int)


(assert 
(exists ((sm8 Int)(bg6 Int)(flted9 Int)(d2 Int)(p2 node))(and 
;lexvar(= xsprm xs)
(< 0 n)
(distinct xsprm nil)
(= bg6 bg)
(= sm8 sm)
(< d2 bg)
(<= sm d2)
(= (+ flted9 1) n)
(tobool (ssep 
(bnd p2 flted9 sm8 bg6)
(pto xsprm (sref (ref val d2) (ref next p2) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val5prm) (ref next next5prm) ))
 )
)
))

(check-sat)