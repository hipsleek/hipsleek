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
(exists ((?sm_28 Int)(?flted_21_26 node))(and 
(= ?flted_21_26 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_28 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_28) (ref next ?flted_21_26) ))
 )
))(exists ((?sm_29 Int)(?lg_30 Int)(?flted_22_27 Int))(and 
(= (+ ?flted_22_27 1) ?n)
(<= ?sm ?qs)
(= ?sm_29 ?sm)
(= ?lg_30 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_29) (ref next ?q) ))
(sll ?q ?flted_22_27 ?qs ?lg_30)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_33 Int)(?bg_34 Int)(?flted_9_32 Int))(and 
(= (+ ?flted_9_32 1) ?n)
(<= ?sm ?d)
(<= ?d ?bg)
(= ?sm_33 ?sm)
(= ?bg_34 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_9_32 ?sm_33 ?bg_34)
) )
)))))

























































































(declare-fun p6_2776 () node)
(declare-fun flted25_2774 () Int)
(declare-fun d6_2775 () Int)
(declare-fun sm20_2772 () Int)
(declare-fun sm () Int)
(declare-fun bg12_2773 () Int)
(declare-fun bg () Int)
(declare-fun xsprm () node)
(declare-fun xs () node)
(declare-fun n () Int)


(assert 
(exists ((sm20 Int)(bg12 Int)(flted25 Int)(d6 Int)(p6 node))(and 
;lexvar(= (+ flted25 1) n)
(<= sm d6)
(<= d6 bg)
(= sm20 sm)
(= bg12 bg)
(= xsprm xs)
(< 0 n)
(tobool (ssep 
(bnd p6 flted25 sm20 bg12)
(pto xsprm (sref (ref val d6) (ref next p6) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val11prm) (ref next next11prm) ))
 )
)
))

(check-sat)