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

























































































(declare-fun p4_2462 () node)
(declare-fun aprm () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun a1 () Int)
(declare-fun bg7_2459 () Int)
(declare-fun sm15_2458 () Int)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun d4_2461 () Int)
(declare-fun flted23_2460 () Int)
(declare-fun n () Int)


(assert 
(exists ((sm15 Int)(bg7 Int)(flted23 Int)(d4 Int)(p4 node))(and 
;lexvar(= (+ aprm 1) a1)
(= xprm x)
(= a1 a)
(< 0 a)
(< a n)
(distinct a1 1)
(= bg7 bg)
(= sm15 sm)
(<= d4 bg)
(<= sm d4)
(= (+ flted23 1) n)
(tobool (ssep 
(bnd p4 flted23 sm15 bg7)
(pto xprm (sref (ref val d4) (ref next p4) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val Anon_12prm) (ref next xnextprm) ))
 )
)
))

(check-sat)