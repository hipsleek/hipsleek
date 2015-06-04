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

























































































(declare-fun n1 () Int)
(declare-fun s1 () Int)
(declare-fun b1 () Int)
(declare-fun q2_1367 () node)
(declare-fun x1 () node)
(declare-fun x2 () node)
(declare-fun x2prm () node)
(declare-fun x1prm () node)
(declare-fun lg3_1365 () Int)
(declare-fun b2 () Int)
(declare-fun sm10_1364 () Int)
(declare-fun s2 () Int)
(declare-fun qs2_1368 () Int)
(declare-fun flted10_1366 () Int)
(declare-fun n2 () Int)


(assert 
(exists ((sm10 Int)(lg3 Int)(flted10 Int)(q2 node)(qs2 Int))(and 
;lexvar(= x1prm x1)
(= x2prm x2)
(distinct x2prm nil)
(distinct x1prm nil)
(= lg3 b2)
(= sm10 s2)
(<= s2 qs2)
(= (+ flted10 1) n2)
(tobool (ssep 
(sll x1 n1 s1 b1)
(pto x2prm (sref (ref val sm10) (ref next q2) ))
(sll q2 flted10 qs2 lg3)
) )
))
)

(assert (not 
(and 
(tobool  
(pto x2prm (sref (ref val val6prm) (ref next next6prm) ))
 )
)
))

(check-sat)