(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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

























































































(declare-fun tmpprm () node)
(declare-fun x2prm () node)
(declare-fun x1 () node)
(declare-fun sm12 () Int)
(declare-fun n () Int)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun x2 () node)
(declare-fun flted12 () Int)
(declare-fun qs3 () Int)
(declare-fun lg4 () Int)
(declare-fun flted16 () Int)
(declare-fun sres6 () Int)
(declare-fun lres6 () Int)
(declare-fun flted17_2052 () Int)
(declare-fun s2_2053 () Int)
(declare-fun b2_2054 () Int)
(declare-fun n4 () Int)
(declare-fun s () Int)
(declare-fun b () Int)
(declare-fun x1prm () node)
(declare-fun n5 () Int)
(declare-fun s1 () Int)
(declare-fun q3 () node)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun n1 () Int)
(declare-fun n2 () Int)


(assert 
(exists ((flted17 Int)(s2 Int)(b2 Int))(and 
;lexvar(= (+ flted12 1) n2)
(<= s2 qs3)
(= sm12 s2)
(= lg4 b2)
(distinct x2prm nil)
(= x2prm x2)
(= x2 x1)
(= n n1)
(= xs s1)
(= xl b1)
(<= 1 n1)
(<= s1 b1)
(distinct x1 nil)
(= flted16 (+ 1 n))
;eqmin;eqmax(<= 1 n)
(<= xs xl)
(distinct x2 nil)
(= n4 flted16)
(= s sres6)
(= b lres6)
(= n5 flted12)
(= s1 qs3)
(= b1 lg4)
(<= 1 flted12)
(<= qs3 lg4)
(<= 1 flted16)
(<= sres6 lres6)
(= flted17 (+ n5 n4))
;eqmin;eqmax(<= 1 n4)
(<= s b)
(distinct x1prm nil)
(<= 1 n5)
(<= s1 b1)
(distinct q3 nil)
(tobool (ssep 
(sll tmpprm flted17 s2 b2)
(pto x2prm (sref (ref val sm12) (ref next q3) ))
) )
))
)

(assert (not 
(exists ((flted18 Int)(flted19 Int))(and 
;eqmax(= flted19 (+ n2 n1))
(tobool  
(sll tmpprm flted19 Anon flted18)
 )
))
))

(check-sat)