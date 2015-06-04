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
























































































(declare-fun xsprm () node)
(declare-fun qs2 () NUM)
(declare-fun q2 () node)
(declare-fun bg9 () Int)
(declare-fun sm11 () NUM)
(declare-fun xsnext3 () node)
(declare-fun xs3 () node)
(declare-fun xs () node)
(declare-fun d3 () Int)
(declare-fun sm9 () Int)
(declare-fun bg8 () Int)
(declare-fun bg7 () Int)
(declare-fun flted10 () Int)
(declare-fun b10 () Int)
(declare-fun n3 () Int)
(declare-fun tmp3 () node)
(declare-fun sm10 () Int)
(declare-fun a5 () Int)
(declare-fun sm12 () Int)
(declare-fun bg10 () NUM)
(declare-fun n4 () Int)
(declare-fun smres1 () NUM)
(declare-fun bgres1 () Int)
(declare-fun tmp () node)
(declare-fun n5 () Int)
(declare-fun smres4 () Int)
(declare-fun bgres4 () Int)
(declare-fun flted11_3934 () Int)
(declare-fun nn () Int)
(declare-fun s0 () Int)
(declare-fun b0 () Int)
(declare-fun xsnext6 () node)
(declare-fun m () Int)
(declare-fun s2 () NUM)
(declare-fun b2 () Int)
(declare-fun tmp_3935 () node)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(exists ((flted11 Int)(tmpprm Int)(bprm boolean))(and 
;lexvar(= (+ n4 1) m)
(= bgres1 b2)
(<= s2 qs2)
(= qs2 smres1)
(= q2 tmp)
(<= 0 n4)
(< bgres1 bg9)
(<= sm11 smres1)
(<= 0 b10)
(= bg9 bg8)
(= sm11 s2)
(= n4 b10)
(distinct xsnext3 nil)
(= (+ flted10 1) n)
(<= sm d3)
(< d3 bg)
(= sm9 sm)
(= bg7 bg)
(distinct xs3 nil)
(< 0 n)
(= xs3 xs)
(= s2 d3)
(= n3 flted10)
(= sm10 sm9)
(= bg8 bg7)
(<= 0 flted10)
(= n3 (+ b10 a5))
(<= 0 n3)
(distinct tmp3 nil)
(= n5 a5)
(= sm12 sm10)
(= bg10 s2)
(<= 0 a5)
(<= sm12 smres4)
(< bgres4 bg10)
(<= 0 n5)
(= nn n5)
(= s0 smres4)
(= b0 bgres4)
(<= 1 n4)
(<= smres1 bgres1)
(distinct tmp nil)
(<= 1 n5)
(<= smres4 bgres4)
(= flted11 (+ m nn))
(<= 1 nn)
(<= s0 b0)
(distinct xsnext6 nil)
(<= 1 m)
(<= s2 b2)
(distinct tmpprm nil)
(tobool (ssep 
(sll xsprm flted11 s0 b2)
(pto xs3 (sref (ref val d3) (ref next xsnext6) ))
) )
))
)

(assert (not 
(exists ((n6 Int)(smres7 Int)(bgres7 Int))(and 
(= n6 n)
(< bgres7 bg)
(<= sm smres7)
(<= 0 n)
(tobool  
(sll xsprm n6 smres7 bgres7)
 )
))
))

(check-sat)