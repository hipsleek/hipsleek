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
(declare-fun xsnext3 () node)
(declare-fun xs5 () node)
(declare-fun xs () node)
(declare-fun d3 () Int)
(declare-fun sm9 () Int)
(declare-fun bg8 () Int)
(declare-fun bg7 () Int)
(declare-fun flted10 () Int)
(declare-fun b10 () Int)
(declare-fun n3 () Int)
(declare-fun tmp2 () node)
(declare-fun sm10 () Int)
(declare-fun qmin2 () Int)
(declare-fun a5 () Int)
(declare-fun sm12 () Int)
(declare-fun bg10 () Int)
(declare-fun n5 () Int)
(declare-fun smres5 () Int)
(declare-fun bgres5 () Int)
(declare-fun flted12_4136 () Int)
(declare-fun nn () Int)
(declare-fun s0 () Int)
(declare-fun b0 () Int)
(declare-fun xsnext7 () node)
(declare-fun m () Int)
(declare-fun s2 () Int)
(declare-fun b2 () Int)
(declare-fun tmp_4137 () node)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(exists ((flted12 Int)(tmpprm Int)(bprm boolean))(and 
;lexvar(= qmin2 s2)
(= qmin2 b2)
(= m 1)
(distinct xsnext3 nil)
(= (+ flted10 1) n)
(<= sm d3)
(< d3 bg)
(= sm9 sm)
(= bg7 bg)
(distinct xs5 nil)
(< 0 n)
(= xs5 xs)
(= qmin2 d3)
(= n3 flted10)
(= sm10 sm9)
(= bg8 bg7)
(<= 0 flted10)
(= n3 (+ b10 a5))
(<= 0 n3)
(= tmp2 nil)
(= n5 a5)
(= sm12 sm10)
(= bg10 qmin2)
(<= 0 a5)
(<= sm12 smres5)
(< bgres5 bg10)
(<= 0 n5)
(= nn n5)
(= s0 smres5)
(= b0 bgres5)
(<= 1 n5)
(<= smres5 bgres5)
(= flted12 (+ m nn))
(<= 1 nn)
(<= s0 b0)
(distinct xsnext7 nil)
(<= 1 m)
(<= s2 b2)
(distinct tmpprm nil)
(tobool (ssep 
(sll xsprm flted12 s0 b2)
(bnd tmp2 b10 qmin2 bg8)
(pto xs5 (sref (ref val d3) (ref next xsnext7) ))
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