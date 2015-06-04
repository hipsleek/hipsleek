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
(declare-fun tmp4 () node)
(declare-fun tmp5_3838 () node)
(declare-fun a5 () Int)
(declare-fun sm10 () Int)
(declare-fun n3 () Int)
(declare-fun xs () node)
(declare-fun xs2 () node)
(declare-fun bg7 () Int)
(declare-fun sm9 () Int)
(declare-fun d3 () Int)
(declare-fun flted10 () Int)
(declare-fun xsnext3 () node)
(declare-fun bg8 () Int)
(declare-fun b10 () Int)
(declare-fun smres6_3836 () Int)
(declare-fun bgres6_3837 () Int)
(declare-fun bg9 () Int)
(declare-fun n4 () Int)
(declare-fun sm11_3840 () Int)
(declare-fun sm11 () Int)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(exists ((smres6 Int)(bgres6 Int)(tmp5 Int)(bprm boolean))(and 
;lexvar(distinct tmp5 nil)
(<= 0 n3)
(= n3 (+ b10 a5))
(<= 0 flted10)
(= bg8 bg7)
(= sm10 sm9)
(= n3 flted10)
(= sm11 d3)
(= xs2 xs)
(< 0 n)
(distinct xs2 nil)
(= bg7 bg)
(= sm9 sm)
(< d3 bg)
(<= sm d3)
(= (+ flted10 1) n)
(= xsnext3 nil)
(= n4 b10)
(= bg9 bg8)
(<= 0 b10)
(<= sm11 smres6)
(< bgres6 bg9)
(<= 0 n4)
(tobool (ssep 
(pto xsprm (sref (ref val sm11) (ref next tmp4) ))
(sll tmp4 n4 smres6 bgres6)
(bnd xsnext3 a5 sm10 sm11)
(pto xs2 (sref (ref val d3) (ref next xsnext3) ))
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