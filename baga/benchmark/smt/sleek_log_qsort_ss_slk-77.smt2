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
























































































(declare-fun tmpprm () node)
(declare-fun xsnext5_3246 () node)
(declare-fun bgres3_3245 () Int)
(declare-fun smres3_3244 () Int)
(declare-fun bg10 () Int)
(declare-fun sm12 () Int)
(declare-fun n5 () Int)
(declare-fun tmp2 () node)
(declare-fun a5 () Int)
(declare-fun b10 () Int)
(declare-fun bg8 () Int)
(declare-fun sm10 () Int)
(declare-fun n3 () Int)
(declare-fun xs () node)
(declare-fun xsprm () node)
(declare-fun bg7 () Int)
(declare-fun sm9 () Int)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun d3 () Int)
(declare-fun flted10 () Int)
(declare-fun n () Int)
(declare-fun xsnext3 () node)
(declare-fun v5_3247 () Int)
(declare-fun v5prm () Int)


(assert 
(exists ((smres3 Int)(bgres3 Int)(xsnext5 node))(and 
;lexvar(<= 0 n5)
(< bgres3 bg10)
(<= sm12 smres3)
(<= 0 a5)
(= bg10 v5prm)
(= sm12 sm10)
(= n5 a5)
(= tmp2 nil)
(<= 0 n3)
(= n3 (+ b10 a5))
(<= 0 flted10)
(= bg8 bg7)
(= sm10 sm9)
(= n3 flted10)
(= v5prm d3)
(= xsprm xs)
(< 0 n)
(distinct xsprm nil)
(= bg7 bg)
(= sm9 sm)
(< d3 bg)
(<= sm d3)
(= (+ flted10 1) n)
(distinct xsnext3 nil)
(tobool (ssep 
(pto tmpprm (sref (ref val v5prm) (ref next tmp2) ))
(bnd tmp2 b10 v5prm bg8)
(sll xsnext5 n5 smres3 bgres3)
(pto xsprm (sref (ref val d3) (ref next xsnext5) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val7prm) (ref next next7prm) ))
 )
)
))

(check-sat)