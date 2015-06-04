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
























































































(declare-fun xsnext_1452 () node)
(declare-fun d1 () Int)
(declare-fun xsprm () node)
(declare-fun xs () node)
(declare-fun sm6 () Int)
(declare-fun sm4 () Int)
(declare-fun bg4 () Int)
(declare-fun bg2 () Int)
(declare-fun flted8 () Int)
(declare-fun a3_1450 () Int)
(declare-fun b8_1451 () Int)
(declare-fun n2 () Int)
(declare-fun c_1453 () Int)
(declare-fun cprm () Int)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun c () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(exists ((a3 Int)(b8 Int)(xsnextprm node))(and 
;lexvar(< d1 cprm)
(= (+ flted8 1) n)
(<= sm d1)
(< d1 bg)
(= sm4 sm)
(= bg2 bg)
(distinct xsprm nil)
(<= c bg)
(<= sm c)
(= cprm c)
(= xsprm xs)
(= n2 flted8)
(= sm6 sm4)
(= bg4 bg2)
(<= 0 flted8)
(= n2 (+ b8 a3))
(<= 0 n2)
(tobool (ssep 
(bnd res b8 cprm bg4)
(bnd xsnextprm a3 sm6 cprm)
(pto xsprm (sref (ref val d1) (ref next xsnextprm) ))
) )
))
)

(assert (not 
(exists ((sm7 Int)(c1 Int)(c2 Int)(bg5 Int)(a1 Int)(b6 Int))(and 
(= bg5 bg)
(= c2 c)
(= c1 c)
(= sm7 sm)
(= n (+ b6 a1))
(<= 0 n)
(tobool (ssep 
(bnd xsprm a1 sm7 c1)
(bnd res b6 c2 bg5)
) )
))
))

(check-sat)