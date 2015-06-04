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
























































































(declare-fun tmp1prm () node)
(declare-fun xsnext_1139 () node)
(declare-fun a_1137 () Int)
(declare-fun b5_1138 () Int)
(declare-fun bg3 () Int)
(declare-fun sm5 () Int)
(declare-fun n1 () Int)
(declare-fun v5prm () Int)
(declare-fun xs () node)
(declare-fun c () Int)
(declare-fun xsprm () node)
(declare-fun bg2 () Int)
(declare-fun sm4 () Int)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun flted8 () Int)
(declare-fun n () Int)
(declare-fun d1 () Int)
(declare-fun c_1140 () Int)
(declare-fun cprm () Int)


(assert 
(exists ((a Int)(b5 Int)(xsnext node))(and 
;lexvar(<= 0 n1)
(= n1 (+ b5 a))
(<= 0 flted8)
(= bg3 bg2)
(= sm5 sm4)
(= n1 flted8)
(= v5prm d1)
(= xsprm xs)
(= cprm c)
(<= sm c)
(<= c bg)
(distinct xsprm nil)
(= bg2 bg)
(= sm4 sm)
(< d1 bg)
(<= sm d1)
(= (+ flted8 1) n)
(<= cprm d1)
(tobool (ssep 
(bnd tmp1prm b5 cprm bg3)
(bnd xsnext a sm5 cprm)
(pto xsprm (sref (ref val d1) (ref next xsnext) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val4prm) (ref next next4prm) ))
 )
)
))

(check-sat)