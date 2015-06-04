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
























































































(declare-fun tmp1_1346 () node)
(declare-fun v7prm () node)
(declare-fun xsprm () node)
(declare-fun xsnext1 () node)
(declare-fun a2 () Int)
(declare-fun b7 () Int)
(declare-fun bg3 () Int)
(declare-fun sm5 () Int)
(declare-fun n1 () Int)
(declare-fun xs () node)
(declare-fun xs1 () node)
(declare-fun bg2 () Int)
(declare-fun sm4 () Int)
(declare-fun flted8 () Int)
(declare-fun c_1347 () Int)
(declare-fun cprm () Int)
(declare-fun d1_1348 () Int)
(declare-fun d1 () Int)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun c () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(exists ((tmp1prm node))(and 
;lexvar(= res v7prm)
(= xsprm xsnext1)
(<= 0 n1)
(= n1 (+ b7 a2))
(<= 0 flted8)
(= bg3 bg2)
(= sm5 sm4)
(= n1 flted8)
(= xs1 xs)
(= cprm c)
(<= sm c)
(<= c bg)
(distinct xs1 nil)
(= bg2 bg)
(= sm4 sm)
(< d1 bg)
(<= sm d1)
(= (+ flted8 1) n)
(<= cprm d1)
(tobool (ssep 
(bnd tmp1prm b7 cprm bg3)
(bnd xsnext1 a2 sm5 cprm)
(pto xs1 (sref (ref val d1) (ref next xsnext1) ))
(pto v7prm (sref (ref val d1) (ref next tmp1prm) ))
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