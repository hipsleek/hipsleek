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
























































































(declare-fun v6prm () node)
(declare-fun xs () node)
(declare-fun cprm () Int)
(declare-fun xsprm () node)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun c () Int)
(declare-fun sm () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v6prm)
(= v6prm nil)
(= xsprm xs)
(= cprm c)
(<= sm c)
(<= c bg)
(= xsprm nil)
(tobool  
(bnd xs n sm bg)
 )
)
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