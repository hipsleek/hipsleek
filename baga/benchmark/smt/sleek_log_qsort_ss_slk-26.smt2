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
























































































(declare-fun p_915 () node)
(declare-fun xs () node)
(declare-fun cprm () NUM)
(declare-fun c () NUM)
(declare-fun xsprm () node)
(declare-fun bg1_912 () Int)
(declare-fun sm3_911 () Int)
(declare-fun bg () Int)
(declare-fun sm () NUM)
(declare-fun d_914 () Int)
(declare-fun flted7_913 () Int)
(declare-fun n () Int)


(assert 
(exists ((sm3 Int)(bg1 Int)(flted7 Int)(d Int)(p node))(and 
;lexvar(= xsprm xs)
(= cprm c)
(<= sm c)
(<= c bg)
(distinct xsprm nil)
(= bg1 bg)
(= sm3 sm)
(< d bg)
(<= sm d)
(= (+ flted7 1) n)
(tobool (ssep 
(bnd p flted7 sm3 bg1)
(pto xsprm (sref (ref val d) (ref next p) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val2prm) (ref next next2prm) ))
 )
)
))

(check-sat)