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
























































































(declare-fun m () Int)
(declare-fun b2 () Int)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun s2 () Int)
(declare-fun xprm () node)
(declare-fun nn () Int)
(declare-fun b0 () Int)
(declare-fun qmin_260 () Int)
(declare-fun s0 () Int)
(declare-fun flted_259 () node)


(assert 
(exists ((flted node)(qmin Int))(and 
;lexvar(= xprm x)
(= yprm y)
(<= b0 s2)
(distinct xprm nil)
(= nn 1)
(= qmin b0)
(= qmin s0)
(= flted nil)
(tobool (ssep 
(pto xprm (sref (ref val qmin) (ref next flted) ))
(sll y m s2 b2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)