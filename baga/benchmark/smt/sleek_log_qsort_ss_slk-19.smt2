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
























































































(declare-fun xnprm () node)
(declare-fun q1 () node)
(declare-fun flted4_598 () Int)
(declare-fun b2 () Int)
(declare-fun s3 () Int)
(declare-fun m3 () Int)
(declare-fun m () Int)
(declare-fun b3 () Int)
(declare-fun nn1 () Int)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun s2 () Int)
(declare-fun xprm () node)
(declare-fun lg2 () NUM)
(declare-fun b0 () Int)
(declare-fun sm2 () Int)
(declare-fun s0 () Int)
(declare-fun qs1 () Int)
(declare-fun flted3 () Int)
(declare-fun nn () Int)


(assert 
(exists ((flted4 Int))(and 
;lexvar(distinct yprm nil)
(<= s3 b2)
(<= 1 m3)
(distinct q1 nil)
(<= s2 b3)
(<= 1 nn1)
(= flted4 (+ m3 nn1))
(<= qs1 lg2)
(<= 1 flted3)
(distinct y nil)
(<= s2 b2)
(<= 1 m)
(= b2 b2)
(= s3 s2)
(= m3 m)
(= b3 lg2)
(= s2 qs1)
(= nn1 flted3)
(= xprm x)
(= yprm y)
(<= b0 s2)
(distinct xprm nil)
(= lg2 b0)
(= sm2 s0)
(<= s0 qs1)
(= (+ flted3 1) nn)
(tobool (ssep 
(sll xnprm flted4 s2 b2)
(pto xprm (sref (ref val sm2) (ref next q1) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref next next1prm) ))
 )
)
))

(check-sat)