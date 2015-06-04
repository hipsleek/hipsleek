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
(exists ((?sm_35 Int)(?flted_9_33 node))(and 
(= ?flted_9_33 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_35 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_35) (ref next ?flted_9_33) ))
 )
))(exists ((?sm_36 Int)(?lg_37 Int)(?flted_10_34 Int))(and 
(= (+ ?flted_10_34 1) ?n)
(distinct ?q nil)
(<= ?sm ?qs)
(= ?sm_36 ?sm)
(= ?lg_37 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_36) (ref next ?q) ))
(sll ?q ?flted_10_34 ?qs ?lg_37)
) )
)))))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_19_26 Int))(and 
(= (+ ?flted_19_26 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?r) ))
(ll ?r ?flted_19_26)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_29 Int)(?bg_30 Int)(?flted_15_28 Int))(and 
(= (+ ?flted_15_28 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
(= ?sm_29 ?sm)
(= ?bg_30 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_15_28 ?sm_29 ?bg_30)
) )
)))))
























































































(declare-fun v10_2806 () node)
(declare-fun next () node)
(declare-fun lg5 () NUM)
(declare-fun sm9 () NUM)
(declare-fun n7 () Int)
(declare-fun flted11 () Int)
(declare-fun qs3 () NUM)
(declare-fun sm8 () Int)
(declare-fun lg4 () NUM)
(declare-fun xsprm () node)
(declare-fun xs () node)
(declare-fun q3 () node)
(declare-fun res () node)
(declare-fun sm () NUM)
(declare-fun lg () NUM)
(declare-fun n () Int)


(assert 
(exists ((v10prm node))(and 
;lexvar(= res xsprm)
(= next q3)
(<= sm9 lg5)
(<= 1 n7)
(<= qs3 lg4)
(<= 1 flted11)
(= lg5 lg4)
(= sm9 qs3)
(= n7 flted11)
(= (+ flted11 1) n)
(<= sm qs3)
(= sm8 sm)
(= lg4 lg)
(= xsprm xs)
(distinct q3 nil)
(tobool (ssep 
(ll v10prm n7)
(pto xsprm (sref (ref val sm8) (ref next v10prm) ))
) )
))
)

(assert (not 
(exists ((n8 Int))(and 
(= n8 n)
(<= sm lg)
(<= 1 n)
(tobool  
(ll res n8)
 )
))
))

(check-sat)