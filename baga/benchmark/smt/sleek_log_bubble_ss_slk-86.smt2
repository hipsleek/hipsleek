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
























































































(declare-fun xprm () node)
(declare-fun sm13 () Int)
(declare-fun q5 () node)
(declare-fun flted15 () Int)
(declare-fun qs5 () Int)
(declare-fun lg7 () Int)
(declare-fun n9 () Int)
(declare-fun sm14 () Int)
(declare-fun lg8 () Int)
(declare-fun x () node)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xprm x)
(= lg7 lg)
(= sm13 sm)
(<= sm qs5)
(distinct q5 nil)
(= (+ flted15 1) n)
(= n9 flted15)
(= sm14 qs5)
(= lg8 lg7)
(<= 1 flted15)
(<= qs5 lg7)
(<= 1 n9)
(<= sm14 lg8)
(tobool (ssep 
(pto xprm (sref (ref val sm13) (ref next q5) ))
(ll q5 n9)
) )
)
)

(assert (not 
(exists ((n10 Int))(and 
(= n10 n)
(<= sm lg)
(<= 1 n)
(tobool  
(ll x n10)
 )
))
))

(check-sat)