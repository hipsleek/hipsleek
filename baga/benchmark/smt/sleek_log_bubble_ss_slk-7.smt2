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
























































































(declare-fun Anon_190 () Int)
(declare-fun r_191 () node)
(declare-fun flted_189 () Int)
(declare-fun xsprm () node)
(declare-fun xs () node)
(declare-fun n () Int)


(assert 
(exists ((flted Int)(Anon Int)(r node))(and 
;lexvar(= (+ flted 1) n)
(= xsprm xs)
(< 0 n)
(tobool (ssep 
(pto xsprm (sref (ref val Anon) (ref next r) ))
(ll r flted)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)