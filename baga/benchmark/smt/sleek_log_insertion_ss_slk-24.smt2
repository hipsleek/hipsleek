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
(exists ((?sm_25 Int)(?flted_14_23 node))(and 
(= ?flted_14_23 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_25 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_25) (ref next ?flted_14_23) ))
 )
))(exists ((?sm_26 Int)(?lg_27 Int)(?flted_15_24 Int))(and 
(= (+ ?flted_15_24 1) ?n)
(distinct ?q nil)
(<= ?sm ?qs)
(= ?sm_26 ?sm)
(= ?lg_27 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_26) (ref next ?q) ))
(sll ?q ?flted_15_24 ?qs ?lg_27)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_30 Int)(?bg_31 Int)(?flted_10_29 Int))(and 
(= (+ ?flted_10_29 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
(= ?sm_30 ?sm)
(= ?bg_31 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_10_29 ?sm_30 ?bg_31)
) )
)))))






































(declare-fun xn_837 () node)
(declare-fun next () node)
(declare-fun lres2 () Int)
(declare-fun sres2 () Int)
(declare-fun flted6 () Int)
(declare-fun xl1 () Int)
(declare-fun xs1 () Int)
(declare-fun n1 () Int)
(declare-fun flted3 () Int)
(declare-fun qs1 () NUM)
(declare-fun lg2 () NUM)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun sm4 () Int)
(declare-fun vprm () Int)
(declare-fun q1 () node)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun n () Int)


(assert 
(exists ((xnprm node))(and 
;lexvar(= res xprm)
(= next q1)
(<= xs1 xl1)
(<= 1 n1)
;eqmax;eqmin(= flted6 (+ 1 n1))
(<= qs1 lg2)
(<= 1 flted3)
(= xl1 lg2)
(= xs1 qs1)
(= n1 flted3)
(= (+ flted3 1) n)
(<= xs qs1)
(= sm4 xs)
(= lg2 xl)
(= xprm x)
(= vprm v)
(< 0 n)
(< sm4 vprm)
(distinct q1 nil)
(tobool (ssep 
(sll xnprm flted6 sres2 lres2)
(pto xprm (sref (ref val sm4) (ref next xnprm) ))
) )
))
)

(assert (not 
(exists ((flted5 Int)(sres1 Int)(lres1 Int))(and 
;eqmax;eqmin(= flted5 (+ 1 n))
(<= xs xl)
(<= 1 n)
(tobool  
(sll res flted5 sres1 lres1)
 )
))
))

(check-sat)