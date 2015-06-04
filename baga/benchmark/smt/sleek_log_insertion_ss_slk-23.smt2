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






































(declare-fun v7prm () node)
(declare-fun flted3 () Int)
(declare-fun q1 () node)
(declare-fun qs1 () Int)
(declare-fun lg2 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun vprm () Int)
(declare-fun sm4 () Int)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v7prm)
(= (+ flted3 1) n)
(distinct q1 nil)
(<= xs qs1)
(= sm4 xs)
(= lg2 xl)
(= xprm x)
(= vprm v)
(< 0 n)
(<= vprm sm4)
(tobool (ssep 
(pto xprm (sref (ref val sm4) (ref next q1) ))
(sll q1 flted3 qs1 lg2)
(pto v7prm (sref (ref val vprm) (ref next xprm) ))
) )
)
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