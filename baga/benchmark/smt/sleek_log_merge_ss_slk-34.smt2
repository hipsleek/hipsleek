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
(exists ((?sm_28 Int)(?flted_21_26 node))(and 
(= ?flted_21_26 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_28 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_28) (ref next ?flted_21_26) ))
 )
))(exists ((?sm_29 Int)(?lg_30 Int)(?flted_22_27 Int))(and 
(= (+ ?flted_22_27 1) ?n)
(<= ?sm ?qs)
(= ?sm_29 ?sm)
(= ?lg_30 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_29) (ref next ?q) ))
(sll ?q ?flted_22_27 ?qs ?lg_30)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_33 Int)(?bg_34 Int)(?flted_9_32 Int))(and 
(= (+ ?flted_9_32 1) ?n)
(<= ?sm ?d)
(<= ?d ?bg)
(= ?sm_33 ?sm)
(= ?bg_34 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_9_32 ?sm_33 ?bg_34)
) )
)))))

























































































(declare-fun q1 () node)
(declare-fun v14prm () node)
(declare-fun flted5 () Int)
(declare-fun qs1 () Int)
(declare-fun lg2 () Int)
(declare-fun xprm () node)
(declare-fun v6prm () Int)
(declare-fun sm8 () Int)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun x () node)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v14prm)
(= (+ flted5 1) n)
(<= xs qs1)
(= sm8 xs)
(= lg2 xl)
(= xprm x)
(= v6prm v)
(< 0 n)
(<= v6prm sm8)
(tobool (ssep 
(sll q1 flted5 qs1 lg2)
(pto xprm (sref (ref val sm8) (ref next q1) ))
(pto v14prm (sref (ref val v6prm) (ref next xprm) ))
) )
)
)

(assert (not 
(exists ((flted7 Int)(sres1 Int)(lres1 Int))(and 
;eqmax;eqmin(= flted7 (+ 1 n))
(distinct x nil)
(<= xs xl)
(<= 1 n)
(tobool  
(sll res flted7 sres1 lres1)
 )
))
))

(check-sat)