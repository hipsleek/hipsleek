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

(define-fun bndl ((?in node) (?n Int) (?sm NUM) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(<= ?sm ?bg)

)(exists ((?sm_23 Int)(?bg_24 Int)(?flted_11_22 Int))(and 
(= (+ ?flted_11_22 1) ?n)
(<= ?sm ?d)
(<= ?d ?bg)
(= ?sm_23 ?sm)
(= ?bg_24 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bndl ?p ?flted_11_22 ?sm_23 ?bg_24)
) )
)))))






(declare-fun vprm () node)
(declare-fun p1 () node)
(declare-fun flted1 () Int)
(declare-fun d1 () Int)
(declare-fun sm2 () Int)
(declare-fun bg2 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun sm () Int)
(declare-fun bg () Int)


(assert 
(and 
;lexvar(= res vprm)
(= vprm p1)
(= (+ flted1 1) n)
(<= sm d1)
(<= d1 bg)
(= sm2 sm)
(= bg2 bg)
(= xprm x)
(distinct x nil)
(tobool (ssep 
(pto xprm (sref (ref val d1) (ref next p1) ))
(bndl p1 flted1 sm2 bg2)
) )
)
)

(assert (not 
(exists ((sm3 Int)(bg3 Int)(flted2 Int))(and 
(= bg3 bg)
(= sm3 sm)
(= (+ flted2 1) n)
(<= 0 n)
(<= sm bg)
(tobool  
(bndl res flted2 sm3 bg3)
 )
))
))

(check-sat)