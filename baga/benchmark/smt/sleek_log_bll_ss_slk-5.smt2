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






(declare-fun v1prm () node)
(declare-fun v2prm () Int)
(declare-fun v () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun sm () Int)
(declare-fun bg () Int)


(assert 
(and 
;lexvar(= res v1prm)
(<= v bg)
(<= sm v)
(= v2prm v)
(= xprm x)
(tobool (ssep 
(bndl x n sm bg)
(pto v1prm (sref (ref val v2prm) (ref next xprm) ))
) )
)
)

(assert (not 
(exists ((sm4 Int)(bg4 Int)(flted3 Int))(and 
(= bg4 bg)
(= sm4 sm)
(= flted3 (+ 1 n))
(<= 0 n)
(<= sm bg)
(tobool  
(bndl res flted3 sm4 bg4)
 )
))
))

(check-sat)