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






(declare-fun self () __Exc)
(declare-fun n () Int)
(declare-fun sm () NUM)
(declare-fun bg () NUM)


(assert 

)

(assert (not 
(and 
(<= 0 n)
(<= sm bg)

)
))

(check-sat)